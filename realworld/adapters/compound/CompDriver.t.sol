pragma solidity ^0.5.16;

// Runs operation sequences on Compound's Comptroller, compiled unmodified from
// compound-finance/compound-protocol at the pinned commits, and prints the reward state after
// every operation. Used by eval/realworld_compound.py, which copies the Comptroller sources of
// each commit into src/p62, src/p64 and src/p65 at run time.
//
// Per case: a Unitroller is deployed and its storage is set to the pre-upgrade state (one
// listed market, compSpeeds, compSupplyState, compBorrowState, each account's
// compSupplierIndex, compBorrowerIndex and compAccrued) with the storage slots of the
// Proposal 62 Comptroller, which `forge inspect` reports and the evaluator passes in. The
// market is a mock cToken whose balances the driver sets and whose borrow index is 1e18, so an
// account's borrow units are its borrowBalanceStored. COMP is a mock token placed at the
// address the Comptroller has hard-coded. Then the Proposal 62 implementation is installed
// with _setPendingImplementation and _become, which runs _upgradeSplitCompRewards, as
// Proposal 62 did on mainnet. For COMP_VARIANT p64 or p65 the Proposal 64 or Proposal 65
// implementation is installed next, as those proposals did.
//
// Operations: 0 mint(who, x) calls mintAllowed, 1 redeem(who, x) redeemAllowed, 2 transfer(src,
// dst, x) transferAllowed, 3 borrow(who, x) and 4 repay(who, x) repayBorrowAllowed (borrowAllowed
// runs the same reward code but also needs an oracle and collateral), then the driver changes
// the mock balance; 5 claim(who) claimComp(who, [market]); 6 setSpeeds(a, b) _setCompSpeeds;
// 7 advance(k) rolls k blocks; 8 drip(x) sends x COMP to the Comptroller. An operation is
// refused, and the state rolled back, when a call reverts or returns an error code, or as the
// specification refuses it (an account beyond the list, an amount above the balance, a
// transfer to the same account).
//
// Input (env COMP_CASES): a header line, then one line per case, each the hex of
// abi.encode(uint256[]). Header: [8 storage slots, number of cases]. Case: [n, blockNumber,
// compSpeed, supplyIndex, supplyBlock, borrowIndex, borrowBlock, reserve, then per account
// supply, borrow, supplierIndex, borrowerIndex, accrued, wallet, then the number of
// operations and 4 words per operation (kind, a, b, c)]. Output (env COMP_OUT): per case a
// line "s <state>", a line "o <applied> <state>" per operation and a line "e"; a state is
// blockNumber, supply index, block, speed, borrow index, block, speed, reserve, n and 6 words
// per account.

import {Comptroller as ComptrollerP62} from "../src/p62/Comptroller.sol";
import {Unitroller as UnitrollerP62} from "../src/p62/Unitroller.sol";
import {Comptroller as ComptrollerP64} from "../src/p64/Comptroller.sol";
import {Comptroller as ComptrollerP65} from "../src/p65/Comptroller.sol";

interface Vm {
    function roll(uint256) external;
    function store(address, bytes32, bytes32) external;
    function etch(address, bytes calldata) external;
    function readLine(string calldata) external returns (string memory);
    function writeLine(string calldata, string calldata) external;
    function envString(string calldata) external returns (string memory);
    function parseBytes(string calldata) external returns (bytes memory);
    function toString(uint256) external returns (string memory);
    function snapshotState() external returns (uint256);
    function revertToState(uint256) external returns (bool);
}

contract MockComp {
    mapping(address => uint256) public balanceOf;

    function transfer(address to, uint256 amount) external returns (bool) {
        require(balanceOf[msg.sender] >= amount, "comp: insufficient balance");
        balanceOf[msg.sender] -= amount;
        balanceOf[to] += amount;
        return true;
    }

    function mint(address to, uint256 amount) external {
        balanceOf[to] += amount;
    }
}

contract MockCToken {
    bool public constant isCToken = true;
    uint256 public totalSupply;
    uint256 public totalBorrows;
    uint256 public borrowIndex = 1e18;
    mapping(address => uint256) public balanceOf;
    mapping(address => uint256) public borrows;

    function borrowBalanceStored(address a) external view returns (uint256) {
        return borrows[a];
    }

    function setSupply(address a, uint256 v) external {
        totalSupply = totalSupply - balanceOf[a] + v;
        balanceOf[a] = v;
    }

    function setBorrow(address a, uint256 v) external {
        totalBorrows = totalBorrows - borrows[a] + v;
        borrows[a] = v;
    }
}

contract CompDriver {
    Vm constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    address constant COMP = 0xc00e94Cb662C3520282E6f5717214004A7f26888;

    address p62;
    address p64;
    address p65;
    // markets, allMarkets, compSpeeds, compSupplyState, compBorrowState, compSupplierIndex,
    // compBorrowerIndex, compAccrued
    uint256[8] slots;

    function codeOf(address a) internal view returns (bytes memory o) {
        assembly {
            let size := extcodesize(a)
            o := mload(0x40)
            mstore(0x40, add(o, and(add(add(size, 0x20), 0x1f), not(0x1f))))
            mstore(o, size)
            extcodecopy(a, add(o, 0x20), 0, size)
        }
    }

    function setUp() public {
        vm.etch(COMP, codeOf(address(new MockComp())));
        p62 = address(new ComptrollerP62());
        p64 = address(new ComptrollerP64());
        p65 = address(new ComptrollerP65());
    }

    function acct(uint256 i) internal pure returns (address) {
        return address(uint160(0x10000 + i));
    }

    function mapSlot(address key, uint256 slot) internal pure returns (bytes32) {
        return keccak256(abi.encode(key, slot));
    }

    function nestedSlot(address outer, address inner, uint256 slot) internal pure returns (bytes32) {
        return keccak256(abi.encode(inner, keccak256(abi.encode(outer, slot))));
    }

    function put(address uni, bytes32 slot, uint256 v) internal {
        vm.store(uni, slot, bytes32(v));
    }

    function upgradeTo(address uni, address impl) internal {
        (bool ok, bytes memory ret) = uni.call(abi.encodeWithSignature("_setPendingImplementation(address)", impl));
        require(ok && abi.decode(ret, (uint256)) == 0, "setPendingImplementation");
        (ok, ) = impl.call(abi.encodeWithSignature("_become(address)", uni));
        require(ok, "become");
    }

    function readUint(address target, bytes memory data) internal view returns (uint256) {
        (bool ok, bytes memory ret) = target.staticcall(data);
        require(ok, "read");
        return abi.decode(ret, (uint256));
    }

    function readPair(address target, bytes memory data) internal view returns (uint256, uint256) {
        (bool ok, bytes memory ret) = target.staticcall(data);
        require(ok, "read pair");
        return abi.decode(ret, (uint256, uint256));
    }

    function stateLine(string memory tag, address uni, MockCToken ct, uint256 n) internal returns (string memory) {
        uint256[] memory v = new uint256[](9 + 6 * n);
        v[0] = block.number;
        (v[1], v[2]) = readPair(uni, abi.encodeWithSignature("compSupplyState(address)", address(ct)));
        v[3] = readUint(uni, abi.encodeWithSignature("compSupplySpeeds(address)", address(ct)));
        (v[4], v[5]) = readPair(uni, abi.encodeWithSignature("compBorrowState(address)", address(ct)));
        v[6] = readUint(uni, abi.encodeWithSignature("compBorrowSpeeds(address)", address(ct)));
        v[7] = MockComp(COMP).balanceOf(uni);
        v[8] = n;
        for (uint256 i = 0; i < n; i++) {
            address a = acct(i);
            uint256 b = 9 + 6 * i;
            v[b] = ct.balanceOf(a);
            v[b + 1] = ct.borrows(a);
            v[b + 2] = readUint(uni, abi.encodeWithSignature("compSupplierIndex(address,address)", address(ct), a));
            v[b + 3] = readUint(uni, abi.encodeWithSignature("compBorrowerIndex(address,address)", address(ct), a));
            v[b + 4] = readUint(uni, abi.encodeWithSignature("compAccrued(address)", a));
            v[b + 5] = MockComp(COMP).balanceOf(a);
        }
        bytes memory s = bytes(tag);
        for (uint256 i = 0; i < v.length; i++) {
            s = abi.encodePacked(s, " ", vm.toString(v[i]));
        }
        return string(s);
    }

    function hook(address uni, bytes memory data) internal returns (bool) {
        (bool ok, bytes memory ret) = uni.call(data);
        if (!ok) return false;
        return abi.decode(ret, (uint256)) == 0;
    }

    function one(address x) internal pure returns (address[] memory r) {
        r = new address[](1);
        r[0] = x;
    }

    function oneUint(uint256 x) internal pure returns (uint256[] memory r) {
        r = new uint256[](1);
        r[0] = x;
    }

    struct Op {
        uint256 k;
        uint256 a;
        uint256 b;
        uint256 c;
    }

    function doOp(address uni, MockCToken ct, uint256 n, Op memory op) internal returns (bool) {
        address m = address(ct);
        uint256 k = op.k;
        uint256 a = op.a;
        uint256 b = op.b;
        if (k == 0 || k == 1) {
            if (a >= n) return false;
            bytes memory data = k == 0
                ? abi.encodeWithSignature("mintAllowed(address,address,uint256)", m, acct(a), b)
                : abi.encodeWithSignature("redeemAllowed(address,address,uint256)", m, acct(a), b);
            if (!hook(uni, data)) return false;
            uint256 bal = ct.balanceOf(acct(a));
            if (k == 1 && b > bal) return false;
            ct.setSupply(acct(a), k == 0 ? bal + b : bal - b);
            return true;
        }
        if (k == 2) {
            if (a >= n || b >= n || a == b) return false;
            if (!hook(uni, abi.encodeWithSignature("transferAllowed(address,address,address,uint256)", m, acct(a), acct(b), op.c)))
                return false;
            uint256 bal = ct.balanceOf(acct(a));
            if (op.c > bal) return false;
            ct.setSupply(acct(a), bal - op.c);
            ct.setSupply(acct(b), ct.balanceOf(acct(b)) + op.c);
            return true;
        }
        if (k == 3 || k == 4) {
            if (a >= n) return false;
            if (!hook(uni, abi.encodeWithSignature("repayBorrowAllowed(address,address,address,uint256)", m, acct(a), acct(a), b)))
                return false;
            uint256 bal = ct.borrows(acct(a));
            if (k == 4 && b > bal) return false;
            ct.setBorrow(acct(a), k == 3 ? bal + b : bal - b);
            return true;
        }
        if (k == 5) {
            (bool ok, ) = uni.call(abi.encodeWithSignature("claimComp(address,address[])", acct(a), one(m)));
            return ok;
        }
        if (k == 6) {
            (bool ok, ) = uni.call(abi.encodeWithSignature("_setCompSpeeds(address[],uint256[],uint256[])",
                one(m), oneUint(a), oneUint(b)));
            return ok;
        }
        if (k == 7) {
            vm.roll(block.number + a);
            return true;
        }
        MockComp(COMP).mint(uni, a);
        return true;
    }

    function setLegacy(address uni, MockCToken ct, uint256[] memory w) internal {
        address m = address(ct);
        uint256 n = w[0];
        put(uni, bytes32(slots[1]), 1);
        put(uni, keccak256(abi.encode(slots[1])), uint256(uint160(m)));
        put(uni, mapSlot(m, slots[0]), 1);
        put(uni, mapSlot(m, slots[2]), w[2]);
        put(uni, mapSlot(m, slots[3]), w[3] | (w[4] << 224));
        put(uni, mapSlot(m, slots[4]), w[5] | (w[6] << 224));
        MockComp(COMP).mint(uni, w[7]);
        for (uint256 i = 0; i < n; i++) {
            uint256 b = 8 + 6 * i;
            address a = acct(i);
            ct.setSupply(a, w[b]);
            ct.setBorrow(a, w[b + 1]);
            put(uni, nestedSlot(m, a, slots[5]), w[b + 2]);
            put(uni, nestedSlot(m, a, slots[6]), w[b + 3]);
            put(uni, mapSlot(a, slots[7]), w[b + 4]);
            MockComp(COMP).mint(a, w[b + 5]);
        }
    }

    function step(address uni, MockCToken ct, uint256 n, uint256[] memory w, uint256 o, string memory outp) internal {
        uint256 snap = vm.snapshotState();
        bool ok = doOp(uni, ct, n, Op(w[o], w[o + 1], w[o + 2], w[o + 3]));
        if (!ok) vm.revertToState(snap);
        vm.writeLine(outp, stateLine(ok ? "o 1" : "o 0", uni, ct, n));
    }

    function runCase(uint256[] memory w, uint256 variant, string memory outp) internal {
        uint256 n = w[0];
        vm.roll(w[1]);
        address uni = address(new UnitrollerP62());
        MockCToken ct = new MockCToken();
        setLegacy(uni, ct, w);
        upgradeTo(uni, p62);
        if (variant == 64) upgradeTo(uni, p64);
        if (variant == 65) upgradeTo(uni, p65);
        vm.writeLine(outp, stateLine("s", uni, ct, n));
        uint256 base = 8 + 6 * n;
        uint256 count = w[base];
        for (uint256 j = 0; j < count; j++) {
            step(uni, ct, n, w, base + 1 + 4 * j, outp);
        }
        vm.writeLine(outp, "e");
    }

    function testRunCases() public {
        string memory variantName = vm.envString("COMP_VARIANT");
        uint256 variant = keccak256(bytes(variantName)) == keccak256("p64") ? 64
            : keccak256(bytes(variantName)) == keccak256("p65") ? 65 : 62;
        string memory inp = vm.envString("COMP_CASES");
        string memory outp = vm.envString("COMP_OUT");
        uint256[] memory h = abi.decode(vm.parseBytes(vm.readLine(inp)), (uint256[]));
        for (uint256 i = 0; i < 8; i++) slots[i] = h[i];
        for (uint256 c = 0; c < h[8]; c++) {
            uint256[] memory w = abi.decode(vm.parseBytes(vm.readLine(inp)), (uint256[]));
            uint256 snap = vm.snapshotState();
            runCase(w, variant, outp);
            vm.revertToState(snap);
        }
    }
}
