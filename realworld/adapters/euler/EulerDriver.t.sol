// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// Runs operation sequences on Euler v1 deployed locally from the contracts at a pinned commit,
// unmodified, and prints the market state after every operation as one JSON line per sequence.
// Used by eval/realworld_euler.py; Euler's sources are copied into src/ at run time.
//
// Deployment follows test/lib/eTestLib.js (deployContracts): module implementations, the Euler
// contract with the installer, then installModules. The market's asset is the reference asset,
// priced at 1 (PRICINGTYPE__PEGGED), with its borrow factor set to 1.0 by governance. 1e6 wei of
// the asset is sent to the Euler contract after activation so that the pool holds as many
// underlying units as the INITIAL_RESERVES eTokens: the eToken exchange rate is then exactly 1.
// No time passes, so no interest accrues.
//
// Input (env EULER_CASES): one line per sequence, the hex of abi.encode(uint256[]) with
// [n, m, kind, a, b, c, ...] for m operations on n accounts. Kinds: 0 deposit(a, b),
// 1 withdraw(a, b), 2 borrow(a, b), 3 repay(a, b), 4 mint(a, b), 5 burn(a, b),
// 6 transfer(a -> b, c), 7 donate(a, b), 8 liquidate(liquidator a, violator b, the largest
// repay that checkLiquidation offers, minimum yield 0: checkLiquidation's yield can exceed the
// yield executeLiquidation pays for that repay by rounding, and then e/liq/min-yield reverts). Output (env EULER_OUT): per sequence
// {"steps": [{"ok", "repay", "err" (the revert reason), "acct": [[eToken balance, dToken balance], ...],
// "liq": [[collateralValue, liabilityValue], ...], "pool", "reserveBalance"}, ...]}.

import "../src/Euler.sol";
import "../src/Storage.sol";
import "../src/modules/Installer.sol";
import "../src/modules/Markets.sol";
import "../src/modules/Liquidation.sol";
import "../src/modules/Governance.sol";
import "../src/modules/Exec.sol";
import "../src/modules/EToken.sol";
import "../src/modules/DToken.sol";
import "../src/modules/RiskManager.sol";
import "../src/modules/interest-rate-models/IRMDefault.sol";
import "../src/test/TestERC20.sol";

interface Vm {
    function prank(address) external;
    function readLine(string calldata) external returns (string memory);
    function writeLine(string calldata, string calldata) external;
    function envString(string calldata) external returns (string memory);
    function parseBytes(string calldata) external returns (bytes memory);
    function toString(uint256) external returns (string memory);
    function snapshotState() external returns (uint256);
    function revertToState(uint256) external returns (bool);
}

contract EulerDriver {
    Vm constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    uint constant SEED = 1e6;
    uint constant MAX_USERS = 8;

    Euler euler;
    Markets markets;
    Liquidation liquidation;
    Exec exec;
    EToken eTok;
    DToken dTok;
    TestERC20 token;
    address[MAX_USERS] users;

    function setUp() public {
        bytes32 gc = bytes32(0);
        token = new TestERC20("Test Token", "TST", 18, false);
        Installer installer = new Installer(gc);
        address[] memory mods = new address[](8);
        mods[0] = address(new Markets(gc));
        mods[1] = address(new Liquidation(gc));
        mods[2] = address(new Governance(gc));
        mods[3] = address(new Exec(gc));
        mods[4] = address(new EToken(gc));
        mods[5] = address(new DToken(gc));
        mods[6] = address(new RiskManager(gc, RiskManager.RiskManagerSettings(address(token), address(0), bytes32(0))));
        mods[7] = address(new IRMDefault(gc));
        euler = new Euler(address(this), address(installer));
        Installer(euler.moduleIdToProxy(1)).installModules(mods);
        markets = Markets(euler.moduleIdToProxy(2));
        liquidation = Liquidation(euler.moduleIdToProxy(3));
        Governance gov = Governance(euler.moduleIdToProxy(4));
        exec = Exec(euler.moduleIdToProxy(5));
        eTok = EToken(markets.activateMarket(address(token)));
        dTok = DToken(markets.underlyingToDToken(address(token)));
        Storage.AssetConfig memory c = markets.underlyingToAssetConfigUnresolved(address(token));
        c.borrowFactor = 4_000_000_000;
        c.collateralFactor = 3_000_000_000;
        gov.setAssetConfig(address(token), c);
        token.mint(address(euler), SEED);
        for (uint i = 0; i < MAX_USERS; ++i) {
            // Distinct in their first 19 bytes, so no two are sub-accounts of one another.
            users[i] = address(uint160(uint(keccak256(abi.encode("proofforge user", i)))));
            token.mint(users[i], 2**200);
            vm.prank(users[i]);
            token.approve(address(euler), type(uint).max);
        }
    }

    // The revert reason of a failed call, when it is an Error(string).
    function reason(bytes memory ret) internal pure returns (string memory) {
        if (ret.length < 68 || ret[0] != 0x08 || ret[1] != 0xc3 || ret[2] != 0x79 || ret[3] != 0xa0) return "";
        bytes memory body = new bytes(ret.length - 4);
        for (uint i = 4; i < ret.length; ++i) body[i - 4] = ret[i];
        return abi.decode(body, (string));
    }

    function op(uint k, uint a, uint b, uint c) internal returns (bool ok, uint repay, string memory err) {
        address u = users[a];
        bytes memory ret;
        if (k == 8) {
            vm.prank(u);
            (ok, ret) = address(liquidation).call(abi.encodeWithSelector(
                Liquidation.checkLiquidation.selector, u, users[b], address(token), address(token)));
            if (!ok) return (false, 0, reason(ret));
            Liquidation.LiquidationOpportunity memory opp = abi.decode(ret, (Liquidation.LiquidationOpportunity));
            vm.prank(u);
            (ok, ret) = address(liquidation).call(abi.encodeWithSelector(
                Liquidation.liquidate.selector, users[b], address(token), address(token), opp.repay, 0));
            return (ok, opp.repay, ok ? "" : reason(ret));
        }
        bytes memory data;
        address target = address(eTok);
        if (k == 0) data = abi.encodeWithSelector(EToken.deposit.selector, 0, b);
        else if (k == 1) data = abi.encodeWithSelector(EToken.withdraw.selector, 0, b);
        else if (k == 2) { target = address(dTok); data = abi.encodeWithSelector(DToken.borrow.selector, 0, b); }
        else if (k == 3) { target = address(dTok); data = abi.encodeWithSelector(DToken.repay.selector, 0, b); }
        else if (k == 4) data = abi.encodeWithSelector(EToken.mint.selector, 0, b);
        else if (k == 5) data = abi.encodeWithSelector(EToken.burn.selector, 0, b);
        else if (k == 6) data = abi.encodeWithSelector(EToken.transferFrom.selector, u, users[b], c);
        else if (k == 7) data = abi.encodeWithSelector(EToken.donateToReserves.selector, 0, b);
        else revert("unknown op");
        vm.prank(u);
        (ok, ret) = target.call(data);
        return (ok, 0, ok ? "" : reason(ret));
    }

    function state(uint n) internal returns (string memory s) {
        bytes memory acct;
        bytes memory liq;
        for (uint i = 0; i < n; ++i) {
            IRiskManager.LiquidityStatus memory st = exec.liquidity(users[i]);
            acct = abi.encodePacked(acct, i == 0 ? "" : ",", "[", vm.toString(eTok.balanceOf(users[i])), ",",
                                    vm.toString(dTok.balanceOf(users[i])), "]");
            liq = abi.encodePacked(liq, i == 0 ? "" : ",", "[", vm.toString(st.collateralValue), ",",
                                   vm.toString(st.liabilityValue), "]");
        }
        s = string(abi.encodePacked("\"acct\":[", acct, "],\"liq\":[", liq, "],\"pool\":",
                                    vm.toString(token.balanceOf(address(euler))), ",\"reserveBalance\":",
                                    vm.toString(eTok.reserveBalance())));
    }

    function testRunCases() public {
        string memory inPath = vm.envString("EULER_CASES");
        string memory outPath = vm.envString("EULER_OUT");
        uint snap = vm.snapshotState();
        while (true) {
            string memory line = vm.readLine(inPath);
            if (bytes(line).length == 0) break;
            uint[] memory w = abi.decode(vm.parseBytes(line), (uint[]));
            uint n = w[0];
            bytes memory out = abi.encodePacked("{\"genesis\":{", state(n), "},\"steps\":[");
            for (uint j = 0; j < w[1]; ++j) {
                uint p = 2 + 4 * j;
                (bool ok, uint repay, string memory err) = op(w[p], w[p + 1], w[p + 2], w[p + 3]);
                out = abi.encodePacked(out, j == 0 ? "" : ",", "{\"ok\":", ok ? "true" : "false",
                                       ",\"repay\":", vm.toString(repay), ",\"err\":\"", err, "\",", state(n), "}");
            }
            vm.writeLine(outPath, string(abi.encodePacked(out, "]}")));
            vm.revertToState(snap);
        }
    }
}
