pragma solidity ^0.5.16;

// Replays the cSUSHI part of the claim in mainnet transaction
// 0xc9244e5349f49f3b74a54a882e71f1ca11ba14ed74f73bf2cd091ed8be2b0001 (block 13322937) on a
// fork of mainnet at block 13322936, three times: with the deployed Proposal 62 implementation,
// and with the runtime code of the Proposal 64 and Proposal 65 implementations, compiled from
// the pinned sources, placed at the address of the Proposal 62 implementation (the Unitroller
// delegates to it; the storage is the Unitroller's). Each line of the output (env COMP_OUT):
// variant, then the account's compAccrued, COMP balance and compBorrowerIndex in cSUSHI before
// the claim, the same three after it, and the Comptroller's COMP before and after.

import {Comptroller as ComptrollerP64} from "../src/p64/Comptroller.sol";
import {Comptroller as ComptrollerP65} from "../src/p65/Comptroller.sol";

interface Vm {
    function roll(uint256) external;
    function etch(address, bytes calldata) external;
    function prank(address) external;
    function writeLine(string calldata, string calldata) external;
    function envString(string calldata) external returns (string memory);
    function toString(uint256) external returns (string memory);
    function snapshotState() external returns (uint256);
    function revertToState(uint256) external returns (bool);
    function createSelectFork(string calldata, uint256) external returns (uint256);
}

interface IERC20 {
    function balanceOf(address) external view returns (uint256);
}

contract ForkReplay {
    Vm constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    address constant UNITROLLER = 0x3d9819210A31b4961b30EF54bE2aeD79B9c9Cd3B;
    address constant P62_IMPL = 0x374ABb8cE19A73f2c4EFAd642bda76c797f19233;
    address constant CSUSHI = 0x4B0181102A0112A2ef11AbEE5563bb4a3176c9d7;
    address constant HOLDER = 0xf3f5C252e8ACd60671f92c7F72cf33661221Ef42;
    address constant COMP = 0xc00e94Cb662C3520282E6f5717214004A7f26888;

    function codeOf(address a) internal view returns (bytes memory o) {
        assembly {
            let size := extcodesize(a)
            o := mload(0x40)
            mstore(0x40, add(o, and(add(add(size, 0x20), 0x1f), not(0x1f))))
            mstore(o, size)
            extcodecopy(a, add(o, 0x20), 0, size)
        }
    }

    function readUint(bytes memory data) internal view returns (uint256) {
        (bool ok, bytes memory ret) = UNITROLLER.staticcall(data);
        require(ok, "read");
        return abi.decode(ret, (uint256));
    }

    function snapshot(uint256[] memory v, uint256 at) internal view {
        v[at] = readUint(abi.encodeWithSignature("compAccrued(address)", HOLDER));
        v[at + 1] = IERC20(COMP).balanceOf(HOLDER);
        v[at + 2] = readUint(abi.encodeWithSignature("compBorrowerIndex(address,address)", CSUSHI, HOLDER));
    }

    function claim(string memory tag, string memory outp) internal {
        uint256[] memory v = new uint256[](8);
        snapshot(v, 0);
        v[6] = IERC20(COMP).balanceOf(UNITROLLER);
        address[] memory markets = new address[](1);
        markets[0] = CSUSHI;
        vm.prank(HOLDER);
        (bool ok, ) = UNITROLLER.call(abi.encodeWithSignature("claimComp(address,address[])", HOLDER, markets));
        require(ok, "claimComp reverted");
        snapshot(v, 3);
        v[7] = IERC20(COMP).balanceOf(UNITROLLER);
        bytes memory s = bytes(tag);
        for (uint256 i = 0; i < v.length; i++) s = abi.encodePacked(s, " ", vm.toString(v[i]));
        vm.writeLine(outp, string(s));
    }

    function testReplay() public {
        string memory outp = vm.envString("COMP_OUT");
        vm.createSelectFork(vm.envString("COMP_RPC"), 13322936);
        vm.roll(13322937);
        bytes memory code64 = codeOf(address(new ComptrollerP64()));
        bytes memory code65 = codeOf(address(new ComptrollerP65()));
        uint256 snap = vm.snapshotState();
        claim("p62", outp);
        vm.revertToState(snap);
        vm.etch(P62_IMPL, code64);
        claim("p64", outp);
        vm.revertToState(snap);
        vm.etch(P62_IMPL, code65);
        claim("p65", outp);
    }
}
