// SPDX-License-Identifier: MIT
pragma solidity 0.8.24;

import "forge-std/Test.sol";

interface ICToken {
    function mint(uint256) external returns (uint256);
    function redeem(uint256) external returns (uint256);
    function redeemUnderlying(uint256) external returns (uint256);
    function totalSupply() external view returns (uint256);
    function getCash() external view returns (uint256);
    function totalBorrows() external view returns (uint256);
    function totalReserves() external view returns (uint256);
    function balanceOf(address) external view returns (uint256);
    function implementation() external view returns (address);
    function admin() external view returns (address);
    function _reduceReserves(uint256) external returns (uint256);
}

interface IERC20 {
    function approve(address, uint256) external returns (bool);
    function transfer(address, uint256) external returns (bool);
    function balanceOf(address) external view returns (uint256);
}

/// Runs the operation sequences in io/cases.txt on the deployed hWBTC market and writes the
/// state after every operation to io/out.txt. The market code is the deployed bytecode of the
/// fork; nothing here reimplements it.
///
/// Input, one case per line: `n k1 w1 a1 ... kn wn an` with kind k = 0 deposit (mint),
/// 1 redeem, 2 withdraw (redeemUnderlying), 3 donate (WBTC transfer to the market), actor w
/// and amount a. Output, per operation: `ok assets supply b0 b1 b2 b3`, where assets is
/// getCash() + totalBorrows() - totalReserves(); a line `end` closes each case. Before the
/// cases, the only holder redeems every share and the admin withdraws the reserves.
contract Replay is Test {
    ICToken constant HWBTC = ICToken(0x35594E4992DFefcB0C20EC487d7af22a30bDec60);
    IERC20 constant WBTC = IERC20(0x68f180fcCe6836688e9084f035309E29Bf0A2095);
    address constant IMPL = 0x7100CBCa885905F922a19006cF7fD5d0E1bBb26c;
    // The attacker contract that held every hWBTC share before the attack (it redeems them at
    // log index 5 of the attack transaction).
    address constant HOLDER = 0x978D0CE23869EC666BFDE9868a8514F3D2754982;
    uint256 constant FORK_BLOCK = 90761917;
    uint256 constant ACTORS = 4;
    address constant DONOR = address(0xD0D0);

    function actor(uint256 i) internal pure returns (address) {
        return address(uint160(0xA11CE0 + i));
    }

    /// cash + totalBorrows - totalReserves; borrows and reserves stay zero in these runs.
    function assets() internal view returns (uint256) {
        return HWBTC.getCash() + HWBTC.totalBorrows() - HWBTC.totalReserves();
    }

    function stateLine(bool ok) internal view returns (string memory s) {
        s = string.concat(ok ? "1 " : "0 ", vm.toString(assets()), " ", vm.toString(HWBTC.totalSupply()));
        for (uint256 i = 0; i < ACTORS; i++) {
            s = string.concat(s, " ", vm.toString(HWBTC.balanceOf(actor(i))));
        }
    }

    function call(uint256 k, address who, uint256 a) internal returns (bool) {
        if (k == 3) {
            vm.prank(DONOR);
            return WBTC.transfer(address(HWBTC), a);
        }
        currentActor = who;
        try this.dispatch(k, a) returns (uint256 err) {
            return err == 0;
        } catch {
            return false;
        }
    }

    /// Called through `this` so that a revert in the market is caught; the market sees the
    /// actor as msg.sender.
    function dispatch(uint256 k, uint256 a) external returns (uint256) {
        vm.prank(currentActor);
        if (k == 0) return HWBTC.mint(a);
        if (k == 1) return HWBTC.redeem(a);
        return HWBTC.redeemUnderlying(a);
    }

    address currentActor;

    function test_replay() public {
        vm.createSelectFork(vm.envString("PF_OP_RPC"), FORK_BLOCK);
        require(HWBTC.implementation() == IMPL, "unexpected implementation");
        // Empty the market as the attacker did: the holder redeems every share.
        uint256 held = HWBTC.balanceOf(HOLDER);
        vm.prank(HOLDER);
        require(HWBTC.redeem(held) == 0, "redeem all failed");
        require(HWBTC.totalSupply() == 0, "market not empty");
        // The model has no reserves. The admin withdraws them (377 satoshi), so that the
        // underlying backing the shares equals the market's cash.
        uint256 reserves = HWBTC.totalReserves();
        address admin = HWBTC.admin();
        vm.prank(admin);
        require(HWBTC._reduceReserves(reserves) == 0, "reduce reserves failed");
        require(HWBTC.totalReserves() == 0 && HWBTC.totalBorrows() == 0, "reserves or borrows left");
        string memory out = "io/out.txt";
        vm.writeLine(out, string.concat("start ", vm.toString(assets()), " ", vm.toString(HWBTC.totalSupply()),
            " cash ", vm.toString(HWBTC.getCash()), " reserves_withdrawn ", vm.toString(reserves)));
        deal(address(WBTC), DONOR, 1e30);
        for (uint256 i = 0; i < ACTORS; i++) {
            deal(address(WBTC), actor(i), 1e30);
            vm.prank(actor(i));
            WBTC.approve(address(HWBTC), type(uint256).max);
        }
        uint256 snap = vm.snapshotState();
        while (true) {
            string memory line = vm.readLine("io/cases.txt");
            if (bytes(line).length == 0) break;
            string[] memory f = vm.split(line, " ");
            uint256 n = vm.parseUint(f[0]);
            for (uint256 j = 0; j < n; j++) {
                uint256 k = vm.parseUint(f[1 + 3 * j]);
                address who = actor(vm.parseUint(f[2 + 3 * j]));
                uint256 a = vm.parseUint(f[3 + 3 * j]);
                bool ok = call(k, who, a);
                vm.writeLine(out, stateLine(ok));
            }
            vm.writeLine(out, "end");
            vm.revertToState(snap);
            snap = vm.snapshotState();
        }
    }
}
