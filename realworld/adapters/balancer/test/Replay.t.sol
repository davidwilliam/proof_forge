// SPDX-License-Identifier: MIT
pragma solidity 0.8.24;

import "forge-std/Test.sol";

interface IERC20 {
    function approve(address, uint256) external returns (bool);
    function balanceOf(address) external view returns (uint256);
}

interface IVault {
    enum SwapKind { GIVEN_IN, GIVEN_OUT }

    struct SingleSwap {
        bytes32 poolId;
        SwapKind kind;
        address assetIn;
        address assetOut;
        uint256 amount;
        bytes userData;
    }

    struct BatchSwapStep {
        bytes32 poolId;
        uint256 assetInIndex;
        uint256 assetOutIndex;
        uint256 amount;
        bytes userData;
    }

    struct FundManagement {
        address sender;
        bool fromInternalBalance;
        address payable recipient;
        bool toInternalBalance;
    }

    function swap(SingleSwap memory singleSwap, FundManagement memory funds, uint256 limit, uint256 deadline)
        external
        payable
        returns (uint256);

    function batchSwap(
        SwapKind kind,
        BatchSwapStep[] memory swaps,
        address[] memory assets,
        FundManagement memory funds,
        int256[] memory limits,
        uint256 deadline
    ) external payable returns (int256[] memory);

    function getPoolTokens(bytes32 poolId)
        external
        view
        returns (address[] memory tokens, uint256[] memory balances, uint256 lastChangeBlock);
}

interface IPool {
    function getRate() external view returns (uint256);
    function getScalingFactors() external view returns (uint256[] memory);
    function getSwapFeePercentage() external view returns (uint256);
    function getAmplificationParameter() external view returns (uint256, bool, uint256);
    function updateTokenRateCache(address token) external;
}

/// Runs swap batches through Balancer V2's deployed Vault and the deployed osETH/WETH Composable
/// Stable Pool, on a fork of Ethereum taken just before the attack transaction
/// 0x6ed07db1a9fe5c0794d44cd36081d6a6df103fab868cdd75d581e3bd23bc9742. Nothing here reimplements
/// pool or Vault code: every amount comes from `Vault.swap` on the deployed bytecode.
///
/// io/setup.txt: one GIVEN_OUT step per line, `assetInIndex assetOutIndex amount` over the
/// registered tokens [WETH, BPT, osETH]. The steps run as one `batchSwap` before the cases (the
/// attack's first 22 swaps, which bring the pool to 67,000 wei of each token).
///
/// io/cases.txt: one batch per line, `start n k1 i1 j1 a1 ... kn in jn an`. `start` 0 is the
/// state after the setup batch, 1 the state before it (the fork itself, with the pool's expired
/// osETH rate cache refreshed). Kind k is 0 for
/// GIVEN_IN and 1 for GIVEN_OUT; tokens i and j are 0 for WETH and 1 for osETH.
///
/// io/out.txt: a header line `pool ...` with the scaling factors, fee and amplification, a line
/// `state s weth oseth rate` for both start states, then per swap `ok amountCalculated weth oseth`
/// and per batch `end rateAfter` (the pool's getRate() after the batch, `x` when it reverts). A
/// batch stops at its first failed swap and is then reverted.
contract Replay is Test {
    IVault constant VAULT = IVault(0xBA12222222228d8Ba445958a75a0704d566BF2C8);
    address constant POOL = 0xDACf5Fa19b1f720111609043ac67A9818262850c;
    bytes32 constant POOL_ID = 0xdacf5fa19b1f720111609043ac67a9818262850c000000000000000000000635;
    address constant WETH = 0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2;
    address constant OSETH = 0xf1C9acDc66974dFB6dEcB12aA385b9cD01190E38;
    bytes32 constant ATTACK_TX = 0x6ed07db1a9fe5c0794d44cd36081d6a6df103fab868cdd75d581e3bd23bc9742;

    function token(uint256 k) internal pure returns (address) {
        return k == 0 ? WETH : OSETH;
    }

    function rateString() internal view returns (string memory) {
        try IPool(POOL).getRate() returns (uint256 r) {
            return vm.toString(r);
        } catch {
            return "x";
        }
    }

    function balances() internal view returns (uint256 w, uint256 o) {
        (, uint256[] memory b,) = VAULT.getPoolTokens(POOL_ID);
        return (b[0], b[2]);
    }

    function funds() internal view returns (IVault.FundManagement memory) {
        return IVault.FundManagement(address(this), false, payable(address(this)), false);
    }

    /// Called through `this`, so that a revert in the Vault or the pool is caught.
    function doSwap(uint256 k, uint256 i, uint256 j, uint256 a) external returns (uint256) {
        IVault.SingleSwap memory s = IVault.SingleSwap(
            POOL_ID, k == 0 ? IVault.SwapKind.GIVEN_IN : IVault.SwapKind.GIVEN_OUT, token(i), token(j), a, "");
        return VAULT.swap(s, funds(), k == 0 ? 0 : type(uint256).max, type(uint256).max);
    }

    function setupBatch() internal {
        string[] memory lines = new string[](64);
        uint256 n = 0;
        while (true) {
            string memory line = vm.readLine("io/setup.txt");
            if (bytes(line).length == 0) break;
            lines[n++] = line;
        }
        IVault.BatchSwapStep[] memory steps = new IVault.BatchSwapStep[](n);
        for (uint256 s = 0; s < n; s++) {
            string[] memory f = vm.split(lines[s], " ");
            steps[s] = IVault.BatchSwapStep(POOL_ID, vm.parseUint(f[0]), vm.parseUint(f[1]), vm.parseUint(f[2]), "");
        }
        address[] memory assets = new address[](3);
        assets[0] = WETH;
        assets[1] = POOL;
        assets[2] = OSETH;
        int256[] memory limits = new int256[](3);
        for (uint256 k = 0; k < 3; k++) limits[k] = type(int256).max;
        VAULT.batchSwap(IVault.SwapKind.GIVEN_OUT, steps, assets, funds(), limits, type(uint256).max);
    }

    /// Swap `s` of a case line; writes `ok amountCalculated weth oseth`.
    function runSwap(string[] memory f, uint256 s, string memory out) internal returns (bool ok) {
        uint256 calc;
        try this.doSwap(vm.parseUint(f[2 + 4 * s]), vm.parseUint(f[3 + 4 * s]), vm.parseUint(f[4 + 4 * s]),
            vm.parseUint(f[5 + 4 * s])) returns (uint256 c) {
            ok = true;
            calc = c;
        } catch {
            ok = false;
        }
        (uint256 w, uint256 o) = balances();
        vm.writeLine(out, string.concat(ok ? "1 " : "0 ", vm.toString(calc), " ", vm.toString(w), " ", vm.toString(o)));
    }

    string constant OUT = "io/out.txt";

    function stateLine(uint256 id, string memory rate) internal view returns (string memory) {
        (uint256 w, uint256 o) = balances();
        return string.concat("state ", vm.toString(id), " ", vm.toString(w), " ", vm.toString(o), " ", rate);
    }

    /// Forks, funds this contract, runs the setup batch, and returns the snapshots of the two
    /// start states.
    function prepare() internal returns (uint256 snap0, uint256 snap1) {
        vm.createSelectFork(vm.envString("PF_ETH_RPC"), ATTACK_TX);
        deal(WETH, address(this), 1e30);
        deal(OSETH, address(this), 1e30);
        deal(POOL, address(this), 1e30);
        IERC20(WETH).approve(address(VAULT), type(uint256).max);
        IERC20(OSETH).approve(address(VAULT), type(uint256).max);
        IERC20(POOL).approve(address(VAULT), type(uint256).max);
        // State 1 is the fork itself, with the pool's cached osETH rate refreshed (it had expired;
        // the attack's first swap refreshed it the same way), so that getRate() before and after a
        // batch uses the same scaling factors.
        IPool(POOL).updateTokenRateCache(OSETH);
        snap1 = vm.snapshotState();
        string memory state1 = stateLine(1, rateString());
        setupBatch();
        uint256[] memory sf = IPool(POOL).getScalingFactors();
        (uint256 amp,,) = IPool(POOL).getAmplificationParameter();
        vm.writeLine(OUT, string.concat("pool ", vm.toString(sf[0]), " ", vm.toString(sf[2]), " ",
            vm.toString(IPool(POOL).getSwapFeePercentage()), " ", vm.toString(amp)));
        vm.writeLine(OUT, stateLine(0, rateString()));
        vm.writeLine(OUT, state1);
        snap0 = vm.snapshotState();
    }

    function test_replay() public {
        (uint256 snap0, uint256 snap1) = prepare();
        while (true) {
            string memory line = vm.readLine("io/cases.txt");
            if (bytes(line).length == 0) break;
            string[] memory f = vm.split(line, " ");
            vm.revertToState(vm.parseUint(f[0]) == 0 ? snap0 : snap1);
            uint256 n = vm.parseUint(f[1]);
            for (uint256 s = 0; s < n; s++) {
                if (!runSwap(f, s, OUT)) break;
            }
            vm.writeLine(OUT, string.concat("end ", rateString()));
        }
    }
}
