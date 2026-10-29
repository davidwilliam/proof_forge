// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// No-op stand-in for hardhat/console.sol (a Hardhat npm dependency), imported by Euler's test
// contracts TestERC20.sol and InvariantChecker.sol. Logging only; the driver does not use it.
library console {
    function log(string memory) internal pure {}
    function log(string memory, address) internal pure {}
    function log(string memory, uint) internal pure {}
}
