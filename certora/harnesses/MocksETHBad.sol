pragma solidity 0.8.13;

// SPDX-License-Identifier: MIT

// this sETH specifically catches bug1.

import { MocksETH } from "./MocksETH.sol";

contract MocksETHBad is MocksETH {
    function transfer(address recipient, uint256 amount) public virtual override returns (bool val) {
        return false;
    }
}
