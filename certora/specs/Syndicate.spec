using MocksETH as sETHToken
using MocksETHBad as sETHTokenBad
using MockStakeHouseUniverse as stakeHouseUniverse
using MockStakeHouseRegistry as stakeHouseRegistry

methods {
    //// Regular methods
    totalETHReceived() returns (uint256) envfree
    isKnotRegistered(bytes32) returns (bool) envfree
    isNoLongerPartOfSyndicate(bytes32) returns (bool) envfree

    //// Resolving external calls
  // stakeHouseUniverse
  stakeHouseKnotInfo(bytes32) returns (address,address,address,uint256,uint256,bool) => DISPATCHER(true)
    memberKnotToStakeHouse(bytes32) returns (address) => DISPATCHER(true) // not used directly by Syndicate
    // stakeHouseRegistry
    getMemberInfo(bytes32) returns (address,uint256,uint16,bool) => DISPATCHER(true) // not used directly by Syndicate
    // slotSettlementRegistry
  stakeHouseShareTokens(address) returns (address)  => DISPATCHER(true)
  currentSlashedAmountOfSLOTForKnot(bytes32) returns (uint256)  => DISPATCHER(true)
  numberOfCollateralisedSlotOwnersForKnot(bytes32) returns (uint256)  => DISPATCHER(true)
  getCollateralisedOwnerAtIndex(bytes32, uint256) returns (address) => DISPATCHER(true)
  totalUserCollateralisedSLOTBalanceForKnot(address, address, bytes32) returns (uint256) => DISPATCHER(true)
    // sETH
    sETHToken.balanceOf(address) returns (uint256) envfree
    // sETH bad
    sETHTokenBad.balanceOf(address) returns (uint256) envfree
    // ERC20
    name()                                returns (string)  => DISPATCHER(true)
    symbol()                              returns (string)  => DISPATCHER(true)
    decimals()                            returns (string) envfree => DISPATCHER(true)
    totalSupply()                         returns (uint256) => DISPATCHER(true)
    balanceOf(address)                    returns (uint256) => DISPATCHER(true)
    allowance(address,address)            returns (uint)    => DISPATCHER(true)
    approve(address,uint256)              returns (bool)    => DISPATCHER(true)
    transfer(address,uint256)             returns (bool)    => DISPATCHER(true)
    transferFrom(address,address,uint256) returns (bool)    => DISPATCHER(true)

    //// Harnessing
    // harnessed variables
    accruedEarningPerCollateralizedSlotOwnerOfKnot(bytes32,address) returns (uint256) envfree
    calculateNewAccumulatedETHPerCollateralizedSharePerKnot() returns (uint256) envfree
    accumulatedETHPerCollateralizedSlotPerKnot() returns (uint256) envfree
    totalETHProcessedPerCollateralizedKnot(bytes32) returns (uint256) envfree
    sETHStakedBalanceForKnot(bytes32,address) returns (uint256) envfree
    sETHTotalStakeForKnot(bytes32) returns (uint256) envfree
    numberOfRegisteredKnots() returns (uint256) envfree
    totalFreeFloatingShares() returns (uint256) envfree
    // harnessed functions
    deRegisterKnots(bytes32)
    deRegisterKnots(bytes32,bytes32)
    stake(bytes32,uint256,address)
    stake(bytes32,bytes32,uint256,uint256,address)
    unstake(address,address,bytes32,uint256)
    unstake(address,address,bytes32,bytes32,uint256,uint256)
    claimAsStaker(address,bytes32)
    claimAsStaker(address,bytes32,bytes32)
    claimAsCollateralizedSLOTOwner(address,bytes32)
    claimAsCollateralizedSLOTOwner(address,bytes32,bytes32)
    registerKnotsToSyndicate(bytes32)
    registerKnotsToSyndicate(bytes32,bytes32)
    addPriorityStakers(address)
    addPriorityStakers(address,address)
    batchUpdateCollateralizedSlotOwnersAccruedETH(bytes32)
    batchUpdateCollateralizedSlotOwnersAccruedETH(bytes32,bytes32)
    getSETHTokenBalance(bytes32, address) returns (uint256) envfree
}

/// We defined additional functions to get around the complexity of defining dynamic arrays in cvl. We filter them in
/// normal rules and invariants as they serve no purpose.
definition notHarnessCall(method f) returns bool =
    f.selector != batchUpdateCollateralizedSlotOwnersAccruedETH(bytes32).selector
    && f.selector != batchUpdateCollateralizedSlotOwnersAccruedETH(bytes32,bytes32).selector
    && f.selector != deRegisterKnots(bytes32).selector
    && f.selector != deRegisterKnots(bytes32,bytes32).selector
    && f.selector != stake(bytes32,uint256,address).selector
    && f.selector != stake(bytes32,bytes32,uint256,uint256,address).selector
    && f.selector != unstake(address,address,bytes32,uint256).selector
    && f.selector != unstake(address,address,bytes32,bytes32,uint256,uint256).selector
    && f.selector != claimAsStaker(address,bytes32).selector
    && f.selector != claimAsStaker(address,bytes32,bytes32).selector
    && f.selector != claimAsCollateralizedSLOTOwner(address,bytes32).selector
    && f.selector != claimAsCollateralizedSLOTOwner(address,bytes32,bytes32).selector
    && f.selector != registerKnotsToSyndicate(bytes32).selector
    && f.selector != registerKnotsToSyndicate(bytes32,bytes32).selector
    && f.selector != addPriorityStakers(address).selector
    && f.selector != addPriorityStakers(address,address).selector;


function isKnotActive(bytes32 blsKey) returns bool {
    return (isKnotRegistered(blsKey) && !isNoLongerPartOfSyndicate(blsKey));
}

/// Corrollary that can be used as requirement after sETH solvency is proven.
function sETHSolvencyCorrollary(address user1, address user2, bytes32 knot) returns bool {
    return sETHStakedBalanceForKnot(knot,user1) + sETHStakedBalanceForKnot(knot,user2) <= sETHTotalStakeForKnot(knot);
}

/**
 * An unregistered knot can not be deregistered.
 */
rule canNotDegisterUnregisteredKnot(method f) filtered {
    f -> notHarnessCall(f)
} {
    bytes32 knot; env e;
    require !isKnotRegistered(knot);

    deRegisterKnots@withrevert(e, knot);

    assert lastReverted, "deRegisterKnots must revert if knot is not registered";
}

/**
 * Total ETH received must not decrease.
 */
rule totalEthReceivedMonotonicallyIncreases(method f) filtered {
    f -> notHarnessCall(f)
}{

    uint256 totalEthReceivedBefore = totalETHReceived();

    env e; calldataarg args;
    f(e, args);

    uint256 totalEthReceivedAfter = totalETHReceived();

    assert totalEthReceivedAfter >= totalEthReceivedBefore, "total ether received must not decrease";
}

/**
 * The number of knots registered must not decrease unless deregister function is called.
 */
rule numberOfRegisteredKnotsOnlyDecrementedByDeRegister(method f) filtered {
    f -> notHarnessCall(f)
}{
    uint256 numberOfRegisteredKnotsBefore = numberOfRegisteredKnots();
    env e;
    calldataarg args;
    f(e, args);
    uint256 numberOfRegisteredKnotsAfter = numberOfRegisteredKnots();
    assert(numberOfRegisteredKnotsAfter < numberOfRegisteredKnotsBefore => f.selector == deRegisterKnots(bytes32[]).selector || f.selector == updateCollateralizedSlotOwnersAccruedETH(bytes32).selector || f.selector == claimAsCollateralizedSLOTOwner(address, bytes32[]).selector || f.selector == batchUpdateCollateralizedSlotOwnersAccruedETH(bytes32[]).selector, "knots registered must not decrease unless deregistered function called");
}

/**
 * The number of knots registered must not increase unless register function is called.
 */
rule numberOfRegisteredKnotsOnlyIncrementedByRegister(method f) filtered {
    f -> notHarnessCall(f)
}{
    uint256 numberOfRegisteredKnotsBefore = numberOfRegisteredKnots();
    env e;
    calldataarg args;
    f(e, args);
    uint256 numberOfRegisteredKnotsAfter = numberOfRegisteredKnots();
    assert(numberOfRegisteredKnotsAfter > numberOfRegisteredKnotsBefore => f.selector == registerKnotsToSyndicate(bytes32[]).selector || f.selector == initialize(address, uint256, address[], bytes32[]).selector, "knots registered must not increase unless registered function called");
}

/**
 * The amount of sETH staked must not decrease unless unstake function is called.
 */
rule sETHStakedOnlyDecrementedByUnstake(method f, bytes32 blsKey) filtered {
    f -> notHarnessCall(f)
        }{
    uint256 sETHStakedBefore = sETHTotalStakeForKnot(blsKey);
    env e;
    calldataarg args;
    f(e, args);
    uint256 sETHStakedAfter = sETHTotalStakeForKnot(blsKey);
    assert(sETHStakedAfter < sETHStakedBefore => f.selector == unstake(address, address, bytes32[], uint256[]).selector, "knots registered must not decrease unless unstake function called");
}

/**
 * The amount of sETH staked must not increase unless stake function is called.
 */
rule sETHStakedOnlyIncrementedByStake(method f, bytes32 blsKey) filtered {
    f -> notHarnessCall(f)
}{
    uint256 sETHStakedBefore = sETHTotalStakeForKnot(blsKey);
    env e;
    calldataarg args;
    f(e, args);
    uint256 sETHStakedAfter = sETHTotalStakeForKnot(blsKey);
    assert(sETHStakedAfter > sETHStakedBefore => f.selector == stake(bytes32[], uint256[], address).selector, "knots registered must not decrease unless stake function called");
}

/**
 * Free floating shares should be the same as sETH staked.
 */
rule freeFloatingSharesSameAsSETHPerKnot(method f, bytes32 blsKey1, bytes32 blsKey2) filtered {
    f -> notHarnessCall(f)
}{
    uint256 freeFloatingSharesBefore = totalFreeFloatingShares();
    // uint256 knotActive1Before = isKnotActive(blsKey1) ? to_uint256(1) : to_uint256(0);
    // uint256 knotActive2Before = isKnotActive(blsKey2) ? to_uint256(1) : to_uint256(0);
    uint256 numberOfRegisteredKnotsBefore = numberOfRegisteredKnots();
    // uint256 sETHStakedBefore = sETHTotalStakeForKnot(blsKey1)*knotActive1Before + sETHTotalStakeForKnot(blsKey2)*knotActive2Before;
    uint256 sETHStakedBefore = sETHTotalStakeForKnot(blsKey1) + sETHTotalStakeForKnot(blsKey2);
    bool keysActive = isKnotActive(blsKey1) && isKnotActive(blsKey2);

    address staker; bytes32 blsKey; uint256 sETHAmount; env e;
    unstake(e, staker, staker, blsKey, sETHAmount);
    //env e; calldataarg args;
    //f(e, args);

    uint256 freeFloatingSharesAfter = totalFreeFloatingShares();
    // uint256 knotActive1After = isKnotActive(blsKey1) ? to_uint256(1) : to_uint256(0);
    // uint256 knotActive2After = isKnotActive(blsKey2) ? to_uint256(1) : to_uint256(0);
    uint256 numberOfRegisteredKnotsAfter = numberOfRegisteredKnots();
    // uint256 sETHStakedAfter = sETHTotalStakeForKnot(blsKey1)*knotActive1After + sETHTotalStakeForKnot(blsKey2)*knotActive2After;
    uint256 sETHStakedAfter = sETHTotalStakeForKnot(blsKey1) + sETHTotalStakeForKnot(blsKey2);

    assert(keysActive && numberOfRegisteredKnotsBefore == numberOfRegisteredKnotsAfter && freeFloatingSharesBefore == sETHStakedBefore => freeFloatingSharesAfter == sETHStakedAfter);
}

/**
 * This rule should break for bug1.patch
 */
rule sETHBalanceIncreasesAfterUnstake() {
    address staker; bytes32 blsKey; uint256 sETHAmount; env e;

    require e.msg.sender != currentContract;

    uint256 balanceBefore = getSETHTokenBalance(blsKey, staker);
    unstake(e, staker, staker, blsKey, sETHAmount);
    uint256 balanceAfter = getSETHTokenBalance(blsKey, staker);

    assert balanceAfter - balanceBefore == sETHAmount;
}

rule viewFunctionMatchesActual() {
    uint256 newAccumulatedETHPerCollateralizedSharePerKnot = calculateNewAccumulatedETHPerCollateralizedSharePerKnot();

    env e;
    updateAccruedETHPerShares(e);

    assert(newAccumulatedETHPerCollateralizedSharePerKnot == accumulatedETHPerCollateralizedSlotPerKnot());
}

/**
 * Address 0 must have zero sETH balance.
 */
invariant addressZeroHasNoBalance()
    sETHToken.balanceOf(0) == 0
