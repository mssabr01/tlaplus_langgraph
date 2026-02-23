---------------------------- MODULE free_tokens ----------------------------
(* MUTANT: Swap can output tokens without requiring any input.
   TLC should find a violation of NoFreeTokens. *)

EXTENDS Integers, FiniteSets

CONSTANTS MaxBalance

ASSUME MaxBalance \in Nat /\ MaxBalance > 0

VARIABLES reserve0, reserve1, userBalance0, userBalance1

vars == <<reserve0, reserve1, userBalance0, userBalance1>>

Init ==
    /\ reserve0 = MaxBalance
    /\ reserve1 = MaxBalance
    /\ userBalance0 = 0
    /\ userBalance1 = 0

(* BUG: amtIn can be 0, so user gets free tokens *)
Swap0For1 ==
    /\ \E amtIn \in 0..userBalance0 :
        /\ \E amtOut \in 1..reserve1 :
            /\ reserve0' = reserve0 + amtIn
            /\ reserve1' = reserve1 - amtOut
            /\ userBalance0' = userBalance0 - amtIn
            /\ userBalance1' = userBalance1 + amtOut

Swap1For0 ==
    /\ \E amtIn \in 0..userBalance1 :
        /\ \E amtOut \in 1..reserve0 :
            /\ reserve1' = reserve1 + amtIn
            /\ reserve0' = reserve0 - amtOut
            /\ userBalance1' = userBalance1 - amtIn
            /\ userBalance0' = userBalance0 + amtOut

Next == Swap0For1 \/ Swap1For0

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ reserve0 \in 0..MaxBalance * 2
    /\ reserve1 \in 0..MaxBalance * 2
    /\ userBalance0 \in 0..MaxBalance * 2
    /\ userBalance1 \in 0..MaxBalance * 2

(* This SHOULD be violated — user gets tokens for free *)
NoFreeTokens ==
    userBalance0 + userBalance1 <= MaxBalance

=============================================================================
