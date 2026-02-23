-------------------------- MODULE negative_balance --------------------------
(* MUTANT: Swap allows withdrawing more tokens than reserves hold.
   TLC should find a violation of TypeOK (reserve goes negative). *)

EXTENDS Integers, FiniteSets

CONSTANTS MaxBalance

ASSUME MaxBalance \in Nat /\ MaxBalance > 0

VARIABLES reserve0, reserve1, userBalance0, userBalance1

vars == <<reserve0, reserve1, userBalance0, userBalance1>>

Init ==
    /\ reserve0 = MaxBalance
    /\ reserve1 = MaxBalance
    /\ userBalance0 = MaxBalance
    /\ userBalance1 = 0

(* BUG: amtOut is not bounded by reserve1 — can overdraw *)
Swap0For1 ==
    /\ userBalance0 > 0
    /\ \E amtIn \in 1..userBalance0 :
        /\ \E amtOut \in 1..(MaxBalance * 2) :
            /\ reserve0' = reserve0 + amtIn
            /\ reserve1' = reserve1 - amtOut
            /\ userBalance0' = userBalance0 - amtIn
            /\ userBalance1' = userBalance1 + amtOut
            /\ (reserve0 + amtIn) * (reserve1 - amtOut) >= reserve0 * reserve1

Next == Swap0For1

Spec == Init /\ [][Next]_vars

(* This SHOULD be violated because reserve1 can go below 0 *)
TypeOK ==
    /\ reserve0 \in 0..MaxBalance * 3
    /\ reserve1 \in 0..MaxBalance * 3
    /\ userBalance0 \in 0..MaxBalance * 3
    /\ userBalance1 \in 0..MaxBalance * 3

=============================================================================
