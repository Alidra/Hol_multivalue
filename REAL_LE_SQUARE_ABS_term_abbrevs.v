Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term145 (x0 : nat) (x1 : real) (x2 : real) := (x0 = (NUMERAL 0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ (~ (real_lt x1 x2))).
Definition term152 (x0 : real) (x1 : real) (x2 : nat) := (~ ((~ (x2 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 x1)))) \/ (real_lt (real_pow x0 x2) (real_pow x1 x2)).
Definition term220 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) (real_abs x0)) /\ (real_le (real_abs x0) (real_abs x1)).
Definition term173 := fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y1)) \/ (~ (real_le y1 y2))) \/ (real_le (real_pow y1 y0) (real_pow y2 y0)).
Definition term159 := fun y0 : nat => forall y1 : real, forall y2 : real, ((y0 = (NUMERAL 0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) y1)) \/ (~ (real_lt y1 y2)))) \/ (real_lt (real_pow y1 y0) (real_pow y2 y0)).
Definition term71 := fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0).
Definition term62 := fun y0 : nat => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0).
Definition term10 (x0 : real) := real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0))).
Definition term225 := (~ False) -> False.
Definition term78 (x0 : real) (x1 : real) := ((real_le (real_abs x0) (real_abs x1)) /\ (~ (real_le (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0))))))) \/ ((~ (real_le (real_abs x0) (real_abs x1))) /\ (real_le (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0)))))).
Definition term48 (x0 : real) (x1 : real) := (~ ((real_le (real_abs x0) (real_abs x1)) = (real_le (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> (~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y0)) -> ~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)).
Definition term26 (x0 : real) (x1 : real) := (~ ((real_le (real_abs x0) (real_abs x1)) = (real_le (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) = False) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> False.
Definition term18 (x0 : real) := real_le (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))).
Definition term44 := imp (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)).
Definition term181 (x0 : nat) := (fun y0 : nat => forall y1 : real, forall y2 : real, ((y0 = (NUMERAL 0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) y1)) \/ (~ (real_lt y1 y2)))) \/ (real_lt (real_pow y1 y0) (real_pow y2 y0))) x0.
Definition term178 (x0 : nat) := (fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y1)) \/ (~ (real_le y1 y2))) \/ (real_le (real_pow y1 y0) (real_pow y2 y0))) x0.
Definition term214 (x0 : Prop) := ~ (~ x0).
Definition term177 (x0 : real) := (fun y0 : real => real_le (real_of_num (NUMERAL 0)) (real_abs y0)) x0.
Definition term139 (x0 : real) (x1 : real) := ~ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 x1)).
Definition term180 (x0 : real) (x1 : nat) (x2 : real) := (fun y0 : real => ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le x0 y0))) \/ (real_le (real_pow x0 x1) (real_pow y0 x1))) x2.
Definition term133 := and (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))).
Definition term257 (x0 : real) (x1 : real) (x2 : nat) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (~ (real_lt (real_pow x0 x2) (real_pow x1 x2))).
Definition term235 (x0 : real) (x1 : real) := ~ (real_lt (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0))))).
Definition term202 (x0 : nat) (x1 : real) (x2 : real) := (real_le (real_pow x2 x0) (real_pow x1 x0)) \/ ((~ (real_le x2 x1)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x2))).
Definition term63 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (real_abs x0).
Definition term111 (x0 : real) := and (forall y0 : real, (~ (real_le x0 y0)) \/ (~ (real_lt y0 x0))).
Definition term184 (x0 : real) (x1 : real) (x2 : nat) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ ((~ (real_le x0 x1)) \/ (real_le (real_pow x0 x2) (real_pow x1 x2))).
Definition term32 := imp (~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))).
Definition term79 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term204 (x0 : nat) (x1 : real) (x2 : real) := @eq Prop ((real_le (real_pow x2 x0) (real_pow x1 x0)) \/ ((~ (real_le x2 x1)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x2)))).
Definition term123 (x0 : real) := and ((fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))) x0).
Definition term45 := (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) = False) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> False.
Definition term153 (x0 : real) (x1 : real) (x2 : nat) := ((x2 = (NUMERAL 0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_lt x0 x1)))) \/ (real_lt (real_pow x0 x2) (real_pow x1 x2)).
Definition term176 (x0 : real) (x1 : real) := (~ (real_le (real_abs x0) (real_abs x1))) /\ (real_le (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0))))).
Definition term261 (x0 : real) (x1 : real) (x2 : nat) := imp ((~ (x2 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (~ (real_lt (real_pow x0 x2) (real_pow x1 x2))))).
Definition term114 (x0 : real) := forall y0 : real, (real_le x0 y0) \/ (real_lt y0 x0).
Definition term39 := (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) = False) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> False.
Definition term6 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term37 := (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> False.
Definition term132 := and (forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_le y1 y2)) \/ (~ (real_lt y2 y1))) y0).
Definition term110 (x0 : real) := and (forall y0 : real, (fun y1 : real => (~ (real_le x0 y1)) \/ (~ (real_lt y1 x0))) y0).
Definition term0 := S (Nat.add (BIT1 0) 0).
Definition term23 (x0 : Prop) := (~ x0) -> False.
Definition term238 (x0 : real) (x1 : real) (x2 : nat) := (~ (real_lt x0 x1)) \/ (real_lt (real_pow x0 x2) (real_pow x1 x2)).
Definition term218 (x0 : real) (x1 : real) := imp (~ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le x0 x1)))).
Definition term24 (x0 : real) (x1 : real) := (~ ((real_le (real_abs x0) (real_abs x1)) = (real_le (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0))))))) -> False.
Definition term22 (x0 : real) (x1 : real) := real_le (real_abs x0) (real_abs x1).
Definition term249 (x0 : real) (x1 : real) (x2 : nat) := (~ (real_lt x0 x1)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (real_lt (real_pow x0 x2) (real_pow x1 x2))).
Definition term236 (x0 : real) (x1 : real) := (real_lt (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0))))) -> ~ (real_lt (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0))))).
Definition term116 := fun y0 : real => (forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))) /\ (forall y1 : real, (real_le y0 y1) \/ (real_lt y1 y0)).
Definition term86 (x0 : real) (x1 : real) := ((~ (real_le x1 x0)) \/ (~ (real_lt x0 x1))) /\ ((real_le x1 x0) \/ (real_lt x0 x1)).
Definition term175 (x0 : real) (x1 : real) := (real_le (real_abs x0) (real_abs x1)) /\ (~ (real_le (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0)))))).
Definition term98 (x0 : real) := fun y0 : real => (real_le x0 y0) \/ (real_lt y0 x0).
Definition term140 (x0 : real) (x1 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_lt x0 x1)).
Definition term137 := (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))) /\ (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_lt y1 y0)).
Definition term208 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term119 := (forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_le y1 y2)) \/ (~ (real_lt y2 y1))) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, (real_le y1 y2) \/ (real_lt y2 y1)) y0).
Definition term96 (x0 : real) := (forall y0 : real, (fun y1 : real => (~ (real_le x0 y1)) \/ (~ (real_lt y1 x0))) y0) /\ (forall y0 : real, (fun y1 : real => (real_le x0 y1) \/ (real_lt y1 x0)) y0).
Definition term85 (x0 : real) (x1 : real) := ((~ (real_le x1 x0)) \/ (~ (real_lt x0 x1))) /\ ((~ (~ (real_le x1 x0))) \/ (real_lt x0 x1)).
Definition term264 (x0 : real) (x1 : real) := (~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) (real_abs x0)) /\ (~ (real_lt (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0))))))).
Definition term34 := ~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)).
Definition term52 (x0 : real) := forall y0 : real, (~ ((real_le (real_abs y0) (real_abs x0)) = (real_le (real_pow (real_abs y0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y1 : real, forall y2 : real, (~ (real_le y1 y2)) = (real_lt y2 y1)) -> (forall y1 : nat, forall y2 : real, forall y3 : real, ((~ (y1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt y2 y3))) -> real_lt (real_pow y2 y1) (real_pow y3 y1)) -> (~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) -> (forall y1 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y1)) -> ~ (forall y1 : nat, forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_le y2 y3)) -> real_le (real_pow y2 y1) (real_pow y3 y1)).
Definition term51 (x0 : real) := forall y0 : real, (~ ((real_le (real_abs y0) (real_abs x0)) = (real_le (real_pow (real_abs y0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y1 : real, forall y2 : real, (~ (real_le y1 y2)) = (real_lt y2 y1)) -> (forall y1 : nat, forall y2 : real, forall y3 : real, ((~ (y1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt y2 y3))) -> real_lt (real_pow y2 y1) (real_pow y3 y1)) -> (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) = False) -> (forall y1 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y1)) -> (forall y1 : nat, forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_le y2 y3)) -> real_le (real_pow y2 y1) (real_pow y3 y1)) -> False.
Definition term162 (x0 : real) (x1 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le x0 x1)).
Definition term164 (x0 : real) (x1 : real) := or (~ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 x1))).
Definition term195 (x0 : Prop) := (~ x0) -> x0.
Definition term194 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) (real_abs x0)).
Definition term57 (x0 : real) (x1 : real) (x2 : nat) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 x1)) -> real_le (real_pow x0 x2) (real_pow x1 x2).
Definition term229 (x0 : real) (x1 : real) := @eq Prop ((~ (real_le x1 x0)) \/ (~ (real_lt x0 x1))).
Definition term134 := fun y0 : real => (fun y1 : real => forall y2 : real, (real_le y1 y2) \/ (real_lt y2 y1)) y0.
Definition term129 := fun y0 : real => (fun y1 : real => forall y2 : real, (~ (real_le y1 y2)) \/ (~ (real_lt y2 y1))) y0.
Definition term211 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term185 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) x0).
Definition term198 (x0 : real) (x1 : real) (x2 : nat) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (real_le (real_pow x0 x2) (real_pow x1 x2)).
Definition term275 := forall y0 : real, forall y1 : real, (real_le (real_abs y0) (real_abs y1)) = (real_le (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow y1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term172 (x0 : nat) := forall y0 : real, forall y1 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (~ (real_le y0 y1))) \/ (real_le (real_pow y0 x0) (real_pow y1 x0)).
Definition term158 (x0 : nat) := forall y0 : real, forall y1 : real, ((x0 = (NUMERAL 0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (~ (real_lt y0 y1)))) \/ (real_lt (real_pow y0 x0) (real_pow y1 x0)).
Definition term136 := forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_lt y1 y0).
Definition term131 := forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0)).
Definition term90 := forall y0 : real, forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))) /\ ((real_le y0 y1) \/ (real_lt y1 y0)).
Definition term77 := forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0).
Definition term70 (x0 : nat) := forall y0 : real, forall y1 : real, ((~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1))) -> real_lt (real_pow y0 x0) (real_pow y1 x0).
Definition term61 (x0 : nat) := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_pow y0 x0) (real_pow y1 x0).
Definition term56 := forall y0 : real, forall y1 : real, (~ ((real_le (real_abs y1) (real_abs y0)) = (real_le (real_pow (real_abs y1) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs y0) (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y2 : real, forall y3 : real, (~ (real_le y2 y3)) = (real_lt y3 y2)) -> (forall y2 : nat, forall y3 : real, forall y4 : real, ((~ (y2 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y3) /\ (real_lt y3 y4))) -> real_lt (real_pow y3 y2) (real_pow y4 y2)) -> (~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) -> (forall y2 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y2)) -> ~ (forall y2 : nat, forall y3 : real, forall y4 : real, ((real_le (real_of_num (NUMERAL 0)) y3) /\ (real_le y3 y4)) -> real_le (real_pow y3 y2) (real_pow y4 y2)).
Definition term55 := forall y0 : real, forall y1 : real, (~ ((real_le (real_abs y1) (real_abs y0)) = (real_le (real_pow (real_abs y1) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs y0) (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y2 : real, forall y3 : real, (~ (real_le y2 y3)) = (real_lt y3 y2)) -> (forall y2 : nat, forall y3 : real, forall y4 : real, ((~ (y2 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y3) /\ (real_lt y3 y4))) -> real_lt (real_pow y3 y2) (real_pow y4 y2)) -> (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) = False) -> (forall y2 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y2)) -> (forall y2 : nat, forall y3 : real, forall y4 : real, ((real_le (real_of_num (NUMERAL 0)) y3) /\ (real_le y3 y4)) -> real_le (real_pow y3 y2) (real_pow y4 y2)) -> False.
Definition term271 (x0 : real) (x1 : real) := (real_le (real_abs x0) (real_abs x1)) -> False.
Definition term88 (x0 : real) := forall y0 : real, ((~ (real_le x0 y0)) \/ (~ (real_lt y0 x0))) /\ ((real_le x0 y0) \/ (real_lt y0 x0)).
Definition term92 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term13 := fun y0 : real => (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow (real_abs y0) (NUMERAL (BIT0 (BIT1 0)))).
Definition term148 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 x1).
Definition term209 (x0 : real) (x1 : real) (x2 : nat) := (~ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le x0 x1)))) -> real_le (real_pow x0 x2) (real_pow x1 x2).
Definition term82 (x0 : real) (x1 : real) := (~ (~ (real_le x1 x0))) \/ (real_lt x0 x1).
Definition term8 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term205 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x1)).
Definition term186 (x0 : real) (x1 : real) := ~ (real_le (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0))))).
Definition term68 (x0 : real) (x1 : nat) := forall y0 : real, ((~ (x1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 y0))) -> real_lt (real_pow x0 x1) (real_pow y0 x1).
Definition term59 (x0 : real) (x1 : nat) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 y0)) -> real_le (real_pow x0 x1) (real_pow y0 x1).
Definition term42 := (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) = False) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> False.
Definition term147 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term87 (x0 : real) := fun y0 : real => ((~ (real_le x0 y0)) \/ (~ (real_lt y0 x0))) /\ ((real_le x0 y0) \/ (real_lt y0 x0)).
Definition term219 (x0 : real) (x1 : real) := imp ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 x1)).
Definition term47 (x0 : real) (x1 : real) := imp (~ ((real_le (real_abs x0) (real_abs x1)) = (real_le (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0))))))).
Definition term163 (x0 : real) (x1 : real) (x2 : nat) := real_le (real_pow x0 x2) (real_pow x1 x2).
Definition term224 (x0 : real) (x1 : real) := (real_le (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0))))) -> False.
Definition term74 (x0 : real) := fun y0 : real => (~ (real_le x0 y0)) = (real_lt y0 x0).
Definition term237 (x0 : real) (x1 : real) := real_lt (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0)))).
Definition term128 := @eq Prop (forall y0 : real, (forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))) /\ (forall y1 : real, (real_le y0 y1) \/ (real_lt y1 y0))).
Definition term127 := @eq Prop (forall y0 : real, ((fun y1 : real => forall y2 : real, (~ (real_le y1 y2)) \/ (~ (real_lt y2 y1))) y0) /\ ((fun y1 : real => forall y2 : real, (real_le y1 y2) \/ (real_lt y2 y1)) y0)).
Definition term106 (x0 : real) := @eq Prop (forall y0 : real, ((~ (real_le x0 y0)) \/ (~ (real_lt y0 x0))) /\ ((real_le x0 y0) \/ (real_lt y0 x0))).
Definition term105 (x0 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => (~ (real_le x0 y1)) \/ (~ (real_lt y1 x0))) y0) /\ ((fun y1 : real => (real_le x0 y1) \/ (real_lt y1 x0)) y0)).
Definition term217 (x0 : real) := and (real_le (real_of_num (NUMERAL 0)) x0).
Definition term187 (x0 : real) (x1 : real) (x2 : nat) := (x2 = (NUMERAL 0)) \/ (((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_lt x0 x1))) \/ (real_lt (real_pow x0 x2) (real_pow x1 x2))).
Definition term221 (x0 : real) (x1 : real) (x2 : nat) := ((real_le (real_of_num (NUMERAL 0)) (real_abs x0)) /\ (real_le (real_abs x0) (real_abs x1))) -> real_le (real_pow (real_abs x0) x2) (real_pow (real_abs x1) x2).
Definition term240 (x0 : real) := or (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term228 (x0 : real) (x1 : real) := (~ (real_lt x1 x0)) \/ (~ (real_le x0 x1)).
Definition term259 (x0 : real) (x1 : real) (x2 : nat) := (~ (x2 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (~ (real_lt (real_pow x0 x2) (real_pow x1 x2)))).
Definition term171 (x0 : nat) := fun y0 : real => forall y1 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (~ (real_le y0 y1))) \/ (real_le (real_pow y0 x0) (real_pow y1 x0)).
Definition term157 (x0 : nat) := fun y0 : real => forall y1 : real, ((x0 = (NUMERAL 0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (~ (real_lt y0 y1)))) \/ (real_lt (real_pow y0 x0) (real_pow y1 x0)).
Definition term89 := fun y0 : real => forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))) /\ ((real_le y0 y1) \/ (real_lt y1 y0)).
Definition term69 (x0 : nat) := fun y0 : real => forall y1 : real, ((~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1))) -> real_lt (real_pow y0 x0) (real_pow y1 x0).
Definition term60 (x0 : nat) := fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_pow y0 x0) (real_pow y1 x0).
Definition term54 := fun y0 : real => forall y1 : real, (~ ((real_le (real_abs y1) (real_abs y0)) = (real_le (real_pow (real_abs y1) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs y0) (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y2 : real, forall y3 : real, (~ (real_le y2 y3)) = (real_lt y3 y2)) -> (forall y2 : nat, forall y3 : real, forall y4 : real, ((~ (y2 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y3) /\ (real_lt y3 y4))) -> real_lt (real_pow y3 y2) (real_pow y4 y2)) -> (~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) -> (forall y2 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y2)) -> ~ (forall y2 : nat, forall y3 : real, forall y4 : real, ((real_le (real_of_num (NUMERAL 0)) y3) /\ (real_le y3 y4)) -> real_le (real_pow y3 y2) (real_pow y4 y2)).
Definition term53 := fun y0 : real => forall y1 : real, (~ ((real_le (real_abs y1) (real_abs y0)) = (real_le (real_pow (real_abs y1) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs y0) (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y2 : real, forall y3 : real, (~ (real_le y2 y3)) = (real_lt y3 y2)) -> (forall y2 : nat, forall y3 : real, forall y4 : real, ((~ (y2 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y3) /\ (real_lt y3 y4))) -> real_lt (real_pow y3 y2) (real_pow y4 y2)) -> (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) = False) -> (forall y2 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y2)) -> (forall y2 : nat, forall y3 : real, forall y4 : real, ((real_le (real_of_num (NUMERAL 0)) y3) /\ (real_le y3 y4)) -> real_le (real_pow y3 y2) (real_pow y4 y2)) -> False.
Definition term33 := (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> False.
Definition term83 (x0 : real) (x1 : real) := (real_le x1 x0) \/ (real_lt x0 x1).
Definition term248 (x0 : real) (x1 : real) (x2 : nat) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (real_lt (real_pow x0 x2) (real_pow x1 x2)).
Definition term256 (x0 : real) (x1 : real) (x2 : nat) := ~ (real_lt (real_pow x0 x2) (real_pow x1 x2)).
Definition term75 (x0 : real) := forall y0 : real, (~ (real_le x0 y0)) = (real_lt y0 x0).
Definition term11 (x0 : real) := real_pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term223 (x0 : real) (x1 : real) := (~ (real_le (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0)))))) -> real_le (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0)))).
Definition term29 (x0 : real) (x1 : real) := (((~ ((real_le (real_abs x0) (real_abs x1)) = (real_le (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) = False) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> False) -> (~ ((real_le (real_abs x0) (real_abs x1)) = (real_le (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) = False) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> False) -> ((~ ((real_le (real_abs x0) (real_abs x1)) = (real_le (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) = False) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> False) -> (~ ((real_le (real_abs x0) (real_abs x1)) = (real_le (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) = False) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> False.
Definition term234 (x0 : real) (x1 : real) := (real_le (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0))))) -> ~ (real_lt (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0))))).
Definition term263 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) (real_abs x0)) /\ (~ (real_lt (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0)))))).
Definition term190 (x0 : real) (x1 : real) := ~ (real_lt x0 x1).
Definition term81 (x0 : real) (x1 : real) := or (real_le x0 x1).
Definition term3 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term142 (x0 : nat) := or (~ (~ (x0 = (NUMERAL 0)))).
Definition term241 (x0 : nat) (x1 : real) (x2 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ ((real_lt (real_pow x1 x0) (real_pow x2 x0)) \/ (~ (real_lt x1 x2))).
Definition term274 (x0 : real) := forall y0 : real, (real_le (real_abs x0) (real_abs y0)) = (real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term38 := (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y0)) -> ~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)).
Definition term189 (x0 : real) (x1 : real) (x2 : nat) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ ((~ (real_lt x0 x1)) \/ (real_lt (real_pow x0 x2) (real_pow x1 x2))).
Definition term12 := fun y0 : real => (real_pow (real_abs y0) (NUMERAL (BIT0 (BIT1 0)))) = (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term143 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term210 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term115 (x0 : real) := (forall y0 : real, (~ (real_le x0 y0)) \/ (~ (real_lt y0 x0))) /\ (forall y0 : real, (real_le x0 y0) \/ (real_lt y0 x0)).
Definition term174 := forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y1)) \/ (~ (real_le y1 y2))) \/ (real_le (real_pow y1 y0) (real_pow y2 y0)).
Definition term160 := forall y0 : nat, forall y1 : real, forall y2 : real, ((y0 = (NUMERAL 0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) y1)) \/ (~ (real_lt y1 y2)))) \/ (real_lt (real_pow y1 y0) (real_pow y2 y0)).
Definition term72 := forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0).
Definition term35 := forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0).
Definition term201 (x0 : real) (x1 : nat) (x2 : real) := (~ (real_le x2 x0)) \/ ((real_le (real_pow x2 x1) (real_pow x0 x1)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x2))).
Definition term166 (x0 : real) (x1 : real) (x2 : nat) := (~ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 x1))) \/ (real_le (real_pow x0 x2) (real_pow x1 x2)).
Definition term146 (x0 : nat) (x1 : real) (x2 : real) := ~ ((~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_lt x1 x2))).
Definition term254 (x0 : real) (x1 : real) (x2 : nat) := ~ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (real_lt (real_pow x0 x2) (real_pow x1 x2))).
Definition term144 (x0 : nat) (x1 : real) (x2 : real) := (~ (~ (x0 = (NUMERAL 0)))) \/ (~ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_lt x1 x2))).
Definition term268 (x0 : real) (x1 : real) := real_lt (real_abs x0) (real_abs x1).
Definition term203 (x0 : real) (x1 : real) (x2 : nat) := @eq Prop ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ ((~ (real_le x0 x1)) \/ (real_le (real_pow x0 x2) (real_pow x1 x2)))).
Definition term233 (x0 : real) (x1 : real) := (real_le x1 x0) -> ~ (real_lt x0 x1).
Definition term226 := ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) -> ~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)).
Definition term192 (x0 : real) (x1 : real) := ~ (real_le (real_abs x0) (real_abs x1)).
Definition term109 (x0 : real) := forall y0 : real, (~ (real_le x0 y0)) \/ (~ (real_lt y0 x0)).
Definition term84 (x0 : real) (x1 : real) := and ((~ (real_le x1 x0)) \/ (~ (real_lt x0 x1))).
Definition term107 (x0 : real) := fun y0 : real => (fun y1 : real => (~ (real_le x0 y1)) \/ (~ (real_lt y1 x0))) y0.
Definition term255 (x0 : real) (x1 : real) (x2 : nat) := (~ (~ (real_le (real_of_num (NUMERAL 0)) x0))) /\ (~ (real_lt (real_pow x0 x2) (real_pow x1 x2))).
Definition term243 (x0 : nat) (x1 : real) (x2 : real) := (x0 = (NUMERAL 0)) \/ ((real_lt (real_pow x1 x0) (real_pow x2 x0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ (~ (real_lt x1 x2)))).
Definition term150 (x0 : nat) (x1 : real) (x2 : real) := or (~ ((~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_lt x1 x2)))).
Definition term40 := (~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y0)) -> ~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)).
Definition term50 (x0 : real) := fun y0 : real => (~ ((real_le (real_abs y0) (real_abs x0)) = (real_le (real_pow (real_abs y0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y1 : real, forall y2 : real, (~ (real_le y1 y2)) = (real_lt y2 y1)) -> (forall y1 : nat, forall y2 : real, forall y3 : real, ((~ (y1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt y2 y3))) -> real_lt (real_pow y2 y1) (real_pow y3 y1)) -> (~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) -> (forall y1 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y1)) -> ~ (forall y1 : nat, forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_le y2 y3)) -> real_le (real_pow y2 y1) (real_pow y3 y1)).
Definition term49 (x0 : real) := fun y0 : real => (~ ((real_le (real_abs y0) (real_abs x0)) = (real_le (real_pow (real_abs y0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y1 : real, forall y2 : real, (~ (real_le y1 y2)) = (real_lt y2 y1)) -> (forall y1 : nat, forall y2 : real, forall y3 : real, ((~ (y1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt y2 y3))) -> real_lt (real_pow y2 y1) (real_pow y3 y1)) -> (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) = False) -> (forall y1 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y1)) -> (forall y1 : nat, forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_le y2 y3)) -> real_le (real_pow y2 y1) (real_pow y3 y1)) -> False.
Definition term267 (x0 : real) (x1 : real) := (real_lt (real_abs x0) (real_abs x1)) -> ~ (real_lt (real_abs x0) (real_abs x1)).
Definition term121 := fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_lt y1 y0).
Definition term76 := fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0).
Definition term93 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term230 (x0 : real) (x1 : real) := (~ (~ (real_le x1 x0))) -> ~ (real_lt x0 x1).
Definition term9 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term239 (x0 : nat) (x1 : real) (x2 : real) := (real_lt (real_pow x1 x0) (real_pow x2 x0)) \/ (~ (real_lt x1 x2)).
Definition term272 (x0 : real) := (fun y0 : real => forall y1 : real, (~ ((real_le (real_abs y1) (real_abs y0)) = (real_le (real_pow (real_abs y1) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs y0) (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y2 : real, forall y3 : real, (~ (real_le y2 y3)) = (real_lt y3 y2)) -> (forall y2 : nat, forall y3 : real, forall y4 : real, ((~ (y2 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y3) /\ (real_lt y3 y4))) -> real_lt (real_pow y3 y2) (real_pow y4 y2)) -> (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) = False) -> (forall y2 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y2)) -> (forall y2 : nat, forall y3 : real, forall y4 : real, ((real_le (real_of_num (NUMERAL 0)) y3) /\ (real_le y3 y4)) -> real_le (real_pow y3 y2) (real_pow y4 y2)) -> False) x0.
Definition term124 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_lt y1 y0)) x0.
Definition term122 (x0 : real) := (fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))) x0.
Definition term58 (x0 : real) (x1 : nat) := fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 y0)) -> real_le (real_pow x0 x1) (real_pow y0 x1).
Definition term244 (x0 : real) (x1 : real) (x2 : nat) := @eq Prop ((x2 = (NUMERAL 0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ ((~ (real_lt x0 x1)) \/ (real_lt (real_pow x0 x2) (real_pow x1 x2))))).
Definition term193 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) (real_abs x0))) -> real_le (real_of_num (NUMERAL 0)) (real_abs x0).
Definition term15 := forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow (real_abs y0) (NUMERAL (BIT0 (BIT1 0)))).
Definition term266 (x0 : real) (x1 : real) := ~ (real_lt (real_abs x0) (real_abs x1)).
Definition term165 (x0 : real) (x1 : real) := or ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le x0 x1))).
Definition term141 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term20 (x0 : real) (x1 : real) := real_le (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0)))).
Definition term151 (x0 : nat) (x1 : real) (x2 : real) := or ((x0 = (NUMERAL 0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ (~ (real_lt x1 x2)))).
Definition term16 (x0 : real) := (fun y0 : real => (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow (real_abs y0) (NUMERAL (BIT0 (BIT1 0))))) x0.
Definition term113 (x0 : real) := forall y0 : real, (fun y1 : real => (real_le x0 y1) \/ (real_lt y1 x0)) y0.
Definition term108 (x0 : real) := forall y0 : real, (fun y1 : real => (~ (real_le x0 y1)) \/ (~ (real_lt y1 x0))) y0.
Definition term207 (x0 : nat) (x1 : real) (x2 : real) := (real_le (real_pow x1 x0) (real_pow x2 x0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ (~ (real_le x1 x2))).
Definition term199 (x0 : real) (x1 : nat) (x2 : real) := (real_le (real_pow x2 x1) (real_pow x0 x1)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x2)).
Definition term25 (x0 : real) (x1 : real) := ~ ((real_le (real_abs x0) (real_abs x1)) = (real_le (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0)))))).
Definition term126 := fun y0 : real => ((fun y1 : real => forall y2 : real, (~ (real_le y1 y2)) \/ (~ (real_lt y2 y1))) y0) /\ ((fun y1 : real => forall y2 : real, (real_le y1 y2) \/ (real_lt y2 y1)) y0).
Definition term200 (x0 : real) (x1 : real) := or (~ (real_le x0 x1)).
Definition term216 (x0 : real) := and (~ (~ (real_le (real_of_num (NUMERAL 0)) x0))).
Definition term4 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term103 (x0 : real) (x1 : real) := ((fun y0 : real => (~ (real_le x0 y0)) \/ (~ (real_lt y0 x0))) x1) /\ ((fun y0 : real => (real_le x0 y0) \/ (real_lt y0 x0)) x1).
Definition term182 (x0 : nat) (x1 : real) := (fun y0 : real => forall y1 : real, ((x0 = (NUMERAL 0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (~ (real_lt y0 y1)))) \/ (real_lt (real_pow y0 x0) (real_pow y1 x0))) x1.
Definition term179 (x0 : nat) (x1 : real) := (fun y0 : real => forall y1 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (~ (real_le y0 y1))) \/ (real_le (real_pow y0 x0) (real_pow y1 x0))) x1.
Definition term2 := NUMERAL (BIT0 (BIT1 0)).
Definition term258 (x0 : nat) := and (~ (x0 = (NUMERAL 0))).
Definition term99 (x0 : real) (x1 : real) := (fun y0 : real => (~ (real_le x0 y0)) \/ (~ (real_lt y0 x0))) x1.
Definition term245 (x0 : nat) (x1 : real) (x2 : real) := @eq Prop ((x0 = (NUMERAL 0)) \/ ((real_lt (real_pow x1 x0) (real_pow x2 x0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ (~ (real_lt x1 x2))))).
Definition term97 (x0 : real) := fun y0 : real => (~ (real_le x0 y0)) \/ (~ (real_lt y0 x0)).
Definition term28 (x0 : real) (x1 : real) := (((~ ((real_le (real_abs x0) (real_abs x1)) = (real_le (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) = False) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> False) -> (~ ((real_le (real_abs x0) (real_abs x1)) = (real_le (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) = False) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> False) -> (~ ((real_le (real_abs x0) (real_abs x1)) = (real_le (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) = False) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> False.
Definition term169 (x0 : real) (x1 : nat) := fun y0 : real => ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le x0 y0))) \/ (real_le (real_pow x0 x1) (real_pow y0 x1)).
Definition term17 (x0 : real) := real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term27 (x0 : real) (x1 : real) := ((~ ((real_le (real_abs x0) (real_abs x1)) = (real_le (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) = False) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> False) -> (~ ((real_le (real_abs x0) (real_abs x1)) = (real_le (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) = False) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> False.
Definition term262 (x0 : nat) (x1 : real) (x2 : real) := ((~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (~ (real_lt (real_pow x1 x0) (real_pow x2 x0))))) -> ~ (real_lt x1 x2).
Definition term188 (x0 : real) (x1 : real) (x2 : nat) := ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_lt x0 x1))) \/ (real_lt (real_pow x0 x2) (real_pow x1 x2)).
Definition term66 (x0 : real) (x1 : real) (x2 : nat) := ((~ (x2 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 x1))) -> real_lt (real_pow x0 x2) (real_pow x1 x2).
Definition term250 (x0 : nat) (x1 : real) (x2 : real) := (~ ((x0 = (NUMERAL 0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ (real_lt (real_pow x1 x0) (real_pow x2 x0))))) -> ~ (real_lt x1 x2).
Definition term149 (x0 : real) (x1 : real) (x2 : nat) := real_lt (real_pow x0 x2) (real_pow x1 x2).
Definition term232 (x0 : real) (x1 : real) := imp (real_le x0 x1).
Definition term73 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term100 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) \/ (~ (real_lt x0 x1)).
Definition term30 := ~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)).
Definition term117 := forall y0 : real, (forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))) /\ (forall y1 : real, (real_le y0 y1) \/ (real_lt y1 y0)).
Definition term206 (x0 : real) (x1 : real) (x2 : nat) := or (real_le (real_pow x0 x2) (real_pow x1 x2)).
Definition term212 (x0 : real) (x1 : real) := ~ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le x0 x1))).
Definition term1 := BIT0 (BIT1 0).
Definition term270 (x0 : real) (x1 : real) := (~ (real_lt (real_abs x1) (real_abs x0))) -> real_le (real_abs x0) (real_abs x1).
Definition term196 (x0 : real) (x1 : real) := (~ (real_le (real_abs x0) (real_abs x1))) -> real_le (real_abs x0) (real_abs x1).
Definition term135 := forall y0 : real, (fun y1 : real => forall y2 : real, (real_le y1 y2) \/ (real_lt y2 y1)) y0.
Definition term130 := forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_le y1 y2)) \/ (~ (real_lt y2 y1))) y0.
Definition term252 (x0 : real) (x1 : real) (x2 : nat) := ~ ((x2 = (NUMERAL 0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (real_lt (real_pow x0 x2) (real_pow x1 x2)))).
Definition term154 (x0 : nat) (x1 : real) (x2 : real) := (~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_lt x1 x2)).
Definition term247 (x0 : real) (x1 : real) (x2 : nat) := (x2 = (NUMERAL 0)) \/ ((~ (real_lt x0 x1)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (real_lt (real_pow x0 x2) (real_pow x1 x2)))).
Definition term191 (x0 : real) (x1 : real) (x2 : nat) := (x2 = (NUMERAL 0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ ((~ (real_lt x0 x1)) \/ (real_lt (real_pow x0 x2) (real_pow x1 x2)))).
Definition term14 := forall y0 : real, (real_pow (real_abs y0) (NUMERAL (BIT0 (BIT1 0)))) = (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term125 (x0 : real) := ((fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))) x0) /\ ((fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_lt y1 y0)) x0).
Definition term64 := fun y0 : real => real_le (real_of_num (NUMERAL 0)) (real_abs y0).
Definition term183 (x0 : real) (x1 : nat) (x2 : real) := (fun y0 : real => ((x1 = (NUMERAL 0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_lt x0 y0)))) \/ (real_lt (real_pow x0 x1) (real_pow y0 x1))) x2.
Definition term104 (x0 : real) := fun y0 : real => ((fun y1 : real => (~ (real_le x0 y1)) \/ (~ (real_lt y1 x0))) y0) /\ ((fun y1 : real => (real_le x0 y1) \/ (real_lt y1 x0)) y0).
Definition term242 (x0 : nat) (x1 : real) (x2 : real) := (real_lt (real_pow x1 x0) (real_pow x2 x0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ (~ (real_lt x1 x2))).
Definition term112 (x0 : real) := fun y0 : real => (fun y1 : real => (real_le x0 y1) \/ (real_lt y1 x0)) y0.
Definition term67 (x0 : real) (x1 : nat) := fun y0 : real => ((~ (x1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 y0))) -> real_lt (real_pow x0 x1) (real_pow y0 x1).
Definition term167 (x0 : real) (x1 : real) (x2 : nat) := ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le x0 x1))) \/ (real_le (real_pow x0 x2) (real_pow x1 x2)).
Definition term5 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term36 := imp (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y0)).
Definition term94 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term80 (x0 : real) (x1 : real) := or (~ (~ (real_le x0 x1))).
Definition term251 (x0 : real) (x1 : real) (x2 : nat) := (x2 = (NUMERAL 0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (real_lt (real_pow x0 x2) (real_pow x1 x2))).
Definition term19 (x0 : real) (x1 : real) := real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))).
Definition term46 := (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> (~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y0)) -> ~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)).
Definition term91 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term43 := (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> (~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y0)) -> ~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)).
Definition term21 (x0 : real) (x1 : real) := @eq Prop (real_le (real_abs x0) (real_abs x1)).
Definition term265 (x0 : real) (x1 : real) := ((~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) (real_abs x0)) /\ (~ (real_lt (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x1) (NUMERAL (BIT0 (BIT1 0)))))))) -> ~ (real_lt (real_abs x0) (real_abs x1)).
Definition term7 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term170 (x0 : real) (x1 : nat) := forall y0 : real, ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le x0 y0))) \/ (real_le (real_pow x0 x1) (real_pow y0 x1)).
Definition term156 (x0 : real) (x1 : nat) := forall y0 : real, ((x1 = (NUMERAL 0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_lt x0 y0)))) \/ (real_lt (real_pow x0 x1) (real_pow y0 x1)).
Definition term138 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term155 (x0 : real) (x1 : nat) := fun y0 : real => ((x1 = (NUMERAL 0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_lt x0 y0)))) \/ (real_lt (real_pow x0 x1) (real_pow y0 x1)).
Definition term246 (x0 : real) (x1 : real) (x2 : nat) := (~ (real_lt x0 x1)) \/ ((x2 = (NUMERAL 0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (real_lt (real_pow x0 x2) (real_pow x1 x2)))).
Definition term101 (x0 : real) (x1 : real) := and ((fun y0 : real => (~ (real_le x0 y0)) \/ (~ (real_lt y0 x0))) x1).
Definition term161 (x0 : real) (x1 : real) := ~ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 x1)).
Definition term222 (x0 : real) (x1 : real) (x2 : nat) := real_le (real_pow (real_abs x0) x2) (real_pow (real_abs x1) x2).
Definition term31 := imp (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) = False).
Definition term41 := imp (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)).
Definition term215 (x0 : real) := ~ (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term65 := forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y0).
Definition term213 (x0 : real) (x1 : real) := (~ (~ (real_le (real_of_num (NUMERAL 0)) x0))) /\ (~ (~ (real_le x0 x1))).
Definition term118 := forall y0 : real, ((fun y1 : real => forall y2 : real, (~ (real_le y1 y2)) \/ (~ (real_lt y2 y1))) y0) /\ ((fun y1 : real => forall y2 : real, (real_le y1 y2) \/ (real_lt y2 y1)) y0).
Definition term95 (x0 : real) := forall y0 : real, ((fun y1 : real => (~ (real_le x0 y1)) \/ (~ (real_lt y1 x0))) y0) /\ ((fun y1 : real => (real_le x0 y1) \/ (real_lt y1 x0)) y0).
Definition term269 (x0 : real) (x1 : real) := (~ (real_lt x1 x0)) -> real_le x0 x1.
Definition term197 (x0 : real) (x1 : real) (x2 : nat) := (~ (real_le x0 x1)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (real_le (real_pow x0 x2) (real_pow x1 x2))).
Definition term273 (x0 : real) (x1 : real) := (fun y0 : real => (~ ((real_le (real_abs y0) (real_abs x0)) = (real_le (real_pow (real_abs y0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y1 : real, forall y2 : real, (~ (real_le y1 y2)) = (real_lt y2 y1)) -> (forall y1 : nat, forall y2 : real, forall y3 : real, ((~ (y1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt y2 y3))) -> real_lt (real_pow y2 y1) (real_pow y3 y1)) -> (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) = False) -> (forall y1 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y1)) -> (forall y1 : nat, forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_le y2 y3)) -> real_le (real_pow y2 y1) (real_pow y3 y1)) -> False) x1.
Definition term168 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 x1).
Definition term253 (x0 : real) (x1 : real) (x2 : nat) := (~ (x2 = (NUMERAL 0))) /\ (~ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (real_lt (real_pow x0 x2) (real_pow x1 x2)))).
Definition term102 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) \/ (real_lt y0 x0)) x1.
Definition term260 (x0 : real) (x1 : real) (x2 : nat) := imp (~ ((x2 = (NUMERAL 0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (real_lt (real_pow x0 x2) (real_pow x1 x2))))).
Definition term227 (x0 : Prop) := x0 -> ~ x0.
Definition term120 := fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0)).
Definition term231 (x0 : real) (x1 : real) := imp (~ (~ (real_le x0 x1))).
