Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term89 (x0 : nat) (x1 : nat) := forall y0 : nat, ((~ (num_divides x0 x1)) \/ (~ (num_divides y0 (Nat.div x1 x0)))) \/ (num_divides (Nat.mul x0 y0) x1).
Definition term123 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((num_divides y2 y1) /\ (num_divides y3 (Nat.div y1 y2))) \/ (~ (num_divides (Nat.mul y2 y3) y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((~ (num_divides y2 y1)) \/ (~ (num_divides y3 (Nat.div y1 y2)))) \/ (num_divides (Nat.mul y2 y3) y1)) y0).
Definition term101 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, ((num_divides y1 x0) /\ (num_divides y2 (Nat.div x0 y1))) \/ (~ (num_divides (Nat.mul y1 y2) x0))) y0) /\ ((fun y1 : nat => forall y2 : nat, ((~ (num_divides y1 x0)) \/ (~ (num_divides y2 (Nat.div x0 y1)))) \/ (num_divides (Nat.mul y1 y2) x0)) y0).
Definition term29 (x0 : nat -> Prop) := ~ (all x0).
Definition term158 := (~ False) -> False.
Definition term4 := (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides (Nat.mul y1 y2) y0) -> num_divides y2 (Nat.div y0 y1))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) /\ (num_divides y2 (Nat.div y0 y1))) = (num_divides (Nat.mul y1 y2) y0)) -> False.
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat) := and ((fun y0 : nat => ((num_divides x0 x1) /\ (num_divides y0 (Nat.div x1 x0))) \/ (~ (num_divides (Nat.mul x0 y0) x1))) x2).
Definition term115 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((num_divides y2 y1) /\ (num_divides y3 (Nat.div y1 y2))) \/ (~ (num_divides (Nat.mul y2 y3) y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((~ (num_divides y2 y1)) \/ (~ (num_divides y3 (Nat.div y1 y2)))) \/ (num_divides (Nat.mul y2 y3) y1)) y0).
Definition term93 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((num_divides y1 x0) /\ (num_divides y2 (Nat.div x0 y1))) \/ (~ (num_divides (Nat.mul y1 y2) x0))) y0) /\ ((fun y1 : nat => forall y2 : nat, ((~ (num_divides y1 x0)) \/ (~ (num_divides y2 (Nat.div x0 y1)))) \/ (num_divides (Nat.mul y1 y2) x0)) y0).
Definition term70 (x0 : nat) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => ((num_divides x0 x1) /\ (num_divides y1 (Nat.div x1 x0))) \/ (~ (num_divides (Nat.mul x0 y1) x1))) y0) /\ ((fun y1 : nat => ((~ (num_divides x0 x1)) \/ (~ (num_divides y1 (Nat.div x1 x0)))) \/ (num_divides (Nat.mul x0 y1) x1)) y0).
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) := num_divides (Nat.mul x0 x1) x2.
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (num_divides (Nat.mul x1 y0) x0) -> num_divides y0 (Nat.div x0 x1)) x2.
Definition term152 (x0 : Prop) := ~ (~ x0).
Definition term143 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) \/ (~ (num_divides (Nat.mul y1 y2) y0))) /\ ((num_divides y2 (Nat.div y0 y1)) \/ (~ (num_divides (Nat.mul y1 y2) y0)))) x0.
Definition term121 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (num_divides y1 y0)) \/ (~ (num_divides y2 (Nat.div y0 y1)))) \/ (num_divides (Nat.mul y1 y2) y0)) x0.
Definition term119 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) /\ (num_divides y2 (Nat.div y0 y1))) \/ (~ (num_divides (Nat.mul y1 y2) y0))) x0.
Definition term46 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (num_divides (Nat.mul y1 y2) y0) -> num_divides y2 (Nat.div y0 y1)) x0.
Definition term79 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => ((num_divides x0 x1) /\ (num_divides y1 (Nat.div x1 x0))) \/ (~ (num_divides (Nat.mul x0 y1) x1))) y0) /\ ((fun y1 : nat => ((~ (num_divides x0 x1)) \/ (~ (num_divides y1 (Nat.div x1 x0)))) \/ (num_divides (Nat.mul x0 y1) x1)) y0).
Definition term55 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((num_divides x0 x2) /\ (num_divides x1 (Nat.div x2 x0)))) \/ (num_divides (Nat.mul x0 x1) x2).
Definition term155 (x0 : nat) (x1 : nat) (x2 : nat) := imp (num_divides (Nat.mul x0 x1) x2).
Definition term154 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ (~ (num_divides (Nat.mul x0 x1) x2))).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term116 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((num_divides y2 y1) /\ (num_divides y3 (Nat.div y1 y2))) \/ (~ (num_divides (Nat.mul y2 y3) y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((~ (num_divides y2 y1)) \/ (~ (num_divides y3 (Nat.div y1 y2)))) \/ (num_divides (Nat.mul y2 y3) y1)) y0).
Definition term94 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((num_divides y1 x0) /\ (num_divides y2 (Nat.div x0 y1))) \/ (~ (num_divides (Nat.mul y1 y2) x0))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((~ (num_divides y1 x0)) \/ (~ (num_divides y2 (Nat.div x0 y1)))) \/ (num_divides (Nat.mul y1 y2) x0)) y0).
Definition term71 (x0 : nat) (x1 : nat) := (forall y0 : nat, (fun y1 : nat => ((num_divides x0 x1) /\ (num_divides y1 (Nat.div x1 x0))) \/ (~ (num_divides (Nat.mul x0 y1) x1))) y0) /\ (forall y0 : nat, (fun y1 : nat => ((~ (num_divides x0 x1)) \/ (~ (num_divides y1 (Nat.div x1 x0)))) \/ (num_divides (Nat.mul x0 y1) x1)) y0).
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) := (num_divides (Nat.mul x2 x0) x1) -> num_divides x0 (Nat.div x1 x2).
Definition term134 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) /\ (num_divides y2 (Nat.div y0 y1))) \/ (~ (num_divides (Nat.mul y1 y2) y0))) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (num_divides y1 y0)) \/ (~ (num_divides y2 (Nat.div y0 y1)))) \/ (num_divides (Nat.mul y1 y2) y0)).
Definition term112 (x0 : nat) := (forall y0 : nat, forall y1 : nat, ((num_divides y0 x0) /\ (num_divides y1 (Nat.div x0 y0))) \/ (~ (num_divides (Nat.mul y0 y1) x0))) /\ (forall y0 : nat, forall y1 : nat, ((~ (num_divides y0 x0)) \/ (~ (num_divides y1 (Nat.div x0 y0)))) \/ (num_divides (Nat.mul y0 y1) x0)).
Definition term61 (x0 : nat) (x1 : nat) := forall y0 : nat, (((num_divides x0 x1) /\ (num_divides y0 (Nat.div x1 x0))) \/ (~ (num_divides (Nat.mul x0 y0) x1))) /\ (((~ (num_divides x0 x1)) \/ (~ (num_divides y0 (Nat.div x1 x0)))) \/ (num_divides (Nat.mul x0 y0) x1)).
Definition term41 (x0 : nat) (x1 : nat) := ~ ((fun y0 : nat => forall y1 : nat, (num_divides (Nat.mul y0 y1) x0) -> num_divides y1 (Nat.div x0 y0)) x1).
Definition term113 := fun y0 : nat => (forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) /\ (num_divides y2 (Nat.div y0 y1))) \/ (~ (num_divides (Nat.mul y1 y2) y0))) /\ (forall y1 : nat, forall y2 : nat, ((~ (num_divides y1 y0)) \/ (~ (num_divides y2 (Nat.div y0 y1)))) \/ (num_divides (Nat.mul y1 y2) y0)).
Definition term88 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => ((~ (num_divides x0 x1)) \/ (~ (num_divides y1 (Nat.div x1 x0)))) \/ (num_divides (Nat.mul x0 y1) x1)) y0.
Definition term83 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => ((num_divides x0 x1) /\ (num_divides y1 (Nat.div x1 x0))) \/ (~ (num_divides (Nat.mul x0 y1) x1))) y0.
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((num_divides x2 x1) /\ (num_divides x0 (Nat.div x1 x2))).
Definition term150 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term68 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term31 (x0 : nat) (x1 : nat) := ~ (forall y0 : nat, (num_divides (Nat.mul x1 y0) x0) -> num_divides y0 (Nat.div x0 x1)).
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := (num_divides x2 x1) /\ (num_divides x0 (Nat.div x1 x2)).
Definition term91 (x0 : nat) := fun y0 : nat => (forall y1 : nat, ((num_divides y0 x0) /\ (num_divides y1 (Nat.div x0 y0))) \/ (~ (num_divides (Nat.mul y0 y1) x0))) /\ (forall y1 : nat, ((~ (num_divides y0 x0)) \/ (~ (num_divides y1 (Nat.div x0 y0)))) \/ (num_divides (Nat.mul y0 y1) x0)).
Definition term38 (x0 : nat) := ~ (forall y0 : nat, forall y1 : nat, (num_divides (Nat.mul y0 y1) x0) -> num_divides y1 (Nat.div x0 y0)).
Definition term9 := ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) /\ (num_divides y2 (Nat.div y0 y1))) = (num_divides (Nat.mul y1 y2) y0)).
Definition term3 := ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides (Nat.mul y1 y2) y0) -> num_divides y2 (Nat.div y0 y1)).
Definition term149 (x0 : Prop) := (~ x0) -> x0.
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := (num_divides (Nat.mul x2 x0) x1) /\ (~ (num_divides x0 (Nat.div x1 x2))).
Definition term151 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (num_divides (Nat.mul x2 x0) x1))) -> num_divides x0 (Nat.div x1 x2).
Definition term78 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => ((num_divides x0 x1) /\ (num_divides y0 (Nat.div x1 x0))) \/ (~ (num_divides (Nat.mul x0 y0) x1))) x2) /\ ((fun y0 : nat => ((~ (num_divides x0 x1)) \/ (~ (num_divides y0 (Nat.div x1 x0)))) \/ (num_divides (Nat.mul x0 y0) x1)) x2).
Definition term43 (x0 : nat) := fun y0 : nat => exists y1 : nat, (num_divides (Nat.mul y0 y1) x0) /\ (~ (num_divides y1 (Nat.div x0 y0))).
Definition term125 := @eq Prop (forall y0 : nat, (forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) /\ (num_divides y2 (Nat.div y0 y1))) \/ (~ (num_divides (Nat.mul y1 y2) y0))) /\ (forall y1 : nat, forall y2 : nat, ((~ (num_divides y1 y0)) \/ (~ (num_divides y2 (Nat.div y0 y1)))) \/ (num_divides (Nat.mul y1 y2) y0))).
Definition term124 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((num_divides y2 y1) /\ (num_divides y3 (Nat.div y1 y2))) \/ (~ (num_divides (Nat.mul y2 y3) y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((~ (num_divides y2 y1)) \/ (~ (num_divides y3 (Nat.div y1 y2)))) \/ (num_divides (Nat.mul y2 y3) y1)) y0)).
Definition term103 (x0 : nat) := @eq Prop (forall y0 : nat, (forall y1 : nat, ((num_divides y0 x0) /\ (num_divides y1 (Nat.div x0 y0))) \/ (~ (num_divides (Nat.mul y0 y1) x0))) /\ (forall y1 : nat, ((~ (num_divides y0 x0)) \/ (~ (num_divides y1 (Nat.div x0 y0)))) \/ (num_divides (Nat.mul y0 y1) x0))).
Definition term102 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((num_divides y1 x0) /\ (num_divides y2 (Nat.div x0 y1))) \/ (~ (num_divides (Nat.mul y1 y2) x0))) y0) /\ ((fun y1 : nat => forall y2 : nat, ((~ (num_divides y1 x0)) \/ (~ (num_divides y2 (Nat.div x0 y1)))) \/ (num_divides (Nat.mul y1 y2) x0)) y0)).
Definition term81 (x0 : nat) (x1 : nat) := @eq Prop (forall y0 : nat, (((num_divides x0 x1) /\ (num_divides y0 (Nat.div x1 x0))) \/ (~ (num_divides (Nat.mul x0 y0) x1))) /\ (((~ (num_divides x0 x1)) \/ (~ (num_divides y0 (Nat.div x1 x0)))) \/ (num_divides (Nat.mul x0 y0) x1))).
Definition term80 (x0 : nat) (x1 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => ((num_divides x0 x1) /\ (num_divides y1 (Nat.div x1 x0))) \/ (~ (num_divides (Nat.mul x0 y1) x1))) y0) /\ ((fun y1 : nat => ((~ (num_divides x0 x1)) \/ (~ (num_divides y1 (Nat.div x1 x0)))) \/ (num_divides (Nat.mul x0 y1) x1)) y0)).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term146 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (num_divides x0 (Nat.div x1 x2)).
Definition term144 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((num_divides y0 x0) \/ (~ (num_divides (Nat.mul y0 y1) x0))) /\ ((num_divides y1 (Nat.div x0 y0)) \/ (~ (num_divides (Nat.mul y0 y1) x0)))) x1.
Definition term99 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((~ (num_divides y0 x0)) \/ (~ (num_divides y1 (Nat.div x0 y0)))) \/ (num_divides (Nat.mul y0 y1) x0)) x1.
Definition term97 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((num_divides y0 x0) /\ (num_divides y1 (Nat.div x0 y0))) \/ (~ (num_divides (Nat.mul y0 y1) x0))) x1.
Definition term40 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (num_divides (Nat.mul y0 y1) x0) -> num_divides y1 (Nat.div x0 y0)) x1.
Definition term72 (x0 : nat) (x1 : nat) := fun y0 : nat => ((num_divides x0 x1) /\ (num_divides y0 (Nat.div x1 x0))) \/ (~ (num_divides (Nat.mul x0 y0) x1)).
Definition term59 (x0 : nat) (x1 : nat) (x2 : nat) := (((num_divides x0 x2) /\ (num_divides x1 (Nat.div x2 x0))) \/ (~ (num_divides (Nat.mul x0 x1) x2))) /\ (((~ (num_divides x0 x2)) \/ (~ (num_divides x1 (Nat.div x2 x0)))) \/ (num_divides (Nat.mul x0 x1) x2)).
Definition term96 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((~ (num_divides y0 x0)) \/ (~ (num_divides y1 (Nat.div x0 y0)))) \/ (num_divides (Nat.mul y0 y1) x0).
Definition term17 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((num_divides y0 x0) /\ (num_divides y1 (Nat.div x0 y0))) = (num_divides (Nat.mul y0 y1) x0).
Definition term75 (x0 : nat) (x1 : nat) (x2 : nat) := ((num_divides x0 x2) /\ (num_divides x1 (Nat.div x2 x0))) \/ (~ (num_divides (Nat.mul x0 x1) x2)).
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((num_divides x0 x1) /\ (num_divides y0 (Nat.div x1 x0))) \/ (~ (num_divides (Nat.mul x0 y0) x1))) x2.
Definition term58 (x0 : nat) (x1 : nat) (x2 : nat) := (((num_divides x0 x2) /\ (num_divides x1 (Nat.div x2 x0))) \/ (~ (num_divides (Nat.mul x0 x1) x2))) /\ ((~ ((num_divides x0 x2) /\ (num_divides x1 (Nat.div x2 x0)))) \/ (num_divides (Nat.mul x0 x1) x2)).
Definition term56 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (num_divides x0 x2)) \/ (~ (num_divides x1 (Nat.div x2 x0)))) \/ (num_divides (Nat.mul x0 x1) x2).
Definition term82 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => ((num_divides x0 x1) /\ (num_divides y1 (Nat.div x1 x0))) \/ (~ (num_divides (Nat.mul x0 y1) x1))) y0.
Definition term57 (x0 : nat) (x1 : nat) (x2 : nat) := and (((num_divides x0 x2) /\ (num_divides x1 (Nat.div x2 x0))) \/ (~ (num_divides (Nat.mul x0 x1) x2))).
Definition term8 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) /\ (num_divides y2 (Nat.div y0 y1))) = (num_divides (Nat.mul y1 y2) y0)) -> False.
Definition term54 (x0 : nat) (x1 : nat) (x2 : nat) := or ((~ (num_divides x2 x1)) \/ (~ (num_divides x0 (Nat.div x1 x2)))).
Definition term86 (x0 : nat) (x1 : nat) := and (forall y0 : nat, ((num_divides x0 x1) /\ (num_divides y0 (Nat.div x1 x0))) \/ (~ (num_divides (Nat.mul x0 y0) x1))).
Definition term135 (x0 : nat) (x1 : nat) (x2 : nat) := ((num_divides x0 x2) \/ (~ (num_divides (Nat.mul x0 x1) x2))) /\ ((num_divides x1 (Nat.div x2 x0)) \/ (~ (num_divides (Nat.mul x0 x1) x2))).
Definition term6 := (((~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides (Nat.mul y1 y2) y0) -> num_divides y2 (Nat.div y0 y1))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) /\ (num_divides y2 (Nat.div y0 y1))) = (num_divides (Nat.mul y1 y2) y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides (Nat.mul y1 y2) y0) -> num_divides y2 (Nat.div y0 y1))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) /\ (num_divides y2 (Nat.div y0 y1))) = (num_divides (Nat.mul y1 y2) y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides (Nat.mul y1 y2) y0) -> num_divides y2 (Nat.div y0 y1))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) /\ (num_divides y2 (Nat.div y0 y1))) = (num_divides (Nat.mul y1 y2) y0)) -> False.
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) := num_divides x0 (Nat.div x1 x2).
Definition term77 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((~ (num_divides x0 x1)) \/ (~ (num_divides y0 (Nat.div x1 x0)))) \/ (num_divides (Nat.mul x0 y0) x1)) x2.
Definition term142 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) \/ (~ (num_divides (Nat.mul y1 y2) y0))) /\ ((num_divides y2 (Nat.div y0 y1)) \/ (~ (num_divides (Nat.mul y1 y2) y0))).
Definition term140 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((num_divides y0 x0) \/ (~ (num_divides (Nat.mul y0 y1) x0))) /\ ((num_divides y1 (Nat.div x0 y0)) \/ (~ (num_divides (Nat.mul y0 y1) x0))).
Definition term133 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (num_divides y1 y0)) \/ (~ (num_divides y2 (Nat.div y0 y1)))) \/ (num_divides (Nat.mul y1 y2) y0).
Definition term128 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) /\ (num_divides y2 (Nat.div y0 y1))) \/ (~ (num_divides (Nat.mul y1 y2) y0)).
Definition term111 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((~ (num_divides y0 x0)) \/ (~ (num_divides y1 (Nat.div x0 y0)))) \/ (num_divides (Nat.mul y0 y1) x0).
Definition term106 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((num_divides y0 x0) /\ (num_divides y1 (Nat.div x0 y0))) \/ (~ (num_divides (Nat.mul y0 y1) x0)).
Definition term65 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (((num_divides y1 y0) /\ (num_divides y2 (Nat.div y0 y1))) \/ (~ (num_divides (Nat.mul y1 y2) y0))) /\ (((~ (num_divides y1 y0)) \/ (~ (num_divides y2 (Nat.div y0 y1)))) \/ (num_divides (Nat.mul y1 y2) y0)).
Definition term63 (x0 : nat) := forall y0 : nat, forall y1 : nat, (((num_divides y0 x0) /\ (num_divides y1 (Nat.div x0 y0))) \/ (~ (num_divides (Nat.mul y0 y1) x0))) /\ (((~ (num_divides y0 x0)) \/ (~ (num_divides y1 (Nat.div x0 y0)))) \/ (num_divides (Nat.mul y0 y1) x0)).
Definition term24 (x0 : nat) := forall y0 : nat, forall y1 : nat, (num_divides (Nat.mul y0 y1) x0) -> num_divides y1 (Nat.div x0 y0).
Definition term18 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((num_divides y0 x0) /\ (num_divides y1 (Nat.div x0 y0))) = (num_divides (Nat.mul y0 y1) x0).
Definition term10 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) /\ (num_divides y2 (Nat.div y0 y1))) = (num_divides (Nat.mul y1 y2) y0).
Definition term1 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides (Nat.mul y1 y2) y0) -> num_divides y2 (Nat.div y0 y1).
Definition term148 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (num_divides (Nat.mul x0 x1) x2)) -> num_divides (Nat.mul x0 x1) x2.
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((fun y0 : nat => (num_divides (Nat.mul x1 y0) x0) -> num_divides y0 (Nat.div x0 x1)) x2).
Definition term122 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) /\ (num_divides y2 (Nat.div y0 y1))) \/ (~ (num_divides (Nat.mul y1 y2) y0))) x0) /\ ((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (num_divides y1 y0)) \/ (~ (num_divides y2 (Nat.div y0 y1)))) \/ (num_divides (Nat.mul y1 y2) y0)) x0).
Definition term137 (x0 : nat) (x1 : nat) := fun y0 : nat => ((num_divides x0 x1) \/ (~ (num_divides (Nat.mul x0 y0) x1))) /\ ((num_divides y0 (Nat.div x1 x0)) \/ (~ (num_divides (Nat.mul x0 y0) x1))).
Definition term49 := fun y0 : nat => exists y1 : nat, exists y2 : nat, (num_divides (Nat.mul y1 y2) y0) /\ (~ (num_divides y2 (Nat.div y0 y1))).
Definition term15 (x0 : nat) (x1 : nat) := fun y0 : nat => ((num_divides x0 x1) /\ (num_divides y0 (Nat.div x1 x0))) = (num_divides (Nat.mul x0 y0) x1).
Definition term147 (x0 : nat) (x1 : nat) (x2 : nat) := (num_divides x1 (Nat.div x2 x0)) \/ (~ (num_divides (Nat.mul x0 x1) x2)).
Definition term84 (x0 : nat) (x1 : nat) := forall y0 : nat, ((num_divides x0 x1) /\ (num_divides y0 (Nat.div x1 x0))) \/ (~ (num_divides (Nat.mul x0 y0) x1)).
Definition term60 (x0 : nat) (x1 : nat) := fun y0 : nat => (((num_divides x0 x1) /\ (num_divides y0 (Nat.div x1 x0))) \/ (~ (num_divides (Nat.mul x0 y0) x1))) /\ (((~ (num_divides x0 x1)) \/ (~ (num_divides y0 (Nat.div x1 x0)))) \/ (num_divides (Nat.mul x0 y0) x1)).
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) := or (~ ((num_divides x2 x1) /\ (num_divides x0 (Nat.div x1 x2)))).
Definition term37 (x0 : nat) (x1 : nat) := exists y0 : nat, (num_divides (Nat.mul x1 y0) x0) /\ (~ (num_divides y0 (Nat.div x0 x1))).
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (num_divides x2 x1)) \/ (~ (num_divides x0 (Nat.div x1 x2))).
Definition term2 := (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides (Nat.mul y1 y2) y0) -> num_divides y2 (Nat.div y0 y1))) -> False.
Definition term48 := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, forall y3 : nat, (num_divides (Nat.mul y2 y3) y1) -> num_divides y3 (Nat.div y1 y2)) y0).
Definition term42 (x0 : nat) := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, (num_divides (Nat.mul y1 y2) x0) -> num_divides y2 (Nat.div x0 y1)) y0).
Definition term69 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term156 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (num_divides x0 (Nat.div x1 x2))) -> num_divides x0 (Nat.div x1 x2).
Definition term73 (x0 : nat) (x1 : nat) := fun y0 : nat => ((~ (num_divides x0 x1)) \/ (~ (num_divides y0 (Nat.div x1 x0)))) \/ (num_divides (Nat.mul x0 y0) x1).
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((num_divides (Nat.mul x2 x0) x1) -> num_divides x0 (Nat.div x1 x2)).
Definition term98 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => forall y1 : nat, ((num_divides y0 x0) /\ (num_divides y1 (Nat.div x0 y0))) \/ (~ (num_divides (Nat.mul y0 y1) x0))) x1).
Definition term100 (x0 : nat) (x1 : nat) := ((fun y0 : nat => forall y1 : nat, ((num_divides y0 x0) /\ (num_divides y1 (Nat.div x0 y0))) \/ (~ (num_divides (Nat.mul y0 y1) x0))) x1) /\ ((fun y0 : nat => forall y1 : nat, ((~ (num_divides y0 x0)) \/ (~ (num_divides y1 (Nat.div x0 y0)))) \/ (num_divides (Nat.mul y0 y1) x0)) x1).
Definition term90 (x0 : nat) (x1 : nat) := (forall y0 : nat, ((num_divides x0 x1) /\ (num_divides y0 (Nat.div x1 x0))) \/ (~ (num_divides (Nat.mul x0 y0) x1))) /\ (forall y0 : nat, ((~ (num_divides x0 x1)) \/ (~ (num_divides y0 (Nat.div x1 x0)))) \/ (num_divides (Nat.mul x0 y0) x1)).
Definition term130 := and (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) /\ (num_divides y2 (Nat.div y0 y1))) \/ (~ (num_divides (Nat.mul y1 y2) y0))).
Definition term108 (x0 : nat) := and (forall y0 : nat, forall y1 : nat, ((num_divides y0 x0) /\ (num_divides y1 (Nat.div x0 y0))) \/ (~ (num_divides (Nat.mul y0 y1) x0))).
Definition term47 (x0 : nat) := ~ ((fun y0 : nat => forall y1 : nat, forall y2 : nat, (num_divides (Nat.mul y1 y2) y0) -> num_divides y2 (Nat.div y0 y1)) x0).
Definition term131 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((~ (num_divides y2 y1)) \/ (~ (num_divides y3 (Nat.div y1 y2)))) \/ (num_divides (Nat.mul y2 y3) y1)) y0.
Definition term126 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((num_divides y2 y1) /\ (num_divides y3 (Nat.div y1 y2))) \/ (~ (num_divides (Nat.mul y2 y3) y1))) y0.
Definition term109 (x0 : nat) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, ((~ (num_divides y1 x0)) \/ (~ (num_divides y2 (Nat.div x0 y1)))) \/ (num_divides (Nat.mul y1 y2) x0)) y0.
Definition term104 (x0 : nat) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, ((num_divides y1 x0) /\ (num_divides y2 (Nat.div x0 y1))) \/ (~ (num_divides (Nat.mul y1 y2) x0))) y0.
Definition term36 (x0 : nat) (x1 : nat) := fun y0 : nat => (num_divides (Nat.mul x1 y0) x0) /\ (~ (num_divides y0 (Nat.div x0 x1))).
Definition term45 := exists y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, forall y3 : nat, (num_divides (Nat.mul y2 y3) y1) -> num_divides y3 (Nat.div y1 y2)) y0).
Definition term39 (x0 : nat) := exists y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, (num_divides (Nat.mul y1 y2) x0) -> num_divides y2 (Nat.div x0 y1)) y0).
Definition term32 (x0 : nat) (x1 : nat) := exists y0 : nat, ~ ((fun y1 : nat => (num_divides (Nat.mul x1 y1) x0) -> num_divides y1 (Nat.div x0 x1)) y0).
Definition term12 := (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides (Nat.mul y1 y2) y0) -> num_divides y2 (Nat.div y0 y1))) -> ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) /\ (num_divides y2 (Nat.div y0 y1))) = (num_divides (Nat.mul y1 y2) y0)).
Definition term87 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => ((~ (num_divides x0 x1)) \/ (~ (num_divides y1 (Nat.div x1 x0)))) \/ (num_divides (Nat.mul x0 y1) x1)) y0.
Definition term136 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (num_divides (Nat.mul x0 x1) x2).
Definition term129 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((num_divides y2 y1) /\ (num_divides y3 (Nat.div y1 y2))) \/ (~ (num_divides (Nat.mul y2 y3) y1))) y0).
Definition term107 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((num_divides y1 x0) /\ (num_divides y2 (Nat.div x0 y1))) \/ (~ (num_divides (Nat.mul y1 y2) x0))) y0).
Definition term85 (x0 : nat) (x1 : nat) := and (forall y0 : nat, (fun y1 : nat => ((num_divides x0 x1) /\ (num_divides y1 (Nat.div x1 x0))) \/ (~ (num_divides (Nat.mul x0 y1) x1))) y0).
Definition term120 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) /\ (num_divides y2 (Nat.div y0 y1))) \/ (~ (num_divides (Nat.mul y1 y2) y0))) x0).
Definition term138 (x0 : nat) (x1 : nat) := forall y0 : nat, ((num_divides x0 x1) \/ (~ (num_divides (Nat.mul x0 y0) x1))) /\ ((num_divides y0 (Nat.div x1 x0)) \/ (~ (num_divides (Nat.mul x0 y0) x1))).
Definition term153 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (~ (num_divides (Nat.mul x0 x1) x2)).
Definition term95 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((num_divides y0 x0) /\ (num_divides y1 (Nat.div x0 y0))) \/ (~ (num_divides (Nat.mul y0 y1) x0)).
Definition term157 (x0 : nat) (x1 : nat) (x2 : nat) := (num_divides x0 (Nat.div x1 x2)) -> False.
Definition term66 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term50 := exists y0 : nat, exists y1 : nat, exists y2 : nat, (num_divides (Nat.mul y1 y2) y0) /\ (~ (num_divides y2 (Nat.div y0 y1))).
Definition term44 (x0 : nat) := exists y0 : nat, exists y1 : nat, (num_divides (Nat.mul y0 y1) x0) /\ (~ (num_divides y1 (Nat.div x0 y0))).
Definition term114 := forall y0 : nat, (forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) /\ (num_divides y2 (Nat.div y0 y1))) \/ (~ (num_divides (Nat.mul y1 y2) y0))) /\ (forall y1 : nat, forall y2 : nat, ((~ (num_divides y1 y0)) \/ (~ (num_divides y2 (Nat.div y0 y1)))) \/ (num_divides (Nat.mul y1 y2) y0)).
Definition term92 (x0 : nat) := forall y0 : nat, (forall y1 : nat, ((num_divides y0 x0) /\ (num_divides y1 (Nat.div x0 y0))) \/ (~ (num_divides (Nat.mul y0 y1) x0))) /\ (forall y1 : nat, ((~ (num_divides y0 x0)) \/ (~ (num_divides y1 (Nat.div x0 y0)))) \/ (num_divides (Nat.mul y0 y1) x0)).
Definition term16 (x0 : nat) (x1 : nat) := forall y0 : nat, ((num_divides x0 x1) /\ (num_divides y0 (Nat.div x1 x0))) = (num_divides (Nat.mul x0 y0) x1).
Definition term35 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ ((fun y1 : nat => (num_divides (Nat.mul x1 y1) x0) -> num_divides y1 (Nat.div x0 x1)) y0).
Definition term5 := ((~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides (Nat.mul y1 y2) y0) -> num_divides y2 (Nat.div y0 y1))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) /\ (num_divides y2 (Nat.div y0 y1))) = (num_divides (Nat.mul y1 y2) y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides (Nat.mul y1 y2) y0) -> num_divides y2 (Nat.div y0 y1))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) /\ (num_divides y2 (Nat.div y0 y1))) = (num_divides (Nat.mul y1 y2) y0)) -> False.
Definition term7 := (((~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides (Nat.mul y1 y2) y0) -> num_divides y2 (Nat.div y0 y1))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) /\ (num_divides y2 (Nat.div y0 y1))) = (num_divides (Nat.mul y1 y2) y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides (Nat.mul y1 y2) y0) -> num_divides y2 (Nat.div y0 y1))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) /\ (num_divides y2 (Nat.div y0 y1))) = (num_divides (Nat.mul y1 y2) y0)) -> False) -> ((~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides (Nat.mul y1 y2) y0) -> num_divides y2 (Nat.div y0 y1))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) /\ (num_divides y2 (Nat.div y0 y1))) = (num_divides (Nat.mul y1 y2) y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides (Nat.mul y1 y2) y0) -> num_divides y2 (Nat.div y0 y1))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) /\ (num_divides y2 (Nat.div y0 y1))) = (num_divides (Nat.mul y1 y2) y0)) -> False.
Definition term21 (x0 : nat) (x1 : nat) := fun y0 : nat => (num_divides (Nat.mul x1 y0) x0) -> num_divides y0 (Nat.div x0 x1).
Definition term132 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((~ (num_divides y2 y1)) \/ (~ (num_divides y3 (Nat.div y1 y2)))) \/ (num_divides (Nat.mul y2 y3) y1)) y0.
Definition term127 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((num_divides y2 y1) /\ (num_divides y3 (Nat.div y1 y2))) \/ (~ (num_divides (Nat.mul y2 y3) y1))) y0.
Definition term110 (x0 : nat) := forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((~ (num_divides y1 x0)) \/ (~ (num_divides y2 (Nat.div x0 y1)))) \/ (num_divides (Nat.mul y1 y2) x0)) y0.
Definition term105 (x0 : nat) := forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((num_divides y1 x0) /\ (num_divides y2 (Nat.div x0 y1))) \/ (~ (num_divides (Nat.mul y1 y2) x0))) y0.
Definition term30 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term139 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((num_divides y0 x0) \/ (~ (num_divides (Nat.mul y0 y1) x0))) /\ ((num_divides y1 (Nat.div x0 y0)) \/ (~ (num_divides (Nat.mul y0 y1) x0))).
Definition term62 (x0 : nat) := fun y0 : nat => forall y1 : nat, (((num_divides y0 x0) /\ (num_divides y1 (Nat.div x0 y0))) \/ (~ (num_divides (Nat.mul y0 y1) x0))) /\ (((~ (num_divides y0 x0)) \/ (~ (num_divides y1 (Nat.div x0 y0)))) \/ (num_divides (Nat.mul y0 y1) x0)).
Definition term23 (x0 : nat) := fun y0 : nat => forall y1 : nat, (num_divides (Nat.mul y0 y1) x0) -> num_divides y1 (Nat.div x0 y0).
Definition term11 := imp (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides (Nat.mul y1 y2) y0) -> num_divides y2 (Nat.div y0 y1))).
Definition term141 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) \/ (~ (num_divides (Nat.mul y1 y2) y0))) /\ ((num_divides y2 (Nat.div y0 y1)) \/ (~ (num_divides (Nat.mul y1 y2) y0))).
Definition term118 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (num_divides y1 y0)) \/ (~ (num_divides y2 (Nat.div y0 y1)))) \/ (num_divides (Nat.mul y1 y2) y0).
Definition term117 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) /\ (num_divides y2 (Nat.div y0 y1))) \/ (~ (num_divides (Nat.mul y1 y2) y0)).
Definition term64 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (((num_divides y1 y0) /\ (num_divides y2 (Nat.div y0 y1))) \/ (~ (num_divides (Nat.mul y1 y2) y0))) /\ (((~ (num_divides y1 y0)) \/ (~ (num_divides y2 (Nat.div y0 y1)))) \/ (num_divides (Nat.mul y1 y2) y0)).
Definition term25 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (num_divides (Nat.mul y1 y2) y0) -> num_divides y2 (Nat.div y0 y1).
Definition term19 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((num_divides y1 y0) /\ (num_divides y2 (Nat.div y0 y1))) = (num_divides (Nat.mul y1 y2) y0).
Definition term145 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((num_divides x0 x1) \/ (~ (num_divides (Nat.mul x0 y0) x1))) /\ ((num_divides y0 (Nat.div x1 x0)) \/ (~ (num_divides (Nat.mul x0 y0) x1)))) x2.
Definition term22 (x0 : nat) (x1 : nat) := forall y0 : nat, (num_divides (Nat.mul x1 y0) x0) -> num_divides y0 (Nat.div x0 x1).
