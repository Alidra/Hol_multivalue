Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term72 (x0 : real) (x1 : nat) (x2 : nat) := ((Peano.le x1 x2) -> ((real_div (real_pow x0 x2) (real_pow x0 x1)) = (real_pow x0 (Nat.sub x2 x1))) = True) -> ((Peano.le x1 x2) -> (real_div (real_pow x0 x2) (real_pow x0 x1)) = (real_pow x0 (Nat.sub x2 x1))) = ((Peano.le x1 x2) -> True).
Definition term22 (x0 : real) (x1 : Prop) (x2 : nat) (x3 : real) (x4 : nat) (x5 : real) := (x1 -> (fun y0 : real => (real_div (real_pow x3 x2) (real_pow x3 x4)) = y0) x0) /\ ((~ x1) -> (fun y0 : real => (real_div (real_pow x3 x2) (real_pow x3 x4)) = y0) x5).
Definition term14 := fun y0 : real => y0 = (real_inv (real_inv y0)).
Definition term51 := real_of_num (NUMERAL 0).
Definition term50 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (x0 = (real_of_num (NUMERAL 0))) = False.
Definition term23 (x0 : nat) (x1 : real) (x2 : nat) := fun y0 : real => (real_div (real_pow x1 x0) (real_pow x1 x2)) = y0.
Definition term16 := forall y0 : real, y0 = (real_inv (real_inv y0)).
Definition term21 (x0 : nat) (x1 : real) (x2 : nat) (x3 : Prop) (x4 : real) (x5 : real) := (fun y0 : real => (real_div (real_pow x1 x0) (real_pow x1 x2)) = y0) (@COND real x3 x4 x5).
Definition term69 (x0 : real) (x1 : nat) (x2 : nat) (x3 : Prop) := ((Peano.le x1 x2) = (Peano.le x1 x2)) -> ((Peano.le x1 x2) -> ((real_div (real_pow x0 x2) (real_pow x0 x1)) = (real_pow x0 (Nat.sub x2 x1))) = x3) -> ((Peano.le x1 x2) -> (real_div (real_pow x0 x2) (real_pow x0 x1)) = (real_pow x0 (Nat.sub x2 x1))) = ((Peano.le x1 x2) -> x3).
Definition term13 := fun y0 : real => (real_inv (real_inv y0)) = y0.
Definition term54 (x0 : nat) (x1 : real) (x2 : nat) := real_inv (real_inv (real_div (real_pow x1 x0) (real_pow x1 x2))).
Definition term34 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term39 (x0 : real) (x1 : nat) (x2 : nat) := ((Peano.le x1 x2) -> (real_div (real_pow x0 x2) (real_pow x0 x1)) = (real_pow x0 (Nat.sub x2 x1))) /\ ((~ (Peano.le x1 x2)) -> (real_div (real_pow x0 x2) (real_pow x0 x1)) = (real_inv (real_pow x0 (Nat.sub x1 x2)))).
Definition term28 (x0 : real) (x1 : nat) (x2 : nat) := (fun y0 : real => (real_div (real_pow x0 x2) (real_pow x0 x1)) = y0) (real_inv (real_pow x0 (Nat.sub x1 x2))).
Definition term77 := forall y0 : real, forall y1 : nat, forall y2 : nat, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_div (real_pow y0 y1) (real_pow y0 y2)) = (@COND real (Peano.le y2 y1) (real_pow y0 (Nat.sub y1 y2)) (real_inv (real_pow y0 (Nat.sub y2 y1)))).
Definition term17 (x0 : real) := (fun y0 : real => y0 = (real_inv (real_inv y0))) x0.
Definition term57 (x0 : nat) (x1 : real) (x2 : nat) := @eq real (real_inv (real_div (real_pow x1 x0) (real_pow x1 x2))).
Definition term65 (x0 : real) (x1 : nat) (x2 : nat) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((Peano.le x2 x1) = y0) -> (y0 -> ((real_div (real_pow x0 x1) (real_pow x0 x2)) = (real_pow x0 (Nat.sub x1 x2))) = y1) -> ((Peano.le x2 x1) -> (real_div (real_pow x0 x1) (real_pow x0 x2)) = (real_pow x0 (Nat.sub x1 x2))) = (y0 -> y1)) x3.
Definition term29 (x0 : nat) (x1 : real) (x2 : nat) := real_div (real_pow x1 x0) (real_pow x1 x2).
Definition term45 (x0 : real) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (Peano.le y0 y1)) -> (real_pow x0 (Nat.sub y1 y0)) = (real_div (real_pow x0 y1) (real_pow x0 y0))) x1.
Definition term15 := forall y0 : real, (real_inv (real_inv y0)) = y0.
Definition term71 (x0 : real) (x1 : nat) (x2 : nat) := (Peano.le x2 x1) -> ((real_div (real_pow x0 x1) (real_pow x0 x2)) = (real_pow x0 (Nat.sub x1 x2))) = True.
Definition term18 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term20 (x0 : real) (x1 : Prop) (x2 : real -> Prop) (x3 : real) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term53 (x0 : nat) (x1 : real) (x2 : nat) := @eq real (real_div (real_pow x1 x0) (real_pow x1 x2)).
Definition term61 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term38 (x0 : real) (x1 : nat) (x2 : nat) := and ((Peano.le x2 x1) -> (real_div (real_pow x0 x1) (real_pow x0 x2)) = (real_pow x0 (Nat.sub x1 x2))).
Definition term7 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term68 (x0 : real) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) := ((Peano.le x2 x1) = x3) -> (x3 -> ((real_div (real_pow x0 x1) (real_pow x0 x2)) = (real_pow x0 (Nat.sub x1 x2))) = x4) -> ((Peano.le x2 x1) -> (real_div (real_pow x0 x1) (real_pow x0 x2)) = (real_pow x0 (Nat.sub x1 x2))) = (x3 -> x4).
Definition term32 (x0 : real) (x1 : nat) (x2 : nat) := (~ (Peano.le x1 x2)) -> (real_div (real_pow x0 x2) (real_pow x0 x1)) = (real_inv (real_pow x0 (Nat.sub x1 x2))).
Definition term75 (x0 : real) (x1 : nat) := forall y0 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_div (real_pow x0 x1) (real_pow x0 y0)) = (@COND real (Peano.le y0 x1) (real_pow x0 (Nat.sub x1 y0)) (real_inv (real_pow x0 (Nat.sub y0 x1)))).
Definition term9 (x0 : real) := forall y0 : real, (real_inv (real_div x0 y0)) = (real_div y0 x0).
Definition term60 (x0 : real) (x1 : nat) (x2 : nat) := (Peano.lt x2 x1) -> (real_div (real_pow x0 x1) (real_pow x0 x2)) = (real_pow x0 (Nat.sub x1 x2)).
Definition term25 (x0 : real) (x1 : nat) (x2 : nat) := ((Peano.le x1 x2) -> (fun y0 : real => (real_div (real_pow x0 x2) (real_pow x0 x1)) = y0) (real_pow x0 (Nat.sub x2 x1))) /\ ((~ (Peano.le x1 x2)) -> (fun y0 : real => (real_div (real_pow x0 x2) (real_pow x0 x1)) = y0) (real_inv (real_pow x0 (Nat.sub x1 x2)))).
Definition term56 (x0 : nat) (x1 : real) (x2 : nat) := real_inv (real_div (real_pow x1 x0) (real_pow x1 x2)).
Definition term36 (x0 : real) (x1 : nat) (x2 : nat) := (Peano.le x2 x1) -> (real_div (real_pow x0 x1) (real_pow x0 x2)) = (real_pow x0 (Nat.sub x1 x2)).
Definition term12 (x0 : real) := real_inv (real_inv x0).
Definition term76 (x0 : real) := forall y0 : nat, forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_div (real_pow x0 y0) (real_pow x0 y1)) = (@COND real (Peano.le y1 y0) (real_pow x0 (Nat.sub y0 y1)) (real_inv (real_pow x0 (Nat.sub y1 y0)))).
Definition term44 (x0 : real) := forall y0 : nat, forall y1 : nat, ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (Peano.le y0 y1)) -> (real_pow x0 (Nat.sub y1 y0)) = (real_div (real_pow x0 y1) (real_pow x0 y0)).
Definition term5 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term33 (x0 : real) (x1 : nat) (x2 : nat) := (fun y0 : real => (real_div (real_pow x0 x1) (real_pow x0 x2)) = y0) (real_pow x0 (Nat.sub x1 x2)).
Definition term11 (x0 : real) (x1 : real) := real_inv (real_div x0 x1).
Definition term26 (x0 : real) (x1 : nat) (x2 : nat) := real_pow x0 (Nat.sub x1 x2).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) -> Peano.le x0 y0) x1.
Definition term59 (x0 : real) (x1 : nat) (x2 : nat) := (~ (Peano.le x1 x2)) -> (real_div (real_pow x0 x1) (real_pow x0 x2)) = (real_pow x0 (Nat.sub x1 x2)).
Definition term8 (x0 : real) := (fun y0 : real => forall y1 : real, (real_inv (real_div y0 y1)) = (real_div y1 y0)) x0.
Definition term35 (x0 : real) (x1 : nat) (x2 : nat) := (Peano.le x2 x1) -> (fun y0 : real => (real_div (real_pow x0 x1) (real_pow x0 x2)) = y0) (real_pow x0 (Nat.sub x1 x2)).
Definition term66 (x0 : real) (x1 : nat) (x2 : nat) (x3 : Prop) := forall y0 : Prop, ((Peano.le x2 x1) = x3) -> (x3 -> ((real_div (real_pow x0 x1) (real_pow x0 x2)) = (real_pow x0 (Nat.sub x1 x2))) = y0) -> ((Peano.le x2 x1) -> (real_div (real_pow x0 x1) (real_pow x0 x2)) = (real_pow x0 (Nat.sub x1 x2))) = (x3 -> y0).
Definition term62 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term58 (x0 : nat) (x1 : nat) := imp (Peano.lt x0 x1).
Definition term74 (x0 : real) (x1 : nat) (x2 : nat) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_div (real_pow x0 x2) (real_pow x0 x1)) = (@COND real (Peano.le x1 x2) (real_pow x0 (Nat.sub x2 x1)) (real_inv (real_pow x0 (Nat.sub x1 x2)))).
Definition term64 (x0 : real) (x1 : nat) (x2 : nat) := forall y0 : Prop, forall y1 : Prop, ((Peano.le x2 x1) = y0) -> (y0 -> ((real_div (real_pow x0 x1) (real_pow x0 x2)) = (real_pow x0 (Nat.sub x1 x2))) = y1) -> ((Peano.le x2 x1) -> (real_div (real_pow x0 x1) (real_pow x0 x2)) = (real_pow x0 (Nat.sub x1 x2))) = (y0 -> y1).
Definition term63 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term73 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> True.
Definition term70 (x0 : real) (x1 : nat) (x2 : nat) (x3 : Prop) := ((Peano.le x1 x2) -> ((real_div (real_pow x0 x2) (real_pow x0 x1)) = (real_pow x0 (Nat.sub x2 x1))) = x3) -> ((Peano.le x1 x2) -> (real_div (real_pow x0 x2) (real_pow x0 x1)) = (real_pow x0 (Nat.sub x2 x1))) = ((Peano.le x1 x2) -> x3).
Definition term49 (x0 : real) (x1 : nat) (x2 : nat) := (~ (x0 = (real_of_num (NUMERAL 0)))) /\ (Peano.le x1 x2).
Definition term67 (x0 : real) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((Peano.le x2 x1) = x3) -> (x3 -> ((real_div (real_pow x0 x1) (real_pow x0 x2)) = (real_pow x0 (Nat.sub x1 x2))) = y0) -> ((Peano.le x2 x1) -> (real_div (real_pow x0 x1) (real_pow x0 x2)) = (real_pow x0 (Nat.sub x1 x2))) = (x3 -> y0)) x4.
Definition term42 (x0 : real) (x1 : nat) (x2 : nat) := @eq Prop ((real_div (real_pow x0 x2) (real_pow x0 x1)) = (@COND real (Peano.le x1 x2) (real_pow x0 (Nat.sub x2 x1)) (real_inv (real_pow x0 (Nat.sub x1 x2))))).
Definition term55 (x0 : nat) (x1 : real) (x2 : nat) := @eq real (real_inv (real_inv (real_div (real_pow x1 x0) (real_pow x1 x2)))).
Definition term4 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) x0.
Definition term37 (x0 : real) (x1 : nat) (x2 : nat) := and ((Peano.le x2 x1) -> (fun y0 : real => (real_div (real_pow x0 x1) (real_pow x0 x2)) = y0) (real_pow x0 (Nat.sub x1 x2))).
Definition term43 (x0 : real) := (fun y0 : real => forall y1 : nat, forall y2 : nat, ((~ (y0 = (real_of_num (NUMERAL 0)))) /\ (Peano.le y1 y2)) -> (real_pow y0 (Nat.sub y2 y1)) = (real_div (real_pow y0 y2) (real_pow y0 y1))) x0.
Definition term40 (x0 : real) (x1 : nat) (x2 : nat) := @COND real (Peano.le x1 x2) (real_pow x0 (Nat.sub x2 x1)) (real_inv (real_pow x0 (Nat.sub x1 x2))).
Definition term30 (x0 : nat) (x1 : nat) := imp (~ (Peano.le x0 x1)).
Definition term10 (x0 : real) (x1 : real) := (fun y0 : real => (real_inv (real_div x0 y0)) = (real_div y0 x0)) x1.
Definition term19 (x0 : real -> Prop) (x1 : Prop) (x2 : real) (x3 : real) := x0 (@COND real x1 x2 x3).
Definition term48 (x0 : nat) (x1 : real) (x2 : nat) := ((~ (x1 = (real_of_num (NUMERAL 0)))) /\ (Peano.le x2 x0)) -> (real_pow x1 (Nat.sub x0 x2)) = (real_div (real_pow x1 x0) (real_pow x1 x2)).
Definition term47 (x0 : real) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (Peano.le x1 y0)) -> (real_pow x0 (Nat.sub y0 x1)) = (real_div (real_pow x0 y0) (real_pow x0 x1))) x2.
Definition term41 (x0 : real) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : real => (real_div (real_pow x0 x2) (real_pow x0 x1)) = y0) (@COND real (Peano.le x1 x2) (real_pow x0 (Nat.sub x2 x1)) (real_inv (real_pow x0 (Nat.sub x1 x2))))).
Definition term46 (x0 : real) (x1 : nat) := forall y0 : nat, ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (Peano.le x1 y0)) -> (real_pow x0 (Nat.sub y0 x1)) = (real_div (real_pow x0 y0) (real_pow x0 x1)).
Definition term27 (x0 : real) (x1 : nat) (x2 : nat) := real_inv (real_pow x0 (Nat.sub x1 x2)).
Definition term3 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) -> Peano.le x0 x1.
Definition term1 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) -> Peano.le x0 y0.
Definition term6 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0)) x1.
Definition term52 (x0 : real) := and (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term31 (x0 : real) (x1 : nat) (x2 : nat) := (~ (Peano.le x1 x2)) -> (fun y0 : real => (real_div (real_pow x0 x2) (real_pow x0 x1)) = y0) (real_inv (real_pow x0 (Nat.sub x1 x2))).
Definition term24 (x0 : real) (x1 : nat) (x2 : nat) := (fun y0 : real => (real_div (real_pow x0 x2) (real_pow x0 x1)) = y0) (@COND real (Peano.le x1 x2) (real_pow x0 (Nat.sub x2 x1)) (real_inv (real_pow x0 (Nat.sub x1 x2)))).
