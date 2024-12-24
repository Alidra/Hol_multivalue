Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term7 (x0 : nat) := Peano.lt (NUMERAL 0) (S x0).
Definition term22 := real_of_num (NUMERAL 0).
Definition term3 := fun y0 : nat => (~ (y0 = (NUMERAL 0))) = (Peano.lt (NUMERAL 0) y0).
Definition term21 (x0 : nat) := real_of_num (S x0).
Definition term19 (x0 : nat) := forall y0 : nat, ((real_of_num x0) = (real_of_num y0)) = (x0 = y0).
Definition term8 (x0 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) = (Peano.lt (NUMERAL 0) y0)) x0.
Definition term10 (x0 : nat) := real_lt (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term1 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term12 := fun y0 : nat => (real_lt (real_of_num (NUMERAL 0)) (real_of_num y0)) = (~ ((real_of_num y0) = (real_of_num (NUMERAL 0)))).
Definition term11 := fun y0 : nat => (~ ((real_of_num y0) = (real_of_num (NUMERAL 0)))) = (real_lt (real_of_num (NUMERAL 0)) (real_of_num y0)).
Definition term14 := forall y0 : nat, (real_lt (real_of_num (NUMERAL 0)) (real_of_num y0)) = (~ ((real_of_num y0) = (real_of_num (NUMERAL 0)))).
Definition term2 := fun y0 : nat => (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0))).
Definition term13 := forall y0 : nat, (~ ((real_of_num y0) = (real_of_num (NUMERAL 0)))) = (real_lt (real_of_num (NUMERAL 0)) (real_of_num y0)).
Definition term23 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term24 := forall y0 : nat, real_lt (real_of_num (NUMERAL 0)) (real_of_num (S y0)).
Definition term16 (x0 : nat) := real_lt (real_of_num (NUMERAL 0)) (real_of_num (S x0)).
Definition term9 (x0 : nat) := ~ ((real_of_num x0) = (real_of_num (NUMERAL 0))).
Definition term4 := forall y0 : nat, (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0))).
Definition term17 (x0 : nat) := ~ ((real_of_num (S x0)) = (real_of_num (NUMERAL 0))).
Definition term18 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((real_of_num y0) = (real_of_num y1)) = (y0 = y1)) x0.
Definition term5 := forall y0 : nat, (~ (y0 = (NUMERAL 0))) = (Peano.lt (NUMERAL 0) y0).
Definition term20 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((real_of_num x0) = (real_of_num y0)) = (x0 = y0)) x1.
Definition term15 (x0 : nat) := (fun y0 : nat => (real_lt (real_of_num (NUMERAL 0)) (real_of_num y0)) = (~ ((real_of_num y0) = (real_of_num (NUMERAL 0))))) (S x0).
Definition term0 (x0 : nat) := Peano.lt (NUMERAL 0) x0.
Definition term6 (x0 : nat) := (fun y0 : nat => Peano.lt (NUMERAL 0) (S y0)) x0.
