Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := (forall y0 : nat, forall y1 : nat, (real_gt (real_of_num y0) (real_of_num y1)) = (Peano.gt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_le (real_of_num y0) (real_of_num y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_lt (real_of_num y0) (real_of_num y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_max (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.max y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_min (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.min y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_mul (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.mul y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (real_pow (real_of_num y0) y1) = (real_of_num (Nat.pow y0 y1))))))))).
