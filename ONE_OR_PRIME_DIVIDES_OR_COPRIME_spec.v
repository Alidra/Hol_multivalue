Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3145207 : forall p : nat, ((p = (NUMERAL (BIT1 0))) \/ (prime p)) = (forall n : nat, (num_divides p n) \/ (num_coprime (@pair nat nat p n))).
