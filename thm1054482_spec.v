Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1054482 : (fun X : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop => forall _17372 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))), exists Y : nat -> nat, forall x : Prop, forall y : nat, ((X _17372 (NUMSUM x y)) = x) /\ ((Y (NUMSUM x y)) = y)) (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop) (fun X : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop => forall _17372 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))), exists Y : nat -> nat, forall x : Prop, forall y : nat, ((X _17372 (NUMSUM x y)) = x) /\ ((Y (NUMSUM x y)) = y))).
