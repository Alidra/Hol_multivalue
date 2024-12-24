Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1054820 : (fun Y : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> nat -> nat => forall _17373 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))), forall x : Prop, forall y : nat, ((NUMLEFT (NUMSUM x y)) = x) /\ ((Y _17373 (NUMSUM x y)) = y)) (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> nat -> nat) (fun Y : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> nat -> nat => forall _17373 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))), forall x : Prop, forall y : nat, ((NUMLEFT (NUMSUM x y)) = x) /\ ((Y _17373 (NUMSUM x y)) = y))).
