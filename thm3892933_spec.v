Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3892933 : forall {_100607 : Type'} (n : nat) (P : (_100607 -> Prop) -> Prop), ((exists s : _100607 -> Prop, (@HAS_SIZE _100607 s (NUMERAL 0)) /\ (P s)) = (P (@EMPTY _100607))) /\ ((exists s : _100607 -> Prop, (@HAS_SIZE _100607 s (S n)) /\ (P s)) = (exists a : _100607, exists s : _100607 -> Prop, (@HAS_SIZE _100607 s n) /\ ((~ (@IN _100607 a s)) /\ (P (@INSERT _100607 a s))))).
