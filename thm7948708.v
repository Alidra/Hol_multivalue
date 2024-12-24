Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7948706_spec.
Lemma lem7948708 : (@dimindex unit (@UNIV unit)) = (BIT1 0).
Proof. exact (proj2 (@lem7948706 Prop (@el nat))). Qed.
