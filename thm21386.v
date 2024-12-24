Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21384_spec.
Lemma lem21386 {A : Type'} (x : A) : x = x.
Proof. exact (proj1 (@lem21384 A x (@el A) (@el A))). Qed.
