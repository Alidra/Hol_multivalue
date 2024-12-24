Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Lemma lem20427 (b : Prop) (h1 : b = False) : b = False.
Proof. exact (h1). Qed.
