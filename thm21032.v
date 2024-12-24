Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Lemma lem21032 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
