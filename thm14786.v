Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Lemma lem14786 (g : Prop) (h1 : g = False) : g = False.
Proof. exact (h1). Qed.
