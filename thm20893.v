Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20893_term_abbrevs.
Require Import thm20815_spec.
Require Import thm20862_spec.
Lemma lem20893 (b : Prop) (a : Prop) (h1 : a = True) : (term0 a b) = (term1 a b).
Proof. exact (EQ_MP (@lem20815 b a h1) (@lem20862 b)). Qed.
