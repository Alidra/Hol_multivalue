Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21005_term_abbrevs.
Require Import thm20930_spec.
Require Import thm20972_spec.
Lemma lem21005 (b : Prop) (a : Prop) (h1 : a = True) : (term0 a b) = (term1 a b).
Proof. exact (EQ_MP (@lem20930 b a h1) (@lem20972 b)). Qed.
