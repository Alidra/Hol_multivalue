Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21488_term_abbrevs.
Require Import thm21420_spec.
Require Import thm21460_spec.
Lemma lem21488 (b : Prop) (a : Prop) (h1 : a = True) : (a -> b) = (term0 a b).
Proof. exact (EQ_MP (@lem21420 b a h1) (@lem21460 b)). Qed.
