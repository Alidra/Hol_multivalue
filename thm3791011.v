Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3791011_term_abbrevs.
Require Import thm3791009_spec.
Require Import thm3791010_spec.
Lemma lem3791011 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) (b : B) : (term0 A B f b s a) = (term1 A B s a b).
Proof. exact (EQ_MP (@lem3791010 A B f s a b) (@lem3791009 A B f s a b)). Qed.
