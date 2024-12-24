Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm18393_term_abbrevs.
Require Import thm18017_spec.
Require Import thm18385_spec.
Lemma lem18393 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (EQ_MP (@lem18017 A P) (@lem18385 A P)). Qed.
