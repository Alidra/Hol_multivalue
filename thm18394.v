Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm18394_term_abbrevs.
Require Import thm18004_spec.
Require Import thm18065_spec.
Lemma lem18394 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (EQ_MP (@lem18004 A P) (@lem18065 A P)). Qed.
