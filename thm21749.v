Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21749_term_abbrevs.
Require Import OR_CLAUSES_spec.
Lemma lem21747 (t : Prop) : term0 t.
Proof. exact (@lem1631 t). Qed.
Lemma lem21748 (t : Prop) : (term0 t) = (term1 t).
Proof. exact (eq_refl (term0 t)). Qed.
Lemma lem21749 (t : Prop) : term1 t.
Proof. exact (EQ_MP (@lem21748 t) (@lem21747 t)). Qed.
