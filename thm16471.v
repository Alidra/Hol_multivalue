Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm16471_term_abbrevs.
Require Import IMP_CLAUSES_spec.
Lemma lem16469 (t : Prop) : term0 t.
Proof. exact (@lem1763 t). Qed.
Lemma lem16470 (t : Prop) : (term0 t) = (term1 t).
Proof. exact (eq_refl (term0 t)). Qed.
Lemma lem16471 (t : Prop) : term1 t.
Proof. exact (EQ_MP (@lem16470 t) (@lem16469 t)). Qed.
