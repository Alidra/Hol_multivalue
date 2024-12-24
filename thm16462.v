Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm16462_term_abbrevs.
Require Import EQ_CLAUSES_spec.
Lemma lem16460 (t : Prop) : term0 t.
Proof. exact (@lem1445 t). Qed.
Lemma lem16461 (t : Prop) : (term0 t) = (term1 t).
Proof. exact (eq_refl (term0 t)). Qed.
Lemma lem16462 (t : Prop) : term1 t.
Proof. exact (EQ_MP (@lem16461 t) (@lem16460 t)). Qed.
