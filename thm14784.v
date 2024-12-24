Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm14784_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Lemma lem14782 (g : Prop) : term0 g.
Proof. exact (@lem9851 g). Qed.
Lemma lem14783 (g : Prop) : (term0 g) = (term1 g).
Proof. exact (eq_refl (term0 g)). Qed.
Lemma lem14784 (g : Prop) : term1 g.
Proof. exact (EQ_MP (@lem14783 g) (@lem14782 g)). Qed.
