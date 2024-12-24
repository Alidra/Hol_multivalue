Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1988128_term_abbrevs.
Require Import RIGHT_AND_EXISTS_THM_spec.
Lemma lem1988125 {A : Type'} (P : Prop) : term0 A P.
Proof. exact (@lem5950 A P). Qed.
Lemma lem1988126 {A : Type'} (P : Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem1988127 {A : Type'} (P : Prop) : term1 A P.
Proof. exact (EQ_MP (@lem1988126 A P) (@lem1988125 A P)). Qed.
Lemma lem1988128 {A : Type'} (P : Prop) (Q : A -> Prop) : term2 A P Q.
Proof. exact (@lem1988127 A P Q). Qed.
