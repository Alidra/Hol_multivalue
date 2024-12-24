Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2447249_term_abbrevs.
Require Import RIGHT_OR_EXISTS_THM_spec.
Lemma lem2447246 {A : Type'} (P : Prop) : term0 A P.
Proof. exact (@lem5612 A P). Qed.
Lemma lem2447247 {A : Type'} (P : Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem2447248 {A : Type'} (P : Prop) : term1 A P.
Proof. exact (EQ_MP (@lem2447247 A P) (@lem2447246 A P)). Qed.
Lemma lem2447249 {A : Type'} (P : Prop) (Q : A -> Prop) : term2 A P Q.
Proof. exact (@lem2447248 A P Q). Qed.
