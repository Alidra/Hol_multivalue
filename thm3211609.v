Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3211609_term_abbrevs.
Require Import IN_spec.
Lemma lem3211606 {A : Type'} (P : A -> Prop) : term0 A P.
Proof. exact (@lem3181151 A P). Qed.
Lemma lem3211607 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem3211608 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (EQ_MP (@lem3211607 A P) (@lem3211606 A P)). Qed.
Lemma lem3211609 {A : Type'} (P : A -> Prop) (x : A) : term2 A P x.
Proof. exact (@lem3211608 A P x). Qed.
