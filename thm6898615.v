Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm6898615_term_abbrevs.
Require Import SELECT_UNIQUE_spec.
Lemma lem6898595 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem6898596 {A : Type'} (P : A -> Prop) (h1 : term0 A) : term1 A P.
Proof. exact (@lem6898595 A h1 P). Qed.
Lemma lem6898597 {A : Type'} (P : A -> Prop) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem6898598 {A : Type'} (P : A -> Prop) (h1 : term0 A) : term2 A P.
Proof. exact (EQ_MP (@lem6898597 A P) (@lem6898596 A P h1)). Qed.
Lemma lem6898599 {A : Type'} (P : A -> Prop) (x : A) (h1 : term0 A) : term3 A P x.
Proof. exact (@lem6898598 A P h1 x). Qed.
Lemma lem6898600 {A : Type'} (P : A -> Prop) (x : A) : (term3 A P x) = (term4 A P x).
Proof. exact (eq_refl (term3 A P x)). Qed.
Lemma lem6898601 {A : Type'} (P : A -> Prop) (x : A) (h1 : term0 A) : term4 A P x.
Proof. exact (EQ_MP (@lem6898600 A P x) (@lem6898599 A P x h1)). Qed.
Lemma lem6898602 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) : term5 A P x.
Proof. exact (h1). Qed.
Lemma lem6898603 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) (h2 : term0 A) : (@ε A P) = x.
Proof. exact (@lem6898601 A P x h2 (@lem6898602 A P x h1)). Qed.
Lemma lem6898604 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) : term6 A P x.
Proof. exact (fun h0 : term0 A => @lem6898603 A P x h1 h0). Qed.
Lemma lem6898605 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem6898606 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) (h2 : term0 A) : (@ε A P) = x.
Proof. exact (@lem6898604 A P x h1 (@lem6898605 A h2)). Qed.
Lemma lem6898607 {A : Type'} (P : A -> Prop) (x : A) (h1 : term0 A) : term4 A P x.
Proof. exact (fun h0 : term5 A P x => @lem6898606 A P x h0 h1). Qed.
Lemma lem6898608 {A : Type'} (P : A -> Prop) (h1 : term0 A) : term2 A P.
Proof. exact (fun x : A => @lem6898607 A P x h1). Qed.
Lemma lem6898609 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (fun P : A -> Prop => @lem6898608 A P h1). Qed.
Lemma lem6898610 {A : Type'} : term7 A.
Proof. exact (fun h0 : term0 A => @lem6898609 A h0). Qed.
Lemma lem6898611 {A : Type'} : term0 A.
Proof. exact (@lem6898610 A (@lem9522 A)). Qed.
Lemma lem6898612 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (@lem6898611 A P). Qed.
Lemma lem6898613 {A : Type'} (P : A -> Prop) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem6898614 {A : Type'} (P : A -> Prop) : term2 A P.
Proof. exact (EQ_MP (@lem6898613 A P) (@lem6898612 A P)). Qed.
Lemma lem6898615 {A : Type'} (P : A -> Prop) (x : A) : term3 A P x.
Proof. exact (@lem6898614 A P x). Qed.
