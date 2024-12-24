Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm6904609_term_abbrevs.
Require Import SELECT_UNIQUE_spec.
Lemma lem6904589 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem6904590 {A : Type'} (P : A -> Prop) (h1 : term0 A) : term1 A P.
Proof. exact (@lem6904589 A h1 P). Qed.
Lemma lem6904591 {A : Type'} (P : A -> Prop) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem6904592 {A : Type'} (P : A -> Prop) (h1 : term0 A) : term2 A P.
Proof. exact (EQ_MP (@lem6904591 A P) (@lem6904590 A P h1)). Qed.
Lemma lem6904593 {A : Type'} (P : A -> Prop) (x : A) (h1 : term0 A) : term3 A P x.
Proof. exact (@lem6904592 A P h1 x). Qed.
Lemma lem6904594 {A : Type'} (P : A -> Prop) (x : A) : (term3 A P x) = (term4 A P x).
Proof. exact (eq_refl (term3 A P x)). Qed.
Lemma lem6904595 {A : Type'} (P : A -> Prop) (x : A) (h1 : term0 A) : term4 A P x.
Proof. exact (EQ_MP (@lem6904594 A P x) (@lem6904593 A P x h1)). Qed.
Lemma lem6904596 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) : term5 A P x.
Proof. exact (h1). Qed.
Lemma lem6904597 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) (h2 : term0 A) : (@ε A P) = x.
Proof. exact (@lem6904595 A P x h2 (@lem6904596 A P x h1)). Qed.
Lemma lem6904598 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) : term6 A P x.
Proof. exact (fun h0 : term0 A => @lem6904597 A P x h1 h0). Qed.
Lemma lem6904599 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem6904600 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) (h2 : term0 A) : (@ε A P) = x.
Proof. exact (@lem6904598 A P x h1 (@lem6904599 A h2)). Qed.
Lemma lem6904601 {A : Type'} (P : A -> Prop) (x : A) (h1 : term0 A) : term4 A P x.
Proof. exact (fun h0 : term5 A P x => @lem6904600 A P x h0 h1). Qed.
Lemma lem6904602 {A : Type'} (P : A -> Prop) (h1 : term0 A) : term2 A P.
Proof. exact (fun x : A => @lem6904601 A P x h1). Qed.
Lemma lem6904603 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (fun P : A -> Prop => @lem6904602 A P h1). Qed.
Lemma lem6904604 {A : Type'} : term7 A.
Proof. exact (fun h0 : term0 A => @lem6904603 A h0). Qed.
Lemma lem6904605 {A : Type'} : term0 A.
Proof. exact (@lem6904604 A (@lem9522 A)). Qed.
Lemma lem6904606 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (@lem6904605 A P). Qed.
Lemma lem6904607 {A : Type'} (P : A -> Prop) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem6904608 {A : Type'} (P : A -> Prop) : term2 A P.
Proof. exact (EQ_MP (@lem6904607 A P) (@lem6904606 A P)). Qed.
Lemma lem6904609 {A : Type'} (P : A -> Prop) (x : A) : term3 A P x.
Proof. exact (@lem6904608 A P x). Qed.
