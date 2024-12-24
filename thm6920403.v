Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm6920403_term_abbrevs.
Require Import SELECT_UNIQUE_spec.
Lemma lem6920383 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem6920384 {A : Type'} (P : A -> Prop) (h1 : term0 A) : term1 A P.
Proof. exact (@lem6920383 A h1 P). Qed.
Lemma lem6920385 {A : Type'} (P : A -> Prop) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem6920386 {A : Type'} (P : A -> Prop) (h1 : term0 A) : term2 A P.
Proof. exact (EQ_MP (@lem6920385 A P) (@lem6920384 A P h1)). Qed.
Lemma lem6920387 {A : Type'} (P : A -> Prop) (x : A) (h1 : term0 A) : term3 A P x.
Proof. exact (@lem6920386 A P h1 x). Qed.
Lemma lem6920388 {A : Type'} (P : A -> Prop) (x : A) : (term3 A P x) = (term4 A P x).
Proof. exact (eq_refl (term3 A P x)). Qed.
Lemma lem6920389 {A : Type'} (P : A -> Prop) (x : A) (h1 : term0 A) : term4 A P x.
Proof. exact (EQ_MP (@lem6920388 A P x) (@lem6920387 A P x h1)). Qed.
Lemma lem6920390 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) : term5 A P x.
Proof. exact (h1). Qed.
Lemma lem6920391 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) (h2 : term0 A) : (@ε A P) = x.
Proof. exact (@lem6920389 A P x h2 (@lem6920390 A P x h1)). Qed.
Lemma lem6920392 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) : term6 A P x.
Proof. exact (fun h0 : term0 A => @lem6920391 A P x h1 h0). Qed.
Lemma lem6920393 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem6920394 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) (h2 : term0 A) : (@ε A P) = x.
Proof. exact (@lem6920392 A P x h1 (@lem6920393 A h2)). Qed.
Lemma lem6920395 {A : Type'} (P : A -> Prop) (x : A) (h1 : term0 A) : term4 A P x.
Proof. exact (fun h0 : term5 A P x => @lem6920394 A P x h0 h1). Qed.
Lemma lem6920396 {A : Type'} (P : A -> Prop) (h1 : term0 A) : term2 A P.
Proof. exact (fun x : A => @lem6920395 A P x h1). Qed.
Lemma lem6920397 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (fun P : A -> Prop => @lem6920396 A P h1). Qed.
Lemma lem6920398 {A : Type'} : term7 A.
Proof. exact (fun h0 : term0 A => @lem6920397 A h0). Qed.
Lemma lem6920399 {A : Type'} : term0 A.
Proof. exact (@lem6920398 A (@lem9522 A)). Qed.
Lemma lem6920400 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (@lem6920399 A P). Qed.
Lemma lem6920401 {A : Type'} (P : A -> Prop) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem6920402 {A : Type'} (P : A -> Prop) : term2 A P.
Proof. exact (EQ_MP (@lem6920401 A P) (@lem6920400 A P)). Qed.
Lemma lem6920403 {A : Type'} (P : A -> Prop) (x : A) : term3 A P x.
Proof. exact (@lem6920402 A P x). Qed.
