Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm6914211_term_abbrevs.
Require Import SELECT_UNIQUE_spec.
Lemma lem6914191 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem6914192 {A : Type'} (P : A -> Prop) (h1 : term0 A) : term1 A P.
Proof. exact (@lem6914191 A h1 P). Qed.
Lemma lem6914193 {A : Type'} (P : A -> Prop) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem6914194 {A : Type'} (P : A -> Prop) (h1 : term0 A) : term2 A P.
Proof. exact (EQ_MP (@lem6914193 A P) (@lem6914192 A P h1)). Qed.
Lemma lem6914195 {A : Type'} (P : A -> Prop) (x : A) (h1 : term0 A) : term3 A P x.
Proof. exact (@lem6914194 A P h1 x). Qed.
Lemma lem6914196 {A : Type'} (P : A -> Prop) (x : A) : (term3 A P x) = (term4 A P x).
Proof. exact (eq_refl (term3 A P x)). Qed.
Lemma lem6914197 {A : Type'} (P : A -> Prop) (x : A) (h1 : term0 A) : term4 A P x.
Proof. exact (EQ_MP (@lem6914196 A P x) (@lem6914195 A P x h1)). Qed.
Lemma lem6914198 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) : term5 A P x.
Proof. exact (h1). Qed.
Lemma lem6914199 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) (h2 : term0 A) : (@ε A P) = x.
Proof. exact (@lem6914197 A P x h2 (@lem6914198 A P x h1)). Qed.
Lemma lem6914200 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) : term6 A P x.
Proof. exact (fun h0 : term0 A => @lem6914199 A P x h1 h0). Qed.
Lemma lem6914201 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem6914202 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) (h2 : term0 A) : (@ε A P) = x.
Proof. exact (@lem6914200 A P x h1 (@lem6914201 A h2)). Qed.
Lemma lem6914203 {A : Type'} (P : A -> Prop) (x : A) (h1 : term0 A) : term4 A P x.
Proof. exact (fun h0 : term5 A P x => @lem6914202 A P x h0 h1). Qed.
Lemma lem6914204 {A : Type'} (P : A -> Prop) (h1 : term0 A) : term2 A P.
Proof. exact (fun x : A => @lem6914203 A P x h1). Qed.
Lemma lem6914205 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (fun P : A -> Prop => @lem6914204 A P h1). Qed.
Lemma lem6914206 {A : Type'} : term7 A.
Proof. exact (fun h0 : term0 A => @lem6914205 A h0). Qed.
Lemma lem6914207 {A : Type'} : term0 A.
Proof. exact (@lem6914206 A (@lem9522 A)). Qed.
Lemma lem6914208 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (@lem6914207 A P). Qed.
Lemma lem6914209 {A : Type'} (P : A -> Prop) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem6914210 {A : Type'} (P : A -> Prop) : term2 A P.
Proof. exact (EQ_MP (@lem6914209 A P) (@lem6914208 A P)). Qed.
Lemma lem6914211 {A : Type'} (P : A -> Prop) (x : A) : term3 A P x.
Proof. exact (@lem6914210 A P x). Qed.
