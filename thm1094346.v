Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1094346_term_abbrevs.
Require Import list_INDUCT_spec.
Lemma lem1094322 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (@lem1071853 A P). Qed.
Lemma lem1094323 {A : Type'} (P : type1143 A) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem1094326 {A : Type'} (P : type1143 A) : term1 A P.
Proof. exact (EQ_MP (@lem1094323 A P) (@lem1094322 A P)). Qed.
Lemma lem1094327 {A : Type'} (P : type1143 A) : term1 A P.
Proof. exact (@lem1094326 A P). Qed.
Lemma lem1094332 {A : Type'} : term2 A.
Proof. exact (fun P : type1143 A => @lem1094327 A P). Qed.
Lemma lem1094333 {A : Type'} (h1 : term2 A) : term2 A.
Proof. exact (h1). Qed.
Lemma lem1094334 {A : Type'} (P : type1143 A) (h1 : term2 A) : term0 A P.
Proof. exact (@lem1094333 A h1 P). Qed.
Lemma lem1094335 {A : Type'} (P : type1143 A) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem1094336 {A : Type'} (P : type1143 A) (h1 : term2 A) : term1 A P.
Proof. exact (EQ_MP (@lem1094335 A P) (@lem1094334 A P h1)). Qed.
Lemma lem1094337 {A : Type'} (P : type1143 A) (h1 : term3 A P) : term3 A P.
Proof. exact (h1). Qed.
Lemma lem1094338 {A : Type'} (P : type1143 A) (h1 : term2 A) (h2 : term3 A P) : term4 A P.
Proof. exact (@lem1094336 A P h1 (@lem1094337 A P h2)). Qed.
Lemma lem1094339 {A : Type'} (P : type1143 A) (h1 : term3 A P) : term5 A P.
Proof. exact (fun h0 : term2 A => @lem1094338 A P h0 h1). Qed.
Lemma lem1094340 {A : Type'} (h1 : term2 A) : term2 A.
Proof. exact (h1). Qed.
Lemma lem1094341 {A : Type'} (P : type1143 A) (h1 : term2 A) (h2 : term3 A P) : term4 A P.
Proof. exact (@lem1094339 A P h2 (@lem1094340 A h1)). Qed.
Lemma lem1094342 {A : Type'} (P : type1143 A) (h1 : term2 A) : term1 A P.
Proof. exact (fun h0 : term3 A P => @lem1094341 A P h1 h0). Qed.
Lemma lem1094343 {A : Type'} (h1 : term2 A) : term2 A.
Proof. exact (fun P : type1143 A => @lem1094342 A P h1). Qed.
Lemma lem1094344 {A : Type'} : term6 A.
Proof. exact (fun h0 : term2 A => @lem1094343 A h0). Qed.
Lemma lem1094345 {A : Type'} : term2 A.
Proof. exact (@lem1094344 A (@lem1094332 A)). Qed.
Lemma lem1094346 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (@lem1094345 A P). Qed.
