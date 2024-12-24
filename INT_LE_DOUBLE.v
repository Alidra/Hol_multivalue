Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_DOUBLE_term_abbrevs.
Require Import REAL_LE_DOUBLE_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2302348 (x : int) : term0 x.
Proof. exact (@lem1505819 (real_of_int x)). Qed.
Lemma lem2302349 (x : int) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2302350 (x : int) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem2302349 x) (@lem2302348 x)). Qed.
Lemma lem2302352 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302353 : term4 = term5.
Proof. exact (@lem2302352 (NUMERAL 0)). Qed.
Lemma lem2302354 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302355 : term6 = term7.
Proof. exact (MK_COMB (@lem2302354) (@lem2302353)). Qed.
Lemma lem2302357 (x : int) (y : int) : (term8 x y) = (term9 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2302358 (x : int) : (term10 x) = (term11 x).
Proof. exact (@lem2302357 x x). Qed.
Lemma lem2302359 (x : int) : (term1 x) = (term12 x).
Proof. exact (MK_COMB (@lem2302355) (@lem2302358 x)). Qed.
Lemma lem2302361 (x : int) (y : int) : (term13 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302362 (x : int) : (term12 x) = (term14 x).
Proof. exact (@lem2302361 term15 (int_add x x)). Qed.
Lemma lem2302363 (x : int) : (term1 x) = (term14 x).
Proof. exact (TRANS (@lem2302359 x) (@lem2302362 x)). Qed.
Lemma lem2302364 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2302365 (x : int) : (term16 x) = (term17 x).
Proof. exact (MK_COMB (@lem2302364) (@lem2302363 x)). Qed.
Lemma lem2302367 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302368 : term4 = term5.
Proof. exact (@lem2302367 (NUMERAL 0)). Qed.
Lemma lem2302369 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302370 : term6 = term7.
Proof. exact (MK_COMB (@lem2302369) (@lem2302368)). Qed.
Lemma lem2302371 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2302372 (x : int) : (term2 x) = (term18 x).
Proof. exact (MK_COMB (@lem2302370) (@lem2302371 x)). Qed.
Lemma lem2302374 (x : int) (y : int) : (term13 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302375 (x : int) : (term18 x) = (term19 x).
Proof. exact (@lem2302374 term15 x). Qed.
Lemma lem2302376 (x : int) : (term2 x) = (term19 x).
Proof. exact (TRANS (@lem2302372 x) (@lem2302375 x)). Qed.
Lemma lem2302377 (x : int) : ((term1 x) = (term2 x)) = ((term14 x) = (term19 x)).
Proof. exact (MK_COMB (@lem2302365 x) (@lem2302376 x)). Qed.
Lemma lem2302378 (x : int) : (term14 x) = (term19 x).
Proof. exact (EQ_MP (@lem2302377 x) (@lem2302350 x)). Qed.
Lemma lem2302379 : term20.
Proof. exact (fun x : int => @lem2302378 x). Qed.
