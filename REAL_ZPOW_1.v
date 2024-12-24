Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ZPOW_1_term_abbrevs.
Require Import REAL_POW_1_spec.
Require Import REAL_ZPOW_NUM_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3169347 (x : real) : term0 x.
Proof. exact (@lem1631005 x). Qed.
Lemma lem3169348 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem3169350 (x : real) : term2 x.
Proof. exact (@lem3169304 x). Qed.
Lemma lem3169351 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem3169352 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem3169351 x) (@lem3169350 x)). Qed.
Lemma lem3169353 (x : real) (n : nat) : term4 x n.
Proof. exact (@lem3169352 x n). Qed.
Lemma lem3169354 (x : real) (n : nat) : (term4 x n) = ((term5 x n) = (real_pow x n)).
Proof. exact (eq_refl (term4 x n)). Qed.
Lemma lem3169363 (x : real) (n : nat) : (term5 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3169354 x n) (@lem3169353 x n)). Qed.
Lemma lem3169364 (x : real) : (term6 x) = (term1 x).
Proof. exact (@lem3169363 x term7). Qed.
Lemma lem3169366 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem3169348 x) (@lem3169347 x)). Qed.
Lemma lem3169367 (x : real) : (term6 x) = x.
Proof. exact (TRANS (@lem3169364 x) (@lem3169366 x)). Qed.
Lemma lem3169368 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3169369 (x : real) : (term8 x) = (@eq real x).
Proof. exact (MK_COMB (@lem3169368) (@lem3169367 x)). Qed.
Lemma lem3169370 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3169371 (x : real) : ((term6 x) = x) = (x = x).
Proof. exact (MK_COMB (@lem3169369 x) (@lem3169370 x)). Qed.
Lemma lem3169373 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3169374 (x : real) : (x = x) = True.
Proof. exact (@lem3169373 real x). Qed.
Lemma lem3169375 (x : real) : ((term6 x) = x) = True.
Proof. exact (TRANS (@lem3169371 x) (@lem3169374 x)). Qed.
Lemma lem3169376 : term9 = term10.
Proof. exact (fun_ext (fun x : real => @lem3169375 x)). Qed.
Lemma lem3169377 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3169378 : term11 = term12.
Proof. exact (MK_COMB (@lem3169377) (@lem3169376)). Qed.
Lemma lem3169380 {A : Type'} (t : Prop) : (term13 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3169381 (t : Prop) : (term14 t) = t.
Proof. exact (@lem3169380 real t). Qed.
Lemma lem3169382 : term12 = True.
Proof. exact (@lem3169381 True). Qed.
Lemma lem3169383 : term11 = True.
Proof. exact (TRANS (@lem3169378) (@lem3169382)). Qed.
Lemma lem3169384 : True = term11.
Proof. exact (SYM (@lem3169383)). Qed.
Lemma lem3169385 : term11.
Proof. exact (EQ_MP (@lem3169384) (@lem0)). Qed.
