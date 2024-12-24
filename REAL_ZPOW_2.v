Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ZPOW_2_term_abbrevs.
Require Import REAL_POW_2_spec.
Require Import REAL_ZPOW_NUM_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3169386 (x : real) : term0 x.
Proof. exact (@lem1383497 x). Qed.
Lemma lem3169387 (x : real) : (term0 x) = ((term1 x) = (real_mul x x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem3169389 (x : real) : term2 x.
Proof. exact (@lem3169304 x). Qed.
Lemma lem3169390 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem3169391 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem3169390 x) (@lem3169389 x)). Qed.
Lemma lem3169392 (x : real) (n : nat) : term4 x n.
Proof. exact (@lem3169391 x n). Qed.
Lemma lem3169393 (x : real) (n : nat) : (term4 x n) = ((term5 x n) = (real_pow x n)).
Proof. exact (eq_refl (term4 x n)). Qed.
Lemma lem3169402 (x : real) (n : nat) : (term5 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3169393 x n) (@lem3169392 x n)). Qed.
Lemma lem3169403 (x : real) : (term6 x) = (term1 x).
Proof. exact (@lem3169402 x term7). Qed.
Lemma lem3169405 (x : real) : (term1 x) = (real_mul x x).
Proof. exact (EQ_MP (@lem3169387 x) (@lem3169386 x)). Qed.
Lemma lem3169406 (x : real) : (term6 x) = (real_mul x x).
Proof. exact (TRANS (@lem3169403 x) (@lem3169405 x)). Qed.
Lemma lem3169407 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3169408 (x : real) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem3169407) (@lem3169406 x)). Qed.
Lemma lem3169409 (x : real) : (real_mul x x) = (real_mul x x).
Proof. exact (eq_refl (real_mul x x)). Qed.
Lemma lem3169410 (x : real) : ((term6 x) = (real_mul x x)) = ((real_mul x x) = (real_mul x x)).
Proof. exact (MK_COMB (@lem3169408 x) (@lem3169409 x)). Qed.
Lemma lem3169412 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3169413 (x : real) : (x = x) = True.
Proof. exact (@lem3169412 real x). Qed.
Lemma lem3169414 (x : real) : ((real_mul x x) = (real_mul x x)) = True.
Proof. exact (@lem3169413 (real_mul x x)). Qed.
Lemma lem3169415 (x : real) : ((term6 x) = (real_mul x x)) = True.
Proof. exact (TRANS (@lem3169410 x) (@lem3169414 x)). Qed.
Lemma lem3169416 : term10 = term11.
Proof. exact (fun_ext (fun x : real => @lem3169415 x)). Qed.
Lemma lem3169417 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3169418 : term12 = term13.
Proof. exact (MK_COMB (@lem3169417) (@lem3169416)). Qed.
Lemma lem3169420 {A : Type'} (t : Prop) : (term14 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3169421 (t : Prop) : (term15 t) = t.
Proof. exact (@lem3169420 real t). Qed.
Lemma lem3169422 : term13 = True.
Proof. exact (@lem3169421 True). Qed.
Lemma lem3169423 : term12 = True.
Proof. exact (TRANS (@lem3169418) (@lem3169422)). Qed.
Lemma lem3169424 : True = term12.
Proof. exact (SYM (@lem3169423)). Qed.
Lemma lem3169425 : term12.
Proof. exact (EQ_MP (@lem3169424) (@lem0)). Qed.
