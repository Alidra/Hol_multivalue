Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_LT2_ODD_EQ_term_abbrevs.
Require Import REAL_POW_LT2_ODD_EQ_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2308530 (n : nat) : term0 n.
Proof. exact (@lem1663094 n). Qed.
Lemma lem2308531 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2308532 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem2308531 n) (@lem2308530 n)). Qed.
Lemma lem2308533 (n : nat) (x : int) : term2 n x.
Proof. exact (@lem2308532 n (real_of_int x)). Qed.
Lemma lem2308534 (n : nat) (x : int) : (term2 n x) = (term3 n x).
Proof. exact (eq_refl (term2 n x)). Qed.
Lemma lem2308535 (n : nat) (x : int) : term3 n x.
Proof. exact (EQ_MP (@lem2308534 n x) (@lem2308533 n x)). Qed.
Lemma lem2308536 (n : nat) (x : int) (y : int) : term4 n x y.
Proof. exact (@lem2308535 n x (real_of_int y)). Qed.
Lemma lem2308537 (n : nat) (x : int) (y : int) : (term4 n x y) = (term5 n x y).
Proof. exact (eq_refl (term4 n x y)). Qed.
Lemma lem2308538 (n : nat) (x : int) (y : int) : term5 n x y.
Proof. exact (EQ_MP (@lem2308537 n x y) (@lem2308536 n x y)). Qed.
Lemma lem2308540 (x : int) (n : nat) : (term6 x n) = (term7 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308541 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2308542 (x : int) (n : nat) : (term8 x n) = (term9 x n).
Proof. exact (MK_COMB (@lem2308541) (@lem2308540 x n)). Qed.
Lemma lem2308544 (x : int) (n : nat) : (term6 x n) = (term7 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308545 (y : int) (n : nat) : (term6 y n) = (term7 y n).
Proof. exact (@lem2308544 y n). Qed.
Lemma lem2308546 (x : int) (y : int) (n : nat) : (term10 x y n) = (term11 x y n).
Proof. exact (MK_COMB (@lem2308542 x n) (@lem2308545 y n)). Qed.
Lemma lem2308548 (x : int) (y : int) : (term12 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2308549 (x : int) (y : int) (n : nat) : (term11 x y n) = (term13 x y n).
Proof. exact (@lem2308548 (int_pow x n) (int_pow y n)). Qed.
Lemma lem2308550 (x : int) (y : int) (n : nat) : (term10 x y n) = (term13 x y n).
Proof. exact (TRANS (@lem2308546 x y n) (@lem2308549 x y n)). Qed.
Lemma lem2308551 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2308552 (x : int) (y : int) (n : nat) : (term14 x y n) = (term15 x y n).
Proof. exact (MK_COMB (@lem2308551) (@lem2308550 x y n)). Qed.
Lemma lem2308554 (x : int) (y : int) : (term12 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2308555 (n : nat) (x : int) (y : int) : ((term10 x y n) = (term12 x y)) = ((term13 x y n) = (int_lt x y)).
Proof. exact (MK_COMB (@lem2308552 x y n) (@lem2308554 x y)). Qed.
Lemma lem2308556 (n : nat) : (term16 n) = (term16 n).
Proof. exact (eq_refl (term16 n)). Qed.
Lemma lem2308557 (n : nat) (x : int) (y : int) : (term5 n x y) = (term17 n x y).
Proof. exact (MK_COMB (@lem2308556 n) (@lem2308555 n x y)). Qed.
Lemma lem2308558 (n : nat) (x : int) (y : int) : term17 n x y.
Proof. exact (EQ_MP (@lem2308557 n x y) (@lem2308538 n x y)). Qed.
Lemma lem2308559 (n : nat) (x : int) : term18 n x.
Proof. exact (fun y : int => @lem2308558 n x y). Qed.
Lemma lem2308560 (n : nat) : term19 n.
Proof. exact (fun x : int => @lem2308559 n x). Qed.
Lemma lem2308561 : term20.
Proof. exact (fun n : nat => @lem2308560 n). Qed.
