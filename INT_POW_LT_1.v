Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_LT_1_term_abbrevs.
Require Import REAL_POW_LT_1_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2308606 (n : nat) : term0 n.
Proof. exact (@lem1638435 n). Qed.
Lemma lem2308607 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2308608 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem2308607 n) (@lem2308606 n)). Qed.
Lemma lem2308609 (n : nat) (x : int) : term2 n x.
Proof. exact (@lem2308608 n (real_of_int x)). Qed.
Lemma lem2308610 (x : int) (n : nat) : (term2 n x) = (term3 x n).
Proof. exact (eq_refl (term2 n x)). Qed.
Lemma lem2308611 (x : int) (n : nat) : term3 x n.
Proof. exact (EQ_MP (@lem2308610 x n) (@lem2308609 n x)). Qed.
Lemma lem2308613 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2308614 : term5 = term6.
Proof. exact (@lem2308613 term7). Qed.
Lemma lem2308615 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2308616 : term8 = term9.
Proof. exact (MK_COMB (@lem2308615) (@lem2308614)). Qed.
Lemma lem2308617 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2308618 (x : int) : (term10 x) = (term11 x).
Proof. exact (MK_COMB (@lem2308616) (@lem2308617 x)). Qed.
Lemma lem2308620 (x : int) (y : int) : (term12 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2308621 (x : int) : (term11 x) = (term13 x).
Proof. exact (@lem2308620 term14 x). Qed.
Lemma lem2308622 (x : int) : (term10 x) = (term13 x).
Proof. exact (TRANS (@lem2308618 x) (@lem2308621 x)). Qed.
Lemma lem2308623 (n : nat) : (term15 n) = (term15 n).
Proof. exact (eq_refl (term15 n)). Qed.
Lemma lem2308624 (n : nat) (x : int) : (term16 n x) = (term17 n x).
Proof. exact (MK_COMB (@lem2308623 n) (@lem2308622 x)). Qed.
Lemma lem2308625 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2308626 (n : nat) (x : int) : (term18 n x) = (term19 n x).
Proof. exact (MK_COMB (@lem2308625) (@lem2308624 n x)). Qed.
Lemma lem2308628 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2308629 : term5 = term6.
Proof. exact (@lem2308628 term7). Qed.
Lemma lem2308630 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2308631 : term8 = term9.
Proof. exact (MK_COMB (@lem2308630) (@lem2308629)). Qed.
Lemma lem2308633 (x : int) (n : nat) : (term20 x n) = (term21 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308634 (x : int) (n : nat) : (term22 x n) = (term23 x n).
Proof. exact (MK_COMB (@lem2308631) (@lem2308633 x n)). Qed.
Lemma lem2308636 (x : int) (y : int) : (term12 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2308637 (x : int) (n : nat) : (term23 x n) = (term24 x n).
Proof. exact (@lem2308636 term14 (int_pow x n)). Qed.
Lemma lem2308638 (x : int) (n : nat) : (term22 x n) = (term24 x n).
Proof. exact (TRANS (@lem2308634 x n) (@lem2308637 x n)). Qed.
Lemma lem2308639 (x : int) (n : nat) : (term3 x n) = (term25 x n).
Proof. exact (MK_COMB (@lem2308626 n x) (@lem2308638 x n)). Qed.
Lemma lem2308640 (x : int) (n : nat) : term25 x n.
Proof. exact (EQ_MP (@lem2308639 x n) (@lem2308611 x n)). Qed.
Lemma lem2308641 (n : nat) : term26 n.
Proof. exact (fun x : int => @lem2308640 x n). Qed.
Lemma lem2308642 : term27.
Proof. exact (fun n : nat => @lem2308641 n). Qed.
