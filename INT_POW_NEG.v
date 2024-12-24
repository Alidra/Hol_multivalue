Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_NEG_term_abbrevs.
Require Import REAL_POW_NEG_spec.
Require Import thm2299672_spec.
Require Import thm2299871_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2308771 (x : int) : term0 x.
Proof. exact (@lem1362863 (real_of_int x)). Qed.
Lemma lem2308772 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2308773 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2308772 x) (@lem2308771 x)). Qed.
Lemma lem2308774 (x : int) (n : nat) : term2 x n.
Proof. exact (@lem2308773 x n). Qed.
Lemma lem2308775 (x : int) (n : nat) : (term2 x n) = ((term3 x n) = (term4 x n)).
Proof. exact (eq_refl (term2 x n)). Qed.
Lemma lem2308776 (x : int) (n : nat) : (term3 x n) = (term4 x n).
Proof. exact (EQ_MP (@lem2308775 x n) (@lem2308774 x n)). Qed.
Lemma lem2308778 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2308779 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem2308780 (x : int) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem2308779) (@lem2308778 x)). Qed.
Lemma lem2308781 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2308782 (x : int) (n : nat) : (term3 x n) = (term9 x n).
Proof. exact (MK_COMB (@lem2308780 x) (@lem2308781 n)). Qed.
Lemma lem2308784 (x : int) (n : nat) : (term10 x n) = (term11 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308785 (x : int) (n : nat) : (term9 x n) = (term12 x n).
Proof. exact (@lem2308784 (int_neg x) n). Qed.
Lemma lem2308786 (x : int) (n : nat) : (term3 x n) = (term12 x n).
Proof. exact (TRANS (@lem2308782 x n) (@lem2308785 x n)). Qed.
Lemma lem2308787 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2308788 (x : int) (n : nat) : (term13 x n) = (term14 x n).
Proof. exact (MK_COMB (@lem2308787) (@lem2308786 x n)). Qed.
Lemma lem2308790 (x : int) (n : nat) : (term10 x n) = (term11 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308791 (n : nat) : (term15 n) = (term15 n).
Proof. exact (eq_refl (term15 n)). Qed.
Lemma lem2308792 (x : int) (n : nat) : (term16 x n) = (term17 x n).
Proof. exact (MK_COMB (@lem2308791 n) (@lem2308790 x n)). Qed.
Lemma lem2308794 (x : int) (n : nat) : (term10 x n) = (term11 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308795 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2308796 (x : int) (n : nat) : (term18 x n) = (term19 x n).
Proof. exact (MK_COMB (@lem2308795) (@lem2308794 x n)). Qed.
Lemma lem2308798 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2308799 (x : int) (n : nat) : (term19 x n) = (term20 x n).
Proof. exact (@lem2308798 (int_pow x n)). Qed.
Lemma lem2308800 (x : int) (n : nat) : (term18 x n) = (term20 x n).
Proof. exact (TRANS (@lem2308796 x n) (@lem2308799 x n)). Qed.
Lemma lem2308801 (x : int) (n : nat) : (term4 x n) = (term21 x n).
Proof. exact (MK_COMB (@lem2308792 x n) (@lem2308800 x n)). Qed.
Lemma lem2308803 (b : Prop) (x : int) (y : int) : (term22 b x y) = (term23 b x y).
Proof. exact (EQ_MP (@lem2299871 b x y) (@lem2299672 b x y)). Qed.
Lemma lem2308804 (x : int) (n : nat) : (term21 x n) = (term24 x n).
Proof. exact (@lem2308803 (Coq.Arith.PeanoNat.Nat.Even n) (int_pow x n) (term25 x n)). Qed.
Lemma lem2308805 (x : int) (n : nat) : (term4 x n) = (term24 x n).
Proof. exact (TRANS (@lem2308801 x n) (@lem2308804 x n)). Qed.
Lemma lem2308806 (x : int) (n : nat) : ((term3 x n) = (term4 x n)) = ((term12 x n) = (term24 x n)).
Proof. exact (MK_COMB (@lem2308788 x n) (@lem2308805 x n)). Qed.
Lemma lem2308808 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2308809 (x : int) (n : nat) : ((term12 x n) = (term24 x n)) = ((term26 x n) = (term27 x n)).
Proof. exact (@lem2308808 (term26 x n) (term27 x n)). Qed.
Lemma lem2308810 (x : int) (n : nat) : ((term3 x n) = (term4 x n)) = ((term26 x n) = (term27 x n)).
Proof. exact (TRANS (@lem2308806 x n) (@lem2308809 x n)). Qed.
Lemma lem2308811 (x : int) (n : nat) : (term26 x n) = (term27 x n).
Proof. exact (EQ_MP (@lem2308810 x n) (@lem2308776 x n)). Qed.
Lemma lem2308812 (x : int) : term28 x.
Proof. exact (fun n : nat => @lem2308811 x n). Qed.
Lemma lem2308813 : term29.
Proof. exact (fun x : int => @lem2308812 x). Qed.
