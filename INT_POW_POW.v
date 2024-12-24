Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_POW_term_abbrevs.
Require Import REAL_POW_POW_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2308877 (x : int) : term0 x.
Proof. exact (@lem1640492 (real_of_int x)). Qed.
Lemma lem2308878 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2308879 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2308878 x) (@lem2308877 x)). Qed.
Lemma lem2308880 (x : int) (m : nat) : term2 x m.
Proof. exact (@lem2308879 x m). Qed.
Lemma lem2308881 (x : int) (m : nat) : (term2 x m) = (term3 x m).
Proof. exact (eq_refl (term2 x m)). Qed.
Lemma lem2308882 (x : int) (m : nat) : term3 x m.
Proof. exact (EQ_MP (@lem2308881 x m) (@lem2308880 x m)). Qed.
Lemma lem2308883 (x : int) (m : nat) (n : nat) : term4 x m n.
Proof. exact (@lem2308882 x m n). Qed.
Lemma lem2308884 (x : int) (m : nat) (n : nat) : (term4 x m n) = ((term5 x m n) = (term6 x m n)).
Proof. exact (eq_refl (term4 x m n)). Qed.
Lemma lem2308885 (x : int) (m : nat) (n : nat) : (term5 x m n) = (term6 x m n).
Proof. exact (EQ_MP (@lem2308884 x m n) (@lem2308883 x m n)). Qed.
Lemma lem2308887 (x : int) (n : nat) : (term7 x n) = (term8 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308888 (x : int) (m : nat) : (term7 x m) = (term8 x m).
Proof. exact (@lem2308887 x m). Qed.
Lemma lem2308889 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem2308890 (x : int) (m : nat) : (term9 x m) = (term10 x m).
Proof. exact (MK_COMB (@lem2308889) (@lem2308888 x m)). Qed.
Lemma lem2308891 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2308892 (x : int) (m : nat) (n : nat) : (term5 x m n) = (term11 x m n).
Proof. exact (MK_COMB (@lem2308890 x m) (@lem2308891 n)). Qed.
Lemma lem2308894 (x : int) (n : nat) : (term7 x n) = (term8 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308895 (x : int) (m : nat) (n : nat) : (term11 x m n) = (term12 x m n).
Proof. exact (@lem2308894 (int_pow x m) n). Qed.
Lemma lem2308896 (x : int) (m : nat) (n : nat) : (term5 x m n) = (term12 x m n).
Proof. exact (TRANS (@lem2308892 x m n) (@lem2308895 x m n)). Qed.
Lemma lem2308897 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2308898 (x : int) (m : nat) (n : nat) : (term13 x m n) = (term14 x m n).
Proof. exact (MK_COMB (@lem2308897) (@lem2308896 x m n)). Qed.
Lemma lem2308900 (x : int) (n : nat) : (term7 x n) = (term8 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308901 (x : int) (m : nat) (n : nat) : (term6 x m n) = (term15 x m n).
Proof. exact (@lem2308900 x (Nat.mul m n)). Qed.
Lemma lem2308902 (x : int) (m : nat) (n : nat) : ((term5 x m n) = (term6 x m n)) = ((term12 x m n) = (term15 x m n)).
Proof. exact (MK_COMB (@lem2308898 x m n) (@lem2308901 x m n)). Qed.
Lemma lem2308904 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2308905 (x : int) (m : nat) (n : nat) : ((term12 x m n) = (term15 x m n)) = ((term16 x m n) = (term17 x m n)).
Proof. exact (@lem2308904 (term16 x m n) (term17 x m n)). Qed.
Lemma lem2308906 (x : int) (m : nat) (n : nat) : ((term5 x m n) = (term6 x m n)) = ((term16 x m n) = (term17 x m n)).
Proof. exact (TRANS (@lem2308902 x m n) (@lem2308905 x m n)). Qed.
Lemma lem2308907 (x : int) (m : nat) (n : nat) : (term16 x m n) = (term17 x m n).
Proof. exact (EQ_MP (@lem2308906 x m n) (@lem2308885 x m n)). Qed.
Lemma lem2308908 (x : int) (m : nat) : term18 x m.
Proof. exact (fun n : nat => @lem2308907 x m n). Qed.
Lemma lem2308909 (x : int) : term19 x.
Proof. exact (fun m : nat => @lem2308908 x m). Qed.
Lemma lem2308910 : term20.
Proof. exact (fun x : int => @lem2308909 x). Qed.
