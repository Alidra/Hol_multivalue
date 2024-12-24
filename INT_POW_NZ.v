Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_NZ_term_abbrevs.
Require Import REAL_POW_NZ_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2308814 (x : int) : term0 x.
Proof. exact (@lem1598144 (real_of_int x)). Qed.
Lemma lem2308815 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2308816 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2308815 x) (@lem2308814 x)). Qed.
Lemma lem2308817 (x : int) (n : nat) : term2 x n.
Proof. exact (@lem2308816 x n). Qed.
Lemma lem2308818 (x : int) (n : nat) : (term2 x n) = (term3 x n).
Proof. exact (eq_refl (term2 x n)). Qed.
Lemma lem2308819 (x : int) (n : nat) : term3 x n.
Proof. exact (EQ_MP (@lem2308818 x n) (@lem2308817 x n)). Qed.
Lemma lem2308821 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2308822 : term5 = term6.
Proof. exact (@lem2308821 (NUMERAL 0)). Qed.
Lemma lem2308823 (x : int) : (term7 x) = (term7 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem2308824 (x : int) : ((real_of_int x) = term5) = ((real_of_int x) = term6).
Proof. exact (MK_COMB (@lem2308823 x) (@lem2308822)). Qed.
Lemma lem2308826 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2308827 (x : int) : ((real_of_int x) = term6) = (x = term8).
Proof. exact (@lem2308826 x term8). Qed.
Lemma lem2308828 (x : int) : ((real_of_int x) = term5) = (x = term8).
Proof. exact (TRANS (@lem2308824 x) (@lem2308827 x)). Qed.
Lemma lem2308829 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2308830 (x : int) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem2308829) (@lem2308828 x)). Qed.
Lemma lem2308831 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2308832 (x : int) : (term11 x) = (term12 x).
Proof. exact (MK_COMB (@lem2308831) (@lem2308830 x)). Qed.
Lemma lem2308834 (x : int) (n : nat) : (term13 x n) = (term14 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308835 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2308836 (x : int) (n : nat) : (term15 x n) = (term16 x n).
Proof. exact (MK_COMB (@lem2308835) (@lem2308834 x n)). Qed.
Lemma lem2308838 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2308839 : term5 = term6.
Proof. exact (@lem2308838 (NUMERAL 0)). Qed.
Lemma lem2308840 (x : int) (n : nat) : ((term13 x n) = term5) = ((term14 x n) = term6).
Proof. exact (MK_COMB (@lem2308836 x n) (@lem2308839)). Qed.
Lemma lem2308842 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2308843 (x : int) (n : nat) : ((term14 x n) = term6) = ((int_pow x n) = term8).
Proof. exact (@lem2308842 (int_pow x n) term8). Qed.
Lemma lem2308844 (x : int) (n : nat) : ((term13 x n) = term5) = ((int_pow x n) = term8).
Proof. exact (TRANS (@lem2308840 x n) (@lem2308843 x n)). Qed.
Lemma lem2308845 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2308846 (x : int) (n : nat) : (term17 x n) = (term18 x n).
Proof. exact (MK_COMB (@lem2308845) (@lem2308844 x n)). Qed.
Lemma lem2308847 (x : int) (n : nat) : (term3 x n) = (term19 x n).
Proof. exact (MK_COMB (@lem2308832 x) (@lem2308846 x n)). Qed.
Lemma lem2308848 (x : int) (n : nat) : term19 x n.
Proof. exact (EQ_MP (@lem2308847 x n) (@lem2308819 x n)). Qed.
Lemma lem2308849 (x : int) : term20 x.
Proof. exact (fun n : nat => @lem2308848 x n). Qed.
Lemma lem2308850 : term21.
Proof. exact (fun x : int => @lem2308849 x). Qed.
