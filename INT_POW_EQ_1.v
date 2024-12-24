Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_EQ_1_term_abbrevs.
Require Import REAL_POW_EQ_1_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2307873 (x : int) : term0 x.
Proof. exact (@lem1657725 (real_of_int x)). Qed.
Lemma lem2307874 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2307875 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2307874 x) (@lem2307873 x)). Qed.
Lemma lem2307876 (x : int) (n : nat) : term2 x n.
Proof. exact (@lem2307875 x n). Qed.
Lemma lem2307877 (x : int) (n : nat) : (term2 x n) = (((term3 x n) = term4) = (term5 x n)).
Proof. exact (eq_refl (term2 x n)). Qed.
Lemma lem2307878 (x : int) (n : nat) : ((term3 x n) = term4) = (term5 x n).
Proof. exact (EQ_MP (@lem2307877 x n) (@lem2307876 x n)). Qed.
Lemma lem2307880 (x : int) (n : nat) : (term3 x n) = (term6 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2307881 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2307882 (x : int) (n : nat) : (term7 x n) = (term8 x n).
Proof. exact (MK_COMB (@lem2307881) (@lem2307880 x n)). Qed.
Lemma lem2307884 (n : nat) : (real_of_num n) = (term9 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307885 : term4 = term10.
Proof. exact (@lem2307884 term11). Qed.
Lemma lem2307886 (x : int) (n : nat) : ((term3 x n) = term4) = ((term6 x n) = term10).
Proof. exact (MK_COMB (@lem2307882 x n) (@lem2307885)). Qed.
Lemma lem2307888 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2307889 (x : int) (n : nat) : ((term6 x n) = term10) = ((int_pow x n) = term12).
Proof. exact (@lem2307888 (int_pow x n) term12). Qed.
Lemma lem2307890 (x : int) (n : nat) : ((term3 x n) = term4) = ((int_pow x n) = term12).
Proof. exact (TRANS (@lem2307886 x n) (@lem2307889 x n)). Qed.
Lemma lem2307891 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2307892 (x : int) (n : nat) : (term13 x n) = (term14 x n).
Proof. exact (MK_COMB (@lem2307891) (@lem2307890 x n)). Qed.
Lemma lem2307894 (x : int) : (term15 x) = (term16 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2307895 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2307896 (x : int) : (term17 x) = (term18 x).
Proof. exact (MK_COMB (@lem2307895) (@lem2307894 x)). Qed.
Lemma lem2307898 (n : nat) : (real_of_num n) = (term9 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307899 : term4 = term10.
Proof. exact (@lem2307898 term11). Qed.
Lemma lem2307900 (x : int) : ((term15 x) = term4) = ((term16 x) = term10).
Proof. exact (MK_COMB (@lem2307896 x) (@lem2307899)). Qed.
Lemma lem2307902 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2307903 (x : int) : ((term16 x) = term10) = ((int_abs x) = term12).
Proof. exact (@lem2307902 (int_abs x) term12). Qed.
Lemma lem2307904 (x : int) : ((term15 x) = term4) = ((int_abs x) = term12).
Proof. exact (TRANS (@lem2307900 x) (@lem2307903 x)). Qed.
Lemma lem2307905 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2307906 (x : int) : (term19 x) = (term20 x).
Proof. exact (MK_COMB (@lem2307905) (@lem2307904 x)). Qed.
Lemma lem2307908 (n : nat) : (real_of_num n) = (term9 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307909 : term21 = term22.
Proof. exact (@lem2307908 (NUMERAL 0)). Qed.
Lemma lem2307910 (x : int) : (term23 x) = (term23 x).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem2307911 (x : int) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem2307910 x) (@lem2307909)). Qed.
Lemma lem2307913 (x : int) (y : int) : (term26 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2307914 (x : int) : (term25 x) = (term27 x).
Proof. exact (@lem2307913 x term28). Qed.
Lemma lem2307915 (x : int) : (term24 x) = (term27 x).
Proof. exact (TRANS (@lem2307911 x) (@lem2307914 x)). Qed.
Lemma lem2307916 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2307917 (x : int) : (term29 x) = (term30 x).
Proof. exact (MK_COMB (@lem2307916) (@lem2307915 x)). Qed.
Lemma lem2307918 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem2307919 (x : int) (n : nat) : (term31 x n) = (term32 x n).
Proof. exact (MK_COMB (@lem2307917 x) (@lem2307918 n)). Qed.
Lemma lem2307920 (x : int) (n : nat) : (term33 x n) = (term34 x n).
Proof. exact (MK_COMB (@lem2307906 x) (@lem2307919 x n)). Qed.
Lemma lem2307921 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2307922 (x : int) (n : nat) : (term35 x n) = (term36 x n).
Proof. exact (MK_COMB (@lem2307921) (@lem2307920 x n)). Qed.
Lemma lem2307923 (n : nat) : (n = (NUMERAL 0)) = (n = (NUMERAL 0)).
Proof. exact (eq_refl (n = (NUMERAL 0))). Qed.
Lemma lem2307924 (x : int) (n : nat) : (term5 x n) = (term37 x n).
Proof. exact (MK_COMB (@lem2307922 x n) (@lem2307923 n)). Qed.
Lemma lem2307925 (x : int) (n : nat) : (((term3 x n) = term4) = (term5 x n)) = (((int_pow x n) = term12) = (term37 x n)).
Proof. exact (MK_COMB (@lem2307892 x n) (@lem2307924 x n)). Qed.
Lemma lem2307926 (x : int) (n : nat) : ((int_pow x n) = term12) = (term37 x n).
Proof. exact (EQ_MP (@lem2307925 x n) (@lem2307878 x n)). Qed.
Lemma lem2307927 (x : int) : term38 x.
Proof. exact (fun n : nat => @lem2307926 x n). Qed.
Lemma lem2307928 : term39.
Proof. exact (fun x : int => @lem2307927 x). Qed.
