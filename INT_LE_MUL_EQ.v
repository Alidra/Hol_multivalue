Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_MUL_EQ_term_abbrevs.
Require Import REAL_LE_MUL_EQ_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2302817 : term0.
Proof. exact (proj2 (@lem1606637)). Qed.
Lemma lem2302818 (x : int) : term1 x.
Proof. exact (@lem2302817 (real_of_int x)). Qed.
Lemma lem2302819 (x : int) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem2302820 (x : int) : term2 x.
Proof. exact (EQ_MP (@lem2302819 x) (@lem2302818 x)). Qed.
Lemma lem2302821 (x : int) (y : int) : term3 x y.
Proof. exact (@lem2302820 x (real_of_int y)). Qed.
Lemma lem2302822 (y : int) (x : int) : (term3 x y) = (term4 y x).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem2302823 (y : int) (x : int) : term4 y x.
Proof. exact (EQ_MP (@lem2302822 y x) (@lem2302821 x y)). Qed.
Lemma lem2302825 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302826 : term6 = term7.
Proof. exact (@lem2302825 (NUMERAL 0)). Qed.
Lemma lem2302827 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2302828 : term8 = term9.
Proof. exact (MK_COMB (@lem2302827) (@lem2302826)). Qed.
Lemma lem2302829 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2302830 (y : int) : (term10 y) = (term11 y).
Proof. exact (MK_COMB (@lem2302828) (@lem2302829 y)). Qed.
Lemma lem2302832 (x : int) (y : int) : (term12 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2302833 (y : int) : (term11 y) = (term13 y).
Proof. exact (@lem2302832 term14 y). Qed.
Lemma lem2302834 (y : int) : (term10 y) = (term13 y).
Proof. exact (TRANS (@lem2302830 y) (@lem2302833 y)). Qed.
Lemma lem2302835 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2302836 (y : int) : (term15 y) = (term16 y).
Proof. exact (MK_COMB (@lem2302835) (@lem2302834 y)). Qed.
Lemma lem2302838 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302839 : term6 = term7.
Proof. exact (@lem2302838 (NUMERAL 0)). Qed.
Lemma lem2302840 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302841 : term17 = term18.
Proof. exact (MK_COMB (@lem2302840) (@lem2302839)). Qed.
Lemma lem2302843 (x : int) (y : int) : (term19 x y) = (term20 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2302844 (x : int) (y : int) : (term21 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem2302841) (@lem2302843 x y)). Qed.
Lemma lem2302846 (x : int) (y : int) : (term23 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302847 (x : int) (y : int) : (term22 x y) = (term24 x y).
Proof. exact (@lem2302846 term14 (int_mul x y)). Qed.
Lemma lem2302848 (x : int) (y : int) : (term21 x y) = (term24 x y).
Proof. exact (TRANS (@lem2302844 x y) (@lem2302847 x y)). Qed.
Lemma lem2302849 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2302850 (x : int) (y : int) : (term25 x y) = (term26 x y).
Proof. exact (MK_COMB (@lem2302849) (@lem2302848 x y)). Qed.
Lemma lem2302852 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302853 : term6 = term7.
Proof. exact (@lem2302852 (NUMERAL 0)). Qed.
Lemma lem2302854 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302855 : term17 = term18.
Proof. exact (MK_COMB (@lem2302854) (@lem2302853)). Qed.
Lemma lem2302856 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2302857 (x : int) : (term27 x) = (term28 x).
Proof. exact (MK_COMB (@lem2302855) (@lem2302856 x)). Qed.
Lemma lem2302859 (x : int) (y : int) : (term23 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302860 (x : int) : (term28 x) = (term29 x).
Proof. exact (@lem2302859 term14 x). Qed.
Lemma lem2302861 (x : int) : (term27 x) = (term29 x).
Proof. exact (TRANS (@lem2302857 x) (@lem2302860 x)). Qed.
Lemma lem2302862 (y : int) (x : int) : ((term21 x y) = (term27 x)) = ((term24 x y) = (term29 x)).
Proof. exact (MK_COMB (@lem2302850 x y) (@lem2302861 x)). Qed.
Lemma lem2302863 (y : int) (x : int) : (term4 y x) = (term30 y x).
Proof. exact (MK_COMB (@lem2302836 y) (@lem2302862 y x)). Qed.
Lemma lem2302864 (y : int) (x : int) : term30 y x.
Proof. exact (EQ_MP (@lem2302863 y x) (@lem2302823 y x)). Qed.
Lemma lem2302865 (x : int) : term31 x.
Proof. exact (fun y : int => @lem2302864 y x). Qed.
Lemma lem2302866 : term32.
Proof. exact (fun x : int => @lem2302865 x). Qed.
Lemma lem2302867 : term33.
Proof. exact (proj1 (@lem1606637)). Qed.
Lemma lem2302868 (x : int) : term34 x.
Proof. exact (@lem2302867 (real_of_int x)). Qed.
Lemma lem2302869 (x : int) : (term34 x) = (term35 x).
Proof. exact (eq_refl (term34 x)). Qed.
Lemma lem2302870 (x : int) : term35 x.
Proof. exact (EQ_MP (@lem2302869 x) (@lem2302868 x)). Qed.
Lemma lem2302871 (x : int) (y : int) : term36 x y.
Proof. exact (@lem2302870 x (real_of_int y)). Qed.
Lemma lem2302872 (x : int) (y : int) : (term36 x y) = (term37 x y).
Proof. exact (eq_refl (term36 x y)). Qed.
Lemma lem2302873 (x : int) (y : int) : term37 x y.
Proof. exact (EQ_MP (@lem2302872 x y) (@lem2302871 x y)). Qed.
Lemma lem2302875 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302876 : term6 = term7.
Proof. exact (@lem2302875 (NUMERAL 0)). Qed.
Lemma lem2302877 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2302878 : term8 = term9.
Proof. exact (MK_COMB (@lem2302877) (@lem2302876)). Qed.
Lemma lem2302879 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2302880 (x : int) : (term10 x) = (term11 x).
Proof. exact (MK_COMB (@lem2302878) (@lem2302879 x)). Qed.
Lemma lem2302882 (x : int) (y : int) : (term12 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2302883 (x : int) : (term11 x) = (term13 x).
Proof. exact (@lem2302882 term14 x). Qed.
Lemma lem2302884 (x : int) : (term10 x) = (term13 x).
Proof. exact (TRANS (@lem2302880 x) (@lem2302883 x)). Qed.
Lemma lem2302885 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2302886 (x : int) : (term15 x) = (term16 x).
Proof. exact (MK_COMB (@lem2302885) (@lem2302884 x)). Qed.
Lemma lem2302888 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302889 : term6 = term7.
Proof. exact (@lem2302888 (NUMERAL 0)). Qed.
Lemma lem2302890 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302891 : term17 = term18.
Proof. exact (MK_COMB (@lem2302890) (@lem2302889)). Qed.
Lemma lem2302893 (x : int) (y : int) : (term19 x y) = (term20 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2302894 (x : int) (y : int) : (term21 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem2302891) (@lem2302893 x y)). Qed.
Lemma lem2302896 (x : int) (y : int) : (term23 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302897 (x : int) (y : int) : (term22 x y) = (term24 x y).
Proof. exact (@lem2302896 term14 (int_mul x y)). Qed.
Lemma lem2302898 (x : int) (y : int) : (term21 x y) = (term24 x y).
Proof. exact (TRANS (@lem2302894 x y) (@lem2302897 x y)). Qed.
Lemma lem2302899 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2302900 (x : int) (y : int) : (term25 x y) = (term26 x y).
Proof. exact (MK_COMB (@lem2302899) (@lem2302898 x y)). Qed.
Lemma lem2302902 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302903 : term6 = term7.
Proof. exact (@lem2302902 (NUMERAL 0)). Qed.
Lemma lem2302904 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302905 : term17 = term18.
Proof. exact (MK_COMB (@lem2302904) (@lem2302903)). Qed.
Lemma lem2302906 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2302907 (y : int) : (term27 y) = (term28 y).
Proof. exact (MK_COMB (@lem2302905) (@lem2302906 y)). Qed.
Lemma lem2302909 (x : int) (y : int) : (term23 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302910 (y : int) : (term28 y) = (term29 y).
Proof. exact (@lem2302909 term14 y). Qed.
Lemma lem2302911 (y : int) : (term27 y) = (term29 y).
Proof. exact (TRANS (@lem2302907 y) (@lem2302910 y)). Qed.
Lemma lem2302912 (x : int) (y : int) : ((term21 x y) = (term27 y)) = ((term24 x y) = (term29 y)).
Proof. exact (MK_COMB (@lem2302900 x y) (@lem2302911 y)). Qed.
Lemma lem2302913 (x : int) (y : int) : (term37 x y) = (term38 x y).
Proof. exact (MK_COMB (@lem2302886 x) (@lem2302912 x y)). Qed.
Lemma lem2302914 (x : int) (y : int) : term38 x y.
Proof. exact (EQ_MP (@lem2302913 x y) (@lem2302873 x y)). Qed.
Lemma lem2302915 (x : int) : term39 x.
Proof. exact (fun y : int => @lem2302914 x y). Qed.
Lemma lem2302916 : term40.
Proof. exact (fun x : int => @lem2302915 x). Qed.
Lemma lem2302917 : term41.
Proof. exact (conj (@lem2302916) (@lem2302866)). Qed.
