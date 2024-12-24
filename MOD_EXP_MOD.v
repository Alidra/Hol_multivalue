Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_EXP_MOD_term_abbrevs.
Require Import EQ_TRANS_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import MOD_MULT_LMOD_spec.
Require Import MOD_MULT_RMOD_spec.
Require Import MOD_ZERO_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm86199_spec.
Lemma lem205837 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem205838 {A : Type'} (x : A) (h1 : term0 A) : term1 A x.
Proof. exact (@lem205837 A h1 x). Qed.
Lemma lem205839 {A : Type'} (x : A) : (term1 A x) = (term2 A x).
Proof. exact (eq_refl (term1 A x)). Qed.
Lemma lem205840 {A : Type'} (x : A) (h1 : term0 A) : term2 A x.
Proof. exact (EQ_MP (@lem205839 A x) (@lem205838 A x h1)). Qed.
Lemma lem205841 {A : Type'} (x : A) (y : A) (h1 : term0 A) : term3 A x y.
Proof. exact (@lem205840 A x h1 y). Qed.
Lemma lem205842 {A : Type'} (y : A) (x : A) : (term3 A x y) = (term4 A y x).
Proof. exact (eq_refl (term3 A x y)). Qed.
Lemma lem205843 {A : Type'} (y : A) (x : A) (h1 : term0 A) : term4 A y x.
Proof. exact (EQ_MP (@lem205842 A y x) (@lem205841 A x y h1)). Qed.
Lemma lem205844 {A : Type'} (y : A) (x : A) (z : A) (h1 : term0 A) : term5 A y x z.
Proof. exact (@lem205843 A y x h1 z). Qed.
Lemma lem205845 {A : Type'} (y : A) (x : A) (z : A) : (term5 A y x z) = (term6 A y x z).
Proof. exact (eq_refl (term5 A y x z)). Qed.
Lemma lem205846 {A : Type'} (y : A) (x : A) (z : A) (h1 : term0 A) : term6 A y x z.
Proof. exact (EQ_MP (@lem205845 A y x z) (@lem205844 A y x z h1)). Qed.
Lemma lem205847 {A : Type'} (x : A) (y : A) (z : A) (h1 : term7 A x y z) : term7 A x y z.
Proof. exact (h1). Qed.
Lemma lem205848 {A : Type'} (x : A) (y : A) (z : A) (h1 : term0 A) (h2 : term7 A x y z) : x = z.
Proof. exact (@lem205846 A y x z h1 (@lem205847 A x y z h2)). Qed.
Lemma lem205849 {A : Type'} (x : A) (y : A) (z : A) (h1 : term7 A x y z) : term8 A x z.
Proof. exact (fun h0 : term0 A => @lem205848 A x y z h0 h1). Qed.
Lemma lem205850 {A : Type'} (x : A) (z : A) (h1 : term9 A x z) : term9 A x z.
Proof. exact (h1). Qed.
Lemma lem205851 {A : Type'} (x : A) (z : A) (h1 : term9 A x z) : term8 A x z.
Proof. exact (ex_elim (@lem205850 A x z h1) (fun y : A => fun h0 : term10 A x z y => @lem205849 A x y z h0)). Qed.
Lemma lem205852 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem205853 {A : Type'} (x : A) (z : A) (h1 : term0 A) (h2 : term9 A x z) : x = z.
Proof. exact (@lem205851 A x z h2 (@lem205852 A h1)). Qed.
Lemma lem205854 {A : Type'} (x : A) (z : A) (h1 : term0 A) : term11 A x z.
Proof. exact (fun h0 : term9 A x z => @lem205853 A x z h1 h0). Qed.
Lemma lem205855 {A : Type'} (x : A) (h1 : term0 A) : term12 A x.
Proof. exact (fun z : A => @lem205854 A x z h1). Qed.
Lemma lem205856 {A : Type'} (h1 : term0 A) : term13 A.
Proof. exact (fun x : A => @lem205855 A x h1). Qed.
Lemma lem205857 {A : Type'} : term14 A.
Proof. exact (fun h0 : term0 A => @lem205856 A h0). Qed.
Lemma lem205858 {A : Type'} : term13 A.
Proof. exact (@lem205857 A (@lem403 A)). Qed.
Lemma lem205859 {A : Type'} (x : A) : term15 A x.
Proof. exact (@lem205858 A x). Qed.
Lemma lem205860 {A : Type'} (x : A) : (term15 A x) = (term12 A x).
Proof. exact (eq_refl (term15 A x)). Qed.
Lemma lem205861 {A : Type'} (x : A) : term12 A x.
Proof. exact (EQ_MP (@lem205860 A x) (@lem205859 A x)). Qed.
Lemma lem205862 {A : Type'} (x : A) (z : A) : term16 A x z.
Proof. exact (@lem205861 A x z). Qed.
Lemma lem205863 {A : Type'} (x : A) (z : A) : (term16 A x z) = (term11 A x z).
Proof. exact (eq_refl (term16 A x z)). Qed.
Lemma lem205865 (n : nat) : term17 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem205866 (n : nat) : (term17 n) = (term18 n).
Proof. exact (eq_refl (term17 n)). Qed.
Lemma lem205867 (n : nat) : term18 n.
Proof. exact (EQ_MP (@lem205866 n) (@lem205865 n)). Qed.
Lemma lem205870 (n : nat) : term19 n.
Proof. exact (@lem159121 n). Qed.
Lemma lem205871 (n : nat) : (term19 n) = ((term20 n) = n).
Proof. exact (eq_refl (term19 n)). Qed.
Lemma lem205876 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem205877 (m : nat) : (Nat.modulo m) = (Nat.modulo m).
Proof. exact (eq_refl (Nat.modulo m)). Qed.
Lemma lem205878 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo m n) = (term20 m).
Proof. exact (MK_COMB (@lem205877 m) (@lem205876 n h1)). Qed.
Lemma lem205880 (n : nat) : (term20 n) = n.
Proof. exact (EQ_MP (@lem205871 n) (@lem205870 n)). Qed.
Lemma lem205881 (m : nat) : (term20 m) = m.
Proof. exact (@lem205880 m). Qed.
Lemma lem205882 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo m n) = m.
Proof. exact (TRANS (@lem205878 m n h1) (@lem205881 m)). Qed.
Lemma lem205883 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem205884 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term21 m n) = (Nat.pow m).
Proof. exact (MK_COMB (@lem205883) (@lem205882 m n h1)). Qed.
Lemma lem205885 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem205886 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term22 m n p) = (Nat.pow m p).
Proof. exact (MK_COMB (@lem205884 m n h1) (@lem205885 p)). Qed.
Lemma lem205887 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem205888 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term23 m n p) = (term24 m p).
Proof. exact (MK_COMB (@lem205887) (@lem205886 m p n h1)). Qed.
Lemma lem205890 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem205891 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term25 m p n) = (term26 m p).
Proof. exact (MK_COMB (@lem205888 m p n h1) (@lem205890 n h1)). Qed.
Lemma lem205893 (n : nat) : (term20 n) = n.
Proof. exact (EQ_MP (@lem205871 n) (@lem205870 n)). Qed.
Lemma lem205894 (m : nat) (p : nat) : (term26 m p) = (Nat.pow m p).
Proof. exact (@lem205893 (Nat.pow m p)). Qed.
Lemma lem205895 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term25 m p n) = (Nat.pow m p).
Proof. exact (TRANS (@lem205891 m p n h1) (@lem205894 m p)). Qed.
Lemma lem205896 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem205897 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term27 m p n) = (term28 m p).
Proof. exact (MK_COMB (@lem205896) (@lem205895 m p n h1)). Qed.
Lemma lem205899 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem205900 (m : nat) (p : nat) : (term24 m p) = (term24 m p).
Proof. exact (eq_refl (term24 m p)). Qed.
Lemma lem205901 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term29 m p n) = (term26 m p).
Proof. exact (MK_COMB (@lem205900 m p) (@lem205899 n h1)). Qed.
Lemma lem205903 (n : nat) : (term20 n) = n.
Proof. exact (EQ_MP (@lem205871 n) (@lem205870 n)). Qed.
Lemma lem205904 (m : nat) (p : nat) : (term26 m p) = (Nat.pow m p).
Proof. exact (@lem205903 (Nat.pow m p)). Qed.
Lemma lem205905 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term29 m p n) = (Nat.pow m p).
Proof. exact (TRANS (@lem205901 m p n h1) (@lem205904 m p)). Qed.
Lemma lem205906 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term25 m p n) = (term29 m p n)) = ((Nat.pow m p) = (Nat.pow m p)).
Proof. exact (MK_COMB (@lem205897 m p n h1) (@lem205905 m p n h1)). Qed.
Lemma lem205908 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem205909 (x : nat) : (x = x) = True.
Proof. exact (@lem205908 nat x). Qed.
Lemma lem205910 (m : nat) (p : nat) : ((Nat.pow m p) = (Nat.pow m p)) = True.
Proof. exact (@lem205909 (Nat.pow m p)). Qed.
Lemma lem205911 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term25 m p n) = (term29 m p n)) = True.
Proof. exact (TRANS (@lem205906 m p n h1) (@lem205910 m p)). Qed.
Lemma lem205912 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : True = ((term25 m p n) = (term29 m p n)).
Proof. exact (SYM (@lem205911 m p n h1)). Qed.
Lemma lem205913 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term25 m p n) = (term29 m p n).
Proof. exact (EQ_MP (@lem205912 m p n h1) (@lem0)). Qed.
Lemma lem205935 (P : nat -> Prop) : term30 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem205936 (m : nat) (n : nat) : term31 m n.
Proof. exact (@lem205935 (term32 m n)). Qed.
Lemma lem205937 (m : nat) (n : nat) : (term33 m n) = ((term34 m n) = (term35 m n)).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem205938 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem205939 (m : nat) (n : nat) : (term36 m n) = (term37 m n).
Proof. exact (MK_COMB (@lem205938) (@lem205937 m n)). Qed.
Lemma lem205940 (m : nat) (p : nat) (n : nat) : (term38 m n p) = ((term25 m p n) = (term29 m p n)).
Proof. exact (eq_refl (term38 m n p)). Qed.
Lemma lem205941 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem205942 (m : nat) (p : nat) (n : nat) : (term39 m n p) = (term40 m p n).
Proof. exact (MK_COMB (@lem205941) (@lem205940 m p n)). Qed.
Lemma lem205943 (m : nat) (p : nat) (n : nat) : (term41 m n p) = ((term42 m p n) = (term43 m p n)).
Proof. exact (eq_refl (term41 m n p)). Qed.
Lemma lem205944 (m : nat) (p : nat) (n : nat) : (term44 m n p) = (term45 m p n).
Proof. exact (MK_COMB (@lem205942 m p n) (@lem205943 m p n)). Qed.
Lemma lem205945 (m : nat) (n : nat) : (term46 m n) = (term47 m n).
Proof. exact (fun_ext (fun p : nat => @lem205944 m p n)). Qed.
Lemma lem205946 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem205947 (m : nat) (n : nat) : (term48 m n) = (term49 m n).
Proof. exact (MK_COMB (@lem205946) (@lem205945 m n)). Qed.
Lemma lem205948 (m : nat) (n : nat) : (term50 m n) = (term51 m n).
Proof. exact (MK_COMB (@lem205939 m n) (@lem205947 m n)). Qed.
Lemma lem205949 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem205950 (m : nat) (n : nat) : (term52 m n) = (term53 m n).
Proof. exact (MK_COMB (@lem205949) (@lem205948 m n)). Qed.
Lemma lem205951 (m : nat) (p : nat) (n : nat) : (term38 m n p) = ((term25 m p n) = (term29 m p n)).
Proof. exact (eq_refl (term38 m n p)). Qed.
Lemma lem205952 (m : nat) (n : nat) : (term54 m n) = (term32 m n).
Proof. exact (fun_ext (fun p : nat => @lem205951 m p n)). Qed.
Lemma lem205953 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem205954 (m : nat) (n : nat) : (term55 m n) = (term56 m n).
Proof. exact (MK_COMB (@lem205953) (@lem205952 m n)). Qed.
Lemma lem205955 (m : nat) (n : nat) : (term31 m n) = (term57 m n).
Proof. exact (MK_COMB (@lem205950 m n) (@lem205954 m n)). Qed.
Lemma lem205956 (m : nat) (n : nat) : term57 m n.
Proof. exact (EQ_MP (@lem205955 m n) (@lem205936 m n)). Qed.
Lemma lem205965 : term58.
Proof. exact (proj1 (@lem86199)). Qed.
Lemma lem205966 (m : nat) : term59 m.
Proof. exact (@lem205965 m). Qed.
Lemma lem205967 (m : nat) : (term59 m) = ((term60 m) = term61).
Proof. exact (eq_refl (term59 m)). Qed.
Lemma lem205985 (m : nat) : (term60 m) = term61.
Proof. exact (EQ_MP (@lem205967 m) (@lem205966 m)). Qed.
Lemma lem205986 (m : nat) (n : nat) : (term62 m n) = term61.
Proof. exact (@lem205985 (Nat.modulo m n)). Qed.
Lemma lem205987 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem205988 (m : nat) (n : nat) : (term63 m n) = term64.
Proof. exact (MK_COMB (@lem205987) (@lem205986 m n)). Qed.
Lemma lem205989 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem205990 (m : nat) (n : nat) : (term34 m n) = (term65 n).
Proof. exact (MK_COMB (@lem205988 m n) (@lem205989 n)). Qed.
Lemma lem205991 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem205992 (m : nat) (n : nat) : (term66 m n) = (term67 n).
Proof. exact (MK_COMB (@lem205991) (@lem205990 m n)). Qed.
Lemma lem205994 (m : nat) : (term60 m) = term61.
Proof. exact (EQ_MP (@lem205967 m) (@lem205966 m)). Qed.
Lemma lem205995 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem205996 (m : nat) : (term68 m) = term64.
Proof. exact (MK_COMB (@lem205995) (@lem205994 m)). Qed.
Lemma lem205997 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem205998 (m : nat) (n : nat) : (term35 m n) = (term65 n).
Proof. exact (MK_COMB (@lem205996 m) (@lem205997 n)). Qed.
Lemma lem205999 (m : nat) (n : nat) : ((term34 m n) = (term35 m n)) = ((term65 n) = (term65 n)).
Proof. exact (MK_COMB (@lem205992 m n) (@lem205998 m n)). Qed.
Lemma lem206001 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem206002 (x : nat) : (x = x) = True.
Proof. exact (@lem206001 nat x). Qed.
Lemma lem206003 (n : nat) : ((term65 n) = (term65 n)) = True.
Proof. exact (@lem206002 (term65 n)). Qed.
Lemma lem206004 (m : nat) (n : nat) : ((term34 m n) = (term35 m n)) = True.
Proof. exact (TRANS (@lem205999 m n) (@lem206003 n)). Qed.
Lemma lem206005 (m : nat) (n : nat) : True = ((term34 m n) = (term35 m n)).
Proof. exact (SYM (@lem206004 m n)). Qed.
Lemma lem206006 (m : nat) (n : nat) : (term34 m n) = (term35 m n).
Proof. exact (EQ_MP (@lem206005 m n) (@lem0)). Qed.
Lemma lem206007 : term69.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem206008 (m : nat) : term70 m.
Proof. exact (@lem206007 m). Qed.
Lemma lem206009 (m : nat) : (term70 m) = (term71 m).
Proof. exact (eq_refl (term70 m)). Qed.
Lemma lem206010 (m : nat) : term71 m.
Proof. exact (EQ_MP (@lem206009 m) (@lem206008 m)). Qed.
Lemma lem206011 (m : nat) (n : nat) : term72 m n.
Proof. exact (@lem206010 m n). Qed.
Lemma lem206012 (m : nat) (n : nat) : (term72 m n) = ((term73 m n) = (term74 m n)).
Proof. exact (eq_refl (term72 m n)). Qed.
Lemma lem206034 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (EQ_MP (@lem206012 m n) (@lem206011 m n)). Qed.
Lemma lem206035 (m : nat) (n : nat) (p : nat) : (term75 m n p) = (term76 m n p).
Proof. exact (@lem206034 (Nat.modulo m n) p). Qed.
Lemma lem206036 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem206037 (m : nat) (n : nat) (p : nat) : (term77 m n p) = (term78 m n p).
Proof. exact (MK_COMB (@lem206036) (@lem206035 m n p)). Qed.
Lemma lem206038 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem206039 (m : nat) (p : nat) (n : nat) : (term42 m p n) = (term79 m p n).
Proof. exact (MK_COMB (@lem206037 m n p) (@lem206038 n)). Qed.
Lemma lem206040 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem206041 (m : nat) (p : nat) (n : nat) : (term80 m p n) = (term81 m p n).
Proof. exact (MK_COMB (@lem206040) (@lem206039 m p n)). Qed.
Lemma lem206043 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (EQ_MP (@lem206012 m n) (@lem206011 m n)). Qed.
Lemma lem206044 (m : nat) (p : nat) : (term73 m p) = (term74 m p).
Proof. exact (@lem206043 m p). Qed.
Lemma lem206045 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem206046 (m : nat) (p : nat) : (term82 m p) = (term83 m p).
Proof. exact (MK_COMB (@lem206045) (@lem206044 m p)). Qed.
Lemma lem206047 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem206048 (m : nat) (p : nat) (n : nat) : (term43 m p n) = (term84 m p n).
Proof. exact (MK_COMB (@lem206046 m p) (@lem206047 n)). Qed.
Lemma lem206049 (m : nat) (p : nat) (n : nat) : ((term42 m p n) = (term43 m p n)) = ((term79 m p n) = (term84 m p n)).
Proof. exact (MK_COMB (@lem206041 m p n) (@lem206048 m p n)). Qed.
Lemma lem206052 (m : nat) (p : nat) (n : nat) : ((term79 m p n) = (term84 m p n)) = ((term42 m p n) = (term43 m p n)).
Proof. exact (SYM (@lem206049 m p n)). Qed.
Lemma lem206053 (m : nat) : term85 m.
Proof. exact (@lem205763 m). Qed.
Lemma lem206054 (m : nat) : (term85 m) = (term86 m).
Proof. exact (eq_refl (term85 m)). Qed.
Lemma lem206055 (m : nat) : term86 m.
Proof. exact (EQ_MP (@lem206054 m) (@lem206053 m)). Qed.
Lemma lem206056 (m : nat) (n : nat) : term87 m n.
Proof. exact (@lem206055 m n). Qed.
Lemma lem206057 (m : nat) (n : nat) : (term87 m n) = (term88 m n).
Proof. exact (eq_refl (term87 m n)). Qed.
Lemma lem206058 (m : nat) (n : nat) : term88 m n.
Proof. exact (EQ_MP (@lem206057 m n) (@lem206056 m n)). Qed.
Lemma lem206059 (m : nat) (n : nat) (p : nat) : term89 m n p.
Proof. exact (@lem206058 m n p). Qed.
Lemma lem206060 (m : nat) (p : nat) (n : nat) : (term89 m n p) = ((term90 m p n) = (term91 m p n)).
Proof. exact (eq_refl (term89 m n p)). Qed.
Lemma lem206078 (m : nat) (p : nat) (n : nat) : (term90 m p n) = (term91 m p n).
Proof. exact (EQ_MP (@lem206060 m p n) (@lem206059 m n p)). Qed.
Lemma lem206079 (m : nat) (p : nat) (n : nat) : (term79 m p n) = (term92 m p n).
Proof. exact (@lem206078 m (term22 m n p) n). Qed.
Lemma lem206080 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem206081 (m : nat) (p : nat) (n : nat) : (term81 m p n) = (term93 m p n).
Proof. exact (MK_COMB (@lem206080) (@lem206079 m p n)). Qed.
Lemma lem206082 (m : nat) (p : nat) (n : nat) : (term84 m p n) = (term84 m p n).
Proof. exact (eq_refl (term84 m p n)). Qed.
Lemma lem206083 (m : nat) (p : nat) (n : nat) : ((term79 m p n) = (term84 m p n)) = ((term92 m p n) = (term84 m p n)).
Proof. exact (MK_COMB (@lem206081 m p n) (@lem206082 m p n)). Qed.
Lemma lem206086 (m : nat) (p : nat) (n : nat) : ((term92 m p n) = (term84 m p n)) = ((term79 m p n) = (term84 m p n)).
Proof. exact (SYM (@lem206083 m p n)). Qed.
Lemma lem206088 {A : Type'} (x : A) (z : A) : term11 A x z.
Proof. exact (EQ_MP (@lem205863 A x z) (@lem205862 A x z)). Qed.
Lemma lem206089 (x : nat) (z : nat) : term94 x z.
Proof. exact (@lem206088 nat x z). Qed.
Lemma lem206090 (m : nat) (p : nat) (n : nat) : term95 m p n.
Proof. exact (@lem206089 (term92 m p n) (term84 m p n)). Qed.
Lemma lem206107 (m : nat) (p : nat) (n : nat) (h1 : (term25 m p n) = (term29 m p n)) : (term25 m p n) = (term29 m p n).
Proof. exact (h1). Qed.
Lemma lem206108 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem206109 (m : nat) (p : nat) (n : nat) (h1 : (term25 m p n) = (term29 m p n)) : (term96 m p n) = (term97 m p n).
Proof. exact (MK_COMB (@lem206108 m) (@lem206107 m p n h1)). Qed.
Lemma lem206110 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem206111 (m : nat) (p : nat) (n : nat) (h1 : (term25 m p n) = (term29 m p n)) : (term98 m p n) = (term99 m p n).
Proof. exact (MK_COMB (@lem206110) (@lem206109 m p n h1)). Qed.
Lemma lem206112 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem206113 (m : nat) (p : nat) (n : nat) (h1 : (term25 m p n) = (term29 m p n)) : (term100 m p n) = (term101 m p n).
Proof. exact (MK_COMB (@lem206111 m p n h1) (@lem206112 n)). Qed.
Lemma lem206114 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem206115 (m : nat) (p : nat) (n : nat) (h1 : (term25 m p n) = (term29 m p n)) : (term102 m p n) = (term103 m p n).
Proof. exact (MK_COMB (@lem206114) (@lem206113 m p n h1)). Qed.
Lemma lem206116 (m : nat) (p : nat) (n : nat) : (term84 m p n) = (term84 m p n).
Proof. exact (eq_refl (term84 m p n)). Qed.
Lemma lem206117 (m : nat) (p : nat) (n : nat) (h1 : (term25 m p n) = (term29 m p n)) : ((term100 m p n) = (term84 m p n)) = ((term101 m p n) = (term84 m p n)).
Proof. exact (MK_COMB (@lem206115 m p n h1) (@lem206116 m p n)). Qed.
Lemma lem206120 (m : nat) (p : nat) (n : nat) (h1 : (term25 m p n) = (term29 m p n)) : ((term101 m p n) = (term84 m p n)) = ((term100 m p n) = (term84 m p n)).
Proof. exact (SYM (@lem206117 m p n h1)). Qed.
Lemma lem206121 (m : nat) : term104 m.
Proof. exact (@lem205654 m). Qed.
Lemma lem206122 (m : nat) : (term104 m) = (term105 m).
Proof. exact (eq_refl (term104 m)). Qed.
Lemma lem206123 (m : nat) : term105 m.
Proof. exact (EQ_MP (@lem206122 m) (@lem206121 m)). Qed.
Lemma lem206124 (m : nat) (n : nat) : term106 m n.
Proof. exact (@lem206123 m n). Qed.
Lemma lem206125 (m : nat) (n : nat) : (term106 m n) = (term107 m n).
Proof. exact (eq_refl (term106 m n)). Qed.
Lemma lem206126 (m : nat) (n : nat) : term107 m n.
Proof. exact (EQ_MP (@lem206125 m n) (@lem206124 m n)). Qed.
Lemma lem206127 (m : nat) (n : nat) (p : nat) : term108 m n p.
Proof. exact (@lem206126 m n p). Qed.
Lemma lem206128 (m : nat) (p : nat) (n : nat) : (term108 m n p) = ((term109 m p n) = (term91 m p n)).
Proof. exact (eq_refl (term108 m n p)). Qed.
Lemma lem206146 (m : nat) (p : nat) (n : nat) : (term109 m p n) = (term91 m p n).
Proof. exact (EQ_MP (@lem206128 m p n) (@lem206127 m n p)). Qed.
Lemma lem206147 (m : nat) (p : nat) (n : nat) : (term100 m p n) = (term92 m p n).
Proof. exact (@lem206146 m (term22 m n p) n). Qed.
Lemma lem206148 (m : nat) (p : nat) (n : nat) : (term93 m p n) = (term93 m p n).
Proof. exact (eq_refl (term93 m p n)). Qed.
Lemma lem206149 (m : nat) (p : nat) (n : nat) : ((term92 m p n) = (term100 m p n)) = ((term92 m p n) = (term92 m p n)).
Proof. exact (MK_COMB (@lem206148 m p n) (@lem206147 m p n)). Qed.
Lemma lem206151 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem206152 (x : nat) : (x = x) = True.
Proof. exact (@lem206151 nat x). Qed.
Lemma lem206153 (m : nat) (p : nat) (n : nat) : ((term92 m p n) = (term92 m p n)) = True.
Proof. exact (@lem206152 (term92 m p n)). Qed.
Lemma lem206154 (m : nat) (p : nat) (n : nat) : ((term92 m p n) = (term100 m p n)) = True.
Proof. exact (TRANS (@lem206149 m p n) (@lem206153 m p n)). Qed.
Lemma lem206155 (m : nat) (p : nat) (n : nat) : True = ((term92 m p n) = (term100 m p n)).
Proof. exact (SYM (@lem206154 m p n)). Qed.
Lemma lem206156 (m : nat) (p : nat) (n : nat) : (term92 m p n) = (term100 m p n).
Proof. exact (EQ_MP (@lem206155 m p n) (@lem0)). Qed.
Lemma lem206157 (m : nat) : term104 m.
Proof. exact (@lem205654 m). Qed.
Lemma lem206158 (m : nat) : (term104 m) = (term105 m).
Proof. exact (eq_refl (term104 m)). Qed.
Lemma lem206159 (m : nat) : term105 m.
Proof. exact (EQ_MP (@lem206158 m) (@lem206157 m)). Qed.
Lemma lem206160 (m : nat) (n : nat) : term106 m n.
Proof. exact (@lem206159 m n). Qed.
Lemma lem206161 (m : nat) (n : nat) : (term106 m n) = (term107 m n).
Proof. exact (eq_refl (term106 m n)). Qed.
Lemma lem206162 (m : nat) (n : nat) : term107 m n.
Proof. exact (EQ_MP (@lem206161 m n) (@lem206160 m n)). Qed.
Lemma lem206163 (m : nat) (n : nat) (p : nat) : term108 m n p.
Proof. exact (@lem206162 m n p). Qed.
Lemma lem206164 (m : nat) (p : nat) (n : nat) : (term108 m n p) = ((term109 m p n) = (term91 m p n)).
Proof. exact (eq_refl (term108 m n p)). Qed.
Lemma lem206182 (m : nat) (p : nat) (n : nat) : (term109 m p n) = (term91 m p n).
Proof. exact (EQ_MP (@lem206164 m p n) (@lem206163 m n p)). Qed.
Lemma lem206183 (m : nat) (p : nat) (n : nat) : (term101 m p n) = (term84 m p n).
Proof. exact (@lem206182 m (Nat.pow m p) n). Qed.
Lemma lem206184 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem206185 (m : nat) (p : nat) (n : nat) : (term103 m p n) = (term110 m p n).
Proof. exact (MK_COMB (@lem206184) (@lem206183 m p n)). Qed.
Lemma lem206186 (m : nat) (p : nat) (n : nat) : (term84 m p n) = (term84 m p n).
Proof. exact (eq_refl (term84 m p n)). Qed.
Lemma lem206187 (m : nat) (p : nat) (n : nat) : ((term101 m p n) = (term84 m p n)) = ((term84 m p n) = (term84 m p n)).
Proof. exact (MK_COMB (@lem206185 m p n) (@lem206186 m p n)). Qed.
Lemma lem206189 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem206190 (x : nat) : (x = x) = True.
Proof. exact (@lem206189 nat x). Qed.
Lemma lem206191 (m : nat) (p : nat) (n : nat) : ((term84 m p n) = (term84 m p n)) = True.
Proof. exact (@lem206190 (term84 m p n)). Qed.
Lemma lem206192 (m : nat) (p : nat) (n : nat) : ((term101 m p n) = (term84 m p n)) = True.
Proof. exact (TRANS (@lem206187 m p n) (@lem206191 m p n)). Qed.
Lemma lem206193 (m : nat) (p : nat) (n : nat) : True = ((term101 m p n) = (term84 m p n)).
Proof. exact (SYM (@lem206192 m p n)). Qed.
Lemma lem206194 (m : nat) (p : nat) (n : nat) : (term101 m p n) = (term84 m p n).
Proof. exact (EQ_MP (@lem206193 m p n) (@lem0)). Qed.
Lemma lem206195 (m : nat) (p : nat) (n : nat) (h1 : (term25 m p n) = (term29 m p n)) : (term100 m p n) = (term84 m p n).
Proof. exact (EQ_MP (@lem206120 m p n h1) (@lem206194 m p n)). Qed.
Lemma lem206196 (m : nat) (p : nat) (n : nat) (h1 : (term25 m p n) = (term29 m p n)) : term111 m p n.
Proof. exact (conj (@lem206156 m p n) (@lem206195 m p n h1)). Qed.
Lemma lem206197 (m : nat) (p : nat) (n : nat) (h1 : (term25 m p n) = (term29 m p n)) : term112 m p n.
Proof. exact (ex_intro (term113 m p n) (term100 m p n) (@lem206196 m p n h1)). Qed.
Lemma lem206198 (m : nat) (p : nat) (n : nat) (h1 : (term25 m p n) = (term29 m p n)) : (term92 m p n) = (term84 m p n).
Proof. exact (@lem206090 m p n (@lem206197 m p n h1)). Qed.
Lemma lem206199 (m : nat) (p : nat) (n : nat) (h1 : (term25 m p n) = (term29 m p n)) : (term79 m p n) = (term84 m p n).
Proof. exact (EQ_MP (@lem206086 m p n) (@lem206198 m p n h1)). Qed.
Lemma lem206200 (m : nat) (p : nat) (n : nat) (h1 : (term25 m p n) = (term29 m p n)) : (term42 m p n) = (term43 m p n).
Proof. exact (EQ_MP (@lem206052 m p n) (@lem206199 m p n h1)). Qed.
Lemma lem206201 (m : nat) (p : nat) (n : nat) : term45 m p n.
Proof. exact (fun h0 : (term25 m p n) = (term29 m p n) => @lem206200 m p n h0). Qed.
Lemma lem206206 (m : nat) (n : nat) : term49 m n.
Proof. exact (fun p : nat => @lem206201 m p n). Qed.
Lemma lem206207 (m : nat) (n : nat) : term51 m n.
Proof. exact (conj (@lem206006 m n) (@lem206206 m n)). Qed.
Lemma lem206208 (m : nat) (n : nat) : term56 m n.
Proof. exact (@lem205956 m n (@lem206207 m n)). Qed.
Lemma lem206209 (m : nat) (n : nat) (p : nat) : term38 m n p.
Proof. exact (@lem206208 m n p). Qed.
Lemma lem206210 (m : nat) (p : nat) (n : nat) : (term38 m n p) = ((term25 m p n) = (term29 m p n)).
Proof. exact (eq_refl (term38 m n p)). Qed.
Lemma lem206212 (m : nat) (p : nat) (n : nat) : (term25 m p n) = (term29 m p n).
Proof. exact (EQ_MP (@lem206210 m p n) (@lem206209 m n p)). Qed.
Lemma lem206213 (m : nat) (p : nat) (n : nat) : (term25 m p n) = (term29 m p n).
Proof. exact (or_elim (@lem205867 n) (fun h0 : n = (NUMERAL 0) => @lem205913 m p n h0) (fun h0 : term114 n => @lem206212 m p n)). Qed.
Lemma lem206218 (m : nat) (n : nat) : term56 m n.
Proof. exact (fun p : nat => @lem206213 m p n). Qed.
Lemma lem206223 (m : nat) : term115 m.
Proof. exact (fun n : nat => @lem206218 m n). Qed.
Lemma lem206228 : term116.
Proof. exact (fun m : nat => @lem206223 m). Qed.
