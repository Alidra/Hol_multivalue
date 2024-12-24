Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_NZ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_ENTIRE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1340231_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1344313_spec.
Require Import thm1344314_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm1821_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm521920_spec.
Require Import thm522075_spec.
Require Import thm69_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem1596446 : term0.
Proof. exact (EQ_MP (@lem521920) (@lem522075)). Qed.
Lemma lem1596447 : term1.
Proof. exact (proj2 (@lem1596446)). Qed.
Lemma lem1596448 : term2.
Proof. exact (proj2 (@lem1596447)). Qed.
Lemma lem1596449 : term3.
Proof. exact (proj2 (@lem1596448)). Qed.
Lemma lem1596491 : term4.
Proof. exact (proj1 (@lem1596449)). Qed.
Lemma lem1596492 (n : nat) : term5 n.
Proof. exact (@lem1596491 n). Qed.
Lemma lem1596493 (n : nat) : (term5 n) = (((BIT1 n) = 0) = False).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem1596500 : term6.
Proof. exact (proj1 (@lem1596446)). Qed.
Lemma lem1596501 (m : nat) : term7 m.
Proof. exact (@lem1596500 m). Qed.
Lemma lem1596502 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem1596503 (m : nat) : term8 m.
Proof. exact (EQ_MP (@lem1596502 m) (@lem1596501 m)). Qed.
Lemma lem1596504 (m : nat) (n : nat) : term9 m n.
Proof. exact (@lem1596503 m n). Qed.
Lemma lem1596505 (m : nat) (n : nat) : (term9 m n) = (((NUMERAL m) = (NUMERAL n)) = (m = n)).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem1596757 (m : nat) : term10 m.
Proof. exact (@lem1340231 m). Qed.
Lemma lem1596758 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem1596759 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem1596758 m) (@lem1596757 m)). Qed.
Lemma lem1596760 (m : nat) (n : nat) : term12 m n.
Proof. exact (@lem1596759 m n). Qed.
Lemma lem1596761 (m : nat) (n : nat) : (term12 m n) = (((real_of_num m) = (real_of_num n)) = (m = n)).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem1596763 (x : real) : term13 x.
Proof. exact (EQ_MP (@lem1344314 x) (@lem1344313 x)). Qed.
Lemma lem1596764 (x : real) (n : nat) : term14 x n.
Proof. exact (@lem1596763 x n). Qed.
Lemma lem1596765 (x : real) (n : nat) : (term14 x n) = ((term15 x n) = (term16 x n)).
Proof. exact (eq_refl (term14 x n)). Qed.
Lemma lem1596769 (P : nat -> Prop) : term17 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1596770 (x : real) : term18 x.
Proof. exact (@lem1596769 (term19 x)). Qed.
Lemma lem1596771 (x : real) : (term20 x) = (term21 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem1596772 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1596773 (x : real) : (term22 x) = (term23 x).
Proof. exact (MK_COMB (@lem1596772) (@lem1596771 x)). Qed.
Lemma lem1596774 (x : real) (n : nat) : (term24 x n) = (term25 x n).
Proof. exact (eq_refl (term24 x n)). Qed.
Lemma lem1596775 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1596776 (x : real) (n : nat) : (term26 x n) = (term27 x n).
Proof. exact (MK_COMB (@lem1596775) (@lem1596774 x n)). Qed.
Lemma lem1596777 (x : real) (n : nat) : (term28 x n) = (term29 x n).
Proof. exact (eq_refl (term28 x n)). Qed.
Lemma lem1596778 (x : real) (n : nat) : (term30 x n) = (term31 x n).
Proof. exact (MK_COMB (@lem1596776 x n) (@lem1596777 x n)). Qed.
Lemma lem1596779 (x : real) : (term32 x) = (term33 x).
Proof. exact (fun_ext (fun n : nat => @lem1596778 x n)). Qed.
Lemma lem1596780 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1596781 (x : real) : (term34 x) = (term35 x).
Proof. exact (MK_COMB (@lem1596780) (@lem1596779 x)). Qed.
Lemma lem1596782 (x : real) : (term36 x) = (term37 x).
Proof. exact (MK_COMB (@lem1596773 x) (@lem1596781 x)). Qed.
Lemma lem1596783 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1596784 (x : real) : (term38 x) = (term39 x).
Proof. exact (MK_COMB (@lem1596783) (@lem1596782 x)). Qed.
Lemma lem1596785 (x : real) (n : nat) : (term24 x n) = (term25 x n).
Proof. exact (eq_refl (term24 x n)). Qed.
Lemma lem1596786 (x : real) : (term40 x) = (term19 x).
Proof. exact (fun_ext (fun n : nat => @lem1596785 x n)). Qed.
Lemma lem1596787 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1596788 (x : real) : (term41 x) = (term42 x).
Proof. exact (MK_COMB (@lem1596787) (@lem1596786 x)). Qed.
Lemma lem1596789 (x : real) : (term18 x) = (term43 x).
Proof. exact (MK_COMB (@lem1596784 x) (@lem1596788 x)). Qed.
Lemma lem1596790 (x : real) : term43 x.
Proof. exact (EQ_MP (@lem1596789 x) (@lem1596770 x)). Qed.
Lemma lem1596791 (x : real) (n : nat) (h1 : term25 x n) : term25 x n.
Proof. exact (h1). Qed.
Lemma lem1596799 (x : real) : (term44 x) = term45.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1596800 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1596801 (x : real) : (term46 x) = term47.
Proof. exact (MK_COMB (@lem1596800) (@lem1596799 x)). Qed.
Lemma lem1596802 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1596803 (x : real) : ((term44 x) = term48) = (term45 = term48).
Proof. exact (MK_COMB (@lem1596801 x) (@lem1596802)). Qed.
Lemma lem1596805 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem1596761 m n) (@lem1596760 m n)). Qed.
Lemma lem1596806 : (term45 = term48) = (term49 = (NUMERAL 0)).
Proof. exact (@lem1596805 term49 (NUMERAL 0)). Qed.
Lemma lem1596808 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem1596505 m n) (@lem1596504 m n)). Qed.
Lemma lem1596809 : (term49 = (NUMERAL 0)) = ((BIT1 0) = 0).
Proof. exact (@lem1596808 (BIT1 0) 0). Qed.
Lemma lem1596811 (n : nat) : ((BIT1 n) = 0) = False.
Proof. exact (EQ_MP (@lem1596493 n) (@lem1596492 n)). Qed.
Lemma lem1596812 : ((BIT1 0) = 0) = False.
Proof. exact (@lem1596811 0). Qed.
Lemma lem1596813 : (term49 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1596809) (@lem1596812)). Qed.
Lemma lem1596814 : (term45 = term48) = False.
Proof. exact (TRANS (@lem1596806) (@lem1596813)). Qed.
Lemma lem1596815 (x : real) : ((term44 x) = term48) = False.
Proof. exact (TRANS (@lem1596803 x) (@lem1596814)). Qed.
Lemma lem1596816 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1596817 (x : real) : (term50 x) = (~ False).
Proof. exact (MK_COMB (@lem1596816) (@lem1596815 x)). Qed.
Lemma lem1596819 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1596820 (x : real) : (term50 x) = True.
Proof. exact (TRANS (@lem1596817 x) (@lem1596819)). Qed.
Lemma lem1596821 (x : real) : (term51 x) = (term51 x).
Proof. exact (eq_refl (term51 x)). Qed.
Lemma lem1596822 (x : real) : (term21 x) = (term52 x).
Proof. exact (MK_COMB (@lem1596821 x) (@lem1596820 x)). Qed.
Lemma lem1596824 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1596825 (x : real) : (term52 x) = True.
Proof. exact (@lem1596824 (term53 x)). Qed.
Lemma lem1596826 (x : real) : (term21 x) = True.
Proof. exact (TRANS (@lem1596822 x) (@lem1596825 x)). Qed.
Lemma lem1596827 (x : real) : True = (term21 x).
Proof. exact (SYM (@lem1596826 x)). Qed.
Lemma lem1596828 (x : real) : term21 x.
Proof. exact (EQ_MP (@lem1596827 x) (@lem0)). Qed.
Lemma lem1596836 (x : real) (n : nat) : (term15 x n) = (term16 x n).
Proof. exact (EQ_MP (@lem1596765 x n) (@lem1596764 x n)). Qed.
Lemma lem1596837 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1596838 (x : real) (n : nat) : (term54 x n) = (term55 x n).
Proof. exact (MK_COMB (@lem1596837) (@lem1596836 x n)). Qed.
Lemma lem1596839 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1596840 (x : real) (n : nat) : ((term15 x n) = term48) = ((term16 x n) = term48).
Proof. exact (MK_COMB (@lem1596838 x n) (@lem1596839)). Qed.
Lemma lem1596843 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1596844 (x : real) (n : nat) : (term56 x n) = (term57 x n).
Proof. exact (MK_COMB (@lem1596843) (@lem1596840 x n)). Qed.
Lemma lem1596845 (x : real) : (term51 x) = (term51 x).
Proof. exact (eq_refl (term51 x)). Qed.
Lemma lem1596846 (x : real) (n : nat) : (term29 x n) = (term58 x n).
Proof. exact (MK_COMB (@lem1596845 x) (@lem1596844 x n)). Qed.
Lemma lem1596849 (x : real) (n : nat) : (term58 x n) = (term29 x n).
Proof. exact (SYM (@lem1596846 x n)). Qed.
Lemma lem1596851 (p : Prop) : p = (term59 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1596852 (x : real) (n : nat) : (term58 x n) = (term60 x n).
Proof. exact (@lem1596851 (term58 x n)). Qed.
Lemma lem1596853 (x : real) (n : nat) : (term60 x n) = (term58 x n).
Proof. exact (SYM (@lem1596852 x n)). Qed.
Lemma lem1596854 (x : real) (n : nat) (h1 : term61 x n) : term61 x n.
Proof. exact (h1). Qed.
Lemma lem1596857 (x : real) (n : nat) (h1 : term62 x n) : term62 x n.
Proof. exact (h1). Qed.
Lemma lem1596858 (x : real) (n : nat) : term63 x n.
Proof. exact (fun h0 : term62 x n => @lem1596857 x n h0). Qed.
Lemma lem1596859 (x : real) (n : nat) (h1 : term63 x n) : term63 x n.
Proof. exact (h1). Qed.
Lemma lem1596860 (x : real) (n : nat) (h1 : term62 x n) : term62 x n.
Proof. exact (h1). Qed.
Lemma lem1596861 (x : real) (n : nat) (h1 : term62 x n) (h2 : term63 x n) : term62 x n.
Proof. exact (@lem1596859 x n h2 (@lem1596860 x n h1)). Qed.
Lemma lem1596862 (x : real) (n : nat) (h1 : term62 x n) : term64 x n.
Proof. exact (fun h0 : term63 x n => @lem1596861 x n h1 h0). Qed.
Lemma lem1596863 (x : real) (n : nat) (h1 : term63 x n) : term63 x n.
Proof. exact (h1). Qed.
Lemma lem1596864 (x : real) (n : nat) (h1 : term62 x n) (h2 : term63 x n) : term62 x n.
Proof. exact (@lem1596862 x n h1 (@lem1596863 x n h2)). Qed.
Lemma lem1596865 (x : real) (n : nat) (h1 : term63 x n) : term63 x n.
Proof. exact (fun h0 : term62 x n => @lem1596864 x n h0 h1). Qed.
Lemma lem1596866 (x : real) (n : nat) : term65 x n.
Proof. exact (fun h0 : term63 x n => @lem1596865 x n h0). Qed.
Lemma lem1596869 (x : real) (n : nat) : term63 x n.
Proof. exact (@lem1596866 x n (@lem1596858 x n)). Qed.
Lemma lem1596887 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1596888 : term66 = term67.
Proof. exact (@lem1596887 term68). Qed.
Lemma lem1596899 (x : real) (n : nat) : (term69 x n) = (term69 x n).
Proof. exact (eq_refl (term69 x n)). Qed.
Lemma lem1596900 (x : real) (n : nat) : (term70 x n) = (term71 x n).
Proof. exact (MK_COMB (@lem1596899 x n) (@lem1596888)). Qed.
Lemma lem1596903 (x : real) (n : nat) : (term27 x n) = (term27 x n).
Proof. exact (eq_refl (term27 x n)). Qed.
Lemma lem1596904 (x : real) (n : nat) : (term62 x n) = (term72 x n).
Proof. exact (MK_COMB (@lem1596903 x n) (@lem1596900 x n)). Qed.
Lemma lem1596907 (n : nat) : (term73 n) = (term74 n).
Proof. exact (fun_ext (fun x : real => @lem1596904 x n)). Qed.
Lemma lem1596908 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1596909 (n : nat) : (term75 n) = (term76 n).
Proof. exact (MK_COMB (@lem1596908) (@lem1596907 n)). Qed.
Lemma lem1596914 : term77 = term78.
Proof. exact (fun_ext (fun n : nat => @lem1596909 n)). Qed.
Lemma lem1596915 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1596924 : term79 = term80.
Proof. exact (MK_COMB (@lem1596915) (@lem1596914)). Qed.
Lemma lem1596933 (x : real) (y : real) : (((real_mul x y) = term48) = (term81 x y)) = (((real_mul x y) = term48) = (term81 x y)).
Proof. exact (eq_refl (((real_mul x y) = term48) = (term81 x y))). Qed.
Lemma lem1596934 (x : real) : (term82 x) = (term82 x).
Proof. exact (fun_ext (fun y : real => @lem1596933 x y)). Qed.
Lemma lem1596935 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1596936 (x : real) : (term83 x) = (term83 x).
Proof. exact (MK_COMB (@lem1596935) (@lem1596934 x)). Qed.
Lemma lem1596937 : term84 = term84.
Proof. exact (fun_ext (fun x : real => @lem1596936 x)). Qed.
Lemma lem1596938 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1596939 : term68 = term68.
Proof. exact (MK_COMB (@lem1596938) (@lem1596937)). Qed.
Lemma lem1596940 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1596941 : term67 = term67.
Proof. exact (MK_COMB (@lem1596940) (@lem1596939)). Qed.
Lemma lem1596954 (x : real) (n : nat) : (term69 x n) = (term69 x n).
Proof. exact (eq_refl (term69 x n)). Qed.
Lemma lem1596955 (x : real) (n : nat) : (term71 x n) = (term71 x n).
Proof. exact (MK_COMB (@lem1596954 x n) (@lem1596941)). Qed.
Lemma lem1596966 (x : real) (n : nat) : (term27 x n) = (term27 x n).
Proof. exact (eq_refl (term27 x n)). Qed.
Lemma lem1596967 (x : real) (n : nat) : (term72 x n) = (term72 x n).
Proof. exact (MK_COMB (@lem1596966 x n) (@lem1596955 x n)). Qed.
Lemma lem1596968 (n : nat) : (term74 n) = (term74 n).
Proof. exact (fun_ext (fun x : real => @lem1596967 x n)). Qed.
Lemma lem1596969 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1596970 (n : nat) : (term76 n) = (term76 n).
Proof. exact (MK_COMB (@lem1596969) (@lem1596968 n)). Qed.
Lemma lem1596971 : term78 = term78.
Proof. exact (fun_ext (fun n : nat => @lem1596970 n)). Qed.
Lemma lem1596972 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1596973 : term80 = term80.
Proof. exact (MK_COMB (@lem1596972) (@lem1596971)). Qed.
Lemma lem1597010 : term79 = term80.
Proof. exact (TRANS (@lem1596924) (@lem1596973)). Qed.
Lemma lem1597011 : term80 = term79.
Proof. exact (SYM (@lem1597010)). Qed.
Lemma lem1597012 (x : real) (n : nat) (h1 : term25 x n) : term25 x n.
Proof. exact (h1). Qed.
Lemma lem1597013 (x : real) (n : nat) (h1 : term61 x n) : term61 x n.
Proof. exact (h1). Qed.
Lemma lem1597014 (h1 : term68) : term68.
Proof. exact (h1). Qed.
Lemma lem1597017 (x : real) : (term85 x) = (x = term48).
Proof. exact (@lem16933 (x = term48)). Qed.
Lemma lem1597018 (x : real) (n : nat) : (term86 x n) = (term86 x n).
Proof. exact (eq_refl (term86 x n)). Qed.
Lemma lem1597019 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1597020 (x : real) : (term87 x) = (term88 x).
Proof. exact (MK_COMB (@lem1597019) (@lem1597017 x)). Qed.
Lemma lem1597021 (x : real) (n : nat) : (term89 x n) = (term90 x n).
Proof. exact (MK_COMB (@lem1597020 x) (@lem1597018 x n)). Qed.
Lemma lem1597022 (x : real) (n : nat) : (term25 x n) = (term89 x n).
Proof. exact (@lem17265 (term53 x) (term86 x n)). Qed.
Lemma lem1597027 (x : real) (n : nat) : (term25 x n) = (term90 x n).
Proof. exact (TRANS (@lem1597022 x n) (@lem1597021 x n)). Qed.
Lemma lem1597032 (x : real) (n : nat) : (term91 x n) = ((term16 x n) = term48).
Proof. exact (@lem16933 ((term16 x n) = term48)). Qed.
Lemma lem1597034 (x : real) : (term92 x) = (term92 x).
Proof. exact (eq_refl (term92 x)). Qed.
Lemma lem1597035 (x : real) (n : nat) : (term93 x n) = (term94 x n).
Proof. exact (MK_COMB (@lem1597034 x) (@lem1597032 x n)). Qed.
Lemma lem1597036 (x : real) (n : nat) : (term61 x n) = (term93 x n).
Proof. exact (@lem17362 (term53 x) (term57 x n)). Qed.
Lemma lem1597041 (x : real) (n : nat) : (term61 x n) = (term94 x n).
Proof. exact (TRANS (@lem1597036 x n) (@lem1597035 x n)). Qed.
Lemma lem1597053 (x : real) (y : real) : (term95 x y) = (term96 x y).
Proof. exact (@lem17160 (x = term48) (y = term48)). Qed.
Lemma lem1597059 (x : real) (y : real) : (term97 x y) = (term97 x y).
Proof. exact (eq_refl (term97 x y)). Qed.
Lemma lem1597061 (x : real) (y : real) : (term98 x y) = (term98 x y).
Proof. exact (eq_refl (term98 x y)). Qed.
Lemma lem1597062 (x : real) (y : real) : (term99 x y) = (term100 x y).
Proof. exact (MK_COMB (@lem1597061 x y) (@lem1597053 x y)). Qed.
Lemma lem1597063 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1597064 (x : real) (y : real) : (term101 x y) = (term102 x y).
Proof. exact (MK_COMB (@lem1597063) (@lem1597062 x y)). Qed.
Lemma lem1597065 (x : real) (y : real) : (term103 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1597064 x y) (@lem1597059 x y)). Qed.
Lemma lem1597066 (x : real) (y : real) : (((real_mul x y) = term48) = (term81 x y)) = (term103 x y).
Proof. exact (@lem17784 ((real_mul x y) = term48) (term81 x y)). Qed.
Lemma lem1597067 (x : real) (y : real) : (((real_mul x y) = term48) = (term81 x y)) = (term104 x y).
Proof. exact (TRANS (@lem1597066 x y) (@lem1597065 x y)). Qed.
Lemma lem1597068 (x : real) : (term82 x) = (term105 x).
Proof. exact (fun_ext (fun y : real => @lem1597067 x y)). Qed.
Lemma lem1597069 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1597070 (x : real) : (term83 x) = (term106 x).
Proof. exact (MK_COMB (@lem1597069) (@lem1597068 x)). Qed.
Lemma lem1597071 : term84 = term107.
Proof. exact (fun_ext (fun x : real => @lem1597070 x)). Qed.
Lemma lem1597072 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1597073 : term68 = term108.
Proof. exact (MK_COMB (@lem1597072) (@lem1597071)). Qed.
Lemma lem1597079 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1597080 (P : real -> Prop) (Q : real -> Prop) : (term111 P Q) = (term112 P Q).
Proof. exact (@lem1597079 real P Q). Qed.
Lemma lem1597081 (x : real) : (term113 x) = (term114 x).
Proof. exact (@lem1597080 (term115 x) (term116 x)). Qed.
Lemma lem1597082 (x : real) (y : real) : (term117 x y) = (term100 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1597083 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1597084 (x : real) (y : real) : (term118 x y) = (term102 x y).
Proof. exact (MK_COMB (@lem1597083) (@lem1597082 x y)). Qed.
Lemma lem1597085 (x : real) (y : real) : (term119 x y) = (term97 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1597086 (x : real) (y : real) : (term120 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1597084 x y) (@lem1597085 x y)). Qed.
Lemma lem1597087 (x : real) : (term121 x) = (term105 x).
Proof. exact (fun_ext (fun y : real => @lem1597086 x y)). Qed.
Lemma lem1597088 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1597089 (x : real) : (term113 x) = (term106 x).
Proof. exact (MK_COMB (@lem1597088) (@lem1597087 x)). Qed.
Lemma lem1597090 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1597091 (x : real) : (term122 x) = (term123 x).
Proof. exact (MK_COMB (@lem1597090) (@lem1597089 x)). Qed.
Lemma lem1597092 (x : real) (y : real) : (term117 x y) = (term100 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1597093 (x : real) : (term124 x) = (term115 x).
Proof. exact (fun_ext (fun y : real => @lem1597092 x y)). Qed.
Lemma lem1597094 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1597095 (x : real) : (term125 x) = (term126 x).
Proof. exact (MK_COMB (@lem1597094) (@lem1597093 x)). Qed.
Lemma lem1597096 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1597097 (x : real) : (term127 x) = (term128 x).
Proof. exact (MK_COMB (@lem1597096) (@lem1597095 x)). Qed.
Lemma lem1597098 (x : real) (y : real) : (term119 x y) = (term97 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1597099 (x : real) : (term129 x) = (term116 x).
Proof. exact (fun_ext (fun y : real => @lem1597098 x y)). Qed.
Lemma lem1597100 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1597101 (x : real) : (term130 x) = (term131 x).
Proof. exact (MK_COMB (@lem1597100) (@lem1597099 x)). Qed.
Lemma lem1597102 (x : real) : (term114 x) = (term132 x).
Proof. exact (MK_COMB (@lem1597097 x) (@lem1597101 x)). Qed.
Lemma lem1597103 (x : real) : ((term113 x) = (term114 x)) = ((term106 x) = (term132 x)).
Proof. exact (MK_COMB (@lem1597091 x) (@lem1597102 x)). Qed.
Lemma lem1597104 (x : real) : (term106 x) = (term132 x).
Proof. exact (EQ_MP (@lem1597103 x) (@lem1597081 x)). Qed.
Lemma lem1597201 : term107 = term133.
Proof. exact (fun_ext (fun x : real => @lem1597104 x)). Qed.
Lemma lem1597202 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1597203 : term108 = term134.
Proof. exact (MK_COMB (@lem1597202) (@lem1597201)). Qed.
Lemma lem1597205 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1597206 (P : real -> Prop) (Q : real -> Prop) : (term111 P Q) = (term112 P Q).
Proof. exact (@lem1597205 real P Q). Qed.
Lemma lem1597207 : term135 = term136.
Proof. exact (@lem1597206 term137 term138). Qed.
Lemma lem1597208 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1597209 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1597210 (x : real) : (term140 x) = (term128 x).
Proof. exact (MK_COMB (@lem1597209) (@lem1597208 x)). Qed.
Lemma lem1597211 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1597212 (x : real) : (term142 x) = (term132 x).
Proof. exact (MK_COMB (@lem1597210 x) (@lem1597211 x)). Qed.
Lemma lem1597213 : term143 = term133.
Proof. exact (fun_ext (fun x : real => @lem1597212 x)). Qed.
Lemma lem1597214 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1597215 : term135 = term134.
Proof. exact (MK_COMB (@lem1597214) (@lem1597213)). Qed.
Lemma lem1597216 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1597217 : term144 = term145.
Proof. exact (MK_COMB (@lem1597216) (@lem1597215)). Qed.
Lemma lem1597218 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1597219 : term146 = term137.
Proof. exact (fun_ext (fun x : real => @lem1597218 x)). Qed.
Lemma lem1597220 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1597221 : term147 = term148.
Proof. exact (MK_COMB (@lem1597220) (@lem1597219)). Qed.
Lemma lem1597222 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1597223 : term149 = term150.
Proof. exact (MK_COMB (@lem1597222) (@lem1597221)). Qed.
Lemma lem1597224 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1597225 : term151 = term138.
Proof. exact (fun_ext (fun x : real => @lem1597224 x)). Qed.
Lemma lem1597226 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1597227 : term152 = term153.
Proof. exact (MK_COMB (@lem1597226) (@lem1597225)). Qed.
Lemma lem1597228 : term136 = term154.
Proof. exact (MK_COMB (@lem1597223) (@lem1597227)). Qed.
Lemma lem1597229 : (term135 = term136) = (term134 = term154).
Proof. exact (MK_COMB (@lem1597217) (@lem1597228)). Qed.
Lemma lem1597230 : term134 = term154.
Proof. exact (EQ_MP (@lem1597229) (@lem1597207)). Qed.
Lemma lem1597337 : term108 = term154.
Proof. exact (TRANS (@lem1597203) (@lem1597230)). Qed.
Lemma lem1597338 : term68 = term154.
Proof. exact (TRANS (@lem1597073) (@lem1597337)). Qed.
Lemma lem1597339 (h1 : term68) : term154.
Proof. exact (EQ_MP (@lem1597338) (@lem1597014 h1)). Qed.
Lemma lem1597367 (x : real) (n : nat) (h1 : term25 x n) : term90 x n.
Proof. exact (EQ_MP (@lem1597027 x n) (@lem1597012 x n h1)). Qed.
Lemma lem1597399 (x : real) (n : nat) (h1 : term61 x n) : term94 x n.
Proof. exact (EQ_MP (@lem1597041 x n) (@lem1597013 x n h1)). Qed.
Lemma lem1597438 (x : real) (y : real) : (term97 x y) = (term97 x y).
Proof. exact (eq_refl (term97 x y)). Qed.
Lemma lem1597439 (x : real) : (term116 x) = (term116 x).
Proof. exact (fun_ext (fun y : real => @lem1597438 x y)). Qed.
Lemma lem1597440 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1597441 (x : real) : (term131 x) = (term131 x).
Proof. exact (MK_COMB (@lem1597440) (@lem1597439 x)). Qed.
Lemma lem1597442 : term138 = term138.
Proof. exact (fun_ext (fun x : real => @lem1597441 x)). Qed.
Lemma lem1597443 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1597444 : term153 = term153.
Proof. exact (MK_COMB (@lem1597443) (@lem1597442)). Qed.
Lemma lem1597485 (x : real) (y : real) : (term100 x y) = (term100 x y).
Proof. exact (eq_refl (term100 x y)). Qed.
Lemma lem1597486 (x : real) : (term115 x) = (term115 x).
Proof. exact (fun_ext (fun y : real => @lem1597485 x y)). Qed.
Lemma lem1597487 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1597488 (x : real) : (term126 x) = (term126 x).
Proof. exact (MK_COMB (@lem1597487) (@lem1597486 x)). Qed.
Lemma lem1597489 : term137 = term137.
Proof. exact (fun_ext (fun x : real => @lem1597488 x)). Qed.
Lemma lem1597490 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1597491 : term148 = term148.
Proof. exact (MK_COMB (@lem1597490) (@lem1597489)). Qed.
Lemma lem1597492 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1597493 : term150 = term150.
Proof. exact (MK_COMB (@lem1597492) (@lem1597491)). Qed.
Lemma lem1597494 : term154 = term154.
Proof. exact (MK_COMB (@lem1597493) (@lem1597444)). Qed.
Lemma lem1597495 (h1 : term68) : term154.
Proof. exact (EQ_MP (@lem1597494) (@lem1597339 h1)). Qed.
Lemma lem1597496 (h1 : term68) : term153.
Proof. exact (proj2 (@lem1597495 h1)). Qed.
Lemma lem1597561 (x : real) (h1 : x = term48) : x = term48.
Proof. exact (h1). Qed.
Lemma lem1597601 (x : real) (y : real) : (term97 x y) = (term97 x y).
Proof. exact (eq_refl (term97 x y)). Qed.
Lemma lem1597602 (x : real) : (term116 x) = (term116 x).
Proof. exact (fun_ext (fun y : real => @lem1597601 x y)). Qed.
Lemma lem1597603 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1597604 (x : real) : (term131 x) = (term131 x).
Proof. exact (MK_COMB (@lem1597603) (@lem1597602 x)). Qed.
Lemma lem1597605 : term138 = term138.
Proof. exact (fun_ext (fun x : real => @lem1597604 x)). Qed.
Lemma lem1597606 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1597608 : term153 = term153.
Proof. exact (MK_COMB (@lem1597606) (@lem1597605)). Qed.
Lemma lem1597609 (h1 : term68) : term153.
Proof. exact (EQ_MP (@lem1597608) (@lem1597496 h1)). Qed.
Lemma lem1597621 (x : real) (n : nat) (h1 : term86 x n) : term86 x n.
Proof. exact (h1). Qed.
Lemma lem1597640 (_25195 : real) (h1 : term68) : term141 _25195.
Proof. exact (@lem1597609 h1 _25195). Qed.
Lemma lem1597641 (_25195 : real) : (term141 _25195) = (term131 _25195).
Proof. exact (eq_refl (term141 _25195)). Qed.
Lemma lem1597642 (_25195 : real) (h1 : term68) : term131 _25195.
Proof. exact (EQ_MP (@lem1597641 _25195) (@lem1597640 _25195 h1)). Qed.
Lemma lem1597643 (_25195 : real) (_25196 : real) (h1 : term68) : term119 _25195 _25196.
Proof. exact (@lem1597642 _25195 h1 _25196). Qed.
Lemma lem1597644 (_25195 : real) (_25196 : real) : (term119 _25195 _25196) = (term97 _25195 _25196).
Proof. exact (eq_refl (term119 _25195 _25196)). Qed.
Lemma lem1597661 (x : real) (n : nat) (h1 : term61 x n) : term53 x.
Proof. exact (proj1 (@lem1597399 x n h1)). Qed.
Lemma lem1597665 (x : real) (h1 : x = term48) : x = term48.
Proof. exact (h1). Qed.
Lemma lem1597687 (_25195 : real) (_25196 : real) (h1 : term68) : term97 _25195 _25196.
Proof. exact (EQ_MP (@lem1597644 _25195 _25196) (@lem1597643 _25195 _25196 h1)). Qed.
Lemma lem1597693 (x : real) (n : nat) (h1 : term86 x n) : term86 x n.
Proof. exact (h1). Qed.
Lemma lem1597734 : term155 = term155.
Proof. exact (eq_refl term155). Qed.
Lemma lem1597735 (x : real) (h1 : x = term48) : (term156 x) = term157.
Proof. exact (MK_COMB (@lem1597734) (@lem1597665 x h1)). Qed.
Lemma lem1597736 : term157 = term158.
Proof. exact (eq_refl term157). Qed.
Lemma lem1597737 (x : real) : (term159 x) = (term159 x).
Proof. exact (eq_refl (term159 x)). Qed.
Lemma lem1597738 (x : real) : ((term156 x) = term157) = ((term156 x) = term158).
Proof. exact (MK_COMB (@lem1597737 x) (@lem1597736)). Qed.
Lemma lem1597739 (x : real) : (term156 x) = (term53 x).
Proof. exact (eq_refl (term156 x)). Qed.
Lemma lem1597740 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1597741 (x : real) : (term159 x) = (term160 x).
Proof. exact (MK_COMB (@lem1597740) (@lem1597739 x)). Qed.
Lemma lem1597742 : term158 = term158.
Proof. exact (eq_refl term158). Qed.
Lemma lem1597743 (x : real) : ((term156 x) = term158) = ((term53 x) = term158).
Proof. exact (MK_COMB (@lem1597741 x) (@lem1597742)). Qed.
Lemma lem1597744 (x : real) : ((term156 x) = term157) = ((term53 x) = term158).
Proof. exact (TRANS (@lem1597738 x) (@lem1597743 x)). Qed.
Lemma lem1597745 (x : real) (h1 : x = term48) : (term53 x) = term158.
Proof. exact (EQ_MP (@lem1597744 x) (@lem1597735 x h1)). Qed.
Lemma lem1597746 (n : nat) (x : real) (h1 : term61 x n) (h2 : x = term48) : term158.
Proof. exact (EQ_MP (@lem1597745 x h2) (@lem1597661 x n h1)). Qed.
Lemma lem1597839 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1597840 : term48 = term48.
Proof. exact (@lem1597839 term48). Qed.
Lemma lem1597841 : term161.
Proof. exact (fun h0 : term158 => @lem1597840). Qed.
Lemma lem1597843 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1597844 : term161 = (term48 = term48).
Proof. exact (@lem1597843 (term48 = term48)). Qed.
Lemma lem1597845 : term48 = term48.
Proof. exact (EQ_MP (@lem1597844) (@lem1597841)). Qed.
Lemma lem1597848 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1597850 : term158 = term163.
Proof. exact (@lem1597848 (term48 = term48)). Qed.
Lemma lem1597853 (n : nat) (x : real) (h1 : term61 x n) (h2 : x = term48) : term163.
Proof. exact (EQ_MP (@lem1597850) (@lem1597746 n x h1 h2)). Qed.
Lemma lem1597856 (n : nat) (x : real) (h1 : term61 x n) (h2 : x = term48) : False.
Proof. exact (@lem1597853 n x h1 h2 (@lem1597845)). Qed.
Lemma lem1597857 (n : nat) (x : real) (h1 : term61 x n) (h2 : x = term48) : term164.
Proof. exact (fun h0 : ~ False => @lem1597856 n x h1 h2). Qed.
Lemma lem1597859 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1597860 : term164 = False.
Proof. exact (@lem1597859 False). Qed.
Lemma lem1597913 (x : real) (n : nat) (h1 : term61 x n) : (term16 x n) = term48.
Proof. exact (proj2 (@lem1597399 x n h1)). Qed.
Lemma lem1597914 (x : real) (n : nat) (h1 : term61 x n) : term165 x n.
Proof. exact (fun h0 : term57 x n => @lem1597913 x n h1). Qed.
Lemma lem1597916 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1597917 (x : real) (n : nat) : (term165 x n) = ((term16 x n) = term48).
Proof. exact (@lem1597916 ((term16 x n) = term48)). Qed.
Lemma lem1597918 (x : real) (n : nat) (h1 : term61 x n) : (term16 x n) = term48.
Proof. exact (EQ_MP (@lem1597917 x n) (@lem1597914 x n h1)). Qed.
Lemma lem1597920 (x : real) (n : nat) (h1 : term61 x n) : term53 x.
Proof. exact (proj1 (@lem1597399 x n h1)). Qed.
Lemma lem1597921 (x : real) (n : nat) (h1 : term61 x n) : term166 x.
Proof. exact (fun h0 : x = term48 => @lem1597920 x n h1). Qed.
Lemma lem1597923 (p : Prop) : (term167 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1597924 (x : real) : (term166 x) = (term53 x).
Proof. exact (@lem1597923 (x = term48)). Qed.
Lemma lem1597925 (x : real) (n : nat) (h1 : term61 x n) : term53 x.
Proof. exact (EQ_MP (@lem1597924 x) (@lem1597921 x n h1)). Qed.
Lemma lem1597931 (q : Prop) (p : Prop) (r : Prop) : (term168 p q r) = (term168 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1597932 (_25195 : real) (_25196 : real) : (term97 _25195 _25196) = (term169 _25195 _25196).
Proof. exact (@lem1597931 (_25195 = term48) (term170 _25195 _25196) (_25196 = term48)). Qed.
Lemma lem1597948 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1597949 (_25195 : real) (_25196 : real) : (term171 _25195 _25196) = (term172 _25195 _25196).
Proof. exact (@lem1597948 (_25196 = term48) (term170 _25195 _25196)). Qed.
Lemma lem1597959 (_25195 : real) : (term88 _25195) = (term88 _25195).
Proof. exact (eq_refl (term88 _25195)). Qed.
Lemma lem1597960 (_25195 : real) (_25196 : real) : (term169 _25195 _25196) = (term173 _25195 _25196).
Proof. exact (MK_COMB (@lem1597959 _25195) (@lem1597949 _25195 _25196)). Qed.
Lemma lem1597971 (_25195 : real) (_25196 : real) : (term97 _25195 _25196) = (term173 _25195 _25196).
Proof. exact (TRANS (@lem1597932 _25195 _25196) (@lem1597960 _25195 _25196)). Qed.
Lemma lem1597972 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1597973 (_25195 : real) (_25196 : real) : (term174 _25195 _25196) = (term175 _25195 _25196).
Proof. exact (MK_COMB (@lem1597972) (@lem1597971 _25195 _25196)). Qed.
Lemma lem1597989 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1597990 (_25195 : real) (_25196 : real) : (term176 _25196 _25195) = (term177 _25195 _25196).
Proof. exact (@lem1597989 (_25195 = term48) (term170 _25195 _25196)). Qed.
Lemma lem1598000 (_25196 : real) : (term88 _25196) = (term88 _25196).
Proof. exact (eq_refl (term88 _25196)). Qed.
Lemma lem1598001 (_25195 : real) (_25196 : real) : (term178 _25196 _25195) = (term179 _25195 _25196).
Proof. exact (MK_COMB (@lem1598000 _25196) (@lem1597990 _25195 _25196)). Qed.
Lemma lem1598005 (q : Prop) (p : Prop) (r : Prop) : (term168 p q r) = (term168 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1598006 (_25195 : real) (_25196 : real) : (term179 _25195 _25196) = (term173 _25195 _25196).
Proof. exact (@lem1598005 (_25195 = term48) (_25196 = term48) (term170 _25195 _25196)). Qed.
Lemma lem1598028 (_25195 : real) (_25196 : real) : (term178 _25196 _25195) = (term173 _25195 _25196).
Proof. exact (TRANS (@lem1598001 _25195 _25196) (@lem1598006 _25195 _25196)). Qed.
Lemma lem1598029 (_25195 : real) (_25196 : real) : ((term97 _25195 _25196) = (term178 _25196 _25195)) = ((term173 _25195 _25196) = (term173 _25195 _25196)).
Proof. exact (MK_COMB (@lem1597973 _25195 _25196) (@lem1598028 _25195 _25196)). Qed.
Lemma lem1598031 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1598032 (x : Prop) : (x = x) = True.
Proof. exact (@lem1598031 Prop x). Qed.
Lemma lem1598033 (_25195 : real) (_25196 : real) : ((term173 _25195 _25196) = (term173 _25195 _25196)) = True.
Proof. exact (@lem1598032 (term173 _25195 _25196)). Qed.
Lemma lem1598034 (_25196 : real) (_25195 : real) : ((term97 _25195 _25196) = (term178 _25196 _25195)) = True.
Proof. exact (TRANS (@lem1598029 _25195 _25196) (@lem1598033 _25195 _25196)). Qed.
Lemma lem1598035 (_25196 : real) (_25195 : real) : True = ((term97 _25195 _25196) = (term178 _25196 _25195)).
Proof. exact (SYM (@lem1598034 _25196 _25195)). Qed.
Lemma lem1598036 (_25196 : real) (_25195 : real) : (term97 _25195 _25196) = (term178 _25196 _25195).
Proof. exact (EQ_MP (@lem1598035 _25196 _25195) (@lem0)). Qed.
Lemma lem1598037 (_25196 : real) (_25195 : real) (h1 : term68) : term178 _25196 _25195.
Proof. exact (EQ_MP (@lem1598036 _25196 _25195) (@lem1597687 _25195 _25196 h1)). Qed.
Lemma lem1598039 (b : Prop) (a : Prop) : (a \/ b) = (term180 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1598040 (_25195 : real) (_25196 : real) : (term178 _25196 _25195) = (term181 _25195 _25196).
Proof. exact (@lem1598039 (term176 _25196 _25195) (_25196 = term48)). Qed.
Lemma lem1598042 (a : Prop) (b : Prop) : (term182 a b) = (term183 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1598043 (_25196 : real) (_25195 : real) : (term184 _25196 _25195) = (term185 _25196 _25195).
Proof. exact (@lem1598042 (term170 _25195 _25196) (_25195 = term48)). Qed.
Lemma lem1598045 (a : Prop) : (term186 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1598046 (_25195 : real) (_25196 : real) : (term187 _25195 _25196) = ((real_mul _25195 _25196) = term48).
Proof. exact (@lem1598045 ((real_mul _25195 _25196) = term48)). Qed.
Lemma lem1598047 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1598048 (_25195 : real) (_25196 : real) : (term188 _25195 _25196) = (term189 _25195 _25196).
Proof. exact (MK_COMB (@lem1598047) (@lem1598046 _25195 _25196)). Qed.
Lemma lem1598049 (_25195 : real) : (term53 _25195) = (term53 _25195).
Proof. exact (eq_refl (term53 _25195)). Qed.
Lemma lem1598050 (_25196 : real) (_25195 : real) : (term185 _25196 _25195) = (term190 _25196 _25195).
Proof. exact (MK_COMB (@lem1598048 _25195 _25196) (@lem1598049 _25195)). Qed.
Lemma lem1598051 (_25196 : real) (_25195 : real) : (term184 _25196 _25195) = (term190 _25196 _25195).
Proof. exact (TRANS (@lem1598043 _25196 _25195) (@lem1598050 _25196 _25195)). Qed.
Lemma lem1598052 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1598053 (_25196 : real) (_25195 : real) : (term191 _25196 _25195) = (term192 _25196 _25195).
Proof. exact (MK_COMB (@lem1598052) (@lem1598051 _25196 _25195)). Qed.
Lemma lem1598054 (_25196 : real) : (_25196 = term48) = (_25196 = term48).
Proof. exact (eq_refl (_25196 = term48)). Qed.
Lemma lem1598055 (_25195 : real) (_25196 : real) : (term181 _25195 _25196) = (term193 _25195 _25196).
Proof. exact (MK_COMB (@lem1598053 _25196 _25195) (@lem1598054 _25196)). Qed.
Lemma lem1598056 (_25195 : real) (_25196 : real) : (term178 _25196 _25195) = (term193 _25195 _25196).
Proof. exact (TRANS (@lem1598040 _25195 _25196) (@lem1598055 _25195 _25196)). Qed.
Lemma lem1598058 (x : real) (n : nat) (h1 : term61 x n) : term194 n x.
Proof. exact (conj (@lem1597918 x n h1) (@lem1597925 x n h1)). Qed.
Lemma lem1598060 (_25195 : real) (_25196 : real) (h1 : term68) : term193 _25195 _25196.
Proof. exact (EQ_MP (@lem1598056 _25195 _25196) (@lem1598037 _25196 _25195 h1)). Qed.
Lemma lem1598061 (x : real) (n : nat) (h1 : term68) : term195 x n.
Proof. exact (@lem1598060 x (real_pow x n) h1). Qed.
Lemma lem1598064 (x : real) (n : nat) (h1 : term68) (h2 : term61 x n) : (real_pow x n) = term48.
Proof. exact (@lem1598061 x n h1 (@lem1598058 x n h2)). Qed.
Lemma lem1598065 (x : real) (n : nat) (h1 : term68) (h2 : term61 x n) : term196 x n.
Proof. exact (fun h0 : term86 x n => @lem1598064 x n h1 h2). Qed.
Lemma lem1598067 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1598068 (x : real) (n : nat) : (term196 x n) = ((real_pow x n) = term48).
Proof. exact (@lem1598067 ((real_pow x n) = term48)). Qed.
Lemma lem1598069 (x : real) (n : nat) (h1 : term68) (h2 : term61 x n) : (real_pow x n) = term48.
Proof. exact (EQ_MP (@lem1598068 x n) (@lem1598065 x n h1 h2)). Qed.
Lemma lem1598072 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1598074 (x : real) (n : nat) : (term86 x n) = (term197 x n).
Proof. exact (@lem1598072 ((real_pow x n) = term48)). Qed.
Lemma lem1598077 (x : real) (n : nat) (h1 : term86 x n) : term197 x n.
Proof. exact (EQ_MP (@lem1598074 x n) (@lem1597693 x n h1)). Qed.
Lemma lem1598080 (x : real) (n : nat) (h1 : term68) (h2 : term86 x n) (h3 : term61 x n) : False.
Proof. exact (@lem1598077 x n h2 (@lem1598069 x n h1 h3)). Qed.
Lemma lem1598081 (x : real) (n : nat) (h1 : term68) (h2 : term86 x n) (h3 : term61 x n) : term164.
Proof. exact (fun h0 : ~ False => @lem1598080 x n h1 h2 h3). Qed.
Lemma lem1598083 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1598084 : term164 = False.
Proof. exact (@lem1598083 False). Qed.
Lemma lem1598085 (x : real) (n : nat) (h1 : term68) (h2 : term86 x n) (h3 : term61 x n) : False.
Proof. exact (EQ_MP (@lem1598084) (@lem1598081 x n h1 h2 h3)). Qed.
Lemma lem1598086 (n : nat) (x : real) (h1 : term61 x n) (h2 : x = term48) : False.
Proof. exact (EQ_MP (@lem1597860) (@lem1597857 n x h1 h2)). Qed.
Lemma lem1598087 (x : real) (n : nat) (h1 : term68) (h2 : term86 x n) (h3 : term61 x n) : (term86 x n) = False.
Proof. exact (prop_ext (fun h4 : term86 x n => @lem1598085 x n h1 h2 h3) (fun h4 : False => @lem1597693 x n h2)). Qed.
Lemma lem1598088 (x : real) (n : nat) (h1 : term68) (h2 : term86 x n) (h3 : term61 x n) : False.
Proof. exact (EQ_MP (@lem1598087 x n h1 h2 h3) (@lem1597693 x n h2)). Qed.
Lemma lem1598089 (n : nat) (x : real) (h1 : term61 x n) (h2 : x = term48) : (x = term48) = False.
Proof. exact (prop_ext (fun h3 : x = term48 => @lem1598086 n x h1 h2) (fun h3 : False => @lem1597665 x h2)). Qed.
Lemma lem1598090 (n : nat) (x : real) (h1 : term61 x n) (h2 : x = term48) : False.
Proof. exact (EQ_MP (@lem1598089 n x h1 h2) (@lem1597665 x h2)). Qed.
Lemma lem1598091 (x : real) (n : nat) (h1 : term68) (h2 : term86 x n) (h3 : term61 x n) : (term86 x n) = False.
Proof. exact (prop_ext (fun h4 : term86 x n => @lem1598088 x n h1 h2 h3) (fun h4 : False => @lem1597621 x n h2)). Qed.
Lemma lem1598092 (x : real) (n : nat) (h1 : term68) (h2 : term86 x n) (h3 : term61 x n) : False.
Proof. exact (EQ_MP (@lem1598091 x n h1 h2 h3) (@lem1597621 x n h2)). Qed.
Lemma lem1598093 (n : nat) (x : real) (h1 : term61 x n) (h2 : x = term48) : (x = term48) = False.
Proof. exact (prop_ext (fun h3 : x = term48 => @lem1598090 n x h1 h2) (fun h3 : False => @lem1597561 x h2)). Qed.
Lemma lem1598094 (n : nat) (x : real) (h1 : term61 x n) (h2 : x = term48) : False.
Proof. exact (EQ_MP (@lem1598093 n x h1 h2) (@lem1597561 x h2)). Qed.
Lemma lem1598095 (x : real) (n : nat) (h1 : term68) (h2 : term86 x n) (h3 : term61 x n) : (term86 x n) = False.
Proof. exact (prop_ext (fun h4 : term86 x n => @lem1598092 x n h1 h2 h3) (fun h4 : False => @lem1597621 x n h2)). Qed.
Lemma lem1598096 (x : real) (n : nat) (h1 : term68) (h2 : term86 x n) (h3 : term61 x n) : False.
Proof. exact (EQ_MP (@lem1598095 x n h1 h2 h3) (@lem1597621 x n h2)). Qed.
Lemma lem1598097 (n : nat) (x : real) (h1 : term61 x n) (h2 : x = term48) : (x = term48) = False.
Proof. exact (prop_ext (fun h3 : x = term48 => @lem1598094 n x h1 h2) (fun h3 : False => @lem1597561 x h2)). Qed.
Lemma lem1598098 (n : nat) (x : real) (h1 : term61 x n) (h2 : x = term48) : False.
Proof. exact (EQ_MP (@lem1598097 n x h1 h2) (@lem1597561 x h2)). Qed.
Lemma lem1598099 (x : real) (n : nat) (h1 : term68) (h2 : term61 x n) (h3 : term25 x n) : False.
Proof. exact (or_elim (@lem1597367 x n h3) (fun h0 : x = term48 => @lem1598098 n x h2 h0) (fun h0 : term86 x n => @lem1598096 x n h1 h0 h2)). Qed.
Lemma lem1598100 (x : real) (n : nat) (h1 : term61 x n) (h2 : term25 x n) : term66.
Proof. exact (fun h0 : term68 => @lem1598099 x n h0 h1 h2). Qed.
Lemma lem1598101 : term66 = term67.
Proof. exact (@lem69 term68). Qed.
Lemma lem1598102 (x : real) (n : nat) (h1 : term61 x n) (h2 : term25 x n) : term67.
Proof. exact (EQ_MP (@lem1598101) (@lem1598100 x n h1 h2)). Qed.
Lemma lem1598103 (x : real) (n : nat) (h1 : term25 x n) : term71 x n.
Proof. exact (fun h0 : term61 x n => @lem1598102 x n h0 h1). Qed.
Lemma lem1598104 (x : real) (n : nat) : term72 x n.
Proof. exact (fun h0 : term25 x n => @lem1598103 x n h0). Qed.
Lemma lem1598109 (n : nat) : term76 n.
Proof. exact (fun x : real => @lem1598104 x n). Qed.
Lemma lem1598114 : term80.
Proof. exact (fun n : nat => @lem1598109 n). Qed.
Lemma lem1598115 : term79.
Proof. exact (EQ_MP (@lem1597011) (@lem1598114)). Qed.
Lemma lem1598116 (n : nat) : term198 n.
Proof. exact (@lem1598115 n). Qed.
Lemma lem1598117 (n : nat) : (term198 n) = (term75 n).
Proof. exact (eq_refl (term198 n)). Qed.
Lemma lem1598118 (n : nat) : term75 n.
Proof. exact (EQ_MP (@lem1598117 n) (@lem1598116 n)). Qed.
Lemma lem1598119 (n : nat) (x : real) : term199 n x.
Proof. exact (@lem1598118 n x). Qed.
Lemma lem1598120 (x : real) (n : nat) : (term199 n x) = (term62 x n).
Proof. exact (eq_refl (term199 n x)). Qed.
Lemma lem1598121 (x : real) (n : nat) : term62 x n.
Proof. exact (EQ_MP (@lem1598120 x n) (@lem1598119 n x)). Qed.
Lemma lem1598123 (x : real) (n : nat) : term62 x n.
Proof. exact (@lem1596869 x n (@lem1598121 x n)). Qed.
Lemma lem1598124 (x : real) (n : nat) (h1 : term25 x n) : term70 x n.
Proof. exact (@lem1598123 x n (@lem1596791 x n h1)). Qed.
Lemma lem1598125 (x : real) (n : nat) (h1 : term61 x n) (h2 : term25 x n) : term66.
Proof. exact (@lem1598124 x n h2 (@lem1596854 x n h1)). Qed.
Lemma lem1598126 (x : real) (n : nat) (h1 : term61 x n) (h2 : term25 x n) : False.
Proof. exact (@lem1598125 x n h1 h2 (@lem1382769)). Qed.
Lemma lem1598127 (x : real) (n : nat) (h1 : term61 x n) (h2 : term25 x n) : (term61 x n) = False.
Proof. exact (prop_ext (fun h3 : term61 x n => @lem1598126 x n h1 h2) (fun h3 : False => @lem1596854 x n h1)). Qed.
Lemma lem1598128 (x : real) (n : nat) (h1 : term61 x n) (h2 : term25 x n) : False.
Proof. exact (EQ_MP (@lem1598127 x n h1 h2) (@lem1596854 x n h1)). Qed.
Lemma lem1598129 (x : real) (n : nat) (h1 : term25 x n) : term60 x n.
Proof. exact (fun h0 : term61 x n => @lem1598128 x n h0 h1). Qed.
Lemma lem1598130 (x : real) (n : nat) (h1 : term25 x n) : term58 x n.
Proof. exact (EQ_MP (@lem1596853 x n) (@lem1598129 x n h1)). Qed.
Lemma lem1598131 (x : real) (n : nat) (h1 : term25 x n) : term29 x n.
Proof. exact (EQ_MP (@lem1596849 x n) (@lem1598130 x n h1)). Qed.
Lemma lem1598132 (x : real) (n : nat) : term31 x n.
Proof. exact (fun h0 : term25 x n => @lem1598131 x n h0). Qed.
Lemma lem1598137 (x : real) : term35 x.
Proof. exact (fun n : nat => @lem1598132 x n). Qed.
Lemma lem1598138 (x : real) : term37 x.
Proof. exact (conj (@lem1596828 x) (@lem1598137 x)). Qed.
Lemma lem1598139 (x : real) : term42 x.
Proof. exact (@lem1596790 x (@lem1598138 x)). Qed.
Lemma lem1598144 : term200.
Proof. exact (fun x : real => @lem1598139 x). Qed.
