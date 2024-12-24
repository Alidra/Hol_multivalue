Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_2_DIVIDES_POW_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import INT_2_DIVIDES_MUL_spec.
Require Import INT_POW_spec.
Require Import INT_REM_2_DIVIDES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_SUC_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1009824_spec.
Require Import thm1011471_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm2403914_spec.
Require Import thm2404231_spec.
Require Import thm2405621_spec.
Require Import thm2406280_spec.
Require Import thm2406442_spec.
Require Import thm2743639_spec.
Require Import thm706821_spec.
Require Import thm706883_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Require Import thm912741_spec.
Lemma lem2745784 : term0.
Proof. exact (proj2 (@lem2725348)). Qed.
Lemma lem2745786 (n : int) (h1 : ((term1 n) = term2) = (term3 n)) : ((term1 n) = term2) = (term3 n).
Proof. exact (h1). Qed.
Lemma lem2745787 (n : int) (h1 : ((term1 n) = term2) = (term3 n)) : (term3 n) = ((term1 n) = term2).
Proof. exact (SYM (@lem2745786 n h1)). Qed.
Lemma lem2745788 (n : int) (h1 : (term3 n) = ((term1 n) = term2)) : (term3 n) = ((term1 n) = term2).
Proof. exact (h1). Qed.
Lemma lem2745789 (n : int) (h1 : (term3 n) = ((term1 n) = term2)) : ((term1 n) = term2) = (term3 n).
Proof. exact (SYM (@lem2745788 n h1)). Qed.
Lemma lem2745790 (n : int) : (((term1 n) = term2) = (term3 n)) = ((term3 n) = ((term1 n) = term2)).
Proof. exact (prop_ext (fun h1 : ((term1 n) = term2) = (term3 n) => @lem2745787 n h1) (fun h1 : (term3 n) = ((term1 n) = term2) => @lem2745789 n h1)). Qed.
Lemma lem2745791 : term4 = term5.
Proof. exact (fun_ext (fun n : int => @lem2745790 n)). Qed.
Lemma lem2745792 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2745793 : term0 = term6.
Proof. exact (MK_COMB (@lem2745792) (@lem2745791)). Qed.
Lemma lem2745794 : term6.
Proof. exact (EQ_MP (@lem2745793) (@lem2745784)). Qed.
Lemma lem2745795 (n : int) : term7 n.
Proof. exact (@lem2745794 n). Qed.
Lemma lem2745796 (n : int) : (term7 n) = ((term3 n) = ((term1 n) = term2)).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem2745798 (x : int) : term8 x.
Proof. exact (proj2 (@lem2318057 x)). Qed.
Lemma lem2745799 (x : int) (n : nat) : term9 x n.
Proof. exact (@lem2745798 x n). Qed.
Lemma lem2745800 (x : int) (n : nat) : (term9 x n) = ((term10 x n) = (term11 x n)).
Proof. exact (eq_refl (term9 x n)). Qed.
Lemma lem2745804 (P : nat -> Prop) : term12 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem2745805 (n : int) : term13 n.
Proof. exact (@lem2745804 (term14 n)). Qed.
Lemma lem2745806 (n : int) : (term15 n) = ((term16 n) = (term17 n)).
Proof. exact (eq_refl (term15 n)). Qed.
Lemma lem2745807 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2745808 (n : int) : (term18 n) = (term19 n).
Proof. exact (MK_COMB (@lem2745807) (@lem2745806 n)). Qed.
Lemma lem2745809 (n : int) (k : nat) : (term20 n k) = ((term21 n k) = (term22 n k)).
Proof. exact (eq_refl (term20 n k)). Qed.
Lemma lem2745810 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2745811 (n : int) (k : nat) : (term23 n k) = (term24 n k).
Proof. exact (MK_COMB (@lem2745810) (@lem2745809 n k)). Qed.
Lemma lem2745812 (n : int) (k : nat) : (term25 n k) = ((term26 n k) = (term27 n k)).
Proof. exact (eq_refl (term25 n k)). Qed.
Lemma lem2745813 (n : int) (k : nat) : (term28 n k) = (term29 n k).
Proof. exact (MK_COMB (@lem2745811 n k) (@lem2745812 n k)). Qed.
Lemma lem2745814 (n : int) : (term30 n) = (term31 n).
Proof. exact (fun_ext (fun k : nat => @lem2745813 n k)). Qed.
Lemma lem2745815 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2745816 (n : int) : (term32 n) = (term33 n).
Proof. exact (MK_COMB (@lem2745815) (@lem2745814 n)). Qed.
Lemma lem2745817 (n : int) : (term34 n) = (term35 n).
Proof. exact (MK_COMB (@lem2745808 n) (@lem2745816 n)). Qed.
Lemma lem2745818 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2745819 (n : int) : (term36 n) = (term37 n).
Proof. exact (MK_COMB (@lem2745818) (@lem2745817 n)). Qed.
Lemma lem2745820 (n : int) (k : nat) : (term20 n k) = ((term21 n k) = (term22 n k)).
Proof. exact (eq_refl (term20 n k)). Qed.
Lemma lem2745821 (n : int) : (term38 n) = (term14 n).
Proof. exact (fun_ext (fun k : nat => @lem2745820 n k)). Qed.
Lemma lem2745822 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2745823 (n : int) : (term39 n) = (term40 n).
Proof. exact (MK_COMB (@lem2745822) (@lem2745821 n)). Qed.
Lemma lem2745824 (n : int) : (term13 n) = (term41 n).
Proof. exact (MK_COMB (@lem2745819 n) (@lem2745823 n)). Qed.
Lemma lem2745825 (n : int) : term41 n.
Proof. exact (EQ_MP (@lem2745824 n) (@lem2745805 n)). Qed.
Lemma lem2745830 (x : int) : (term42 x) = term2.
Proof. exact (proj1 (@lem2318057 x)). Qed.
Lemma lem2745831 (n : int) : (term42 n) = term2.
Proof. exact (@lem2745830 n). Qed.
Lemma lem2745832 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2745833 (n : int) : (term16 n) = term44.
Proof. exact (MK_COMB (@lem2745832) (@lem2745831 n)). Qed.
Lemma lem2745834 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2745835 (n : int) : (term45 n) = term46.
Proof. exact (MK_COMB (@lem2745834) (@lem2745833 n)). Qed.
Lemma lem2745839 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2745840 (x : nat) : (x = x) = True.
Proof. exact (@lem2745839 nat x). Qed.
Lemma lem2745841 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem2745840 (NUMERAL 0)). Qed.
Lemma lem2745842 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2745843 : term47 = (~ True).
Proof. exact (MK_COMB (@lem2745842) (@lem2745841)). Qed.
Lemma lem2745845 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem2745846 : term47 = False.
Proof. exact (TRANS (@lem2745843) (@lem2745845)). Qed.
Lemma lem2745847 (n : int) : (term48 n) = (term48 n).
Proof. exact (eq_refl (term48 n)). Qed.
Lemma lem2745848 (n : int) : (term17 n) = (term49 n).
Proof. exact (MK_COMB (@lem2745847 n) (@lem2745846)). Qed.
Lemma lem2745850 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem2745851 (n : int) : (term49 n) = False.
Proof. exact (@lem2745850 (term50 n)). Qed.
Lemma lem2745852 (n : int) : (term17 n) = False.
Proof. exact (TRANS (@lem2745848 n) (@lem2745851 n)). Qed.
Lemma lem2745853 (n : int) : ((term16 n) = (term17 n)) = (term44 = False).
Proof. exact (MK_COMB (@lem2745835 n) (@lem2745852 n)). Qed.
Lemma lem2745855 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem2745856 : (term44 = False) = term51.
Proof. exact (@lem2745855 term44). Qed.
Lemma lem2745857 (n : int) : ((term16 n) = (term17 n)) = term51.
Proof. exact (TRANS (@lem2745853 n) (@lem2745856)). Qed.
Lemma lem2745858 (n : int) : term51 = ((term16 n) = (term17 n)).
Proof. exact (SYM (@lem2745857 n)). Qed.
Lemma lem2745862 (x : int) (n : nat) : (term10 x n) = (term11 x n).
Proof. exact (EQ_MP (@lem2745800 x n) (@lem2745799 x n)). Qed.
Lemma lem2745863 (n : int) (k : nat) : (term10 n k) = (term11 n k).
Proof. exact (@lem2745862 n k). Qed.
Lemma lem2745864 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2745865 (n : int) (k : nat) : (term26 n k) = (term52 n k).
Proof. exact (MK_COMB (@lem2745864) (@lem2745863 n k)). Qed.
Lemma lem2745866 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2745867 (n : int) (k : nat) : (term53 n k) = (term54 n k).
Proof. exact (MK_COMB (@lem2745866) (@lem2745865 n k)). Qed.
Lemma lem2745872 (n : int) (k : nat) : (term27 n k) = (term27 n k).
Proof. exact (eq_refl (term27 n k)). Qed.
Lemma lem2745873 (n : int) (k : nat) : ((term26 n k) = (term27 n k)) = ((term52 n k) = (term27 n k)).
Proof. exact (MK_COMB (@lem2745867 n k) (@lem2745872 n k)). Qed.
Lemma lem2745876 (n : int) (k : nat) : ((term52 n k) = (term27 n k)) = ((term26 n k) = (term27 n k)).
Proof. exact (SYM (@lem2745873 n k)). Qed.
Lemma lem2745878 (n : int) : (term3 n) = ((term1 n) = term2).
Proof. exact (EQ_MP (@lem2745796 n) (@lem2745795 n)). Qed.
Lemma lem2745879 : term51 = (term55 = term2).
Proof. exact (@lem2745878 term2). Qed.
Lemma lem2745882 : (term55 = term2) = term51.
Proof. exact (SYM (@lem2745879)). Qed.
Lemma lem2745883 : term56.
Proof. exact (@lem2743639 term57 term2 term58 term2). Qed.
Lemma lem2745885 (x : nat) : (term59 x) = term57.
Proof. exact (proj1 (@lem2405621 x)). Qed.
Lemma lem2745886 : term60 = term57.
Proof. exact (@lem2745885 term61). Qed.
Lemma lem2745887 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2745888 : term62 = term63.
Proof. exact (MK_COMB (@lem2745887) (@lem2745886)). Qed.
Lemma lem2745889 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2745890 : term64 = term65.
Proof. exact (MK_COMB (@lem2745888) (@lem2745889)). Qed.
Lemma lem2745891 : term65 = term66.
Proof. exact (@lem2406280 (NUMERAL 0) term67). Qed.
Lemma lem2745892 : term68 = (BIT1 0).
Proof. exact (@lem706821). Qed.
Lemma lem2745893 : (term68 = (BIT1 0)) = (term69 = term67).
Proof. exact (@lem1006570 0 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2745894 : term69 = term67.
Proof. exact (EQ_MP (@lem2745893) (@lem2745892)). Qed.
Lemma lem2745895 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2745896 : term66 = term2.
Proof. exact (MK_COMB (@lem2745895) (@lem2745894)). Qed.
Lemma lem2745897 : term65 = term2.
Proof. exact (TRANS (@lem2745891) (@lem2745896)). Qed.
Lemma lem2745898 : term64 = term2.
Proof. exact (TRANS (@lem2745890) (@lem2745897)). Qed.
Lemma lem2745899 : term70.
Proof. exact (@lem2745883 (@lem2745898)). Qed.
Lemma lem2745901 (m : nat) (n : nat) : (term71 m n) = (Peano.le m n).
Proof. exact (proj1 (@lem2403914 m n)). Qed.
Lemma lem2745902 : term72 = term73.
Proof. exact (@lem2745901 (NUMERAL 0) term67). Qed.
Lemma lem2745903 : term74 = (BIT1 0).
Proof. exact (@lem706883). Qed.
Lemma lem2745904 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1011471 (BIT1 0) 0 (BIT1 0) h1). Qed.
Lemma lem2745905 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2745904 h1) (fun h1 : term73 = True => @lem2745903)). Qed.
Lemma lem2745906 : term73 = True.
Proof. exact (EQ_MP (@lem2745905) (@lem2745903)). Qed.
Lemma lem2745907 : term72 = True.
Proof. exact (TRANS (@lem2745902) (@lem2745906)). Qed.
Lemma lem2745908 : True = term72.
Proof. exact (SYM (@lem2745907)). Qed.
Lemma lem2745909 : term72.
Proof. exact (EQ_MP (@lem2745908) (@lem0)). Qed.
Lemma lem2745910 : term75.
Proof. exact (@lem2745899 (@lem2745909)). Qed.
Lemma lem2745912 (x : nat) : (term76 x) = (int_of_num x).
Proof. exact (proj2 (@lem2406442 x)). Qed.
Lemma lem2745913 : term77 = term58.
Proof. exact (@lem2745912 term61). Qed.
Lemma lem2745914 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem2745915 : term79 = term80.
Proof. exact (MK_COMB (@lem2745914) (@lem2745913)). Qed.
Lemma lem2745917 (m : nat) (n : nat) : (term81 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem2404231 m n)). Qed.
Lemma lem2745918 : term80 = term82.
Proof. exact (@lem2745917 term67 term61). Qed.
Lemma lem2745919 : term83 = term84.
Proof. exact (@lem912741). Qed.
Lemma lem2745920 (h1 : term83 = term84) : term82 = True.
Proof. exact (@lem1009824 0 (BIT1 0) term84 h1). Qed.
Lemma lem2745921 : (term83 = term84) = (term82 = True).
Proof. exact (prop_ext (fun h1 : term83 = term84 => @lem2745920 h1) (fun h1 : term82 = True => @lem2745919)). Qed.
Lemma lem2745922 : term82 = True.
Proof. exact (EQ_MP (@lem2745921) (@lem2745919)). Qed.
Lemma lem2745923 : term80 = True.
Proof. exact (TRANS (@lem2745918) (@lem2745922)). Qed.
Lemma lem2745924 : term79 = True.
Proof. exact (TRANS (@lem2745915) (@lem2745923)). Qed.
Lemma lem2745925 : True = term79.
Proof. exact (SYM (@lem2745924)). Qed.
Lemma lem2745926 : term79.
Proof. exact (EQ_MP (@lem2745925) (@lem0)). Qed.
Lemma lem2745927 : term85.
Proof. exact (@lem2745910 (@lem2745926)). Qed.
Lemma lem2745928 : term55 = term2.
Proof. exact (proj2 (@lem2745927)). Qed.
Lemma lem2745929 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2745930 : term86 = term87.
Proof. exact (MK_COMB (@lem2745929) (@lem2745928)). Qed.
Lemma lem2745931 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2745932 : (term55 = term2) = (term2 = term2).
Proof. exact (MK_COMB (@lem2745930) (@lem2745931)). Qed.
Lemma lem2745934 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2745935 (x : int) : (x = x) = True.
Proof. exact (@lem2745934 int x). Qed.
Lemma lem2745936 : (term2 = term2) = True.
Proof. exact (@lem2745935 term2). Qed.
Lemma lem2745937 : (term55 = term2) = True.
Proof. exact (TRANS (@lem2745932) (@lem2745936)). Qed.
Lemma lem2745938 : True = (term55 = term2).
Proof. exact (SYM (@lem2745937)). Qed.
Lemma lem2745939 : term55 = term2.
Proof. exact (EQ_MP (@lem2745938) (@lem0)). Qed.
Lemma lem2745940 : term51.
Proof. exact (EQ_MP (@lem2745882) (@lem2745939)). Qed.
Lemma lem2745941 (n : nat) : term88 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem2745942 (n : nat) : (term88 n) = (term89 n).
Proof. exact (eq_refl (term88 n)). Qed.
Lemma lem2745943 (n : nat) : term89 n.
Proof. exact (EQ_MP (@lem2745942 n) (@lem2745941 n)). Qed.
Lemma lem2745944 (n : nat) : term90 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem2745957 (m : int) : term91 m.
Proof. exact (@lem2745783 m). Qed.
Lemma lem2745958 (m : int) : (term91 m) = (term92 m).
Proof. exact (eq_refl (term91 m)). Qed.
Lemma lem2745959 (m : int) : term92 m.
Proof. exact (EQ_MP (@lem2745958 m) (@lem2745957 m)). Qed.
Lemma lem2745960 (m : int) (n : int) : term93 m n.
Proof. exact (@lem2745959 m n). Qed.
Lemma lem2745961 (m : int) (n : int) : (term93 m n) = ((term94 m n) = (term95 m n)).
Proof. exact (eq_refl (term93 m n)). Qed.
Lemma lem2745966 (m : int) (n : int) : (term94 m n) = (term95 m n).
Proof. exact (EQ_MP (@lem2745961 m n) (@lem2745960 m n)). Qed.
Lemma lem2745967 (n : int) (k : nat) : (term52 n k) = (term96 n k).
Proof. exact (@lem2745966 n (int_pow n k)). Qed.
Lemma lem2745971 (n : int) (k : nat) (h1 : (term21 n k) = (term22 n k)) : (term21 n k) = (term22 n k).
Proof. exact (h1). Qed.
Lemma lem2745976 (n : int) : (term97 n) = (term97 n).
Proof. exact (eq_refl (term97 n)). Qed.
Lemma lem2745977 (n : int) (k : nat) (h1 : (term21 n k) = (term22 n k)) : (term96 n k) = (term98 n k).
Proof. exact (MK_COMB (@lem2745976 n) (@lem2745971 n k h1)). Qed.
Lemma lem2745980 (n : int) (k : nat) (h1 : (term21 n k) = (term22 n k)) : (term52 n k) = (term98 n k).
Proof. exact (TRANS (@lem2745967 n k) (@lem2745977 n k h1)). Qed.
Lemma lem2745981 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2745982 (n : int) (k : nat) (h1 : (term21 n k) = (term22 n k)) : (term54 n k) = (term99 n k).
Proof. exact (MK_COMB (@lem2745981) (@lem2745980 n k h1)). Qed.
Lemma lem2745986 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem2745944 n (@lem2745943 n)). Qed.
Lemma lem2745987 (k : nat) : ((S k) = (NUMERAL 0)) = False.
Proof. exact (@lem2745986 k). Qed.
Lemma lem2745988 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2745989 (k : nat) : (term89 k) = (~ False).
Proof. exact (MK_COMB (@lem2745988) (@lem2745987 k)). Qed.
Lemma lem2745991 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2745992 (k : nat) : (term89 k) = True.
Proof. exact (TRANS (@lem2745989 k) (@lem2745991)). Qed.
Lemma lem2745993 (n : int) : (term48 n) = (term48 n).
Proof. exact (eq_refl (term48 n)). Qed.
Lemma lem2745994 (k : nat) (n : int) : (term27 n k) = (term100 n).
Proof. exact (MK_COMB (@lem2745993 n) (@lem2745992 k)). Qed.
Lemma lem2745996 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem2745997 (n : int) : (term100 n) = (term50 n).
Proof. exact (@lem2745996 (term50 n)). Qed.
Lemma lem2745998 (k : nat) (n : int) : (term27 n k) = (term50 n).
Proof. exact (TRANS (@lem2745994 k n) (@lem2745997 n)). Qed.
Lemma lem2745999 (n : int) (k : nat) (h1 : (term21 n k) = (term22 n k)) : ((term52 n k) = (term27 n k)) = ((term98 n k) = (term50 n)).
Proof. exact (MK_COMB (@lem2745982 n k h1) (@lem2745998 k n)). Qed.
Lemma lem2746002 (n : int) (k : nat) (h1 : (term21 n k) = (term22 n k)) : ((term98 n k) = (term50 n)) = ((term52 n k) = (term27 n k)).
Proof. exact (SYM (@lem2745999 n k h1)). Qed.
Lemma lem2746013 (n : int) : term101 n.
Proof. exact (@lem9851 (term50 n)). Qed.
Lemma lem2746014 (n : int) : (term101 n) = (term102 n).
Proof. exact (eq_refl (term101 n)). Qed.
Lemma lem2746015 (n : int) : term102 n.
Proof. exact (EQ_MP (@lem2746014 n) (@lem2746013 n)). Qed.
Lemma lem2746016 (n : int) (h1 : (term50 n) = True) : (term50 n) = True.
Proof. exact (h1). Qed.
Lemma lem2746017 (n : int) (h1 : (term50 n) = False) : (term50 n) = False.
Proof. exact (h1). Qed.
Lemma lem2746028 (k : nat) : (term103 k) = (term103 k).
Proof. exact (eq_refl (term103 k)). Qed.
Lemma lem2746029 (k : nat) (n : int) (h1 : (term50 n) = True) : (term104 k n) = (term105 k).
Proof. exact (MK_COMB (@lem2746028 k) (@lem2746016 n h1)). Qed.
Lemma lem2746030 (k : nat) : (term105 k) = ((term106 k) = True).
Proof. exact (eq_refl (term105 k)). Qed.
Lemma lem2746031 (k : nat) (n : int) : (term107 k n) = (term107 k n).
Proof. exact (eq_refl (term107 k n)). Qed.
Lemma lem2746032 (n : int) (k : nat) : ((term104 k n) = (term105 k)) = ((term104 k n) = ((term106 k) = True)).
Proof. exact (MK_COMB (@lem2746031 k n) (@lem2746030 k)). Qed.
Lemma lem2746033 (k : nat) (n : int) : (term104 k n) = ((term98 n k) = (term50 n)).
Proof. exact (eq_refl (term104 k n)). Qed.
Lemma lem2746034 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2746035 (k : nat) (n : int) : (term107 k n) = (term108 k n).
Proof. exact (MK_COMB (@lem2746034) (@lem2746033 k n)). Qed.
Lemma lem2746036 (k : nat) : ((term106 k) = True) = ((term106 k) = True).
Proof. exact (eq_refl ((term106 k) = True)). Qed.
Lemma lem2746037 (n : int) (k : nat) : ((term104 k n) = ((term106 k) = True)) = (((term98 n k) = (term50 n)) = ((term106 k) = True)).
Proof. exact (MK_COMB (@lem2746035 k n) (@lem2746036 k)). Qed.
Lemma lem2746038 (n : int) (k : nat) : ((term104 k n) = (term105 k)) = (((term98 n k) = (term50 n)) = ((term106 k) = True)).
Proof. exact (TRANS (@lem2746032 n k) (@lem2746037 n k)). Qed.
Lemma lem2746039 (k : nat) (n : int) (h1 : (term50 n) = True) : ((term98 n k) = (term50 n)) = ((term106 k) = True).
Proof. exact (EQ_MP (@lem2746038 n k) (@lem2746029 k n h1)). Qed.
Lemma lem2746040 (k : nat) (n : int) (h1 : (term50 n) = True) : ((term106 k) = True) = ((term98 n k) = (term50 n)).
Proof. exact (SYM (@lem2746039 k n h1)). Qed.
Lemma lem2746041 (k : nat) : (term103 k) = (term103 k).
Proof. exact (eq_refl (term103 k)). Qed.
Lemma lem2746042 (k : nat) (n : int) (h1 : (term50 n) = False) : (term104 k n) = (term109 k).
Proof. exact (MK_COMB (@lem2746041 k) (@lem2746017 n h1)). Qed.
Lemma lem2746043 (k : nat) : (term109 k) = ((term110 k) = False).
Proof. exact (eq_refl (term109 k)). Qed.
Lemma lem2746044 (k : nat) (n : int) : (term107 k n) = (term107 k n).
Proof. exact (eq_refl (term107 k n)). Qed.
Lemma lem2746045 (n : int) (k : nat) : ((term104 k n) = (term109 k)) = ((term104 k n) = ((term110 k) = False)).
Proof. exact (MK_COMB (@lem2746044 k n) (@lem2746043 k)). Qed.
Lemma lem2746046 (k : nat) (n : int) : (term104 k n) = ((term98 n k) = (term50 n)).
Proof. exact (eq_refl (term104 k n)). Qed.
Lemma lem2746047 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2746048 (k : nat) (n : int) : (term107 k n) = (term108 k n).
Proof. exact (MK_COMB (@lem2746047) (@lem2746046 k n)). Qed.
Lemma lem2746049 (k : nat) : ((term110 k) = False) = ((term110 k) = False).
Proof. exact (eq_refl ((term110 k) = False)). Qed.
Lemma lem2746050 (n : int) (k : nat) : ((term104 k n) = ((term110 k) = False)) = (((term98 n k) = (term50 n)) = ((term110 k) = False)).
Proof. exact (MK_COMB (@lem2746048 k n) (@lem2746049 k)). Qed.
Lemma lem2746051 (n : int) (k : nat) : ((term104 k n) = (term109 k)) = (((term98 n k) = (term50 n)) = ((term110 k) = False)).
Proof. exact (TRANS (@lem2746045 n k) (@lem2746050 n k)). Qed.
Lemma lem2746052 (k : nat) (n : int) (h1 : (term50 n) = False) : ((term98 n k) = (term50 n)) = ((term110 k) = False).
Proof. exact (EQ_MP (@lem2746051 n k) (@lem2746042 k n h1)). Qed.
Lemma lem2746053 (k : nat) (n : int) (h1 : (term50 n) = False) : ((term110 k) = False) = ((term98 n k) = (term50 n)).
Proof. exact (SYM (@lem2746052 k n h1)). Qed.
Lemma lem2746055 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem2746056 (k : nat) : ((term106 k) = True) = (term106 k).
Proof. exact (@lem2746055 (term106 k)). Qed.
Lemma lem2746058 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem2746059 (k : nat) : (term106 k) = True.
Proof. exact (@lem2746058 (term111 k)). Qed.
Lemma lem2746060 (k : nat) : ((term106 k) = True) = True.
Proof. exact (TRANS (@lem2746056 k) (@lem2746059 k)). Qed.
Lemma lem2746061 (k : nat) : True = ((term106 k) = True).
Proof. exact (SYM (@lem2746060 k)). Qed.
Lemma lem2746062 (k : nat) : (term106 k) = True.
Proof. exact (EQ_MP (@lem2746061 k) (@lem0)). Qed.
Lemma lem2746064 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem2746065 (k : nat) : ((term110 k) = False) = (term112 k).
Proof. exact (@lem2746064 (term110 k)). Qed.
Lemma lem2746067 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem2746068 (k : nat) : (term110 k) = (term113 k).
Proof. exact (@lem2746067 (term113 k)). Qed.
Lemma lem2746070 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem2746071 (k : nat) : (term113 k) = False.
Proof. exact (@lem2746070 (term114 k)). Qed.
Lemma lem2746072 (k : nat) : (term110 k) = False.
Proof. exact (TRANS (@lem2746068 k) (@lem2746071 k)). Qed.
Lemma lem2746073 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2746074 (k : nat) : (term112 k) = (~ False).
Proof. exact (MK_COMB (@lem2746073) (@lem2746072 k)). Qed.
Lemma lem2746076 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2746077 (k : nat) : (term112 k) = True.
Proof. exact (TRANS (@lem2746074 k) (@lem2746076)). Qed.
Lemma lem2746078 (k : nat) : ((term110 k) = False) = True.
Proof. exact (TRANS (@lem2746065 k) (@lem2746077 k)). Qed.
Lemma lem2746079 (k : nat) : True = ((term110 k) = False).
Proof. exact (SYM (@lem2746078 k)). Qed.
Lemma lem2746080 (k : nat) : (term110 k) = False.
Proof. exact (EQ_MP (@lem2746079 k) (@lem0)). Qed.
Lemma lem2746081 (k : nat) (n : int) (h1 : (term50 n) = False) : (term98 n k) = (term50 n).
Proof. exact (EQ_MP (@lem2746053 k n h1) (@lem2746080 k)). Qed.
Lemma lem2746082 (k : nat) (n : int) (h1 : (term50 n) = True) : (term98 n k) = (term50 n).
Proof. exact (EQ_MP (@lem2746040 k n h1) (@lem2746062 k)). Qed.
Lemma lem2746085 (k : nat) (n : int) : (term98 n k) = (term50 n).
Proof. exact (or_elim (@lem2746015 n) (fun h0 : (term50 n) = True => @lem2746082 k n h0) (fun h0 : (term50 n) = False => @lem2746081 k n h0)). Qed.
Lemma lem2746086 (n : int) (k : nat) (h1 : (term21 n k) = (term22 n k)) : (term52 n k) = (term27 n k).
Proof. exact (EQ_MP (@lem2746002 n k h1) (@lem2746085 k n)). Qed.
Lemma lem2746087 (n : int) (k : nat) (h1 : (term21 n k) = (term22 n k)) : (term26 n k) = (term27 n k).
Proof. exact (EQ_MP (@lem2745876 n k) (@lem2746086 n k h1)). Qed.
Lemma lem2746088 (n : int) : (term16 n) = (term17 n).
Proof. exact (EQ_MP (@lem2745858 n) (@lem2745940)). Qed.
Lemma lem2746089 (n : int) (k : nat) : term29 n k.
Proof. exact (fun h0 : (term21 n k) = (term22 n k) => @lem2746087 n k h0). Qed.
Lemma lem2746094 (n : int) : term33 n.
Proof. exact (fun k : nat => @lem2746089 n k). Qed.
Lemma lem2746095 (n : int) : term35 n.
Proof. exact (conj (@lem2746088 n) (@lem2746094 n)). Qed.
Lemma lem2746096 (n : int) : term40 n.
Proof. exact (@lem2745825 n (@lem2746095 n)). Qed.
Lemma lem2746101 : term115.
Proof. exact (fun n : int => @lem2746096 n). Qed.
