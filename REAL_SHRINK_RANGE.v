Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SHRINK_RANGE_term_abbrevs.
Require Import REAL_ABS_DIV_spec.
Require Import REAL_LT_LDIV_EQ_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365720_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm1482679_spec.
Require Import thm1482703_spec.
Require Import thm1482705_spec.
Require Import thm1482981_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982709_spec.
Require Import thm1982711_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982717_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988289_spec.
Require Import thm1988291_spec.
Require Import thm1988295_spec.
Require Import thm1988318_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Lemma lem1999808 (x : real) : (term0 x) = (term1 x).
Proof. exact (@lem1988295 term2 (term3 x)). Qed.
Lemma lem1999817 (x : real) : (term3 x) = (term4 x).
Proof. exact (@lem1982761 (real_abs x) term5). Qed.
Lemma lem1999820 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1999821 (x : real) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem1999820) (@lem1999817 x)). Qed.
Lemma lem1999822 (x : real) : (term8 x) = (term9 x).
Proof. exact (@lem1982792 term2 (term4 x)). Qed.
Lemma lem1999823 (x : real) : (term10 x) = (term11 x).
Proof. exact (@lem1982781 (real_abs x) term12 term5). Qed.
Lemma lem1999825 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1999826 : term5 = term14.
Proof. exact (@lem1999825 term15). Qed.
Lemma lem1999828 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1999829 : term12 = term18.
Proof. exact (@lem1999828 term15). Qed.
Lemma lem1999830 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1999831 : term19 = term20.
Proof. exact (MK_COMB (@lem1999830) (@lem1999829)). Qed.
Lemma lem1999832 : term21 = term22.
Proof. exact (MK_COMB (@lem1999831) (@lem1999826)). Qed.
Lemma lem1999833 : term22 = term23.
Proof. exact (@lem1981613 term12 term5 term5 term5). Qed.
Lemma lem1999835 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1999836 : term26 = term27.
Proof. exact (@lem1999835 term15 term15). Qed.
Lemma lem1999837 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1999838 : term29 = term15.
Proof. exact (EQ_MP (@lem1999837) (@lem940073)). Qed.
Lemma lem1999839 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1999840 : term27 = term5.
Proof. exact (MK_COMB (@lem1999839) (@lem1999838)). Qed.
Lemma lem1999841 : term26 = term5.
Proof. exact (TRANS (@lem1999836) (@lem1999840)). Qed.
Lemma lem1999843 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1999844 : term21 = term32.
Proof. exact (@lem1999843 term15 term15). Qed.
Lemma lem1999845 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1999846 : term29 = term15.
Proof. exact (EQ_MP (@lem1999845) (@lem940073)). Qed.
Lemma lem1999847 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1999848 : term27 = term5.
Proof. exact (MK_COMB (@lem1999847) (@lem1999846)). Qed.
Lemma lem1999849 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1999850 : term32 = term12.
Proof. exact (MK_COMB (@lem1999849) (@lem1999848)). Qed.
Lemma lem1999851 : term21 = term12.
Proof. exact (TRANS (@lem1999844) (@lem1999850)). Qed.
Lemma lem1999852 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem1999853 : term33 = term34.
Proof. exact (MK_COMB (@lem1999852) (@lem1999851)). Qed.
Lemma lem1999854 : term23 = term18.
Proof. exact (MK_COMB (@lem1999853) (@lem1999841)). Qed.
Lemma lem1999855 : term22 = term18.
Proof. exact (TRANS (@lem1999833) (@lem1999854)). Qed.
Lemma lem1999856 : term21 = term18.
Proof. exact (TRANS (@lem1999832) (@lem1999855)). Qed.
Lemma lem1999858 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem1999859 : term18 = term12.
Proof. exact (@lem1999858 term12). Qed.
Lemma lem1999860 : term21 = term12.
Proof. exact (TRANS (@lem1999856) (@lem1999859)). Qed.
Lemma lem1999863 (x : real) : (term36 x) = (term36 x).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem1999864 (x : real) : (term11 x) = (term37 x).
Proof. exact (MK_COMB (@lem1999863 x) (@lem1999860)). Qed.
Lemma lem1999865 (x : real) : (term10 x) = (term37 x).
Proof. exact (TRANS (@lem1999823 x) (@lem1999864 x)). Qed.
Lemma lem1999866 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1999867 (x : real) : (term9 x) = (term39 x).
Proof. exact (MK_COMB (@lem1999866) (@lem1999865 x)). Qed.
Lemma lem1999868 (x : real) : (term39 x) = (term37 x).
Proof. exact (@lem1982721 (term37 x)). Qed.
Lemma lem1999869 (x : real) : (term9 x) = (term37 x).
Proof. exact (TRANS (@lem1999867 x) (@lem1999868 x)). Qed.
Lemma lem1999870 (x : real) : (term8 x) = (term37 x).
Proof. exact (TRANS (@lem1999822 x) (@lem1999869 x)). Qed.
Lemma lem1999871 (x : real) : (term7 x) = (term37 x).
Proof. exact (TRANS (@lem1999821 x) (@lem1999870 x)). Qed.
Lemma lem1999872 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1999873 (x : real) : (term40 x) = (term41 x).
Proof. exact (MK_COMB (@lem1999872) (@lem1999871 x)). Qed.
Lemma lem1999874 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1999875 (x : real) : (term1 x) = (term42 x).
Proof. exact (MK_COMB (@lem1999873 x) (@lem1999874)). Qed.
Lemma lem1999885 (x : real) : (term0 x) = (term42 x).
Proof. exact (TRANS (@lem1999808 x) (@lem1999875 x)). Qed.
Lemma lem1999887 (a : real) (x : real) (r : real) : (term43 x a r) = (term44 a x r).
Proof. exact (proj1 (@lem1482679 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1999888 (x : real) : (term42 x) = (term45 x).
Proof. exact (@lem1999887 term12 x term2). Qed.
Lemma lem1999895 (x : real) : (term46 x) = x.
Proof. exact (@lem1982733 x). Qed.
Lemma lem1999898 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1999899 (x : real) : (term48 x) = (term49 x).
Proof. exact (MK_COMB (@lem1999898) (@lem1999895 x)). Qed.
Lemma lem1999900 (x : real) : (term49 x) = (term50 x).
Proof. exact (@lem1982761 x term12). Qed.
Lemma lem1999901 (x : real) : (term48 x) = (term50 x).
Proof. exact (TRANS (@lem1999899 x) (@lem1999900 x)). Qed.
Lemma lem1999902 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1999903 (x : real) : (term51 x) = (term52 x).
Proof. exact (MK_COMB (@lem1999902) (@lem1999901 x)). Qed.
Lemma lem1999904 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1999905 (x : real) : (term53 x) = (term54 x).
Proof. exact (MK_COMB (@lem1999903 x) (@lem1999904)). Qed.
Lemma lem1999918 (x : real) : (term55 x) = (term56 x).
Proof. exact (@lem1982761 (term57 x) term12). Qed.
Lemma lem1999919 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1999920 (x : real) : (term58 x) = (term59 x).
Proof. exact (MK_COMB (@lem1999919) (@lem1999918 x)). Qed.
Lemma lem1999921 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1999922 (x : real) : (term60 x) = (term61 x).
Proof. exact (MK_COMB (@lem1999920 x) (@lem1999921)). Qed.
Lemma lem1999923 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1999924 (x : real) : (term62 x) = (term63 x).
Proof. exact (MK_COMB (@lem1999923) (@lem1999922 x)). Qed.
Lemma lem1999925 (x : real) : (term45 x) = (term64 x).
Proof. exact (MK_COMB (@lem1999924 x) (@lem1999905 x)). Qed.
Lemma lem1999928 (x : real) : (term42 x) = (term64 x).
Proof. exact (TRANS (@lem1999888 x) (@lem1999925 x)). Qed.
Lemma lem1999929 (x : real) (h1 : term64 x) : term64 x.
Proof. exact (h1). Qed.
Lemma lem1999930 (x : real) (h1 : term64 x) : term54 x.
Proof. exact (proj2 (@lem1999929 x h1)). Qed.
Lemma lem1999931 (x : real) (h1 : term64 x) : term61 x.
Proof. exact (proj1 (@lem1999929 x h1)). Qed.
Lemma lem1999933 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1999934 : term65 = term66.
Proof. exact (@lem1999933 term2 term5). Qed.
Lemma lem1999936 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1999937 : term5 = term14.
Proof. exact (@lem1999936 term15). Qed.
Lemma lem1999939 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1999940 : term2 = term67.
Proof. exact (@lem1999939 (NUMERAL 0)). Qed.
Lemma lem1999941 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1999942 : term68 = term69.
Proof. exact (MK_COMB (@lem1999941) (@lem1999940)). Qed.
Lemma lem1999943 : term66 = term70.
Proof. exact (MK_COMB (@lem1999942) (@lem1999937)). Qed.
Lemma lem1999944 : term71.
Proof. exact (@lem1980255 term2 term5 term5 term5). Qed.
Lemma lem1999946 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999947 : term66 = term73.
Proof. exact (@lem1999946 (NUMERAL 0) term15). Qed.
Lemma lem1999948 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999949 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999950 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem1999949 h1) (fun h1 : term73 = True => @lem1999948)). Qed.
Lemma lem1999951 : term73 = True.
Proof. exact (EQ_MP (@lem1999950) (@lem1999948)). Qed.
Lemma lem1999952 : term66 = True.
Proof. exact (TRANS (@lem1999947) (@lem1999951)). Qed.
Lemma lem1999953 : True = term66.
Proof. exact (SYM (@lem1999952)). Qed.
Lemma lem1999954 : term66.
Proof. exact (EQ_MP (@lem1999953) (@lem0)). Qed.
Lemma lem1999955 : term75.
Proof. exact (@lem1999944 (@lem1999954)). Qed.
Lemma lem1999957 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999958 : term66 = term73.
Proof. exact (@lem1999957 (NUMERAL 0) term15). Qed.
Lemma lem1999959 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999960 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999961 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem1999960 h1) (fun h1 : term73 = True => @lem1999959)). Qed.
Lemma lem1999962 : term73 = True.
Proof. exact (EQ_MP (@lem1999961) (@lem1999959)). Qed.
Lemma lem1999963 : term66 = True.
Proof. exact (TRANS (@lem1999958) (@lem1999962)). Qed.
Lemma lem1999964 : True = term66.
Proof. exact (SYM (@lem1999963)). Qed.
Lemma lem1999965 : term66.
Proof. exact (EQ_MP (@lem1999964) (@lem0)). Qed.
Lemma lem1999966 : term70 = term76.
Proof. exact (@lem1999955 (@lem1999965)). Qed.
Lemma lem1999968 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1999969 : term26 = term27.
Proof. exact (@lem1999968 term15 term15). Qed.
Lemma lem1999970 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1999971 : term29 = term15.
Proof. exact (EQ_MP (@lem1999970) (@lem940073)). Qed.
Lemma lem1999972 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1999973 : term27 = term5.
Proof. exact (MK_COMB (@lem1999972) (@lem1999971)). Qed.
Lemma lem1999974 : term26 = term5.
Proof. exact (TRANS (@lem1999969) (@lem1999973)). Qed.
Lemma lem1999976 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1999977 : term78 = term2.
Proof. exact (@lem1999976 term15). Qed.
Lemma lem1999978 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1999979 : term79 = term68.
Proof. exact (MK_COMB (@lem1999978) (@lem1999977)). Qed.
Lemma lem1999980 : term76 = term66.
Proof. exact (MK_COMB (@lem1999979) (@lem1999974)). Qed.
Lemma lem1999982 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999983 : term66 = term73.
Proof. exact (@lem1999982 (NUMERAL 0) term15). Qed.
Lemma lem1999984 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999985 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999986 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem1999985 h1) (fun h1 : term73 = True => @lem1999984)). Qed.
Lemma lem1999987 : term73 = True.
Proof. exact (EQ_MP (@lem1999986) (@lem1999984)). Qed.
Lemma lem1999988 : term66 = True.
Proof. exact (TRANS (@lem1999983) (@lem1999987)). Qed.
Lemma lem1999989 : term76 = True.
Proof. exact (TRANS (@lem1999980) (@lem1999988)). Qed.
Lemma lem1999990 : term70 = True.
Proof. exact (TRANS (@lem1999966) (@lem1999989)). Qed.
Lemma lem1999991 : term66 = True.
Proof. exact (TRANS (@lem1999943) (@lem1999990)). Qed.
Lemma lem1999992 : term65 = True.
Proof. exact (TRANS (@lem1999934) (@lem1999991)). Qed.
Lemma lem1999993 : True = term65.
Proof. exact (SYM (@lem1999992)). Qed.
Lemma lem1999994 : term65.
Proof. exact (EQ_MP (@lem1999993) (@lem0)). Qed.
Lemma lem1999995 (x : real) (h1 : term64 x) : term80 x.
Proof. exact (conj (@lem1999994) (@lem1999930 x h1)). Qed.
Lemma lem1999997 (x : real) (y : real) : term81 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem1999998 (x : real) : term82 x.
Proof. exact (@lem1999997 term5 (term50 x)). Qed.
Lemma lem1999999 (x : real) (h1 : term64 x) : term83 x.
Proof. exact (@lem1999998 x (@lem1999995 x h1)). Qed.
Lemma lem2000000 (x : real) : (term84 x) = (term50 x).
Proof. exact (@lem1982733 (term50 x)). Qed.
Lemma lem2000001 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2000002 (x : real) : (term85 x) = (term52 x).
Proof. exact (MK_COMB (@lem2000001) (@lem2000000 x)). Qed.
Lemma lem2000003 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2000004 (x : real) : (term83 x) = (term54 x).
Proof. exact (MK_COMB (@lem2000002 x) (@lem2000003)). Qed.
Lemma lem2000005 (x : real) (h1 : term64 x) : term54 x.
Proof. exact (EQ_MP (@lem2000004 x) (@lem1999999 x h1)). Qed.
Lemma lem2000007 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2000008 : term65 = term66.
Proof. exact (@lem2000007 term2 term5). Qed.
Lemma lem2000010 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2000011 : term5 = term14.
Proof. exact (@lem2000010 term15). Qed.
Lemma lem2000013 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2000014 : term2 = term67.
Proof. exact (@lem2000013 (NUMERAL 0)). Qed.
Lemma lem2000015 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2000016 : term68 = term69.
Proof. exact (MK_COMB (@lem2000015) (@lem2000014)). Qed.
Lemma lem2000017 : term66 = term70.
Proof. exact (MK_COMB (@lem2000016) (@lem2000011)). Qed.
Lemma lem2000018 : term71.
Proof. exact (@lem1980255 term2 term5 term5 term5). Qed.
Lemma lem2000020 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2000021 : term66 = term73.
Proof. exact (@lem2000020 (NUMERAL 0) term15). Qed.
Lemma lem2000022 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2000023 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2000024 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2000023 h1) (fun h1 : term73 = True => @lem2000022)). Qed.
Lemma lem2000025 : term73 = True.
Proof. exact (EQ_MP (@lem2000024) (@lem2000022)). Qed.
Lemma lem2000026 : term66 = True.
Proof. exact (TRANS (@lem2000021) (@lem2000025)). Qed.
Lemma lem2000027 : True = term66.
Proof. exact (SYM (@lem2000026)). Qed.
Lemma lem2000028 : term66.
Proof. exact (EQ_MP (@lem2000027) (@lem0)). Qed.
Lemma lem2000029 : term75.
Proof. exact (@lem2000018 (@lem2000028)). Qed.
Lemma lem2000031 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2000032 : term66 = term73.
Proof. exact (@lem2000031 (NUMERAL 0) term15). Qed.
Lemma lem2000033 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2000034 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2000035 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2000034 h1) (fun h1 : term73 = True => @lem2000033)). Qed.
Lemma lem2000036 : term73 = True.
Proof. exact (EQ_MP (@lem2000035) (@lem2000033)). Qed.
Lemma lem2000037 : term66 = True.
Proof. exact (TRANS (@lem2000032) (@lem2000036)). Qed.
Lemma lem2000038 : True = term66.
Proof. exact (SYM (@lem2000037)). Qed.
Lemma lem2000039 : term66.
Proof. exact (EQ_MP (@lem2000038) (@lem0)). Qed.
Lemma lem2000040 : term70 = term76.
Proof. exact (@lem2000029 (@lem2000039)). Qed.
Lemma lem2000042 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2000043 : term26 = term27.
Proof. exact (@lem2000042 term15 term15). Qed.
Lemma lem2000044 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2000045 : term29 = term15.
Proof. exact (EQ_MP (@lem2000044) (@lem940073)). Qed.
Lemma lem2000046 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2000047 : term27 = term5.
Proof. exact (MK_COMB (@lem2000046) (@lem2000045)). Qed.
Lemma lem2000048 : term26 = term5.
Proof. exact (TRANS (@lem2000043) (@lem2000047)). Qed.
Lemma lem2000050 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2000051 : term78 = term2.
Proof. exact (@lem2000050 term15). Qed.
Lemma lem2000052 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2000053 : term79 = term68.
Proof. exact (MK_COMB (@lem2000052) (@lem2000051)). Qed.
Lemma lem2000054 : term76 = term66.
Proof. exact (MK_COMB (@lem2000053) (@lem2000048)). Qed.
Lemma lem2000056 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2000057 : term66 = term73.
Proof. exact (@lem2000056 (NUMERAL 0) term15). Qed.
Lemma lem2000058 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2000059 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2000060 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2000059 h1) (fun h1 : term73 = True => @lem2000058)). Qed.
Lemma lem2000061 : term73 = True.
Proof. exact (EQ_MP (@lem2000060) (@lem2000058)). Qed.
Lemma lem2000062 : term66 = True.
Proof. exact (TRANS (@lem2000057) (@lem2000061)). Qed.
Lemma lem2000063 : term76 = True.
Proof. exact (TRANS (@lem2000054) (@lem2000062)). Qed.
Lemma lem2000064 : term70 = True.
Proof. exact (TRANS (@lem2000040) (@lem2000063)). Qed.
Lemma lem2000065 : term66 = True.
Proof. exact (TRANS (@lem2000017) (@lem2000064)). Qed.
Lemma lem2000066 : term65 = True.
Proof. exact (TRANS (@lem2000008) (@lem2000065)). Qed.
Lemma lem2000067 : True = term65.
Proof. exact (SYM (@lem2000066)). Qed.
Lemma lem2000068 : term65.
Proof. exact (EQ_MP (@lem2000067) (@lem0)). Qed.
Lemma lem2000069 (x : real) (h1 : term64 x) : term86 x.
Proof. exact (conj (@lem2000068) (@lem1999931 x h1)). Qed.
Lemma lem2000071 (x : real) (y : real) : term81 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2000072 (x : real) : term87 x.
Proof. exact (@lem2000071 term5 (term56 x)). Qed.
Lemma lem2000073 (x : real) (h1 : term64 x) : term88 x.
Proof. exact (@lem2000072 x (@lem2000069 x h1)). Qed.
Lemma lem2000074 (x : real) : (term89 x) = (term56 x).
Proof. exact (@lem1982733 (term56 x)). Qed.
Lemma lem2000075 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2000076 (x : real) : (term90 x) = (term59 x).
Proof. exact (MK_COMB (@lem2000075) (@lem2000074 x)). Qed.
Lemma lem2000077 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2000078 (x : real) : (term88 x) = (term61 x).
Proof. exact (MK_COMB (@lem2000076 x) (@lem2000077)). Qed.
Lemma lem2000079 (x : real) (h1 : term64 x) : term61 x.
Proof. exact (EQ_MP (@lem2000078 x) (@lem2000073 x h1)). Qed.
Lemma lem2000080 (x : real) (h1 : term64 x) : term64 x.
Proof. exact (conj (@lem2000079 x h1) (@lem2000005 x h1)). Qed.
Lemma lem2000082 (x : real) (y : real) : term91 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2000083 (x : real) : term92 x.
Proof. exact (@lem2000082 (term56 x) (term50 x)). Qed.
Lemma lem2000084 (x : real) (h1 : term64 x) : term93 x.
Proof. exact (@lem2000083 x (@lem2000080 x h1)). Qed.
Lemma lem2000085 (x : real) : (term94 x) = (term95 x).
Proof. exact (@lem1982753 (term57 x) x term12 term12). Qed.
Lemma lem2000086 (x : real) : (term96 x) = (term97 x).
Proof. exact (@lem1982713 term12 x). Qed.
Lemma lem2000088 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2000089 : term5 = term14.
Proof. exact (@lem2000088 term15). Qed.
Lemma lem2000091 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2000092 : term12 = term18.
Proof. exact (@lem2000091 term15). Qed.
Lemma lem2000093 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2000094 : term47 = term98.
Proof. exact (MK_COMB (@lem2000093) (@lem2000092)). Qed.
Lemma lem2000095 : term99 = term100.
Proof. exact (MK_COMB (@lem2000094) (@lem2000089)). Qed.
Lemma lem2000096 : term101.
Proof. exact (@lem1981473 term12 term5 term5 term5 term2 term5). Qed.
Lemma lem2000098 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2000099 : term66 = term73.
Proof. exact (@lem2000098 (NUMERAL 0) term15). Qed.
Lemma lem2000100 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2000101 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2000102 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2000101 h1) (fun h1 : term73 = True => @lem2000100)). Qed.
Lemma lem2000103 : term73 = True.
Proof. exact (EQ_MP (@lem2000102) (@lem2000100)). Qed.
Lemma lem2000104 : term66 = True.
Proof. exact (TRANS (@lem2000099) (@lem2000103)). Qed.
Lemma lem2000105 : True = term66.
Proof. exact (SYM (@lem2000104)). Qed.
Lemma lem2000106 : term66.
Proof. exact (EQ_MP (@lem2000105) (@lem0)). Qed.
Lemma lem2000107 : term102.
Proof. exact (@lem2000096 (@lem2000106)). Qed.
Lemma lem2000109 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2000110 : term66 = term73.
Proof. exact (@lem2000109 (NUMERAL 0) term15). Qed.
Lemma lem2000111 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2000112 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2000113 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2000112 h1) (fun h1 : term73 = True => @lem2000111)). Qed.
Lemma lem2000114 : term73 = True.
Proof. exact (EQ_MP (@lem2000113) (@lem2000111)). Qed.
Lemma lem2000115 : term66 = True.
Proof. exact (TRANS (@lem2000110) (@lem2000114)). Qed.
Lemma lem2000116 : True = term66.
Proof. exact (SYM (@lem2000115)). Qed.
Lemma lem2000117 : term66.
Proof. exact (EQ_MP (@lem2000116) (@lem0)). Qed.
Lemma lem2000118 : term103.
Proof. exact (@lem2000107 (@lem2000117)). Qed.
Lemma lem2000120 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2000121 : term66 = term73.
Proof. exact (@lem2000120 (NUMERAL 0) term15). Qed.
Lemma lem2000122 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2000123 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2000124 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2000123 h1) (fun h1 : term73 = True => @lem2000122)). Qed.
Lemma lem2000125 : term73 = True.
Proof. exact (EQ_MP (@lem2000124) (@lem2000122)). Qed.
Lemma lem2000126 : term66 = True.
Proof. exact (TRANS (@lem2000121) (@lem2000125)). Qed.
Lemma lem2000127 : True = term66.
Proof. exact (SYM (@lem2000126)). Qed.
Lemma lem2000128 : term66.
Proof. exact (EQ_MP (@lem2000127) (@lem0)). Qed.
Lemma lem2000129 : term104.
Proof. exact (@lem2000118 (@lem2000128)). Qed.
Lemma lem2000131 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2000132 : term26 = term27.
Proof. exact (@lem2000131 term15 term15). Qed.
Lemma lem2000133 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2000134 : term29 = term15.
Proof. exact (EQ_MP (@lem2000133) (@lem940073)). Qed.
Lemma lem2000135 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2000136 : term27 = term5.
Proof. exact (MK_COMB (@lem2000135) (@lem2000134)). Qed.
Lemma lem2000137 : term26 = term5.
Proof. exact (TRANS (@lem2000132) (@lem2000136)). Qed.
Lemma lem2000139 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2000140 : term21 = term32.
Proof. exact (@lem2000139 term15 term15). Qed.
Lemma lem2000141 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2000142 : term29 = term15.
Proof. exact (EQ_MP (@lem2000141) (@lem940073)). Qed.
Lemma lem2000143 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2000144 : term27 = term5.
Proof. exact (MK_COMB (@lem2000143) (@lem2000142)). Qed.
Lemma lem2000145 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2000146 : term32 = term12.
Proof. exact (MK_COMB (@lem2000145) (@lem2000144)). Qed.
Lemma lem2000147 : term21 = term12.
Proof. exact (TRANS (@lem2000140) (@lem2000146)). Qed.
Lemma lem2000148 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2000149 : term105 = term47.
Proof. exact (MK_COMB (@lem2000148) (@lem2000147)). Qed.
Lemma lem2000150 : term106 = term99.
Proof. exact (MK_COMB (@lem2000149) (@lem2000137)). Qed.
Lemma lem2000152 (m : nat) : (term107 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2000153 : term99 = term2.
Proof. exact (@lem2000152 term15). Qed.
Lemma lem2000154 : term106 = term2.
Proof. exact (TRANS (@lem2000150) (@lem2000153)). Qed.
Lemma lem2000155 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2000156 : term108 = term109.
Proof. exact (MK_COMB (@lem2000155) (@lem2000154)). Qed.
Lemma lem2000157 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem2000158 : term110 = term78.
Proof. exact (MK_COMB (@lem2000156) (@lem2000157)). Qed.
Lemma lem2000160 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2000161 : term78 = term2.
Proof. exact (@lem2000160 term15). Qed.
Lemma lem2000162 : term110 = term2.
Proof. exact (TRANS (@lem2000158) (@lem2000161)). Qed.
Lemma lem2000164 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2000165 : term26 = term27.
Proof. exact (@lem2000164 term15 term15). Qed.
Lemma lem2000166 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2000167 : term29 = term15.
Proof. exact (EQ_MP (@lem2000166) (@lem940073)). Qed.
Lemma lem2000168 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2000169 : term27 = term5.
Proof. exact (MK_COMB (@lem2000168) (@lem2000167)). Qed.
Lemma lem2000170 : term26 = term5.
Proof. exact (TRANS (@lem2000165) (@lem2000169)). Qed.
Lemma lem2000171 : term109 = term109.
Proof. exact (eq_refl term109). Qed.
Lemma lem2000172 : term111 = term78.
Proof. exact (MK_COMB (@lem2000171) (@lem2000170)). Qed.
Lemma lem2000174 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2000175 : term78 = term2.
Proof. exact (@lem2000174 term15). Qed.
Lemma lem2000176 : term111 = term2.
Proof. exact (TRANS (@lem2000172) (@lem2000175)). Qed.
Lemma lem2000177 : term2 = term111.
Proof. exact (SYM (@lem2000176)). Qed.
Lemma lem2000178 : term110 = term111.
Proof. exact (TRANS (@lem2000162) (@lem2000177)). Qed.
Lemma lem2000179 : term100 = term67.
Proof. exact (@lem2000129 (@lem2000178)). Qed.
Lemma lem2000180 : term99 = term67.
Proof. exact (TRANS (@lem2000095) (@lem2000179)). Qed.
Lemma lem2000182 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2000183 : term67 = term2.
Proof. exact (@lem2000182 term2). Qed.
Lemma lem2000184 : term99 = term2.
Proof. exact (TRANS (@lem2000180) (@lem2000183)). Qed.
Lemma lem2000185 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2000186 : term112 = term109.
Proof. exact (MK_COMB (@lem2000185) (@lem2000184)). Qed.
Lemma lem2000187 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2000188 (x : real) : (term97 x) = (term113 x).
Proof. exact (MK_COMB (@lem2000186) (@lem2000187 x)). Qed.
Lemma lem2000189 (x : real) : (term96 x) = (term113 x).
Proof. exact (TRANS (@lem2000086 x) (@lem2000188 x)). Qed.
Lemma lem2000190 (x : real) : (term113 x) = term2.
Proof. exact (@lem1982719 x). Qed.
Lemma lem2000191 (x : real) : (term96 x) = term2.
Proof. exact (TRANS (@lem2000189 x) (@lem2000190 x)). Qed.
Lemma lem2000192 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2000193 (x : real) : (term114 x) = term38.
Proof. exact (MK_COMB (@lem2000192) (@lem2000191 x)). Qed.
Lemma lem2000195 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2000196 : term12 = term18.
Proof. exact (@lem2000195 term15). Qed.
Lemma lem2000198 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2000199 : term12 = term18.
Proof. exact (@lem2000198 term15). Qed.
Lemma lem2000200 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2000201 : term47 = term98.
Proof. exact (MK_COMB (@lem2000200) (@lem2000199)). Qed.
Lemma lem2000202 : term115 = term116.
Proof. exact (MK_COMB (@lem2000201) (@lem2000196)). Qed.
Lemma lem2000203 : term117.
Proof. exact (@lem1981473 term12 term5 term12 term5 term118 term5). Qed.
Lemma lem2000205 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2000206 : term66 = term73.
Proof. exact (@lem2000205 (NUMERAL 0) term15). Qed.
Lemma lem2000207 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2000208 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2000209 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2000208 h1) (fun h1 : term73 = True => @lem2000207)). Qed.
Lemma lem2000210 : term73 = True.
Proof. exact (EQ_MP (@lem2000209) (@lem2000207)). Qed.
Lemma lem2000211 : term66 = True.
Proof. exact (TRANS (@lem2000206) (@lem2000210)). Qed.
Lemma lem2000212 : True = term66.
Proof. exact (SYM (@lem2000211)). Qed.
Lemma lem2000213 : term66.
Proof. exact (EQ_MP (@lem2000212) (@lem0)). Qed.
Lemma lem2000214 : term119.
Proof. exact (@lem2000203 (@lem2000213)). Qed.
Lemma lem2000216 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2000217 : term66 = term73.
Proof. exact (@lem2000216 (NUMERAL 0) term15). Qed.
Lemma lem2000218 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2000219 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2000220 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2000219 h1) (fun h1 : term73 = True => @lem2000218)). Qed.
Lemma lem2000221 : term73 = True.
Proof. exact (EQ_MP (@lem2000220) (@lem2000218)). Qed.
Lemma lem2000222 : term66 = True.
Proof. exact (TRANS (@lem2000217) (@lem2000221)). Qed.
Lemma lem2000223 : True = term66.
Proof. exact (SYM (@lem2000222)). Qed.
Lemma lem2000224 : term66.
Proof. exact (EQ_MP (@lem2000223) (@lem0)). Qed.
Lemma lem2000225 : term120.
Proof. exact (@lem2000214 (@lem2000224)). Qed.
Lemma lem2000227 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2000228 : term66 = term73.
Proof. exact (@lem2000227 (NUMERAL 0) term15). Qed.
Lemma lem2000229 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2000230 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2000231 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2000230 h1) (fun h1 : term73 = True => @lem2000229)). Qed.
Lemma lem2000232 : term73 = True.
Proof. exact (EQ_MP (@lem2000231) (@lem2000229)). Qed.
Lemma lem2000233 : term66 = True.
Proof. exact (TRANS (@lem2000228) (@lem2000232)). Qed.
Lemma lem2000234 : True = term66.
Proof. exact (SYM (@lem2000233)). Qed.
Lemma lem2000235 : term66.
Proof. exact (EQ_MP (@lem2000234) (@lem0)). Qed.
Lemma lem2000236 : term121.
Proof. exact (@lem2000225 (@lem2000235)). Qed.
Lemma lem2000238 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2000239 : term21 = term32.
Proof. exact (@lem2000238 term15 term15). Qed.
Lemma lem2000240 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2000241 : term29 = term15.
Proof. exact (EQ_MP (@lem2000240) (@lem940073)). Qed.
Lemma lem2000242 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2000243 : term27 = term5.
Proof. exact (MK_COMB (@lem2000242) (@lem2000241)). Qed.
Lemma lem2000244 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2000245 : term32 = term12.
Proof. exact (MK_COMB (@lem2000244) (@lem2000243)). Qed.
Lemma lem2000246 : term21 = term12.
Proof. exact (TRANS (@lem2000239) (@lem2000245)). Qed.
Lemma lem2000248 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2000249 : term21 = term32.
Proof. exact (@lem2000248 term15 term15). Qed.
Lemma lem2000250 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2000251 : term29 = term15.
Proof. exact (EQ_MP (@lem2000250) (@lem940073)). Qed.
Lemma lem2000252 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2000253 : term27 = term5.
Proof. exact (MK_COMB (@lem2000252) (@lem2000251)). Qed.
Lemma lem2000254 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2000255 : term32 = term12.
Proof. exact (MK_COMB (@lem2000254) (@lem2000253)). Qed.
Lemma lem2000256 : term21 = term12.
Proof. exact (TRANS (@lem2000249) (@lem2000255)). Qed.
Lemma lem2000257 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2000258 : term105 = term47.
Proof. exact (MK_COMB (@lem2000257) (@lem2000256)). Qed.
Lemma lem2000259 : term122 = term115.
Proof. exact (MK_COMB (@lem2000258) (@lem2000246)). Qed.
Lemma lem2000260 : term115 = term123.
Proof. exact (@lem1367763 term15 term15). Qed.
Lemma lem2000261 : term124 = term125.
Proof. exact (@lem706885). Qed.
Lemma lem2000262 : (term124 = term125) = (term126 = term127).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term125). Qed.
Lemma lem2000263 : term126 = term127.
Proof. exact (EQ_MP (@lem2000262) (@lem2000261)). Qed.
Lemma lem2000264 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2000265 : term128 = term129.
Proof. exact (MK_COMB (@lem2000264) (@lem2000263)). Qed.
Lemma lem2000266 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2000267 : term123 = term118.
Proof. exact (MK_COMB (@lem2000266) (@lem2000265)). Qed.
Lemma lem2000268 : term115 = term118.
Proof. exact (TRANS (@lem2000260) (@lem2000267)). Qed.
Lemma lem2000269 : term122 = term118.
Proof. exact (TRANS (@lem2000259) (@lem2000268)). Qed.
Lemma lem2000270 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2000271 : term130 = term131.
Proof. exact (MK_COMB (@lem2000270) (@lem2000269)). Qed.
Lemma lem2000272 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem2000273 : term132 = term133.
Proof. exact (MK_COMB (@lem2000271) (@lem2000272)). Qed.
Lemma lem2000275 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2000276 : term133 = term134.
Proof. exact (@lem2000275 term127 term15). Qed.
Lemma lem2000277 : term135 = term125.
Proof. exact (@lem996237 term125). Qed.
Lemma lem2000278 : (term135 = term125) = (term136 = term127).
Proof. exact (@lem1007663 term125 (BIT1 0) term125). Qed.
Lemma lem2000279 : term136 = term127.
Proof. exact (EQ_MP (@lem2000278) (@lem2000277)). Qed.
Lemma lem2000280 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2000281 : term137 = term129.
Proof. exact (MK_COMB (@lem2000280) (@lem2000279)). Qed.
Lemma lem2000282 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2000283 : term134 = term118.
Proof. exact (MK_COMB (@lem2000282) (@lem2000281)). Qed.
Lemma lem2000284 : term133 = term118.
Proof. exact (TRANS (@lem2000276) (@lem2000283)). Qed.
Lemma lem2000285 : term132 = term118.
Proof. exact (TRANS (@lem2000273) (@lem2000284)). Qed.
Lemma lem2000287 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2000288 : term26 = term27.
Proof. exact (@lem2000287 term15 term15). Qed.
Lemma lem2000289 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2000290 : term29 = term15.
Proof. exact (EQ_MP (@lem2000289) (@lem940073)). Qed.
Lemma lem2000291 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2000292 : term27 = term5.
Proof. exact (MK_COMB (@lem2000291) (@lem2000290)). Qed.
Lemma lem2000293 : term26 = term5.
Proof. exact (TRANS (@lem2000288) (@lem2000292)). Qed.
Lemma lem2000294 : term131 = term131.
Proof. exact (eq_refl term131). Qed.
Lemma lem2000295 : term138 = term133.
Proof. exact (MK_COMB (@lem2000294) (@lem2000293)). Qed.
Lemma lem2000297 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2000298 : term133 = term134.
Proof. exact (@lem2000297 term127 term15). Qed.
Lemma lem2000299 : term135 = term125.
Proof. exact (@lem996237 term125). Qed.
Lemma lem2000300 : (term135 = term125) = (term136 = term127).
Proof. exact (@lem1007663 term125 (BIT1 0) term125). Qed.
Lemma lem2000301 : term136 = term127.
Proof. exact (EQ_MP (@lem2000300) (@lem2000299)). Qed.
Lemma lem2000302 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2000303 : term137 = term129.
Proof. exact (MK_COMB (@lem2000302) (@lem2000301)). Qed.
Lemma lem2000304 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2000305 : term134 = term118.
Proof. exact (MK_COMB (@lem2000304) (@lem2000303)). Qed.
Lemma lem2000306 : term133 = term118.
Proof. exact (TRANS (@lem2000298) (@lem2000305)). Qed.
Lemma lem2000307 : term138 = term118.
Proof. exact (TRANS (@lem2000295) (@lem2000306)). Qed.
Lemma lem2000308 : term118 = term138.
Proof. exact (SYM (@lem2000307)). Qed.
Lemma lem2000309 : term132 = term138.
Proof. exact (TRANS (@lem2000285) (@lem2000308)). Qed.
Lemma lem2000310 : term116 = term139.
Proof. exact (@lem2000236 (@lem2000309)). Qed.
Lemma lem2000311 : term115 = term139.
Proof. exact (TRANS (@lem2000202) (@lem2000310)). Qed.
Lemma lem2000313 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2000314 : term139 = term118.
Proof. exact (@lem2000313 term118). Qed.
Lemma lem2000315 : term115 = term118.
Proof. exact (TRANS (@lem2000311) (@lem2000314)). Qed.
Lemma lem2000316 (x : real) : (term95 x) = term140.
Proof. exact (MK_COMB (@lem2000193 x) (@lem2000315)). Qed.
Lemma lem2000317 (x : real) : (term94 x) = term140.
Proof. exact (TRANS (@lem2000085 x) (@lem2000316 x)). Qed.
Lemma lem2000318 : term140 = term118.
Proof. exact (@lem1982721 term118). Qed.
Lemma lem2000319 (x : real) : (term94 x) = term118.
Proof. exact (TRANS (@lem2000317 x) (@lem2000318)). Qed.
Lemma lem2000320 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2000321 (x : real) : (term141 x) = term142.
Proof. exact (MK_COMB (@lem2000320) (@lem2000319 x)). Qed.
Lemma lem2000322 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2000323 (x : real) : (term93 x) = term143.
Proof. exact (MK_COMB (@lem2000321 x) (@lem2000322)). Qed.
Lemma lem2000324 (x : real) (h1 : term64 x) : term143.
Proof. exact (EQ_MP (@lem2000323 x) (@lem2000084 x h1)). Qed.
Lemma lem2000326 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2000327 : term143 = term144.
Proof. exact (@lem2000326 term2 term118). Qed.
Lemma lem2000329 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2000330 : term118 = term139.
Proof. exact (@lem2000329 term127). Qed.
Lemma lem2000332 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2000333 : term2 = term67.
Proof. exact (@lem2000332 (NUMERAL 0)). Qed.
Lemma lem2000334 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2000335 : term145 = term146.
Proof. exact (MK_COMB (@lem2000334) (@lem2000333)). Qed.
Lemma lem2000336 : term144 = term147.
Proof. exact (MK_COMB (@lem2000335) (@lem2000330)). Qed.
Lemma lem2000337 : term148.
Proof. exact (@lem1980026 term2 term5 term118 term5). Qed.
Lemma lem2000339 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2000340 : term66 = term73.
Proof. exact (@lem2000339 (NUMERAL 0) term15). Qed.
Lemma lem2000341 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2000342 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2000343 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2000342 h1) (fun h1 : term73 = True => @lem2000341)). Qed.
Lemma lem2000344 : term73 = True.
Proof. exact (EQ_MP (@lem2000343) (@lem2000341)). Qed.
Lemma lem2000345 : term66 = True.
Proof. exact (TRANS (@lem2000340) (@lem2000344)). Qed.
Lemma lem2000346 : True = term66.
Proof. exact (SYM (@lem2000345)). Qed.
Lemma lem2000347 : term66.
Proof. exact (EQ_MP (@lem2000346) (@lem0)). Qed.
Lemma lem2000348 : term149.
Proof. exact (@lem2000337 (@lem2000347)). Qed.
Lemma lem2000350 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2000351 : term66 = term73.
Proof. exact (@lem2000350 (NUMERAL 0) term15). Qed.
Lemma lem2000352 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2000353 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2000354 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2000353 h1) (fun h1 : term73 = True => @lem2000352)). Qed.
Lemma lem2000355 : term73 = True.
Proof. exact (EQ_MP (@lem2000354) (@lem2000352)). Qed.
Lemma lem2000356 : term66 = True.
Proof. exact (TRANS (@lem2000351) (@lem2000355)). Qed.
Lemma lem2000357 : True = term66.
Proof. exact (SYM (@lem2000356)). Qed.
Lemma lem2000358 : term66.
Proof. exact (EQ_MP (@lem2000357) (@lem0)). Qed.
Lemma lem2000359 : term147 = term150.
Proof. exact (@lem2000348 (@lem2000358)). Qed.
Lemma lem2000361 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2000362 : term133 = term134.
Proof. exact (@lem2000361 term127 term15). Qed.
Lemma lem2000363 : term135 = term125.
Proof. exact (@lem996237 term125). Qed.
Lemma lem2000364 : (term135 = term125) = (term136 = term127).
Proof. exact (@lem1007663 term125 (BIT1 0) term125). Qed.
Lemma lem2000365 : term136 = term127.
Proof. exact (EQ_MP (@lem2000364) (@lem2000363)). Qed.
Lemma lem2000366 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2000367 : term137 = term129.
Proof. exact (MK_COMB (@lem2000366) (@lem2000365)). Qed.
Lemma lem2000368 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2000369 : term134 = term118.
Proof. exact (MK_COMB (@lem2000368) (@lem2000367)). Qed.
Lemma lem2000370 : term133 = term118.
Proof. exact (TRANS (@lem2000362) (@lem2000369)). Qed.
Lemma lem2000372 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2000373 : term78 = term2.
Proof. exact (@lem2000372 term15). Qed.
Lemma lem2000374 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2000375 : term151 = term145.
Proof. exact (MK_COMB (@lem2000374) (@lem2000373)). Qed.
Lemma lem2000376 : term150 = term144.
Proof. exact (MK_COMB (@lem2000375) (@lem2000370)). Qed.
Lemma lem2000378 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2000379 : term144 = term154.
Proof. exact (@lem2000378 (NUMERAL 0) term127). Qed.
Lemma lem2000380 : term155 = term125.
Proof. exact (@lem912803). Qed.
Lemma lem2000381 (h1 : term155 = term125) : (term127 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term125 h1). Qed.
Lemma lem2000382 : (term155 = term125) = ((term127 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term155 = term125 => @lem2000381 h1) (fun h1 : (term127 = (NUMERAL 0)) = False => @lem2000380)). Qed.
Lemma lem2000383 : (term127 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2000382) (@lem2000380)). Qed.
Lemma lem2000384 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2000385 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2000386 : term156 = (and True).
Proof. exact (MK_COMB (@lem2000385) (@lem2000384)). Qed.
Lemma lem2000387 : term154 = (True /\ False).
Proof. exact (MK_COMB (@lem2000386) (@lem2000383)). Qed.
Lemma lem2000389 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2000390 : term154 = False.
Proof. exact (TRANS (@lem2000387) (@lem2000389)). Qed.
Lemma lem2000391 : term144 = False.
Proof. exact (TRANS (@lem2000379) (@lem2000390)). Qed.
Lemma lem2000392 : term150 = False.
Proof. exact (TRANS (@lem2000376) (@lem2000391)). Qed.
Lemma lem2000393 : term147 = False.
Proof. exact (TRANS (@lem2000359) (@lem2000392)). Qed.
Lemma lem2000394 : term144 = False.
Proof. exact (TRANS (@lem2000336) (@lem2000393)). Qed.
Lemma lem2000395 : term143 = False.
Proof. exact (TRANS (@lem2000327) (@lem2000394)). Qed.
Lemma lem2000396 (x : real) (h1 : term64 x) : False.
Proof. exact (EQ_MP (@lem2000395) (@lem2000324 x h1)). Qed.
Lemma lem2000397 (x : real) (h1 : term42 x) : term42 x.
Proof. exact (h1). Qed.
Lemma lem2000398 (x : real) (h1 : term42 x) : term64 x.
Proof. exact (EQ_MP (@lem1999928 x) (@lem2000397 x h1)). Qed.
Lemma lem2000399 (x : real) (h1 : term42 x) : (term64 x) = False.
Proof. exact (prop_ext (fun h2 : term64 x => @lem2000396 x h2) (fun h2 : False => @lem2000398 x h1)). Qed.
Lemma lem2000400 (x : real) (h1 : term42 x) : False.
Proof. exact (EQ_MP (@lem2000399 x h1) (@lem2000398 x h1)). Qed.
Lemma lem2000401 (x : real) (h1 : term0 x) : term0 x.
Proof. exact (h1). Qed.
Lemma lem2000402 (x : real) (h1 : term0 x) : term42 x.
Proof. exact (EQ_MP (@lem1999885 x) (@lem2000401 x h1)). Qed.
Lemma lem2000403 (x : real) (h1 : term0 x) : (term42 x) = False.
Proof. exact (prop_ext (fun h2 : term42 x => @lem2000400 x h2) (fun h2 : False => @lem2000402 x h1)). Qed.
Lemma lem2000404 (x : real) (h1 : term0 x) : False.
Proof. exact (EQ_MP (@lem2000403 x h1) (@lem2000402 x h1)). Qed.
Lemma lem2000405 (x : real) : term157 x.
Proof. exact (fun h0 : term0 x => @lem2000404 x h0). Qed.
Lemma lem2000406 (x : real) : term158 x.
Proof. exact (@lem1386578 (term159 x)). Qed.
Lemma lem2000409 (x : real) : term159 x.
Proof. exact (@lem2000406 x (@lem2000405 x)). Qed.
Lemma lem2000410 (x : real) : (term159 x) = ((term159 x) = True).
Proof. exact (@lem7 (term159 x)). Qed.
Lemma lem2000412 (x : real) : term160 x.
Proof. exact (@lem1629051 x). Qed.
Lemma lem2000413 (x : real) : (term160 x) = (term161 x).
Proof. exact (eq_refl (term160 x)). Qed.
Lemma lem2000414 (x : real) : term161 x.
Proof. exact (EQ_MP (@lem2000413 x) (@lem2000412 x)). Qed.
Lemma lem2000415 (x : real) (y : real) : term162 x y.
Proof. exact (@lem2000414 x y). Qed.
Lemma lem2000416 (x : real) (y : real) : (term162 x y) = (term163 x y).
Proof. exact (eq_refl (term162 x y)). Qed.
Lemma lem2000417 (x : real) (y : real) : term163 x y.
Proof. exact (EQ_MP (@lem2000416 x y) (@lem2000415 x y)). Qed.
Lemma lem2000418 (x : real) (y : real) (z : real) : term164 x y z.
Proof. exact (@lem2000417 x y z). Qed.
Lemma lem2000419 (x : real) (y : real) (z : real) : (term164 x y z) = (term165 x y z).
Proof. exact (eq_refl (term164 x y z)). Qed.
Lemma lem2000420 (x : real) (y : real) (z : real) : term165 x y z.
Proof. exact (EQ_MP (@lem2000419 x y z) (@lem2000418 x y z)). Qed.
Lemma lem2000421 (z : real) (h1 : term166 z) : term166 z.
Proof. exact (h1). Qed.
Lemma lem2000422 (x : real) (y : real) (z : real) (h1 : term166 z) : (term167 x z y) = (term168 x y z).
Proof. exact (@lem2000420 x y z (@lem2000421 z h1)). Qed.
Lemma lem2000438 (x : real) : (term169 x) = (term170 x).
Proof. exact (@lem1988318 (term171 x) (term3 x)). Qed.
Lemma lem2000447 (x : real) : (term3 x) = (term4 x).
Proof. exact (@lem1982761 (real_abs x) term5). Qed.
Lemma lem2000456 (x : real) : (term3 x) = (term4 x).
Proof. exact (@lem1982761 (real_abs x) term5). Qed.
Lemma lem2000457 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2000458 (x : real) : (term171 x) = (term172 x).
Proof. exact (MK_COMB (@lem2000457) (@lem2000456 x)). Qed.
Lemma lem2000459 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2000460 (x : real) : (term173 x) = (term174 x).
Proof. exact (MK_COMB (@lem2000459) (@lem2000458 x)). Qed.
Lemma lem2000461 (x : real) : (term175 x) = (term176 x).
Proof. exact (MK_COMB (@lem2000460 x) (@lem2000447 x)). Qed.
Lemma lem2000462 (x : real) : (term176 x) = (term177 x).
Proof. exact (@lem1982792 (term172 x) (term4 x)). Qed.
Lemma lem2000463 (x : real) : (term10 x) = (term11 x).
Proof. exact (@lem1982781 (real_abs x) term12 term5). Qed.
Lemma lem2000465 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2000466 : term5 = term14.
Proof. exact (@lem2000465 term15). Qed.
Lemma lem2000468 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2000469 : term12 = term18.
Proof. exact (@lem2000468 term15). Qed.
Lemma lem2000470 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2000471 : term19 = term20.
Proof. exact (MK_COMB (@lem2000470) (@lem2000469)). Qed.
Lemma lem2000472 : term21 = term22.
Proof. exact (MK_COMB (@lem2000471) (@lem2000466)). Qed.
Lemma lem2000473 : term22 = term23.
Proof. exact (@lem1981613 term12 term5 term5 term5). Qed.
Lemma lem2000475 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2000476 : term26 = term27.
Proof. exact (@lem2000475 term15 term15). Qed.
Lemma lem2000477 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2000478 : term29 = term15.
Proof. exact (EQ_MP (@lem2000477) (@lem940073)). Qed.
Lemma lem2000479 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2000480 : term27 = term5.
Proof. exact (MK_COMB (@lem2000479) (@lem2000478)). Qed.
Lemma lem2000481 : term26 = term5.
Proof. exact (TRANS (@lem2000476) (@lem2000480)). Qed.
Lemma lem2000483 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2000484 : term21 = term32.
Proof. exact (@lem2000483 term15 term15). Qed.
Lemma lem2000485 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2000486 : term29 = term15.
Proof. exact (EQ_MP (@lem2000485) (@lem940073)). Qed.
Lemma lem2000487 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2000488 : term27 = term5.
Proof. exact (MK_COMB (@lem2000487) (@lem2000486)). Qed.
Lemma lem2000489 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2000490 : term32 = term12.
Proof. exact (MK_COMB (@lem2000489) (@lem2000488)). Qed.
Lemma lem2000491 : term21 = term12.
Proof. exact (TRANS (@lem2000484) (@lem2000490)). Qed.
Lemma lem2000492 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2000493 : term33 = term34.
Proof. exact (MK_COMB (@lem2000492) (@lem2000491)). Qed.
Lemma lem2000494 : term23 = term18.
Proof. exact (MK_COMB (@lem2000493) (@lem2000481)). Qed.
Lemma lem2000495 : term22 = term18.
Proof. exact (TRANS (@lem2000473) (@lem2000494)). Qed.
Lemma lem2000496 : term21 = term18.
Proof. exact (TRANS (@lem2000472) (@lem2000495)). Qed.
Lemma lem2000498 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2000499 : term18 = term12.
Proof. exact (@lem2000498 term12). Qed.
Lemma lem2000500 : term21 = term12.
Proof. exact (TRANS (@lem2000496) (@lem2000499)). Qed.
Lemma lem2000503 (x : real) : (term36 x) = (term36 x).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem2000504 (x : real) : (term11 x) = (term37 x).
Proof. exact (MK_COMB (@lem2000503 x) (@lem2000500)). Qed.
Lemma lem2000505 (x : real) : (term10 x) = (term37 x).
Proof. exact (TRANS (@lem2000463 x) (@lem2000504 x)). Qed.
Lemma lem2000506 (x : real) : (term178 x) = (term178 x).
Proof. exact (eq_refl (term178 x)). Qed.
Lemma lem2000507 (x : real) : (term177 x) = (term179 x).
Proof. exact (MK_COMB (@lem2000506 x) (@lem2000505 x)). Qed.
Lemma lem2000512 (x : real) : (term179 x) = (term180 x).
Proof. exact (@lem1982757 (term181 x) (term172 x) term12). Qed.
Lemma lem2000513 (x : real) : (term177 x) = (term180 x).
Proof. exact (TRANS (@lem2000507 x) (@lem2000512 x)). Qed.
Lemma lem2000514 (x : real) : (term176 x) = (term180 x).
Proof. exact (TRANS (@lem2000462 x) (@lem2000513 x)). Qed.
Lemma lem2000515 (x : real) : (term175 x) = (term180 x).
Proof. exact (TRANS (@lem2000461 x) (@lem2000514 x)). Qed.
Lemma lem2000516 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2000517 (x : real) : (term182 x) = (term183 x).
Proof. exact (MK_COMB (@lem2000516) (@lem2000515 x)). Qed.
Lemma lem2000518 (x : real) : (term183 x) = (term184 x).
Proof. exact (@lem1982785 (term180 x)). Qed.
Lemma lem2000519 (x : real) : (term184 x) = (term185 x).
Proof. exact (@lem1982781 (term181 x) term12 (term186 x)). Qed.
Lemma lem2000520 (x : real) : (term187 x) = (term188 x).
Proof. exact (@lem1982781 (term172 x) term12 term12). Qed.
Lemma lem2000522 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2000523 : term12 = term18.
Proof. exact (@lem2000522 term15). Qed.
Lemma lem2000525 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2000526 : term12 = term18.
Proof. exact (@lem2000525 term15). Qed.
Lemma lem2000527 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2000528 : term19 = term20.
Proof. exact (MK_COMB (@lem2000527) (@lem2000526)). Qed.
Lemma lem2000529 : term189 = term190.
Proof. exact (MK_COMB (@lem2000528) (@lem2000523)). Qed.
Lemma lem2000530 : term190 = term191.
Proof. exact (@lem1981613 term12 term12 term5 term5). Qed.
Lemma lem2000532 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2000533 : term26 = term27.
Proof. exact (@lem2000532 term15 term15). Qed.
Lemma lem2000534 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2000535 : term29 = term15.
Proof. exact (EQ_MP (@lem2000534) (@lem940073)). Qed.
Lemma lem2000536 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2000537 : term27 = term5.
Proof. exact (MK_COMB (@lem2000536) (@lem2000535)). Qed.
Lemma lem2000538 : term26 = term5.
Proof. exact (TRANS (@lem2000533) (@lem2000537)). Qed.
Lemma lem2000540 (m : nat) (n : nat) : (term192 m n) = (term25 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2000541 : term189 = term27.
Proof. exact (@lem2000540 term15 term15). Qed.
Lemma lem2000542 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2000543 : term29 = term15.
Proof. exact (EQ_MP (@lem2000542) (@lem940073)). Qed.
Lemma lem2000544 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2000545 : term27 = term5.
Proof. exact (MK_COMB (@lem2000544) (@lem2000543)). Qed.
Lemma lem2000546 : term189 = term5.
Proof. exact (TRANS (@lem2000541) (@lem2000545)). Qed.
Lemma lem2000547 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2000548 : term193 = term194.
Proof. exact (MK_COMB (@lem2000547) (@lem2000546)). Qed.
Lemma lem2000549 : term191 = term14.
Proof. exact (MK_COMB (@lem2000548) (@lem2000538)). Qed.
Lemma lem2000550 : term190 = term14.
Proof. exact (TRANS (@lem2000530) (@lem2000549)). Qed.
Lemma lem2000551 : term189 = term14.
Proof. exact (TRANS (@lem2000529) (@lem2000550)). Qed.
Lemma lem2000553 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2000554 : term14 = term5.
Proof. exact (@lem2000553 term5). Qed.
Lemma lem2000555 : term189 = term5.
Proof. exact (TRANS (@lem2000551) (@lem2000554)). Qed.
Lemma lem2000558 (x : real) : (term195 x) = (term195 x).
Proof. exact (eq_refl (term195 x)). Qed.
Lemma lem2000559 (x : real) : (term188 x) = (term196 x).
Proof. exact (MK_COMB (@lem2000558 x) (@lem2000555)). Qed.
Lemma lem2000560 (x : real) : (term187 x) = (term196 x).
Proof. exact (TRANS (@lem2000520 x) (@lem2000559 x)). Qed.
Lemma lem2000561 (x : real) : (term197 x) = (term198 x).
Proof. exact (@lem1982749 term12 term12 (real_abs x)). Qed.
Lemma lem2000563 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2000564 : term12 = term18.
Proof. exact (@lem2000563 term15). Qed.
Lemma lem2000566 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2000567 : term12 = term18.
Proof. exact (@lem2000566 term15). Qed.
Lemma lem2000568 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2000569 : term19 = term20.
Proof. exact (MK_COMB (@lem2000568) (@lem2000567)). Qed.
Lemma lem2000570 : term189 = term190.
Proof. exact (MK_COMB (@lem2000569) (@lem2000564)). Qed.
Lemma lem2000571 : term190 = term191.
Proof. exact (@lem1981613 term12 term12 term5 term5). Qed.
Lemma lem2000573 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2000574 : term26 = term27.
Proof. exact (@lem2000573 term15 term15). Qed.
Lemma lem2000575 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2000576 : term29 = term15.
Proof. exact (EQ_MP (@lem2000575) (@lem940073)). Qed.
Lemma lem2000577 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2000578 : term27 = term5.
Proof. exact (MK_COMB (@lem2000577) (@lem2000576)). Qed.
Lemma lem2000579 : term26 = term5.
Proof. exact (TRANS (@lem2000574) (@lem2000578)). Qed.
Lemma lem2000581 (m : nat) (n : nat) : (term192 m n) = (term25 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2000582 : term189 = term27.
Proof. exact (@lem2000581 term15 term15). Qed.
Lemma lem2000583 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2000584 : term29 = term15.
Proof. exact (EQ_MP (@lem2000583) (@lem940073)). Qed.
Lemma lem2000585 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2000586 : term27 = term5.
Proof. exact (MK_COMB (@lem2000585) (@lem2000584)). Qed.
Lemma lem2000587 : term189 = term5.
Proof. exact (TRANS (@lem2000582) (@lem2000586)). Qed.
Lemma lem2000588 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2000589 : term193 = term194.
Proof. exact (MK_COMB (@lem2000588) (@lem2000587)). Qed.
Lemma lem2000590 : term191 = term14.
Proof. exact (MK_COMB (@lem2000589) (@lem2000579)). Qed.
Lemma lem2000591 : term190 = term14.
Proof. exact (TRANS (@lem2000571) (@lem2000590)). Qed.
Lemma lem2000592 : term189 = term14.
Proof. exact (TRANS (@lem2000570) (@lem2000591)). Qed.
Lemma lem2000594 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2000595 : term14 = term5.
Proof. exact (@lem2000594 term5). Qed.
Lemma lem2000596 : term189 = term5.
Proof. exact (TRANS (@lem2000592) (@lem2000595)). Qed.
Lemma lem2000597 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2000598 : term199 = term200.
Proof. exact (MK_COMB (@lem2000597) (@lem2000596)). Qed.
Lemma lem2000599 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem2000600 (x : real) : (term198 x) = (term201 x).
Proof. exact (MK_COMB (@lem2000598) (@lem2000599 x)). Qed.
Lemma lem2000601 (x : real) : (term197 x) = (term201 x).
Proof. exact (TRANS (@lem2000561 x) (@lem2000600 x)). Qed.
Lemma lem2000602 (x : real) : (term201 x) = (real_abs x).
Proof. exact (@lem1982709 (real_abs x)). Qed.
Lemma lem2000603 (x : real) : (term197 x) = (real_abs x).
Proof. exact (TRANS (@lem2000601 x) (@lem2000602 x)). Qed.
Lemma lem2000604 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2000605 (x : real) : (term202 x) = (term203 x).
Proof. exact (MK_COMB (@lem2000604) (@lem2000603 x)). Qed.
Lemma lem2000606 (x : real) : (term185 x) = (term204 x).
Proof. exact (MK_COMB (@lem2000605 x) (@lem2000560 x)). Qed.
Lemma lem2000607 (x : real) : (term184 x) = (term204 x).
Proof. exact (TRANS (@lem2000519 x) (@lem2000606 x)). Qed.
Lemma lem2000608 (x : real) : (term183 x) = (term204 x).
Proof. exact (TRANS (@lem2000518 x) (@lem2000607 x)). Qed.
Lemma lem2000609 (x : real) : (term205 x) = (term205 x).
Proof. exact (eq_refl (term205 x)). Qed.
Lemma lem2000610 (x : real) : ((term182 x) = (term183 x)) = ((term182 x) = (term204 x)).
Proof. exact (MK_COMB (@lem2000609 x) (@lem2000608 x)). Qed.
Lemma lem2000611 (x : real) : (term182 x) = (term204 x).
Proof. exact (EQ_MP (@lem2000610 x) (@lem2000517 x)). Qed.
Lemma lem2000612 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2000613 (x : real) : (term206 x) = (term207 x).
Proof. exact (MK_COMB (@lem2000612) (@lem2000611 x)). Qed.
Lemma lem2000614 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2000615 (x : real) : (term208 x) = (term209 x).
Proof. exact (MK_COMB (@lem2000613 x) (@lem2000614)). Qed.
Lemma lem2000616 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2000617 (x : real) : (term210 x) = (term211 x).
Proof. exact (MK_COMB (@lem2000616) (@lem2000515 x)). Qed.
Lemma lem2000618 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2000619 (x : real) : (term212 x) = (term213 x).
Proof. exact (MK_COMB (@lem2000617 x) (@lem2000618)). Qed.
Lemma lem2000620 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2000621 (x : real) : (term214 x) = (term215 x).
Proof. exact (MK_COMB (@lem2000620) (@lem2000619 x)). Qed.
Lemma lem2000622 (x : real) : (term170 x) = (term216 x).
Proof. exact (MK_COMB (@lem2000621 x) (@lem2000615 x)). Qed.
Lemma lem2000636 (x : real) : (term169 x) = (term216 x).
Proof. exact (TRANS (@lem2000438 x) (@lem2000622 x)). Qed.
Lemma lem2000638 (a : real) (x : real) (r : real) : (term217 x a r) = (term218 a x r).
Proof. exact (proj1 (@lem1482703 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2000639 (x : real) : (term213 x) = (term219 x).
Proof. exact (@lem2000638 (term186 x) x term2). Qed.
Lemma lem2000646 (x : real) : (term46 x) = x.
Proof. exact (@lem1982733 x). Qed.
Lemma lem2000665 (x : real) : (term220 x) = (term220 x).
Proof. exact (eq_refl (term220 x)). Qed.
Lemma lem2000666 (x : real) : (term221 x) = (term222 x).
Proof. exact (MK_COMB (@lem2000665 x) (@lem2000646 x)). Qed.
Lemma lem2000667 (x : real) : (term222 x) = (term223 x).
Proof. exact (@lem1982761 x (term186 x)). Qed.
Lemma lem2000668 (x : real) : (term221 x) = (term223 x).
Proof. exact (TRANS (@lem2000666 x) (@lem2000667 x)). Qed.
Lemma lem2000669 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2000670 (x : real) : (term224 x) = (term225 x).
Proof. exact (MK_COMB (@lem2000669) (@lem2000668 x)). Qed.
Lemma lem2000671 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2000672 (x : real) : (term226 x) = (term227 x).
Proof. exact (MK_COMB (@lem2000670 x) (@lem2000671)). Qed.
Lemma lem2000701 (x : real) : (term228 x) = (term229 x).
Proof. exact (@lem1982761 (term57 x) (term186 x)). Qed.
Lemma lem2000702 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2000703 (x : real) : (term230 x) = (term231 x).
Proof. exact (MK_COMB (@lem2000702) (@lem2000701 x)). Qed.
Lemma lem2000704 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2000705 (x : real) : (term232 x) = (term233 x).
Proof. exact (MK_COMB (@lem2000703 x) (@lem2000704)). Qed.
Lemma lem2000706 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2000707 (x : real) : (term234 x) = (term235 x).
Proof. exact (MK_COMB (@lem2000706) (@lem2000705 x)). Qed.
Lemma lem2000708 (x : real) : (term219 x) = (term236 x).
Proof. exact (MK_COMB (@lem2000707 x) (@lem2000672 x)). Qed.
Lemma lem2000709 (x : real) : (term213 x) = (term236 x).
Proof. exact (TRANS (@lem2000639 x) (@lem2000708 x)). Qed.
Lemma lem2000710 (x : real) : (term237 x) = (term236 x).
Proof. exact (eq_refl (term237 x)). Qed.
Lemma lem2000711 (x : real) : (term236 x) = (term237 x).
Proof. exact (SYM (@lem2000710 x)). Qed.
Lemma lem2000712 (x : real) : (term237 x) = (term238 x).
Proof. exact (@lem1482981 (term239 x) (term4 x)). Qed.
Lemma lem2000713 (x : real) : (term236 x) = (term238 x).
Proof. exact (TRANS (@lem2000711 x) (@lem2000712 x)). Qed.
Lemma lem2000714 (x : real) : (term240 x) = (term241 x).
Proof. exact (eq_refl (term240 x)). Qed.
Lemma lem2000715 (x : real) : (term242 x) = (term242 x).
Proof. exact (eq_refl (term242 x)). Qed.
Lemma lem2000716 (x : real) : (term243 x) = (term244 x).
Proof. exact (MK_COMB (@lem2000715 x) (@lem2000714 x)). Qed.
Lemma lem2000717 (x : real) : (term245 x) = (term246 x).
Proof. exact (eq_refl (term245 x)). Qed.
Lemma lem2000718 (x : real) : (term247 x) = (term247 x).
Proof. exact (eq_refl (term247 x)). Qed.
Lemma lem2000719 (x : real) : (term248 x) = (term249 x).
Proof. exact (MK_COMB (@lem2000718 x) (@lem2000717 x)). Qed.
Lemma lem2000720 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2000721 (x : real) : (term250 x) = (term251 x).
Proof. exact (MK_COMB (@lem2000720) (@lem2000719 x)). Qed.
Lemma lem2000722 (x : real) : (term238 x) = (term252 x).
Proof. exact (MK_COMB (@lem2000721 x) (@lem2000716 x)). Qed.
Lemma lem2000723 (x : real) : (term253 x) = (term253 x).
Proof. exact (eq_refl (term253 x)). Qed.
Lemma lem2000724 (x : real) : ((term236 x) = (term238 x)) = ((term236 x) = (term252 x)).
Proof. exact (MK_COMB (@lem2000723 x) (@lem2000722 x)). Qed.
Lemma lem2000725 (x : real) : (term236 x) = (term252 x).
Proof. exact (EQ_MP (@lem2000724 x) (@lem2000713 x)). Qed.
Lemma lem2000726 (x : real) : (term254 x) = (term255 x).
Proof. exact (@lem1988291 (term4 x) term2). Qed.
Lemma lem2000740 (x : real) : (term256 x) = (term257 x).
Proof. exact (@lem1982792 (term4 x) term2). Qed.
Lemma lem2000742 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2000743 : term2 = term67.
Proof. exact (@lem2000742 (NUMERAL 0)). Qed.
Lemma lem2000745 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2000746 : term12 = term18.
Proof. exact (@lem2000745 term15). Qed.
Lemma lem2000747 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2000748 : term19 = term20.
Proof. exact (MK_COMB (@lem2000747) (@lem2000746)). Qed.
Lemma lem2000749 : term258 = term259.
Proof. exact (MK_COMB (@lem2000748) (@lem2000743)). Qed.
Lemma lem2000750 : term259 = term260.
Proof. exact (@lem1981613 term12 term2 term5 term5). Qed.
Lemma lem2000752 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2000753 : term26 = term27.
Proof. exact (@lem2000752 term15 term15). Qed.
Lemma lem2000754 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2000755 : term29 = term15.
Proof. exact (EQ_MP (@lem2000754) (@lem940073)). Qed.
Lemma lem2000756 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2000757 : term27 = term5.
Proof. exact (MK_COMB (@lem2000756) (@lem2000755)). Qed.
Lemma lem2000758 : term26 = term5.
Proof. exact (TRANS (@lem2000753) (@lem2000757)). Qed.
Lemma lem2000760 (x : nat) : (term261 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2000761 : term258 = term2.
Proof. exact (@lem2000760 term15). Qed.
Lemma lem2000762 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2000763 : term262 = term263.
Proof. exact (MK_COMB (@lem2000762) (@lem2000761)). Qed.
Lemma lem2000764 : term260 = term67.
Proof. exact (MK_COMB (@lem2000763) (@lem2000758)). Qed.
Lemma lem2000765 : term259 = term67.
Proof. exact (TRANS (@lem2000750) (@lem2000764)). Qed.
Lemma lem2000766 : term258 = term67.
Proof. exact (TRANS (@lem2000749) (@lem2000765)). Qed.
Lemma lem2000768 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2000769 : term67 = term2.
Proof. exact (@lem2000768 term2). Qed.
Lemma lem2000770 : term258 = term2.
Proof. exact (TRANS (@lem2000766) (@lem2000769)). Qed.
Lemma lem2000771 (x : real) : (term264 x) = (term264 x).
Proof. exact (eq_refl (term264 x)). Qed.
Lemma lem2000772 (x : real) : (term257 x) = (term265 x).
Proof. exact (MK_COMB (@lem2000771 x) (@lem2000770)). Qed.
Lemma lem2000773 (x : real) : (term265 x) = (term4 x).
Proof. exact (@lem1982723 (term4 x)). Qed.
Lemma lem2000774 (x : real) : (term257 x) = (term4 x).
Proof. exact (TRANS (@lem2000772 x) (@lem2000773 x)). Qed.
Lemma lem2000776 (x : real) : (term256 x) = (term4 x).
Proof. exact (TRANS (@lem2000740 x) (@lem2000774 x)). Qed.
Lemma lem2000777 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2000778 (x : real) : (term266 x) = (term267 x).
Proof. exact (MK_COMB (@lem2000777) (@lem2000776 x)). Qed.
Lemma lem2000779 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2000780 (x : real) : (term255 x) = (term254 x).
Proof. exact (MK_COMB (@lem2000778 x) (@lem2000779)). Qed.
Lemma lem2000781 (x : real) : (term254 x) = (term254 x).
Proof. exact (TRANS (@lem2000726 x) (@lem2000780 x)). Qed.
Lemma lem2000782 (x : real) : (term268 x) = (term269 x).
Proof. exact (@lem1988289 (term270 x) term2). Qed.
Lemma lem2000783 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2000797 (x : real) : (term271 x) = (term272 x).
Proof. exact (@lem1982755 (real_abs x) term5 term12). Qed.
Lemma lem2000799 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2000800 : term12 = term18.
Proof. exact (@lem2000799 term15). Qed.
Lemma lem2000802 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2000803 : term5 = term14.
Proof. exact (@lem2000802 term15). Qed.
Lemma lem2000804 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2000805 : term273 = term274.
Proof. exact (MK_COMB (@lem2000804) (@lem2000803)). Qed.
Lemma lem2000806 : term275 = term276.
Proof. exact (MK_COMB (@lem2000805) (@lem2000800)). Qed.
Lemma lem2000807 : term277.
Proof. exact (@lem1981473 term5 term5 term12 term5 term2 term5). Qed.
Lemma lem2000809 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2000810 : term66 = term73.
Proof. exact (@lem2000809 (NUMERAL 0) term15). Qed.
Lemma lem2000811 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2000812 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2000813 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2000812 h1) (fun h1 : term73 = True => @lem2000811)). Qed.
Lemma lem2000814 : term73 = True.
Proof. exact (EQ_MP (@lem2000813) (@lem2000811)). Qed.
Lemma lem2000815 : term66 = True.
Proof. exact (TRANS (@lem2000810) (@lem2000814)). Qed.
Lemma lem2000816 : True = term66.
Proof. exact (SYM (@lem2000815)). Qed.
Lemma lem2000817 : term66.
Proof. exact (EQ_MP (@lem2000816) (@lem0)). Qed.
Lemma lem2000818 : term278.
Proof. exact (@lem2000807 (@lem2000817)). Qed.
Lemma lem2000820 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2000821 : term66 = term73.
Proof. exact (@lem2000820 (NUMERAL 0) term15). Qed.
Lemma lem2000822 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2000823 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2000824 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2000823 h1) (fun h1 : term73 = True => @lem2000822)). Qed.
Lemma lem2000825 : term73 = True.
Proof. exact (EQ_MP (@lem2000824) (@lem2000822)). Qed.
Lemma lem2000826 : term66 = True.
Proof. exact (TRANS (@lem2000821) (@lem2000825)). Qed.
Lemma lem2000827 : True = term66.
Proof. exact (SYM (@lem2000826)). Qed.
Lemma lem2000828 : term66.
Proof. exact (EQ_MP (@lem2000827) (@lem0)). Qed.
Lemma lem2000829 : term279.
Proof. exact (@lem2000818 (@lem2000828)). Qed.
Lemma lem2000831 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2000832 : term66 = term73.
Proof. exact (@lem2000831 (NUMERAL 0) term15). Qed.
Lemma lem2000833 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2000834 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2000835 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2000834 h1) (fun h1 : term73 = True => @lem2000833)). Qed.
Lemma lem2000836 : term73 = True.
Proof. exact (EQ_MP (@lem2000835) (@lem2000833)). Qed.
Lemma lem2000837 : term66 = True.
Proof. exact (TRANS (@lem2000832) (@lem2000836)). Qed.
Lemma lem2000838 : True = term66.
Proof. exact (SYM (@lem2000837)). Qed.
Lemma lem2000839 : term66.
Proof. exact (EQ_MP (@lem2000838) (@lem0)). Qed.
Lemma lem2000840 : term280.
Proof. exact (@lem2000829 (@lem2000839)). Qed.
Lemma lem2000842 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2000843 : term21 = term32.
Proof. exact (@lem2000842 term15 term15). Qed.
Lemma lem2000844 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2000845 : term29 = term15.
Proof. exact (EQ_MP (@lem2000844) (@lem940073)). Qed.
Lemma lem2000846 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2000847 : term27 = term5.
Proof. exact (MK_COMB (@lem2000846) (@lem2000845)). Qed.
Lemma lem2000848 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2000849 : term32 = term12.
Proof. exact (MK_COMB (@lem2000848) (@lem2000847)). Qed.
Lemma lem2000850 : term21 = term12.
Proof. exact (TRANS (@lem2000843) (@lem2000849)). Qed.
Lemma lem2000852 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2000853 : term26 = term27.
Proof. exact (@lem2000852 term15 term15). Qed.
Lemma lem2000854 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2000855 : term29 = term15.
Proof. exact (EQ_MP (@lem2000854) (@lem940073)). Qed.
Lemma lem2000856 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2000857 : term27 = term5.
Proof. exact (MK_COMB (@lem2000856) (@lem2000855)). Qed.
Lemma lem2000858 : term26 = term5.
Proof. exact (TRANS (@lem2000853) (@lem2000857)). Qed.
Lemma lem2000859 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2000860 : term281 = term273.
Proof. exact (MK_COMB (@lem2000859) (@lem2000858)). Qed.
Lemma lem2000861 : term282 = term275.
Proof. exact (MK_COMB (@lem2000860) (@lem2000850)). Qed.
Lemma lem2000863 (m : nat) : (term283 m) = term2.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem2000864 : term275 = term2.
Proof. exact (@lem2000863 term15). Qed.
Lemma lem2000865 : term282 = term2.
Proof. exact (TRANS (@lem2000861) (@lem2000864)). Qed.
Lemma lem2000866 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2000867 : term284 = term109.
Proof. exact (MK_COMB (@lem2000866) (@lem2000865)). Qed.
Lemma lem2000868 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem2000869 : term285 = term78.
Proof. exact (MK_COMB (@lem2000867) (@lem2000868)). Qed.
Lemma lem2000871 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2000872 : term78 = term2.
Proof. exact (@lem2000871 term15). Qed.
Lemma lem2000873 : term285 = term2.
Proof. exact (TRANS (@lem2000869) (@lem2000872)). Qed.
Lemma lem2000875 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2000876 : term26 = term27.
Proof. exact (@lem2000875 term15 term15). Qed.
Lemma lem2000877 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2000878 : term29 = term15.
Proof. exact (EQ_MP (@lem2000877) (@lem940073)). Qed.
Lemma lem2000879 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2000880 : term27 = term5.
Proof. exact (MK_COMB (@lem2000879) (@lem2000878)). Qed.
Lemma lem2000881 : term26 = term5.
Proof. exact (TRANS (@lem2000876) (@lem2000880)). Qed.
Lemma lem2000882 : term109 = term109.
Proof. exact (eq_refl term109). Qed.
Lemma lem2000883 : term111 = term78.
Proof. exact (MK_COMB (@lem2000882) (@lem2000881)). Qed.
Lemma lem2000885 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2000886 : term78 = term2.
Proof. exact (@lem2000885 term15). Qed.
Lemma lem2000887 : term111 = term2.
Proof. exact (TRANS (@lem2000883) (@lem2000886)). Qed.
Lemma lem2000888 : term2 = term111.
Proof. exact (SYM (@lem2000887)). Qed.
Lemma lem2000889 : term285 = term111.
Proof. exact (TRANS (@lem2000873) (@lem2000888)). Qed.
Lemma lem2000890 : term276 = term67.
Proof. exact (@lem2000840 (@lem2000889)). Qed.
Lemma lem2000891 : term275 = term67.
Proof. exact (TRANS (@lem2000806) (@lem2000890)). Qed.
Lemma lem2000893 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2000894 : term67 = term2.
Proof. exact (@lem2000893 term2). Qed.
Lemma lem2000895 : term275 = term2.
Proof. exact (TRANS (@lem2000891) (@lem2000894)). Qed.
Lemma lem2000896 (x : real) : (term203 x) = (term203 x).
Proof. exact (eq_refl (term203 x)). Qed.
Lemma lem2000897 (x : real) : (term272 x) = (term286 x).
Proof. exact (MK_COMB (@lem2000896 x) (@lem2000895)). Qed.
Lemma lem2000898 (x : real) : (term271 x) = (term286 x).
Proof. exact (TRANS (@lem2000797 x) (@lem2000897 x)). Qed.
Lemma lem2000899 (x : real) : (term286 x) = (real_abs x).
Proof. exact (@lem1982723 (real_abs x)). Qed.
Lemma lem2000901 (x : real) : (term271 x) = (real_abs x).
Proof. exact (TRANS (@lem2000898 x) (@lem2000899 x)). Qed.
Lemma lem2000910 (x : real) : (term287 x) = (term287 x).
Proof. exact (eq_refl (term287 x)). Qed.
Lemma lem2000913 (x : real) : (term270 x) = (term288 x).
Proof. exact (MK_COMB (@lem2000910 x) (@lem2000901 x)). Qed.
Lemma lem2000914 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2000915 (x : real) : (term289 x) = (term290 x).
Proof. exact (MK_COMB (@lem2000914) (@lem2000913 x)). Qed.
Lemma lem2000916 (x : real) : (term291 x) = (term292 x).
Proof. exact (MK_COMB (@lem2000915 x) (@lem2000783)). Qed.
Lemma lem2000917 (x : real) : (term292 x) = (term293 x).
Proof. exact (@lem1982792 (term288 x) term2). Qed.
Lemma lem2000919 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2000920 : term2 = term67.
Proof. exact (@lem2000919 (NUMERAL 0)). Qed.
Lemma lem2000922 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2000923 : term12 = term18.
Proof. exact (@lem2000922 term15). Qed.
Lemma lem2000924 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2000925 : term19 = term20.
Proof. exact (MK_COMB (@lem2000924) (@lem2000923)). Qed.
Lemma lem2000926 : term258 = term259.
Proof. exact (MK_COMB (@lem2000925) (@lem2000920)). Qed.
Lemma lem2000927 : term259 = term260.
Proof. exact (@lem1981613 term12 term2 term5 term5). Qed.
Lemma lem2000929 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2000930 : term26 = term27.
Proof. exact (@lem2000929 term15 term15). Qed.
Lemma lem2000931 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2000932 : term29 = term15.
Proof. exact (EQ_MP (@lem2000931) (@lem940073)). Qed.
Lemma lem2000933 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2000934 : term27 = term5.
Proof. exact (MK_COMB (@lem2000933) (@lem2000932)). Qed.
Lemma lem2000935 : term26 = term5.
Proof. exact (TRANS (@lem2000930) (@lem2000934)). Qed.
Lemma lem2000937 (x : nat) : (term261 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2000938 : term258 = term2.
Proof. exact (@lem2000937 term15). Qed.
Lemma lem2000939 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2000940 : term262 = term263.
Proof. exact (MK_COMB (@lem2000939) (@lem2000938)). Qed.
Lemma lem2000941 : term260 = term67.
Proof. exact (MK_COMB (@lem2000940) (@lem2000935)). Qed.
Lemma lem2000942 : term259 = term67.
Proof. exact (TRANS (@lem2000927) (@lem2000941)). Qed.
Lemma lem2000943 : term258 = term67.
Proof. exact (TRANS (@lem2000926) (@lem2000942)). Qed.
Lemma lem2000945 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2000946 : term67 = term2.
Proof. exact (@lem2000945 term2). Qed.
Lemma lem2000947 : term258 = term2.
Proof. exact (TRANS (@lem2000943) (@lem2000946)). Qed.
Lemma lem2000948 (x : real) : (term294 x) = (term294 x).
Proof. exact (eq_refl (term294 x)). Qed.
Lemma lem2000949 (x : real) : (term293 x) = (term295 x).
Proof. exact (MK_COMB (@lem2000948 x) (@lem2000947)). Qed.
Lemma lem2000950 (x : real) : (term295 x) = (term288 x).
Proof. exact (@lem1982723 (term288 x)). Qed.
Lemma lem2000951 (x : real) : (term293 x) = (term288 x).
Proof. exact (TRANS (@lem2000949 x) (@lem2000950 x)). Qed.
Lemma lem2000952 (x : real) : (term292 x) = (term288 x).
Proof. exact (TRANS (@lem2000917 x) (@lem2000951 x)). Qed.
Lemma lem2000953 (x : real) : (term291 x) = (term288 x).
Proof. exact (TRANS (@lem2000916 x) (@lem2000952 x)). Qed.
Lemma lem2000954 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2000955 (x : real) : (term296 x) = (term297 x).
Proof. exact (MK_COMB (@lem2000954) (@lem2000953 x)). Qed.
Lemma lem2000956 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2000957 (x : real) : (term269 x) = (term298 x).
Proof. exact (MK_COMB (@lem2000955 x) (@lem2000956)). Qed.
Lemma lem2000958 (x : real) : (term268 x) = (term298 x).
Proof. exact (TRANS (@lem2000782 x) (@lem2000957 x)). Qed.
Lemma lem2000959 (x : real) : (term299 x) = (term300 x).
Proof. exact (@lem1988289 (term301 x) term2). Qed.
Lemma lem2000960 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2000974 (x : real) : (term271 x) = (term272 x).
Proof. exact (@lem1982755 (real_abs x) term5 term12). Qed.
Lemma lem2000976 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2000977 : term12 = term18.
Proof. exact (@lem2000976 term15). Qed.
Lemma lem2000979 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2000980 : term5 = term14.
Proof. exact (@lem2000979 term15). Qed.
Lemma lem2000981 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2000982 : term273 = term274.
Proof. exact (MK_COMB (@lem2000981) (@lem2000980)). Qed.
Lemma lem2000983 : term275 = term276.
Proof. exact (MK_COMB (@lem2000982) (@lem2000977)). Qed.
Lemma lem2000984 : term277.
Proof. exact (@lem1981473 term5 term5 term12 term5 term2 term5). Qed.
Lemma lem2000986 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2000987 : term66 = term73.
Proof. exact (@lem2000986 (NUMERAL 0) term15). Qed.
Lemma lem2000988 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2000989 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2000990 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2000989 h1) (fun h1 : term73 = True => @lem2000988)). Qed.
Lemma lem2000991 : term73 = True.
Proof. exact (EQ_MP (@lem2000990) (@lem2000988)). Qed.
Lemma lem2000992 : term66 = True.
Proof. exact (TRANS (@lem2000987) (@lem2000991)). Qed.
Lemma lem2000993 : True = term66.
Proof. exact (SYM (@lem2000992)). Qed.
Lemma lem2000994 : term66.
Proof. exact (EQ_MP (@lem2000993) (@lem0)). Qed.
Lemma lem2000995 : term278.
Proof. exact (@lem2000984 (@lem2000994)). Qed.
Lemma lem2000997 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2000998 : term66 = term73.
Proof. exact (@lem2000997 (NUMERAL 0) term15). Qed.
Lemma lem2000999 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2001000 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2001001 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2001000 h1) (fun h1 : term73 = True => @lem2000999)). Qed.
Lemma lem2001002 : term73 = True.
Proof. exact (EQ_MP (@lem2001001) (@lem2000999)). Qed.
Lemma lem2001003 : term66 = True.
Proof. exact (TRANS (@lem2000998) (@lem2001002)). Qed.
Lemma lem2001004 : True = term66.
Proof. exact (SYM (@lem2001003)). Qed.
Lemma lem2001005 : term66.
Proof. exact (EQ_MP (@lem2001004) (@lem0)). Qed.
Lemma lem2001006 : term279.
Proof. exact (@lem2000995 (@lem2001005)). Qed.
Lemma lem2001008 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2001009 : term66 = term73.
Proof. exact (@lem2001008 (NUMERAL 0) term15). Qed.
Lemma lem2001010 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2001011 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2001012 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2001011 h1) (fun h1 : term73 = True => @lem2001010)). Qed.
Lemma lem2001013 : term73 = True.
Proof. exact (EQ_MP (@lem2001012) (@lem2001010)). Qed.
Lemma lem2001014 : term66 = True.
Proof. exact (TRANS (@lem2001009) (@lem2001013)). Qed.
Lemma lem2001015 : True = term66.
Proof. exact (SYM (@lem2001014)). Qed.
Lemma lem2001016 : term66.
Proof. exact (EQ_MP (@lem2001015) (@lem0)). Qed.
Lemma lem2001017 : term280.
Proof. exact (@lem2001006 (@lem2001016)). Qed.
Lemma lem2001019 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2001020 : term21 = term32.
Proof. exact (@lem2001019 term15 term15). Qed.
Lemma lem2001021 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2001022 : term29 = term15.
Proof. exact (EQ_MP (@lem2001021) (@lem940073)). Qed.
Lemma lem2001023 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001024 : term27 = term5.
Proof. exact (MK_COMB (@lem2001023) (@lem2001022)). Qed.
Lemma lem2001025 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2001026 : term32 = term12.
Proof. exact (MK_COMB (@lem2001025) (@lem2001024)). Qed.
Lemma lem2001027 : term21 = term12.
Proof. exact (TRANS (@lem2001020) (@lem2001026)). Qed.
Lemma lem2001029 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2001030 : term26 = term27.
Proof. exact (@lem2001029 term15 term15). Qed.
Lemma lem2001031 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2001032 : term29 = term15.
Proof. exact (EQ_MP (@lem2001031) (@lem940073)). Qed.
Lemma lem2001033 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001034 : term27 = term5.
Proof. exact (MK_COMB (@lem2001033) (@lem2001032)). Qed.
Lemma lem2001035 : term26 = term5.
Proof. exact (TRANS (@lem2001030) (@lem2001034)). Qed.
Lemma lem2001036 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2001037 : term281 = term273.
Proof. exact (MK_COMB (@lem2001036) (@lem2001035)). Qed.
Lemma lem2001038 : term282 = term275.
Proof. exact (MK_COMB (@lem2001037) (@lem2001027)). Qed.
Lemma lem2001040 (m : nat) : (term283 m) = term2.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem2001041 : term275 = term2.
Proof. exact (@lem2001040 term15). Qed.
Lemma lem2001042 : term282 = term2.
Proof. exact (TRANS (@lem2001038) (@lem2001041)). Qed.
Lemma lem2001043 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2001044 : term284 = term109.
Proof. exact (MK_COMB (@lem2001043) (@lem2001042)). Qed.
Lemma lem2001045 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem2001046 : term285 = term78.
Proof. exact (MK_COMB (@lem2001044) (@lem2001045)). Qed.
Lemma lem2001048 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2001049 : term78 = term2.
Proof. exact (@lem2001048 term15). Qed.
Lemma lem2001050 : term285 = term2.
Proof. exact (TRANS (@lem2001046) (@lem2001049)). Qed.
Lemma lem2001052 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2001053 : term26 = term27.
Proof. exact (@lem2001052 term15 term15). Qed.
Lemma lem2001054 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2001055 : term29 = term15.
Proof. exact (EQ_MP (@lem2001054) (@lem940073)). Qed.
Lemma lem2001056 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001057 : term27 = term5.
Proof. exact (MK_COMB (@lem2001056) (@lem2001055)). Qed.
Lemma lem2001058 : term26 = term5.
Proof. exact (TRANS (@lem2001053) (@lem2001057)). Qed.
Lemma lem2001059 : term109 = term109.
Proof. exact (eq_refl term109). Qed.
Lemma lem2001060 : term111 = term78.
Proof. exact (MK_COMB (@lem2001059) (@lem2001058)). Qed.
Lemma lem2001062 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2001063 : term78 = term2.
Proof. exact (@lem2001062 term15). Qed.
Lemma lem2001064 : term111 = term2.
Proof. exact (TRANS (@lem2001060) (@lem2001063)). Qed.
Lemma lem2001065 : term2 = term111.
Proof. exact (SYM (@lem2001064)). Qed.
Lemma lem2001066 : term285 = term111.
Proof. exact (TRANS (@lem2001050) (@lem2001065)). Qed.
Lemma lem2001067 : term276 = term67.
Proof. exact (@lem2001017 (@lem2001066)). Qed.
Lemma lem2001068 : term275 = term67.
Proof. exact (TRANS (@lem2000983) (@lem2001067)). Qed.
Lemma lem2001070 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2001071 : term67 = term2.
Proof. exact (@lem2001070 term2). Qed.
Lemma lem2001072 : term275 = term2.
Proof. exact (TRANS (@lem2001068) (@lem2001071)). Qed.
Lemma lem2001073 (x : real) : (term203 x) = (term203 x).
Proof. exact (eq_refl (term203 x)). Qed.
Lemma lem2001074 (x : real) : (term272 x) = (term286 x).
Proof. exact (MK_COMB (@lem2001073 x) (@lem2001072)). Qed.
Lemma lem2001075 (x : real) : (term271 x) = (term286 x).
Proof. exact (TRANS (@lem2000974 x) (@lem2001074 x)). Qed.
Lemma lem2001076 (x : real) : (term286 x) = (real_abs x).
Proof. exact (@lem1982723 (real_abs x)). Qed.
Lemma lem2001078 (x : real) : (term271 x) = (real_abs x).
Proof. exact (TRANS (@lem2001075 x) (@lem2001076 x)). Qed.
Lemma lem2001081 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem2001084 (x : real) : (term301 x) = (term302 x).
Proof. exact (MK_COMB (@lem2001081 x) (@lem2001078 x)). Qed.
Lemma lem2001085 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2001086 (x : real) : (term303 x) = (term304 x).
Proof. exact (MK_COMB (@lem2001085) (@lem2001084 x)). Qed.
Lemma lem2001087 (x : real) : (term305 x) = (term306 x).
Proof. exact (MK_COMB (@lem2001086 x) (@lem2000960)). Qed.
Lemma lem2001088 (x : real) : (term306 x) = (term307 x).
Proof. exact (@lem1982792 (term302 x) term2). Qed.
Lemma lem2001090 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2001091 : term2 = term67.
Proof. exact (@lem2001090 (NUMERAL 0)). Qed.
Lemma lem2001093 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2001094 : term12 = term18.
Proof. exact (@lem2001093 term15). Qed.
Lemma lem2001095 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2001096 : term19 = term20.
Proof. exact (MK_COMB (@lem2001095) (@lem2001094)). Qed.
Lemma lem2001097 : term258 = term259.
Proof. exact (MK_COMB (@lem2001096) (@lem2001091)). Qed.
Lemma lem2001098 : term259 = term260.
Proof. exact (@lem1981613 term12 term2 term5 term5). Qed.
Lemma lem2001100 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2001101 : term26 = term27.
Proof. exact (@lem2001100 term15 term15). Qed.
Lemma lem2001102 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2001103 : term29 = term15.
Proof. exact (EQ_MP (@lem2001102) (@lem940073)). Qed.
Lemma lem2001104 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001105 : term27 = term5.
Proof. exact (MK_COMB (@lem2001104) (@lem2001103)). Qed.
Lemma lem2001106 : term26 = term5.
Proof. exact (TRANS (@lem2001101) (@lem2001105)). Qed.
Lemma lem2001108 (x : nat) : (term261 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2001109 : term258 = term2.
Proof. exact (@lem2001108 term15). Qed.
Lemma lem2001110 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2001111 : term262 = term263.
Proof. exact (MK_COMB (@lem2001110) (@lem2001109)). Qed.
Lemma lem2001112 : term260 = term67.
Proof. exact (MK_COMB (@lem2001111) (@lem2001106)). Qed.
Lemma lem2001113 : term259 = term67.
Proof. exact (TRANS (@lem2001098) (@lem2001112)). Qed.
Lemma lem2001114 : term258 = term67.
Proof. exact (TRANS (@lem2001097) (@lem2001113)). Qed.
Lemma lem2001116 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2001117 : term67 = term2.
Proof. exact (@lem2001116 term2). Qed.
Lemma lem2001118 : term258 = term2.
Proof. exact (TRANS (@lem2001114) (@lem2001117)). Qed.
Lemma lem2001119 (x : real) : (term308 x) = (term308 x).
Proof. exact (eq_refl (term308 x)). Qed.
Lemma lem2001120 (x : real) : (term307 x) = (term309 x).
Proof. exact (MK_COMB (@lem2001119 x) (@lem2001118)). Qed.
Lemma lem2001121 (x : real) : (term309 x) = (term302 x).
Proof. exact (@lem1982723 (term302 x)). Qed.
Lemma lem2001122 (x : real) : (term307 x) = (term302 x).
Proof. exact (TRANS (@lem2001120 x) (@lem2001121 x)). Qed.
Lemma lem2001123 (x : real) : (term306 x) = (term302 x).
Proof. exact (TRANS (@lem2001088 x) (@lem2001122 x)). Qed.
Lemma lem2001124 (x : real) : (term305 x) = (term302 x).
Proof. exact (TRANS (@lem2001087 x) (@lem2001123 x)). Qed.
Lemma lem2001125 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2001126 (x : real) : (term310 x) = (term311 x).
Proof. exact (MK_COMB (@lem2001125) (@lem2001124 x)). Qed.
Lemma lem2001127 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2001128 (x : real) : (term300 x) = (term312 x).
Proof. exact (MK_COMB (@lem2001126 x) (@lem2001127)). Qed.
Lemma lem2001129 (x : real) : (term299 x) = (term312 x).
Proof. exact (TRANS (@lem2000959 x) (@lem2001128 x)). Qed.
Lemma lem2001130 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2001131 (x : real) : (term313 x) = (term314 x).
Proof. exact (MK_COMB (@lem2001130) (@lem2000958 x)). Qed.
Lemma lem2001132 (x : real) : (term246 x) = (term315 x).
Proof. exact (MK_COMB (@lem2001131 x) (@lem2001129 x)). Qed.
Lemma lem2001133 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2001134 (x : real) : (term247 x) = (term247 x).
Proof. exact (MK_COMB (@lem2001133) (@lem2000781 x)). Qed.
Lemma lem2001135 (x : real) : (term249 x) = (term316 x).
Proof. exact (MK_COMB (@lem2001134 x) (@lem2001132 x)). Qed.
Lemma lem2001136 (x : real) : (term317 x) = (term318 x).
Proof. exact (@lem1988289 term2 (term4 x)). Qed.
Lemma lem2001150 (x : real) : (term8 x) = (term9 x).
Proof. exact (@lem1982792 term2 (term4 x)). Qed.
Lemma lem2001151 (x : real) : (term10 x) = (term11 x).
Proof. exact (@lem1982781 (real_abs x) term12 term5). Qed.
Lemma lem2001153 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2001154 : term5 = term14.
Proof. exact (@lem2001153 term15). Qed.
Lemma lem2001156 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2001157 : term12 = term18.
Proof. exact (@lem2001156 term15). Qed.
Lemma lem2001158 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2001159 : term19 = term20.
Proof. exact (MK_COMB (@lem2001158) (@lem2001157)). Qed.
Lemma lem2001160 : term21 = term22.
Proof. exact (MK_COMB (@lem2001159) (@lem2001154)). Qed.
Lemma lem2001161 : term22 = term23.
Proof. exact (@lem1981613 term12 term5 term5 term5). Qed.
Lemma lem2001163 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2001164 : term26 = term27.
Proof. exact (@lem2001163 term15 term15). Qed.
Lemma lem2001165 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2001166 : term29 = term15.
Proof. exact (EQ_MP (@lem2001165) (@lem940073)). Qed.
Lemma lem2001167 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001168 : term27 = term5.
Proof. exact (MK_COMB (@lem2001167) (@lem2001166)). Qed.
Lemma lem2001169 : term26 = term5.
Proof. exact (TRANS (@lem2001164) (@lem2001168)). Qed.
Lemma lem2001171 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2001172 : term21 = term32.
Proof. exact (@lem2001171 term15 term15). Qed.
Lemma lem2001173 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2001174 : term29 = term15.
Proof. exact (EQ_MP (@lem2001173) (@lem940073)). Qed.
Lemma lem2001175 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001176 : term27 = term5.
Proof. exact (MK_COMB (@lem2001175) (@lem2001174)). Qed.
Lemma lem2001177 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2001178 : term32 = term12.
Proof. exact (MK_COMB (@lem2001177) (@lem2001176)). Qed.
Lemma lem2001179 : term21 = term12.
Proof. exact (TRANS (@lem2001172) (@lem2001178)). Qed.
Lemma lem2001180 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2001181 : term33 = term34.
Proof. exact (MK_COMB (@lem2001180) (@lem2001179)). Qed.
Lemma lem2001182 : term23 = term18.
Proof. exact (MK_COMB (@lem2001181) (@lem2001169)). Qed.
Lemma lem2001183 : term22 = term18.
Proof. exact (TRANS (@lem2001161) (@lem2001182)). Qed.
Lemma lem2001184 : term21 = term18.
Proof. exact (TRANS (@lem2001160) (@lem2001183)). Qed.
Lemma lem2001186 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2001187 : term18 = term12.
Proof. exact (@lem2001186 term12). Qed.
Lemma lem2001188 : term21 = term12.
Proof. exact (TRANS (@lem2001184) (@lem2001187)). Qed.
Lemma lem2001191 (x : real) : (term36 x) = (term36 x).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem2001192 (x : real) : (term11 x) = (term37 x).
Proof. exact (MK_COMB (@lem2001191 x) (@lem2001188)). Qed.
Lemma lem2001193 (x : real) : (term10 x) = (term37 x).
Proof. exact (TRANS (@lem2001151 x) (@lem2001192 x)). Qed.
Lemma lem2001194 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2001195 (x : real) : (term9 x) = (term39 x).
Proof. exact (MK_COMB (@lem2001194) (@lem2001193 x)). Qed.
Lemma lem2001196 (x : real) : (term39 x) = (term37 x).
Proof. exact (@lem1982721 (term37 x)). Qed.
Lemma lem2001197 (x : real) : (term9 x) = (term37 x).
Proof. exact (TRANS (@lem2001195 x) (@lem2001196 x)). Qed.
Lemma lem2001199 (x : real) : (term8 x) = (term37 x).
Proof. exact (TRANS (@lem2001150 x) (@lem2001197 x)). Qed.
Lemma lem2001200 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2001201 (x : real) : (term319 x) = (term320 x).
Proof. exact (MK_COMB (@lem2001200) (@lem2001199 x)). Qed.
Lemma lem2001202 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2001203 (x : real) : (term318 x) = (term321 x).
Proof. exact (MK_COMB (@lem2001201 x) (@lem2001202)). Qed.
Lemma lem2001204 (x : real) : (term317 x) = (term321 x).
Proof. exact (TRANS (@lem2001136 x) (@lem2001203 x)). Qed.
Lemma lem2001205 (x : real) : (term322 x) = (term323 x).
Proof. exact (@lem1988289 (term324 x) term2). Qed.
Lemma lem2001206 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2001207 : term12 = term12.
Proof. exact (eq_refl term12). Qed.
Lemma lem2001219 (x : real) : (term325 x) = (term10 x).
Proof. exact (@lem1982785 (term4 x)). Qed.
Lemma lem2001220 (x : real) : (term10 x) = (term11 x).
Proof. exact (@lem1982781 (real_abs x) term12 term5). Qed.
Lemma lem2001222 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2001223 : term5 = term14.
Proof. exact (@lem2001222 term15). Qed.
Lemma lem2001225 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2001226 : term12 = term18.
Proof. exact (@lem2001225 term15). Qed.
Lemma lem2001227 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2001228 : term19 = term20.
Proof. exact (MK_COMB (@lem2001227) (@lem2001226)). Qed.
Lemma lem2001229 : term21 = term22.
Proof. exact (MK_COMB (@lem2001228) (@lem2001223)). Qed.
Lemma lem2001230 : term22 = term23.
Proof. exact (@lem1981613 term12 term5 term5 term5). Qed.
Lemma lem2001232 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2001233 : term26 = term27.
Proof. exact (@lem2001232 term15 term15). Qed.
Lemma lem2001234 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2001235 : term29 = term15.
Proof. exact (EQ_MP (@lem2001234) (@lem940073)). Qed.
Lemma lem2001236 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001237 : term27 = term5.
Proof. exact (MK_COMB (@lem2001236) (@lem2001235)). Qed.
Lemma lem2001238 : term26 = term5.
Proof. exact (TRANS (@lem2001233) (@lem2001237)). Qed.
Lemma lem2001240 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2001241 : term21 = term32.
Proof. exact (@lem2001240 term15 term15). Qed.
Lemma lem2001242 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2001243 : term29 = term15.
Proof. exact (EQ_MP (@lem2001242) (@lem940073)). Qed.
Lemma lem2001244 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001245 : term27 = term5.
Proof. exact (MK_COMB (@lem2001244) (@lem2001243)). Qed.
Lemma lem2001246 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2001247 : term32 = term12.
Proof. exact (MK_COMB (@lem2001246) (@lem2001245)). Qed.
Lemma lem2001248 : term21 = term12.
Proof. exact (TRANS (@lem2001241) (@lem2001247)). Qed.
Lemma lem2001249 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2001250 : term33 = term34.
Proof. exact (MK_COMB (@lem2001249) (@lem2001248)). Qed.
Lemma lem2001251 : term23 = term18.
Proof. exact (MK_COMB (@lem2001250) (@lem2001238)). Qed.
Lemma lem2001252 : term22 = term18.
Proof. exact (TRANS (@lem2001230) (@lem2001251)). Qed.
Lemma lem2001253 : term21 = term18.
Proof. exact (TRANS (@lem2001229) (@lem2001252)). Qed.
Lemma lem2001255 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2001256 : term18 = term12.
Proof. exact (@lem2001255 term12). Qed.
Lemma lem2001257 : term21 = term12.
Proof. exact (TRANS (@lem2001253) (@lem2001256)). Qed.
Lemma lem2001260 (x : real) : (term36 x) = (term36 x).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem2001261 (x : real) : (term11 x) = (term37 x).
Proof. exact (MK_COMB (@lem2001260 x) (@lem2001257)). Qed.
Lemma lem2001262 (x : real) : (term10 x) = (term37 x).
Proof. exact (TRANS (@lem2001220 x) (@lem2001261 x)). Qed.
Lemma lem2001264 (x : real) : (term325 x) = (term37 x).
Proof. exact (TRANS (@lem2001219 x) (@lem2001262 x)). Qed.
Lemma lem2001265 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2001266 (x : real) : (term326 x) = (term327 x).
Proof. exact (MK_COMB (@lem2001265) (@lem2001264 x)). Qed.
Lemma lem2001267 (x : real) : (term328 x) = (term329 x).
Proof. exact (MK_COMB (@lem2001266 x) (@lem2001207)). Qed.
Lemma lem2001268 (x : real) : (term329 x) = (term330 x).
Proof. exact (@lem1982755 (term181 x) term12 term12). Qed.
Lemma lem2001270 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2001271 : term12 = term18.
Proof. exact (@lem2001270 term15). Qed.
Lemma lem2001273 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2001274 : term12 = term18.
Proof. exact (@lem2001273 term15). Qed.
Lemma lem2001275 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2001276 : term47 = term98.
Proof. exact (MK_COMB (@lem2001275) (@lem2001274)). Qed.
Lemma lem2001277 : term115 = term116.
Proof. exact (MK_COMB (@lem2001276) (@lem2001271)). Qed.
Lemma lem2001278 : term117.
Proof. exact (@lem1981473 term12 term5 term12 term5 term118 term5). Qed.
Lemma lem2001280 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2001281 : term66 = term73.
Proof. exact (@lem2001280 (NUMERAL 0) term15). Qed.
Lemma lem2001282 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2001283 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2001284 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2001283 h1) (fun h1 : term73 = True => @lem2001282)). Qed.
Lemma lem2001285 : term73 = True.
Proof. exact (EQ_MP (@lem2001284) (@lem2001282)). Qed.
Lemma lem2001286 : term66 = True.
Proof. exact (TRANS (@lem2001281) (@lem2001285)). Qed.
Lemma lem2001287 : True = term66.
Proof. exact (SYM (@lem2001286)). Qed.
Lemma lem2001288 : term66.
Proof. exact (EQ_MP (@lem2001287) (@lem0)). Qed.
Lemma lem2001289 : term119.
Proof. exact (@lem2001278 (@lem2001288)). Qed.
Lemma lem2001291 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2001292 : term66 = term73.
Proof. exact (@lem2001291 (NUMERAL 0) term15). Qed.
Lemma lem2001293 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2001294 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2001295 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2001294 h1) (fun h1 : term73 = True => @lem2001293)). Qed.
Lemma lem2001296 : term73 = True.
Proof. exact (EQ_MP (@lem2001295) (@lem2001293)). Qed.
Lemma lem2001297 : term66 = True.
Proof. exact (TRANS (@lem2001292) (@lem2001296)). Qed.
Lemma lem2001298 : True = term66.
Proof. exact (SYM (@lem2001297)). Qed.
Lemma lem2001299 : term66.
Proof. exact (EQ_MP (@lem2001298) (@lem0)). Qed.
Lemma lem2001300 : term120.
Proof. exact (@lem2001289 (@lem2001299)). Qed.
Lemma lem2001302 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2001303 : term66 = term73.
Proof. exact (@lem2001302 (NUMERAL 0) term15). Qed.
Lemma lem2001304 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2001305 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2001306 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2001305 h1) (fun h1 : term73 = True => @lem2001304)). Qed.
Lemma lem2001307 : term73 = True.
Proof. exact (EQ_MP (@lem2001306) (@lem2001304)). Qed.
Lemma lem2001308 : term66 = True.
Proof. exact (TRANS (@lem2001303) (@lem2001307)). Qed.
Lemma lem2001309 : True = term66.
Proof. exact (SYM (@lem2001308)). Qed.
Lemma lem2001310 : term66.
Proof. exact (EQ_MP (@lem2001309) (@lem0)). Qed.
Lemma lem2001311 : term121.
Proof. exact (@lem2001300 (@lem2001310)). Qed.
Lemma lem2001313 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2001314 : term21 = term32.
Proof. exact (@lem2001313 term15 term15). Qed.
Lemma lem2001315 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2001316 : term29 = term15.
Proof. exact (EQ_MP (@lem2001315) (@lem940073)). Qed.
Lemma lem2001317 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001318 : term27 = term5.
Proof. exact (MK_COMB (@lem2001317) (@lem2001316)). Qed.
Lemma lem2001319 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2001320 : term32 = term12.
Proof. exact (MK_COMB (@lem2001319) (@lem2001318)). Qed.
Lemma lem2001321 : term21 = term12.
Proof. exact (TRANS (@lem2001314) (@lem2001320)). Qed.
Lemma lem2001323 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2001324 : term21 = term32.
Proof. exact (@lem2001323 term15 term15). Qed.
Lemma lem2001325 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2001326 : term29 = term15.
Proof. exact (EQ_MP (@lem2001325) (@lem940073)). Qed.
Lemma lem2001327 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001328 : term27 = term5.
Proof. exact (MK_COMB (@lem2001327) (@lem2001326)). Qed.
Lemma lem2001329 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2001330 : term32 = term12.
Proof. exact (MK_COMB (@lem2001329) (@lem2001328)). Qed.
Lemma lem2001331 : term21 = term12.
Proof. exact (TRANS (@lem2001324) (@lem2001330)). Qed.
Lemma lem2001332 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2001333 : term105 = term47.
Proof. exact (MK_COMB (@lem2001332) (@lem2001331)). Qed.
Lemma lem2001334 : term122 = term115.
Proof. exact (MK_COMB (@lem2001333) (@lem2001321)). Qed.
Lemma lem2001335 : term115 = term123.
Proof. exact (@lem1367763 term15 term15). Qed.
Lemma lem2001336 : term124 = term125.
Proof. exact (@lem706885). Qed.
Lemma lem2001337 : (term124 = term125) = (term126 = term127).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term125). Qed.
Lemma lem2001338 : term126 = term127.
Proof. exact (EQ_MP (@lem2001337) (@lem2001336)). Qed.
Lemma lem2001339 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001340 : term128 = term129.
Proof. exact (MK_COMB (@lem2001339) (@lem2001338)). Qed.
Lemma lem2001341 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2001342 : term123 = term118.
Proof. exact (MK_COMB (@lem2001341) (@lem2001340)). Qed.
Lemma lem2001343 : term115 = term118.
Proof. exact (TRANS (@lem2001335) (@lem2001342)). Qed.
Lemma lem2001344 : term122 = term118.
Proof. exact (TRANS (@lem2001334) (@lem2001343)). Qed.
Lemma lem2001345 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2001346 : term130 = term131.
Proof. exact (MK_COMB (@lem2001345) (@lem2001344)). Qed.
Lemma lem2001347 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem2001348 : term132 = term133.
Proof. exact (MK_COMB (@lem2001346) (@lem2001347)). Qed.
Lemma lem2001350 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2001351 : term133 = term134.
Proof. exact (@lem2001350 term127 term15). Qed.
Lemma lem2001352 : term135 = term125.
Proof. exact (@lem996237 term125). Qed.
Lemma lem2001353 : (term135 = term125) = (term136 = term127).
Proof. exact (@lem1007663 term125 (BIT1 0) term125). Qed.
Lemma lem2001354 : term136 = term127.
Proof. exact (EQ_MP (@lem2001353) (@lem2001352)). Qed.
Lemma lem2001355 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001356 : term137 = term129.
Proof. exact (MK_COMB (@lem2001355) (@lem2001354)). Qed.
Lemma lem2001357 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2001358 : term134 = term118.
Proof. exact (MK_COMB (@lem2001357) (@lem2001356)). Qed.
Lemma lem2001359 : term133 = term118.
Proof. exact (TRANS (@lem2001351) (@lem2001358)). Qed.
Lemma lem2001360 : term132 = term118.
Proof. exact (TRANS (@lem2001348) (@lem2001359)). Qed.
Lemma lem2001362 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2001363 : term26 = term27.
Proof. exact (@lem2001362 term15 term15). Qed.
Lemma lem2001364 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2001365 : term29 = term15.
Proof. exact (EQ_MP (@lem2001364) (@lem940073)). Qed.
Lemma lem2001366 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001367 : term27 = term5.
Proof. exact (MK_COMB (@lem2001366) (@lem2001365)). Qed.
Lemma lem2001368 : term26 = term5.
Proof. exact (TRANS (@lem2001363) (@lem2001367)). Qed.
Lemma lem2001369 : term131 = term131.
Proof. exact (eq_refl term131). Qed.
Lemma lem2001370 : term138 = term133.
Proof. exact (MK_COMB (@lem2001369) (@lem2001368)). Qed.
Lemma lem2001372 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2001373 : term133 = term134.
Proof. exact (@lem2001372 term127 term15). Qed.
Lemma lem2001374 : term135 = term125.
Proof. exact (@lem996237 term125). Qed.
Lemma lem2001375 : (term135 = term125) = (term136 = term127).
Proof. exact (@lem1007663 term125 (BIT1 0) term125). Qed.
Lemma lem2001376 : term136 = term127.
Proof. exact (EQ_MP (@lem2001375) (@lem2001374)). Qed.
Lemma lem2001377 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001378 : term137 = term129.
Proof. exact (MK_COMB (@lem2001377) (@lem2001376)). Qed.
Lemma lem2001379 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2001380 : term134 = term118.
Proof. exact (MK_COMB (@lem2001379) (@lem2001378)). Qed.
Lemma lem2001381 : term133 = term118.
Proof. exact (TRANS (@lem2001373) (@lem2001380)). Qed.
Lemma lem2001382 : term138 = term118.
Proof. exact (TRANS (@lem2001370) (@lem2001381)). Qed.
Lemma lem2001383 : term118 = term138.
Proof. exact (SYM (@lem2001382)). Qed.
Lemma lem2001384 : term132 = term138.
Proof. exact (TRANS (@lem2001360) (@lem2001383)). Qed.
Lemma lem2001385 : term116 = term139.
Proof. exact (@lem2001311 (@lem2001384)). Qed.
Lemma lem2001386 : term115 = term139.
Proof. exact (TRANS (@lem2001277) (@lem2001385)). Qed.
Lemma lem2001388 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2001389 : term139 = term118.
Proof. exact (@lem2001388 term118). Qed.
Lemma lem2001390 : term115 = term118.
Proof. exact (TRANS (@lem2001386) (@lem2001389)). Qed.
Lemma lem2001391 (x : real) : (term36 x) = (term36 x).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem2001392 (x : real) : (term330 x) = (term331 x).
Proof. exact (MK_COMB (@lem2001391 x) (@lem2001390)). Qed.
Lemma lem2001393 (x : real) : (term329 x) = (term331 x).
Proof. exact (TRANS (@lem2001268 x) (@lem2001392 x)). Qed.
Lemma lem2001394 (x : real) : (term328 x) = (term331 x).
Proof. exact (TRANS (@lem2001267 x) (@lem2001393 x)). Qed.
Lemma lem2001403 (x : real) : (term287 x) = (term287 x).
Proof. exact (eq_refl (term287 x)). Qed.
Lemma lem2001406 (x : real) : (term324 x) = (term332 x).
Proof. exact (MK_COMB (@lem2001403 x) (@lem2001394 x)). Qed.
Lemma lem2001407 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2001408 (x : real) : (term333 x) = (term334 x).
Proof. exact (MK_COMB (@lem2001407) (@lem2001406 x)). Qed.
Lemma lem2001409 (x : real) : (term335 x) = (term336 x).
Proof. exact (MK_COMB (@lem2001408 x) (@lem2001206)). Qed.
Lemma lem2001410 (x : real) : (term336 x) = (term337 x).
Proof. exact (@lem1982792 (term332 x) term2). Qed.
Lemma lem2001412 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2001413 : term2 = term67.
Proof. exact (@lem2001412 (NUMERAL 0)). Qed.
Lemma lem2001415 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2001416 : term12 = term18.
Proof. exact (@lem2001415 term15). Qed.
Lemma lem2001417 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2001418 : term19 = term20.
Proof. exact (MK_COMB (@lem2001417) (@lem2001416)). Qed.
Lemma lem2001419 : term258 = term259.
Proof. exact (MK_COMB (@lem2001418) (@lem2001413)). Qed.
Lemma lem2001420 : term259 = term260.
Proof. exact (@lem1981613 term12 term2 term5 term5). Qed.
Lemma lem2001422 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2001423 : term26 = term27.
Proof. exact (@lem2001422 term15 term15). Qed.
Lemma lem2001424 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2001425 : term29 = term15.
Proof. exact (EQ_MP (@lem2001424) (@lem940073)). Qed.
Lemma lem2001426 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001427 : term27 = term5.
Proof. exact (MK_COMB (@lem2001426) (@lem2001425)). Qed.
Lemma lem2001428 : term26 = term5.
Proof. exact (TRANS (@lem2001423) (@lem2001427)). Qed.
Lemma lem2001430 (x : nat) : (term261 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2001431 : term258 = term2.
Proof. exact (@lem2001430 term15). Qed.
Lemma lem2001432 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2001433 : term262 = term263.
Proof. exact (MK_COMB (@lem2001432) (@lem2001431)). Qed.
Lemma lem2001434 : term260 = term67.
Proof. exact (MK_COMB (@lem2001433) (@lem2001428)). Qed.
Lemma lem2001435 : term259 = term67.
Proof. exact (TRANS (@lem2001420) (@lem2001434)). Qed.
Lemma lem2001436 : term258 = term67.
Proof. exact (TRANS (@lem2001419) (@lem2001435)). Qed.
Lemma lem2001438 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2001439 : term67 = term2.
Proof. exact (@lem2001438 term2). Qed.
Lemma lem2001440 : term258 = term2.
Proof. exact (TRANS (@lem2001436) (@lem2001439)). Qed.
Lemma lem2001441 (x : real) : (term338 x) = (term338 x).
Proof. exact (eq_refl (term338 x)). Qed.
Lemma lem2001442 (x : real) : (term337 x) = (term339 x).
Proof. exact (MK_COMB (@lem2001441 x) (@lem2001440)). Qed.
Lemma lem2001443 (x : real) : (term339 x) = (term332 x).
Proof. exact (@lem1982723 (term332 x)). Qed.
Lemma lem2001444 (x : real) : (term337 x) = (term332 x).
Proof. exact (TRANS (@lem2001442 x) (@lem2001443 x)). Qed.
Lemma lem2001445 (x : real) : (term336 x) = (term332 x).
Proof. exact (TRANS (@lem2001410 x) (@lem2001444 x)). Qed.
Lemma lem2001446 (x : real) : (term335 x) = (term332 x).
Proof. exact (TRANS (@lem2001409 x) (@lem2001445 x)). Qed.
Lemma lem2001447 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2001448 (x : real) : (term340 x) = (term341 x).
Proof. exact (MK_COMB (@lem2001447) (@lem2001446 x)). Qed.
Lemma lem2001449 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2001450 (x : real) : (term323 x) = (term342 x).
Proof. exact (MK_COMB (@lem2001448 x) (@lem2001449)). Qed.
Lemma lem2001451 (x : real) : (term322 x) = (term342 x).
Proof. exact (TRANS (@lem2001205 x) (@lem2001450 x)). Qed.
Lemma lem2001452 (x : real) : (term343 x) = (term344 x).
Proof. exact (@lem1988289 (term345 x) term2). Qed.
Lemma lem2001453 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2001454 : term12 = term12.
Proof. exact (eq_refl term12). Qed.
Lemma lem2001466 (x : real) : (term325 x) = (term10 x).
Proof. exact (@lem1982785 (term4 x)). Qed.
Lemma lem2001467 (x : real) : (term10 x) = (term11 x).
Proof. exact (@lem1982781 (real_abs x) term12 term5). Qed.
Lemma lem2001469 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2001470 : term5 = term14.
Proof. exact (@lem2001469 term15). Qed.
Lemma lem2001472 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2001473 : term12 = term18.
Proof. exact (@lem2001472 term15). Qed.
Lemma lem2001474 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2001475 : term19 = term20.
Proof. exact (MK_COMB (@lem2001474) (@lem2001473)). Qed.
Lemma lem2001476 : term21 = term22.
Proof. exact (MK_COMB (@lem2001475) (@lem2001470)). Qed.
Lemma lem2001477 : term22 = term23.
Proof. exact (@lem1981613 term12 term5 term5 term5). Qed.
Lemma lem2001479 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2001480 : term26 = term27.
Proof. exact (@lem2001479 term15 term15). Qed.
Lemma lem2001481 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2001482 : term29 = term15.
Proof. exact (EQ_MP (@lem2001481) (@lem940073)). Qed.
Lemma lem2001483 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001484 : term27 = term5.
Proof. exact (MK_COMB (@lem2001483) (@lem2001482)). Qed.
Lemma lem2001485 : term26 = term5.
Proof. exact (TRANS (@lem2001480) (@lem2001484)). Qed.
Lemma lem2001487 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2001488 : term21 = term32.
Proof. exact (@lem2001487 term15 term15). Qed.
Lemma lem2001489 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2001490 : term29 = term15.
Proof. exact (EQ_MP (@lem2001489) (@lem940073)). Qed.
Lemma lem2001491 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001492 : term27 = term5.
Proof. exact (MK_COMB (@lem2001491) (@lem2001490)). Qed.
Lemma lem2001493 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2001494 : term32 = term12.
Proof. exact (MK_COMB (@lem2001493) (@lem2001492)). Qed.
Lemma lem2001495 : term21 = term12.
Proof. exact (TRANS (@lem2001488) (@lem2001494)). Qed.
Lemma lem2001496 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2001497 : term33 = term34.
Proof. exact (MK_COMB (@lem2001496) (@lem2001495)). Qed.
Lemma lem2001498 : term23 = term18.
Proof. exact (MK_COMB (@lem2001497) (@lem2001485)). Qed.
Lemma lem2001499 : term22 = term18.
Proof. exact (TRANS (@lem2001477) (@lem2001498)). Qed.
Lemma lem2001500 : term21 = term18.
Proof. exact (TRANS (@lem2001476) (@lem2001499)). Qed.
Lemma lem2001502 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2001503 : term18 = term12.
Proof. exact (@lem2001502 term12). Qed.
Lemma lem2001504 : term21 = term12.
Proof. exact (TRANS (@lem2001500) (@lem2001503)). Qed.
Lemma lem2001507 (x : real) : (term36 x) = (term36 x).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem2001508 (x : real) : (term11 x) = (term37 x).
Proof. exact (MK_COMB (@lem2001507 x) (@lem2001504)). Qed.
Lemma lem2001509 (x : real) : (term10 x) = (term37 x).
Proof. exact (TRANS (@lem2001467 x) (@lem2001508 x)). Qed.
Lemma lem2001511 (x : real) : (term325 x) = (term37 x).
Proof. exact (TRANS (@lem2001466 x) (@lem2001509 x)). Qed.
Lemma lem2001512 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2001513 (x : real) : (term326 x) = (term327 x).
Proof. exact (MK_COMB (@lem2001512) (@lem2001511 x)). Qed.
Lemma lem2001514 (x : real) : (term328 x) = (term329 x).
Proof. exact (MK_COMB (@lem2001513 x) (@lem2001454)). Qed.
Lemma lem2001515 (x : real) : (term329 x) = (term330 x).
Proof. exact (@lem1982755 (term181 x) term12 term12). Qed.
Lemma lem2001517 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2001518 : term12 = term18.
Proof. exact (@lem2001517 term15). Qed.
Lemma lem2001520 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2001521 : term12 = term18.
Proof. exact (@lem2001520 term15). Qed.
Lemma lem2001522 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2001523 : term47 = term98.
Proof. exact (MK_COMB (@lem2001522) (@lem2001521)). Qed.
Lemma lem2001524 : term115 = term116.
Proof. exact (MK_COMB (@lem2001523) (@lem2001518)). Qed.
Lemma lem2001525 : term117.
Proof. exact (@lem1981473 term12 term5 term12 term5 term118 term5). Qed.
Lemma lem2001527 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2001528 : term66 = term73.
Proof. exact (@lem2001527 (NUMERAL 0) term15). Qed.
Lemma lem2001529 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2001530 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2001531 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2001530 h1) (fun h1 : term73 = True => @lem2001529)). Qed.
Lemma lem2001532 : term73 = True.
Proof. exact (EQ_MP (@lem2001531) (@lem2001529)). Qed.
Lemma lem2001533 : term66 = True.
Proof. exact (TRANS (@lem2001528) (@lem2001532)). Qed.
Lemma lem2001534 : True = term66.
Proof. exact (SYM (@lem2001533)). Qed.
Lemma lem2001535 : term66.
Proof. exact (EQ_MP (@lem2001534) (@lem0)). Qed.
Lemma lem2001536 : term119.
Proof. exact (@lem2001525 (@lem2001535)). Qed.
Lemma lem2001538 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2001539 : term66 = term73.
Proof. exact (@lem2001538 (NUMERAL 0) term15). Qed.
Lemma lem2001540 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2001541 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2001542 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2001541 h1) (fun h1 : term73 = True => @lem2001540)). Qed.
Lemma lem2001543 : term73 = True.
Proof. exact (EQ_MP (@lem2001542) (@lem2001540)). Qed.
Lemma lem2001544 : term66 = True.
Proof. exact (TRANS (@lem2001539) (@lem2001543)). Qed.
Lemma lem2001545 : True = term66.
Proof. exact (SYM (@lem2001544)). Qed.
Lemma lem2001546 : term66.
Proof. exact (EQ_MP (@lem2001545) (@lem0)). Qed.
Lemma lem2001547 : term120.
Proof. exact (@lem2001536 (@lem2001546)). Qed.
Lemma lem2001549 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2001550 : term66 = term73.
Proof. exact (@lem2001549 (NUMERAL 0) term15). Qed.
Lemma lem2001551 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2001552 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2001553 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2001552 h1) (fun h1 : term73 = True => @lem2001551)). Qed.
Lemma lem2001554 : term73 = True.
Proof. exact (EQ_MP (@lem2001553) (@lem2001551)). Qed.
Lemma lem2001555 : term66 = True.
Proof. exact (TRANS (@lem2001550) (@lem2001554)). Qed.
Lemma lem2001556 : True = term66.
Proof. exact (SYM (@lem2001555)). Qed.
Lemma lem2001557 : term66.
Proof. exact (EQ_MP (@lem2001556) (@lem0)). Qed.
Lemma lem2001558 : term121.
Proof. exact (@lem2001547 (@lem2001557)). Qed.
Lemma lem2001560 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2001561 : term21 = term32.
Proof. exact (@lem2001560 term15 term15). Qed.
Lemma lem2001562 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2001563 : term29 = term15.
Proof. exact (EQ_MP (@lem2001562) (@lem940073)). Qed.
Lemma lem2001564 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001565 : term27 = term5.
Proof. exact (MK_COMB (@lem2001564) (@lem2001563)). Qed.
Lemma lem2001566 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2001567 : term32 = term12.
Proof. exact (MK_COMB (@lem2001566) (@lem2001565)). Qed.
Lemma lem2001568 : term21 = term12.
Proof. exact (TRANS (@lem2001561) (@lem2001567)). Qed.
Lemma lem2001570 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2001571 : term21 = term32.
Proof. exact (@lem2001570 term15 term15). Qed.
Lemma lem2001572 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2001573 : term29 = term15.
Proof. exact (EQ_MP (@lem2001572) (@lem940073)). Qed.
Lemma lem2001574 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001575 : term27 = term5.
Proof. exact (MK_COMB (@lem2001574) (@lem2001573)). Qed.
Lemma lem2001576 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2001577 : term32 = term12.
Proof. exact (MK_COMB (@lem2001576) (@lem2001575)). Qed.
Lemma lem2001578 : term21 = term12.
Proof. exact (TRANS (@lem2001571) (@lem2001577)). Qed.
Lemma lem2001579 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2001580 : term105 = term47.
Proof. exact (MK_COMB (@lem2001579) (@lem2001578)). Qed.
Lemma lem2001581 : term122 = term115.
Proof. exact (MK_COMB (@lem2001580) (@lem2001568)). Qed.
Lemma lem2001582 : term115 = term123.
Proof. exact (@lem1367763 term15 term15). Qed.
Lemma lem2001583 : term124 = term125.
Proof. exact (@lem706885). Qed.
Lemma lem2001584 : (term124 = term125) = (term126 = term127).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term125). Qed.
Lemma lem2001585 : term126 = term127.
Proof. exact (EQ_MP (@lem2001584) (@lem2001583)). Qed.
Lemma lem2001586 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001587 : term128 = term129.
Proof. exact (MK_COMB (@lem2001586) (@lem2001585)). Qed.
Lemma lem2001588 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2001589 : term123 = term118.
Proof. exact (MK_COMB (@lem2001588) (@lem2001587)). Qed.
Lemma lem2001590 : term115 = term118.
Proof. exact (TRANS (@lem2001582) (@lem2001589)). Qed.
Lemma lem2001591 : term122 = term118.
Proof. exact (TRANS (@lem2001581) (@lem2001590)). Qed.
Lemma lem2001592 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2001593 : term130 = term131.
Proof. exact (MK_COMB (@lem2001592) (@lem2001591)). Qed.
Lemma lem2001594 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem2001595 : term132 = term133.
Proof. exact (MK_COMB (@lem2001593) (@lem2001594)). Qed.
Lemma lem2001597 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2001598 : term133 = term134.
Proof. exact (@lem2001597 term127 term15). Qed.
Lemma lem2001599 : term135 = term125.
Proof. exact (@lem996237 term125). Qed.
Lemma lem2001600 : (term135 = term125) = (term136 = term127).
Proof. exact (@lem1007663 term125 (BIT1 0) term125). Qed.
Lemma lem2001601 : term136 = term127.
Proof. exact (EQ_MP (@lem2001600) (@lem2001599)). Qed.
Lemma lem2001602 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001603 : term137 = term129.
Proof. exact (MK_COMB (@lem2001602) (@lem2001601)). Qed.
Lemma lem2001604 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2001605 : term134 = term118.
Proof. exact (MK_COMB (@lem2001604) (@lem2001603)). Qed.
Lemma lem2001606 : term133 = term118.
Proof. exact (TRANS (@lem2001598) (@lem2001605)). Qed.
Lemma lem2001607 : term132 = term118.
Proof. exact (TRANS (@lem2001595) (@lem2001606)). Qed.
Lemma lem2001609 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2001610 : term26 = term27.
Proof. exact (@lem2001609 term15 term15). Qed.
Lemma lem2001611 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2001612 : term29 = term15.
Proof. exact (EQ_MP (@lem2001611) (@lem940073)). Qed.
Lemma lem2001613 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001614 : term27 = term5.
Proof. exact (MK_COMB (@lem2001613) (@lem2001612)). Qed.
Lemma lem2001615 : term26 = term5.
Proof. exact (TRANS (@lem2001610) (@lem2001614)). Qed.
Lemma lem2001616 : term131 = term131.
Proof. exact (eq_refl term131). Qed.
Lemma lem2001617 : term138 = term133.
Proof. exact (MK_COMB (@lem2001616) (@lem2001615)). Qed.
Lemma lem2001619 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2001620 : term133 = term134.
Proof. exact (@lem2001619 term127 term15). Qed.
Lemma lem2001621 : term135 = term125.
Proof. exact (@lem996237 term125). Qed.
Lemma lem2001622 : (term135 = term125) = (term136 = term127).
Proof. exact (@lem1007663 term125 (BIT1 0) term125). Qed.
Lemma lem2001623 : term136 = term127.
Proof. exact (EQ_MP (@lem2001622) (@lem2001621)). Qed.
Lemma lem2001624 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001625 : term137 = term129.
Proof. exact (MK_COMB (@lem2001624) (@lem2001623)). Qed.
Lemma lem2001626 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2001627 : term134 = term118.
Proof. exact (MK_COMB (@lem2001626) (@lem2001625)). Qed.
Lemma lem2001628 : term133 = term118.
Proof. exact (TRANS (@lem2001620) (@lem2001627)). Qed.
Lemma lem2001629 : term138 = term118.
Proof. exact (TRANS (@lem2001617) (@lem2001628)). Qed.
Lemma lem2001630 : term118 = term138.
Proof. exact (SYM (@lem2001629)). Qed.
Lemma lem2001631 : term132 = term138.
Proof. exact (TRANS (@lem2001607) (@lem2001630)). Qed.
Lemma lem2001632 : term116 = term139.
Proof. exact (@lem2001558 (@lem2001631)). Qed.
Lemma lem2001633 : term115 = term139.
Proof. exact (TRANS (@lem2001524) (@lem2001632)). Qed.
Lemma lem2001635 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2001636 : term139 = term118.
Proof. exact (@lem2001635 term118). Qed.
Lemma lem2001637 : term115 = term118.
Proof. exact (TRANS (@lem2001633) (@lem2001636)). Qed.
Lemma lem2001638 (x : real) : (term36 x) = (term36 x).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem2001639 (x : real) : (term330 x) = (term331 x).
Proof. exact (MK_COMB (@lem2001638 x) (@lem2001637)). Qed.
Lemma lem2001640 (x : real) : (term329 x) = (term331 x).
Proof. exact (TRANS (@lem2001515 x) (@lem2001639 x)). Qed.
Lemma lem2001641 (x : real) : (term328 x) = (term331 x).
Proof. exact (TRANS (@lem2001514 x) (@lem2001640 x)). Qed.
Lemma lem2001644 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem2001647 (x : real) : (term345 x) = (term346 x).
Proof. exact (MK_COMB (@lem2001644 x) (@lem2001641 x)). Qed.
Lemma lem2001648 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2001649 (x : real) : (term347 x) = (term348 x).
Proof. exact (MK_COMB (@lem2001648) (@lem2001647 x)). Qed.
Lemma lem2001650 (x : real) : (term349 x) = (term350 x).
Proof. exact (MK_COMB (@lem2001649 x) (@lem2001453)). Qed.
Lemma lem2001651 (x : real) : (term350 x) = (term351 x).
Proof. exact (@lem1982792 (term346 x) term2). Qed.
Lemma lem2001653 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2001654 : term2 = term67.
Proof. exact (@lem2001653 (NUMERAL 0)). Qed.
Lemma lem2001656 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2001657 : term12 = term18.
Proof. exact (@lem2001656 term15). Qed.
Lemma lem2001658 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2001659 : term19 = term20.
Proof. exact (MK_COMB (@lem2001658) (@lem2001657)). Qed.
Lemma lem2001660 : term258 = term259.
Proof. exact (MK_COMB (@lem2001659) (@lem2001654)). Qed.
Lemma lem2001661 : term259 = term260.
Proof. exact (@lem1981613 term12 term2 term5 term5). Qed.
Lemma lem2001663 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2001664 : term26 = term27.
Proof. exact (@lem2001663 term15 term15). Qed.
Lemma lem2001665 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2001666 : term29 = term15.
Proof. exact (EQ_MP (@lem2001665) (@lem940073)). Qed.
Lemma lem2001667 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001668 : term27 = term5.
Proof. exact (MK_COMB (@lem2001667) (@lem2001666)). Qed.
Lemma lem2001669 : term26 = term5.
Proof. exact (TRANS (@lem2001664) (@lem2001668)). Qed.
Lemma lem2001671 (x : nat) : (term261 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2001672 : term258 = term2.
Proof. exact (@lem2001671 term15). Qed.
Lemma lem2001673 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2001674 : term262 = term263.
Proof. exact (MK_COMB (@lem2001673) (@lem2001672)). Qed.
Lemma lem2001675 : term260 = term67.
Proof. exact (MK_COMB (@lem2001674) (@lem2001669)). Qed.
Lemma lem2001676 : term259 = term67.
Proof. exact (TRANS (@lem2001661) (@lem2001675)). Qed.
Lemma lem2001677 : term258 = term67.
Proof. exact (TRANS (@lem2001660) (@lem2001676)). Qed.
Lemma lem2001679 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2001680 : term67 = term2.
Proof. exact (@lem2001679 term2). Qed.
Lemma lem2001681 : term258 = term2.
Proof. exact (TRANS (@lem2001677) (@lem2001680)). Qed.
Lemma lem2001682 (x : real) : (term352 x) = (term352 x).
Proof. exact (eq_refl (term352 x)). Qed.
Lemma lem2001683 (x : real) : (term351 x) = (term353 x).
Proof. exact (MK_COMB (@lem2001682 x) (@lem2001681)). Qed.
Lemma lem2001684 (x : real) : (term353 x) = (term346 x).
Proof. exact (@lem1982723 (term346 x)). Qed.
Lemma lem2001685 (x : real) : (term351 x) = (term346 x).
Proof. exact (TRANS (@lem2001683 x) (@lem2001684 x)). Qed.
Lemma lem2001686 (x : real) : (term350 x) = (term346 x).
Proof. exact (TRANS (@lem2001651 x) (@lem2001685 x)). Qed.
Lemma lem2001687 (x : real) : (term349 x) = (term346 x).
Proof. exact (TRANS (@lem2001650 x) (@lem2001686 x)). Qed.
Lemma lem2001688 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2001689 (x : real) : (term354 x) = (term355 x).
Proof. exact (MK_COMB (@lem2001688) (@lem2001687 x)). Qed.
Lemma lem2001690 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2001691 (x : real) : (term344 x) = (term356 x).
Proof. exact (MK_COMB (@lem2001689 x) (@lem2001690)). Qed.
Lemma lem2001692 (x : real) : (term343 x) = (term356 x).
Proof. exact (TRANS (@lem2001452 x) (@lem2001691 x)). Qed.
Lemma lem2001693 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2001694 (x : real) : (term357 x) = (term358 x).
Proof. exact (MK_COMB (@lem2001693) (@lem2001451 x)). Qed.
Lemma lem2001695 (x : real) : (term241 x) = (term359 x).
Proof. exact (MK_COMB (@lem2001694 x) (@lem2001692 x)). Qed.
Lemma lem2001696 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2001697 (x : real) : (term242 x) = (term360 x).
Proof. exact (MK_COMB (@lem2001696) (@lem2001204 x)). Qed.
Lemma lem2001698 (x : real) : (term244 x) = (term361 x).
Proof. exact (MK_COMB (@lem2001697 x) (@lem2001695 x)). Qed.
Lemma lem2001699 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2001700 (x : real) : (term251 x) = (term362 x).
Proof. exact (MK_COMB (@lem2001699) (@lem2001135 x)). Qed.
Lemma lem2001701 (x : real) : (term252 x) = (term363 x).
Proof. exact (MK_COMB (@lem2001700 x) (@lem2001698 x)). Qed.
Lemma lem2001702 (x : real) : (term236 x) = (term363 x).
Proof. exact (TRANS (@lem2000725 x) (@lem2001701 x)). Qed.
Lemma lem2001704 (a : real) (x : real) (r : real) : (term217 x a r) = (term218 a x r).
Proof. exact (proj1 (@lem1482703 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2001705 (x : real) : (term321 x) = (term364 x).
Proof. exact (@lem2001704 term12 x term2). Qed.
Lemma lem2001712 (x : real) : (term46 x) = x.
Proof. exact (@lem1982733 x). Qed.
Lemma lem2001715 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem2001716 (x : real) : (term48 x) = (term49 x).
Proof. exact (MK_COMB (@lem2001715) (@lem2001712 x)). Qed.
Lemma lem2001717 (x : real) : (term49 x) = (term50 x).
Proof. exact (@lem1982761 x term12). Qed.
Lemma lem2001718 (x : real) : (term48 x) = (term50 x).
Proof. exact (TRANS (@lem2001716 x) (@lem2001717 x)). Qed.
Lemma lem2001719 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2001720 (x : real) : (term365 x) = (term366 x).
Proof. exact (MK_COMB (@lem2001719) (@lem2001718 x)). Qed.
Lemma lem2001721 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2001722 (x : real) : (term367 x) = (term368 x).
Proof. exact (MK_COMB (@lem2001720 x) (@lem2001721)). Qed.
Lemma lem2001735 (x : real) : (term55 x) = (term56 x).
Proof. exact (@lem1982761 (term57 x) term12). Qed.
Lemma lem2001736 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2001737 (x : real) : (term369 x) = (term370 x).
Proof. exact (MK_COMB (@lem2001736) (@lem2001735 x)). Qed.
Lemma lem2001738 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2001739 (x : real) : (term371 x) = (term372 x).
Proof. exact (MK_COMB (@lem2001737 x) (@lem2001738)). Qed.
Lemma lem2001740 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2001741 (x : real) : (term373 x) = (term374 x).
Proof. exact (MK_COMB (@lem2001740) (@lem2001739 x)). Qed.
Lemma lem2001742 (x : real) : (term364 x) = (term375 x).
Proof. exact (MK_COMB (@lem2001741 x) (@lem2001722 x)). Qed.
Lemma lem2001743 (x : real) : (term321 x) = (term375 x).
Proof. exact (TRANS (@lem2001705 x) (@lem2001742 x)). Qed.
Lemma lem2001744 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2001745 (x : real) : (term360 x) = (term376 x).
Proof. exact (MK_COMB (@lem2001744) (@lem2001743 x)). Qed.
Lemma lem2001747 (a : real) (x : real) (b : real) (r : real) : (term377 a x b r) = (term378 a x b r).
Proof. exact (proj1 (@lem1482705 x a b (@el real) (@el real) r)). Qed.
Lemma lem2001748 (x : real) : (term342 x) = (term379 x).
Proof. exact (@lem2001747 (term57 x) x term118 term2). Qed.
Lemma lem2001749 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem2001756 (x : real) : (term46 x) = x.
Proof. exact (@lem1982733 x). Qed.
Lemma lem2001757 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2001758 (x : real) : (term380 x) = (real_add x).
Proof. exact (MK_COMB (@lem2001757) (@lem2001756 x)). Qed.
Lemma lem2001761 (x : real) : (term381 x) = (term382 x).
Proof. exact (MK_COMB (@lem2001758 x) (@lem2001749)). Qed.
Lemma lem2001770 (x : real) : (term287 x) = (term287 x).
Proof. exact (eq_refl (term287 x)). Qed.
Lemma lem2001771 (x : real) : (term383 x) = (term384 x).
Proof. exact (MK_COMB (@lem2001770 x) (@lem2001761 x)). Qed.
Lemma lem2001772 (x : real) : (term384 x) = (term385 x).
Proof. exact (@lem1982763 (term57 x) x term118). Qed.
Lemma lem2001773 (x : real) : (term96 x) = (term97 x).
Proof. exact (@lem1982713 term12 x). Qed.
Lemma lem2001775 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2001776 : term5 = term14.
Proof. exact (@lem2001775 term15). Qed.
Lemma lem2001778 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2001779 : term12 = term18.
Proof. exact (@lem2001778 term15). Qed.
Lemma lem2001780 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2001781 : term47 = term98.
Proof. exact (MK_COMB (@lem2001780) (@lem2001779)). Qed.
Lemma lem2001782 : term99 = term100.
Proof. exact (MK_COMB (@lem2001781) (@lem2001776)). Qed.
Lemma lem2001783 : term101.
Proof. exact (@lem1981473 term12 term5 term5 term5 term2 term5). Qed.
Lemma lem2001785 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2001786 : term66 = term73.
Proof. exact (@lem2001785 (NUMERAL 0) term15). Qed.
Lemma lem2001787 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2001788 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2001789 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2001788 h1) (fun h1 : term73 = True => @lem2001787)). Qed.
Lemma lem2001790 : term73 = True.
Proof. exact (EQ_MP (@lem2001789) (@lem2001787)). Qed.
Lemma lem2001791 : term66 = True.
Proof. exact (TRANS (@lem2001786) (@lem2001790)). Qed.
Lemma lem2001792 : True = term66.
Proof. exact (SYM (@lem2001791)). Qed.
Lemma lem2001793 : term66.
Proof. exact (EQ_MP (@lem2001792) (@lem0)). Qed.
Lemma lem2001794 : term102.
Proof. exact (@lem2001783 (@lem2001793)). Qed.
Lemma lem2001796 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2001797 : term66 = term73.
Proof. exact (@lem2001796 (NUMERAL 0) term15). Qed.
Lemma lem2001798 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2001799 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2001800 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2001799 h1) (fun h1 : term73 = True => @lem2001798)). Qed.
Lemma lem2001801 : term73 = True.
Proof. exact (EQ_MP (@lem2001800) (@lem2001798)). Qed.
Lemma lem2001802 : term66 = True.
Proof. exact (TRANS (@lem2001797) (@lem2001801)). Qed.
Lemma lem2001803 : True = term66.
Proof. exact (SYM (@lem2001802)). Qed.
Lemma lem2001804 : term66.
Proof. exact (EQ_MP (@lem2001803) (@lem0)). Qed.
Lemma lem2001805 : term103.
Proof. exact (@lem2001794 (@lem2001804)). Qed.
Lemma lem2001807 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2001808 : term66 = term73.
Proof. exact (@lem2001807 (NUMERAL 0) term15). Qed.
Lemma lem2001809 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2001810 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2001811 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2001810 h1) (fun h1 : term73 = True => @lem2001809)). Qed.
Lemma lem2001812 : term73 = True.
Proof. exact (EQ_MP (@lem2001811) (@lem2001809)). Qed.
Lemma lem2001813 : term66 = True.
Proof. exact (TRANS (@lem2001808) (@lem2001812)). Qed.
Lemma lem2001814 : True = term66.
Proof. exact (SYM (@lem2001813)). Qed.
Lemma lem2001815 : term66.
Proof. exact (EQ_MP (@lem2001814) (@lem0)). Qed.
Lemma lem2001816 : term104.
Proof. exact (@lem2001805 (@lem2001815)). Qed.
Lemma lem2001818 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2001819 : term26 = term27.
Proof. exact (@lem2001818 term15 term15). Qed.
Lemma lem2001820 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2001821 : term29 = term15.
Proof. exact (EQ_MP (@lem2001820) (@lem940073)). Qed.
Lemma lem2001822 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001823 : term27 = term5.
Proof. exact (MK_COMB (@lem2001822) (@lem2001821)). Qed.
Lemma lem2001824 : term26 = term5.
Proof. exact (TRANS (@lem2001819) (@lem2001823)). Qed.
Lemma lem2001826 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2001827 : term21 = term32.
Proof. exact (@lem2001826 term15 term15). Qed.
Lemma lem2001828 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2001829 : term29 = term15.
Proof. exact (EQ_MP (@lem2001828) (@lem940073)). Qed.
Lemma lem2001830 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001831 : term27 = term5.
Proof. exact (MK_COMB (@lem2001830) (@lem2001829)). Qed.
Lemma lem2001832 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2001833 : term32 = term12.
Proof. exact (MK_COMB (@lem2001832) (@lem2001831)). Qed.
Lemma lem2001834 : term21 = term12.
Proof. exact (TRANS (@lem2001827) (@lem2001833)). Qed.
Lemma lem2001835 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2001836 : term105 = term47.
Proof. exact (MK_COMB (@lem2001835) (@lem2001834)). Qed.
Lemma lem2001837 : term106 = term99.
Proof. exact (MK_COMB (@lem2001836) (@lem2001824)). Qed.
Lemma lem2001839 (m : nat) : (term107 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2001840 : term99 = term2.
Proof. exact (@lem2001839 term15). Qed.
Lemma lem2001841 : term106 = term2.
Proof. exact (TRANS (@lem2001837) (@lem2001840)). Qed.
Lemma lem2001842 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2001843 : term108 = term109.
Proof. exact (MK_COMB (@lem2001842) (@lem2001841)). Qed.
Lemma lem2001844 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem2001845 : term110 = term78.
Proof. exact (MK_COMB (@lem2001843) (@lem2001844)). Qed.
Lemma lem2001847 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2001848 : term78 = term2.
Proof. exact (@lem2001847 term15). Qed.
Lemma lem2001849 : term110 = term2.
Proof. exact (TRANS (@lem2001845) (@lem2001848)). Qed.
Lemma lem2001851 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2001852 : term26 = term27.
Proof. exact (@lem2001851 term15 term15). Qed.
Lemma lem2001853 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2001854 : term29 = term15.
Proof. exact (EQ_MP (@lem2001853) (@lem940073)). Qed.
Lemma lem2001855 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001856 : term27 = term5.
Proof. exact (MK_COMB (@lem2001855) (@lem2001854)). Qed.
Lemma lem2001857 : term26 = term5.
Proof. exact (TRANS (@lem2001852) (@lem2001856)). Qed.
Lemma lem2001858 : term109 = term109.
Proof. exact (eq_refl term109). Qed.
Lemma lem2001859 : term111 = term78.
Proof. exact (MK_COMB (@lem2001858) (@lem2001857)). Qed.
Lemma lem2001861 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2001862 : term78 = term2.
Proof. exact (@lem2001861 term15). Qed.
Lemma lem2001863 : term111 = term2.
Proof. exact (TRANS (@lem2001859) (@lem2001862)). Qed.
Lemma lem2001864 : term2 = term111.
Proof. exact (SYM (@lem2001863)). Qed.
Lemma lem2001865 : term110 = term111.
Proof. exact (TRANS (@lem2001849) (@lem2001864)). Qed.
Lemma lem2001866 : term100 = term67.
Proof. exact (@lem2001816 (@lem2001865)). Qed.
Lemma lem2001867 : term99 = term67.
Proof. exact (TRANS (@lem2001782) (@lem2001866)). Qed.
Lemma lem2001869 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2001870 : term67 = term2.
Proof. exact (@lem2001869 term2). Qed.
Lemma lem2001871 : term99 = term2.
Proof. exact (TRANS (@lem2001867) (@lem2001870)). Qed.
Lemma lem2001872 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2001873 : term112 = term109.
Proof. exact (MK_COMB (@lem2001872) (@lem2001871)). Qed.
Lemma lem2001874 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2001875 (x : real) : (term97 x) = (term113 x).
Proof. exact (MK_COMB (@lem2001873) (@lem2001874 x)). Qed.
Lemma lem2001876 (x : real) : (term96 x) = (term113 x).
Proof. exact (TRANS (@lem2001773 x) (@lem2001875 x)). Qed.
Lemma lem2001877 (x : real) : (term113 x) = term2.
Proof. exact (@lem1982719 x). Qed.
Lemma lem2001878 (x : real) : (term96 x) = term2.
Proof. exact (TRANS (@lem2001876 x) (@lem2001877 x)). Qed.
Lemma lem2001879 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2001880 (x : real) : (term114 x) = term38.
Proof. exact (MK_COMB (@lem2001879) (@lem2001878 x)). Qed.
Lemma lem2001881 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem2001882 (x : real) : (term385 x) = term140.
Proof. exact (MK_COMB (@lem2001880 x) (@lem2001881)). Qed.
Lemma lem2001883 (x : real) : (term384 x) = term140.
Proof. exact (TRANS (@lem2001772 x) (@lem2001882 x)). Qed.
Lemma lem2001884 : term140 = term118.
Proof. exact (@lem1982721 term118). Qed.
Lemma lem2001885 (x : real) : (term384 x) = term118.
Proof. exact (TRANS (@lem2001883 x) (@lem2001884)). Qed.
Lemma lem2001886 (x : real) : (term383 x) = term118.
Proof. exact (TRANS (@lem2001771 x) (@lem2001885 x)). Qed.
Lemma lem2001887 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2001888 (x : real) : (term386 x) = term387.
Proof. exact (MK_COMB (@lem2001887) (@lem2001886 x)). Qed.
Lemma lem2001889 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2001890 (x : real) : (term388 x) = term389.
Proof. exact (MK_COMB (@lem2001888 x) (@lem2001889)). Qed.
Lemma lem2001914 (x : real) : (term390 x) = (term391 x).
Proof. exact (@lem1982763 (term57 x) (term57 x) term118). Qed.
Lemma lem2001915 (x : real) : (term392 x) = (term393 x).
Proof. exact (@lem1982711 term12 term12 x). Qed.
Lemma lem2001917 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2001918 : term12 = term18.
Proof. exact (@lem2001917 term15). Qed.
Lemma lem2001920 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2001921 : term12 = term18.
Proof. exact (@lem2001920 term15). Qed.
Lemma lem2001922 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2001923 : term47 = term98.
Proof. exact (MK_COMB (@lem2001922) (@lem2001921)). Qed.
Lemma lem2001924 : term115 = term116.
Proof. exact (MK_COMB (@lem2001923) (@lem2001918)). Qed.
Lemma lem2001925 : term117.
Proof. exact (@lem1981473 term12 term5 term12 term5 term118 term5). Qed.
Lemma lem2001927 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2001928 : term66 = term73.
Proof. exact (@lem2001927 (NUMERAL 0) term15). Qed.
Lemma lem2001929 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2001930 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2001931 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2001930 h1) (fun h1 : term73 = True => @lem2001929)). Qed.
Lemma lem2001932 : term73 = True.
Proof. exact (EQ_MP (@lem2001931) (@lem2001929)). Qed.
Lemma lem2001933 : term66 = True.
Proof. exact (TRANS (@lem2001928) (@lem2001932)). Qed.
Lemma lem2001934 : True = term66.
Proof. exact (SYM (@lem2001933)). Qed.
Lemma lem2001935 : term66.
Proof. exact (EQ_MP (@lem2001934) (@lem0)). Qed.
Lemma lem2001936 : term119.
Proof. exact (@lem2001925 (@lem2001935)). Qed.
Lemma lem2001938 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2001939 : term66 = term73.
Proof. exact (@lem2001938 (NUMERAL 0) term15). Qed.
Lemma lem2001940 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2001941 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2001942 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2001941 h1) (fun h1 : term73 = True => @lem2001940)). Qed.
Lemma lem2001943 : term73 = True.
Proof. exact (EQ_MP (@lem2001942) (@lem2001940)). Qed.
Lemma lem2001944 : term66 = True.
Proof. exact (TRANS (@lem2001939) (@lem2001943)). Qed.
Lemma lem2001945 : True = term66.
Proof. exact (SYM (@lem2001944)). Qed.
Lemma lem2001946 : term66.
Proof. exact (EQ_MP (@lem2001945) (@lem0)). Qed.
Lemma lem2001947 : term120.
Proof. exact (@lem2001936 (@lem2001946)). Qed.
Lemma lem2001949 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2001950 : term66 = term73.
Proof. exact (@lem2001949 (NUMERAL 0) term15). Qed.
Lemma lem2001951 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2001952 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2001953 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2001952 h1) (fun h1 : term73 = True => @lem2001951)). Qed.
Lemma lem2001954 : term73 = True.
Proof. exact (EQ_MP (@lem2001953) (@lem2001951)). Qed.
Lemma lem2001955 : term66 = True.
Proof. exact (TRANS (@lem2001950) (@lem2001954)). Qed.
Lemma lem2001956 : True = term66.
Proof. exact (SYM (@lem2001955)). Qed.
Lemma lem2001957 : term66.
Proof. exact (EQ_MP (@lem2001956) (@lem0)). Qed.
Lemma lem2001958 : term121.
Proof. exact (@lem2001947 (@lem2001957)). Qed.
Lemma lem2001960 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2001961 : term21 = term32.
Proof. exact (@lem2001960 term15 term15). Qed.
Lemma lem2001962 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2001963 : term29 = term15.
Proof. exact (EQ_MP (@lem2001962) (@lem940073)). Qed.
Lemma lem2001964 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001965 : term27 = term5.
Proof. exact (MK_COMB (@lem2001964) (@lem2001963)). Qed.
Lemma lem2001966 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2001967 : term32 = term12.
Proof. exact (MK_COMB (@lem2001966) (@lem2001965)). Qed.
Lemma lem2001968 : term21 = term12.
Proof. exact (TRANS (@lem2001961) (@lem2001967)). Qed.
Lemma lem2001970 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2001971 : term21 = term32.
Proof. exact (@lem2001970 term15 term15). Qed.
Lemma lem2001972 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2001973 : term29 = term15.
Proof. exact (EQ_MP (@lem2001972) (@lem940073)). Qed.
Lemma lem2001974 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001975 : term27 = term5.
Proof. exact (MK_COMB (@lem2001974) (@lem2001973)). Qed.
Lemma lem2001976 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2001977 : term32 = term12.
Proof. exact (MK_COMB (@lem2001976) (@lem2001975)). Qed.
Lemma lem2001978 : term21 = term12.
Proof. exact (TRANS (@lem2001971) (@lem2001977)). Qed.
Lemma lem2001979 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2001980 : term105 = term47.
Proof. exact (MK_COMB (@lem2001979) (@lem2001978)). Qed.
Lemma lem2001981 : term122 = term115.
Proof. exact (MK_COMB (@lem2001980) (@lem2001968)). Qed.
Lemma lem2001982 : term115 = term123.
Proof. exact (@lem1367763 term15 term15). Qed.
Lemma lem2001983 : term124 = term125.
Proof. exact (@lem706885). Qed.
Lemma lem2001984 : (term124 = term125) = (term126 = term127).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term125). Qed.
Lemma lem2001985 : term126 = term127.
Proof. exact (EQ_MP (@lem2001984) (@lem2001983)). Qed.
Lemma lem2001986 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2001987 : term128 = term129.
Proof. exact (MK_COMB (@lem2001986) (@lem2001985)). Qed.
Lemma lem2001988 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2001989 : term123 = term118.
Proof. exact (MK_COMB (@lem2001988) (@lem2001987)). Qed.
Lemma lem2001990 : term115 = term118.
Proof. exact (TRANS (@lem2001982) (@lem2001989)). Qed.
Lemma lem2001991 : term122 = term118.
Proof. exact (TRANS (@lem2001981) (@lem2001990)). Qed.
Lemma lem2001992 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2001993 : term130 = term131.
Proof. exact (MK_COMB (@lem2001992) (@lem2001991)). Qed.
Lemma lem2001994 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem2001995 : term132 = term133.
Proof. exact (MK_COMB (@lem2001993) (@lem2001994)). Qed.
Lemma lem2001997 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2001998 : term133 = term134.
Proof. exact (@lem2001997 term127 term15). Qed.
Lemma lem2001999 : term135 = term125.
Proof. exact (@lem996237 term125). Qed.
Lemma lem2002000 : (term135 = term125) = (term136 = term127).
Proof. exact (@lem1007663 term125 (BIT1 0) term125). Qed.
Lemma lem2002001 : term136 = term127.
Proof. exact (EQ_MP (@lem2002000) (@lem2001999)). Qed.
Lemma lem2002002 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002003 : term137 = term129.
Proof. exact (MK_COMB (@lem2002002) (@lem2002001)). Qed.
Lemma lem2002004 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2002005 : term134 = term118.
Proof. exact (MK_COMB (@lem2002004) (@lem2002003)). Qed.
Lemma lem2002006 : term133 = term118.
Proof. exact (TRANS (@lem2001998) (@lem2002005)). Qed.
Lemma lem2002007 : term132 = term118.
Proof. exact (TRANS (@lem2001995) (@lem2002006)). Qed.
Lemma lem2002009 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2002010 : term26 = term27.
Proof. exact (@lem2002009 term15 term15). Qed.
Lemma lem2002011 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2002012 : term29 = term15.
Proof. exact (EQ_MP (@lem2002011) (@lem940073)). Qed.
Lemma lem2002013 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002014 : term27 = term5.
Proof. exact (MK_COMB (@lem2002013) (@lem2002012)). Qed.
Lemma lem2002015 : term26 = term5.
Proof. exact (TRANS (@lem2002010) (@lem2002014)). Qed.
Lemma lem2002016 : term131 = term131.
Proof. exact (eq_refl term131). Qed.
Lemma lem2002017 : term138 = term133.
Proof. exact (MK_COMB (@lem2002016) (@lem2002015)). Qed.
Lemma lem2002019 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2002020 : term133 = term134.
Proof. exact (@lem2002019 term127 term15). Qed.
Lemma lem2002021 : term135 = term125.
Proof. exact (@lem996237 term125). Qed.
Lemma lem2002022 : (term135 = term125) = (term136 = term127).
Proof. exact (@lem1007663 term125 (BIT1 0) term125). Qed.
Lemma lem2002023 : term136 = term127.
Proof. exact (EQ_MP (@lem2002022) (@lem2002021)). Qed.
Lemma lem2002024 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002025 : term137 = term129.
Proof. exact (MK_COMB (@lem2002024) (@lem2002023)). Qed.
Lemma lem2002026 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2002027 : term134 = term118.
Proof. exact (MK_COMB (@lem2002026) (@lem2002025)). Qed.
Lemma lem2002028 : term133 = term118.
Proof. exact (TRANS (@lem2002020) (@lem2002027)). Qed.
Lemma lem2002029 : term138 = term118.
Proof. exact (TRANS (@lem2002017) (@lem2002028)). Qed.
Lemma lem2002030 : term118 = term138.
Proof. exact (SYM (@lem2002029)). Qed.
Lemma lem2002031 : term132 = term138.
Proof. exact (TRANS (@lem2002007) (@lem2002030)). Qed.
Lemma lem2002032 : term116 = term139.
Proof. exact (@lem2001958 (@lem2002031)). Qed.
Lemma lem2002033 : term115 = term139.
Proof. exact (TRANS (@lem2001924) (@lem2002032)). Qed.
Lemma lem2002035 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2002036 : term139 = term118.
Proof. exact (@lem2002035 term118). Qed.
Lemma lem2002037 : term115 = term118.
Proof. exact (TRANS (@lem2002033) (@lem2002036)). Qed.
Lemma lem2002038 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2002039 : term394 = term131.
Proof. exact (MK_COMB (@lem2002038) (@lem2002037)). Qed.
Lemma lem2002040 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2002041 (x : real) : (term393 x) = (term395 x).
Proof. exact (MK_COMB (@lem2002039) (@lem2002040 x)). Qed.
Lemma lem2002042 (x : real) : (term392 x) = (term395 x).
Proof. exact (TRANS (@lem2001915 x) (@lem2002041 x)). Qed.
Lemma lem2002043 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2002044 (x : real) : (term396 x) = (term397 x).
Proof. exact (MK_COMB (@lem2002043) (@lem2002042 x)). Qed.
Lemma lem2002045 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem2002046 (x : real) : (term391 x) = (term398 x).
Proof. exact (MK_COMB (@lem2002044 x) (@lem2002045)). Qed.
Lemma lem2002048 (x : real) : (term390 x) = (term398 x).
Proof. exact (TRANS (@lem2001914 x) (@lem2002046 x)). Qed.
Lemma lem2002049 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2002050 (x : real) : (term399 x) = (term400 x).
Proof. exact (MK_COMB (@lem2002049) (@lem2002048 x)). Qed.
Lemma lem2002051 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2002052 (x : real) : (term401 x) = (term402 x).
Proof. exact (MK_COMB (@lem2002050 x) (@lem2002051)). Qed.
Lemma lem2002053 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2002054 (x : real) : (term403 x) = (term404 x).
Proof. exact (MK_COMB (@lem2002053) (@lem2002052 x)). Qed.
Lemma lem2002055 (x : real) : (term379 x) = (term405 x).
Proof. exact (MK_COMB (@lem2002054 x) (@lem2001890 x)). Qed.
Lemma lem2002056 (x : real) : (term342 x) = (term405 x).
Proof. exact (TRANS (@lem2001748 x) (@lem2002055 x)). Qed.
Lemma lem2002057 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2002058 (x : real) : (term358 x) = (term406 x).
Proof. exact (MK_COMB (@lem2002057) (@lem2002056 x)). Qed.
Lemma lem2002060 (a : real) (x : real) (b : real) (r : real) : (term377 a x b r) = (term378 a x b r).
Proof. exact (proj1 (@lem1482705 x a b (@el real) (@el real) r)). Qed.
Lemma lem2002061 (x : real) : (term356 x) = (term407 x).
Proof. exact (@lem2002060 x x term118 term2). Qed.
Lemma lem2002062 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem2002069 (x : real) : (term46 x) = x.
Proof. exact (@lem1982733 x). Qed.
Lemma lem2002070 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2002071 (x : real) : (term380 x) = (real_add x).
Proof. exact (MK_COMB (@lem2002070) (@lem2002069 x)). Qed.
Lemma lem2002074 (x : real) : (term381 x) = (term382 x).
Proof. exact (MK_COMB (@lem2002071 x) (@lem2002062)). Qed.
Lemma lem2002077 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem2002078 (x : real) : (term408 x) = (term409 x).
Proof. exact (MK_COMB (@lem2002077 x) (@lem2002074 x)). Qed.
Lemma lem2002079 (x : real) : (term409 x) = (term410 x).
Proof. exact (@lem1982763 x x term118). Qed.
Lemma lem2002080 (x : real) : (real_add x x) = (term411 x).
Proof. exact (@lem1982717 x). Qed.
Lemma lem2002082 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2002083 : term5 = term14.
Proof. exact (@lem2002082 term15). Qed.
Lemma lem2002085 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2002086 : term5 = term14.
Proof. exact (@lem2002085 term15). Qed.
Lemma lem2002087 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2002088 : term273 = term274.
Proof. exact (MK_COMB (@lem2002087) (@lem2002086)). Qed.
Lemma lem2002089 : term412 = term413.
Proof. exact (MK_COMB (@lem2002088) (@lem2002083)). Qed.
Lemma lem2002090 : term414.
Proof. exact (@lem1981473 term5 term5 term5 term5 term129 term5). Qed.
Lemma lem2002092 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2002093 : term66 = term73.
Proof. exact (@lem2002092 (NUMERAL 0) term15). Qed.
Lemma lem2002094 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2002095 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2002096 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2002095 h1) (fun h1 : term73 = True => @lem2002094)). Qed.
Lemma lem2002097 : term73 = True.
Proof. exact (EQ_MP (@lem2002096) (@lem2002094)). Qed.
Lemma lem2002098 : term66 = True.
Proof. exact (TRANS (@lem2002093) (@lem2002097)). Qed.
Lemma lem2002099 : True = term66.
Proof. exact (SYM (@lem2002098)). Qed.
Lemma lem2002100 : term66.
Proof. exact (EQ_MP (@lem2002099) (@lem0)). Qed.
Lemma lem2002101 : term415.
Proof. exact (@lem2002090 (@lem2002100)). Qed.
Lemma lem2002103 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2002104 : term66 = term73.
Proof. exact (@lem2002103 (NUMERAL 0) term15). Qed.
Lemma lem2002105 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2002106 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2002107 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2002106 h1) (fun h1 : term73 = True => @lem2002105)). Qed.
Lemma lem2002108 : term73 = True.
Proof. exact (EQ_MP (@lem2002107) (@lem2002105)). Qed.
Lemma lem2002109 : term66 = True.
Proof. exact (TRANS (@lem2002104) (@lem2002108)). Qed.
Lemma lem2002110 : True = term66.
Proof. exact (SYM (@lem2002109)). Qed.
Lemma lem2002111 : term66.
Proof. exact (EQ_MP (@lem2002110) (@lem0)). Qed.
Lemma lem2002112 : term416.
Proof. exact (@lem2002101 (@lem2002111)). Qed.
Lemma lem2002114 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2002115 : term66 = term73.
Proof. exact (@lem2002114 (NUMERAL 0) term15). Qed.
Lemma lem2002116 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2002117 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2002118 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2002117 h1) (fun h1 : term73 = True => @lem2002116)). Qed.
Lemma lem2002119 : term73 = True.
Proof. exact (EQ_MP (@lem2002118) (@lem2002116)). Qed.
Lemma lem2002120 : term66 = True.
Proof. exact (TRANS (@lem2002115) (@lem2002119)). Qed.
Lemma lem2002121 : True = term66.
Proof. exact (SYM (@lem2002120)). Qed.
Lemma lem2002122 : term66.
Proof. exact (EQ_MP (@lem2002121) (@lem0)). Qed.
Lemma lem2002123 : term417.
Proof. exact (@lem2002112 (@lem2002122)). Qed.
Lemma lem2002125 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2002126 : term26 = term27.
Proof. exact (@lem2002125 term15 term15). Qed.
Lemma lem2002127 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2002128 : term29 = term15.
Proof. exact (EQ_MP (@lem2002127) (@lem940073)). Qed.
Lemma lem2002129 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002130 : term27 = term5.
Proof. exact (MK_COMB (@lem2002129) (@lem2002128)). Qed.
Lemma lem2002131 : term26 = term5.
Proof. exact (TRANS (@lem2002126) (@lem2002130)). Qed.
Lemma lem2002133 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2002134 : term26 = term27.
Proof. exact (@lem2002133 term15 term15). Qed.
Lemma lem2002135 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2002136 : term29 = term15.
Proof. exact (EQ_MP (@lem2002135) (@lem940073)). Qed.
Lemma lem2002137 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002138 : term27 = term5.
Proof. exact (MK_COMB (@lem2002137) (@lem2002136)). Qed.
Lemma lem2002139 : term26 = term5.
Proof. exact (TRANS (@lem2002134) (@lem2002138)). Qed.
Lemma lem2002140 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2002141 : term281 = term273.
Proof. exact (MK_COMB (@lem2002140) (@lem2002139)). Qed.
Lemma lem2002142 : term418 = term412.
Proof. exact (MK_COMB (@lem2002141) (@lem2002131)). Qed.
Lemma lem2002143 : term412 = term128.
Proof. exact (@lem1367770 term15 term15). Qed.
Lemma lem2002144 : term124 = term125.
Proof. exact (@lem706885). Qed.
Lemma lem2002145 : (term124 = term125) = (term126 = term127).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term125). Qed.
Lemma lem2002146 : term126 = term127.
Proof. exact (EQ_MP (@lem2002145) (@lem2002144)). Qed.
Lemma lem2002147 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002148 : term128 = term129.
Proof. exact (MK_COMB (@lem2002147) (@lem2002146)). Qed.
Lemma lem2002149 : term412 = term129.
Proof. exact (TRANS (@lem2002143) (@lem2002148)). Qed.
Lemma lem2002150 : term418 = term129.
Proof. exact (TRANS (@lem2002142) (@lem2002149)). Qed.
Lemma lem2002151 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2002152 : term419 = term420.
Proof. exact (MK_COMB (@lem2002151) (@lem2002150)). Qed.
Lemma lem2002153 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem2002154 : term421 = term422.
Proof. exact (MK_COMB (@lem2002152) (@lem2002153)). Qed.
Lemma lem2002156 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2002157 : term422 = term137.
Proof. exact (@lem2002156 term127 term15). Qed.
Lemma lem2002158 : term135 = term125.
Proof. exact (@lem996237 term125). Qed.
Lemma lem2002159 : (term135 = term125) = (term136 = term127).
Proof. exact (@lem1007663 term125 (BIT1 0) term125). Qed.
Lemma lem2002160 : term136 = term127.
Proof. exact (EQ_MP (@lem2002159) (@lem2002158)). Qed.
Lemma lem2002161 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002162 : term137 = term129.
Proof. exact (MK_COMB (@lem2002161) (@lem2002160)). Qed.
Lemma lem2002163 : term422 = term129.
Proof. exact (TRANS (@lem2002157) (@lem2002162)). Qed.
Lemma lem2002164 : term421 = term129.
Proof. exact (TRANS (@lem2002154) (@lem2002163)). Qed.
Lemma lem2002166 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2002167 : term26 = term27.
Proof. exact (@lem2002166 term15 term15). Qed.
Lemma lem2002168 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2002169 : term29 = term15.
Proof. exact (EQ_MP (@lem2002168) (@lem940073)). Qed.
Lemma lem2002170 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002171 : term27 = term5.
Proof. exact (MK_COMB (@lem2002170) (@lem2002169)). Qed.
Lemma lem2002172 : term26 = term5.
Proof. exact (TRANS (@lem2002167) (@lem2002171)). Qed.
Lemma lem2002173 : term420 = term420.
Proof. exact (eq_refl term420). Qed.
Lemma lem2002174 : term423 = term422.
Proof. exact (MK_COMB (@lem2002173) (@lem2002172)). Qed.
Lemma lem2002176 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2002177 : term422 = term137.
Proof. exact (@lem2002176 term127 term15). Qed.
Lemma lem2002178 : term135 = term125.
Proof. exact (@lem996237 term125). Qed.
Lemma lem2002179 : (term135 = term125) = (term136 = term127).
Proof. exact (@lem1007663 term125 (BIT1 0) term125). Qed.
Lemma lem2002180 : term136 = term127.
Proof. exact (EQ_MP (@lem2002179) (@lem2002178)). Qed.
Lemma lem2002181 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002182 : term137 = term129.
Proof. exact (MK_COMB (@lem2002181) (@lem2002180)). Qed.
Lemma lem2002183 : term422 = term129.
Proof. exact (TRANS (@lem2002177) (@lem2002182)). Qed.
Lemma lem2002184 : term423 = term129.
Proof. exact (TRANS (@lem2002174) (@lem2002183)). Qed.
Lemma lem2002185 : term129 = term423.
Proof. exact (SYM (@lem2002184)). Qed.
Lemma lem2002186 : term421 = term423.
Proof. exact (TRANS (@lem2002164) (@lem2002185)). Qed.
Lemma lem2002187 : term413 = term424.
Proof. exact (@lem2002123 (@lem2002186)). Qed.
Lemma lem2002188 : term412 = term424.
Proof. exact (TRANS (@lem2002089) (@lem2002187)). Qed.
Lemma lem2002190 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2002191 : term424 = term129.
Proof. exact (@lem2002190 term129). Qed.
Lemma lem2002192 : term412 = term129.
Proof. exact (TRANS (@lem2002188) (@lem2002191)). Qed.
Lemma lem2002193 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2002194 : term425 = term420.
Proof. exact (MK_COMB (@lem2002193) (@lem2002192)). Qed.
Lemma lem2002195 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2002196 (x : real) : (term411 x) = (term426 x).
Proof. exact (MK_COMB (@lem2002194) (@lem2002195 x)). Qed.
Lemma lem2002197 (x : real) : (real_add x x) = (term426 x).
Proof. exact (TRANS (@lem2002080 x) (@lem2002196 x)). Qed.
Lemma lem2002198 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2002199 (x : real) : (term427 x) = (term428 x).
Proof. exact (MK_COMB (@lem2002198) (@lem2002197 x)). Qed.
Lemma lem2002200 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem2002201 (x : real) : (term410 x) = (term429 x).
Proof. exact (MK_COMB (@lem2002199 x) (@lem2002200)). Qed.
Lemma lem2002202 (x : real) : (term409 x) = (term429 x).
Proof. exact (TRANS (@lem2002079 x) (@lem2002201 x)). Qed.
Lemma lem2002203 (x : real) : (term408 x) = (term429 x).
Proof. exact (TRANS (@lem2002078 x) (@lem2002202 x)). Qed.
Lemma lem2002204 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2002205 (x : real) : (term430 x) = (term431 x).
Proof. exact (MK_COMB (@lem2002204) (@lem2002203 x)). Qed.
Lemma lem2002206 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2002207 (x : real) : (term432 x) = (term433 x).
Proof. exact (MK_COMB (@lem2002205 x) (@lem2002206)). Qed.
Lemma lem2002225 (x : real) : (term434 x) = (term435 x).
Proof. exact (@lem1982763 x (term57 x) term118). Qed.
Lemma lem2002226 (x : real) : (term436 x) = (term97 x).
Proof. exact (@lem1982715 term12 x). Qed.
Lemma lem2002228 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2002229 : term5 = term14.
Proof. exact (@lem2002228 term15). Qed.
Lemma lem2002231 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2002232 : term12 = term18.
Proof. exact (@lem2002231 term15). Qed.
Lemma lem2002233 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2002234 : term47 = term98.
Proof. exact (MK_COMB (@lem2002233) (@lem2002232)). Qed.
Lemma lem2002235 : term99 = term100.
Proof. exact (MK_COMB (@lem2002234) (@lem2002229)). Qed.
Lemma lem2002236 : term101.
Proof. exact (@lem1981473 term12 term5 term5 term5 term2 term5). Qed.
Lemma lem2002238 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2002239 : term66 = term73.
Proof. exact (@lem2002238 (NUMERAL 0) term15). Qed.
Lemma lem2002240 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2002241 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2002242 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2002241 h1) (fun h1 : term73 = True => @lem2002240)). Qed.
Lemma lem2002243 : term73 = True.
Proof. exact (EQ_MP (@lem2002242) (@lem2002240)). Qed.
Lemma lem2002244 : term66 = True.
Proof. exact (TRANS (@lem2002239) (@lem2002243)). Qed.
Lemma lem2002245 : True = term66.
Proof. exact (SYM (@lem2002244)). Qed.
Lemma lem2002246 : term66.
Proof. exact (EQ_MP (@lem2002245) (@lem0)). Qed.
Lemma lem2002247 : term102.
Proof. exact (@lem2002236 (@lem2002246)). Qed.
Lemma lem2002249 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2002250 : term66 = term73.
Proof. exact (@lem2002249 (NUMERAL 0) term15). Qed.
Lemma lem2002251 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2002252 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2002253 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2002252 h1) (fun h1 : term73 = True => @lem2002251)). Qed.
Lemma lem2002254 : term73 = True.
Proof. exact (EQ_MP (@lem2002253) (@lem2002251)). Qed.
Lemma lem2002255 : term66 = True.
Proof. exact (TRANS (@lem2002250) (@lem2002254)). Qed.
Lemma lem2002256 : True = term66.
Proof. exact (SYM (@lem2002255)). Qed.
Lemma lem2002257 : term66.
Proof. exact (EQ_MP (@lem2002256) (@lem0)). Qed.
Lemma lem2002258 : term103.
Proof. exact (@lem2002247 (@lem2002257)). Qed.
Lemma lem2002260 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2002261 : term66 = term73.
Proof. exact (@lem2002260 (NUMERAL 0) term15). Qed.
Lemma lem2002262 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2002263 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2002264 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2002263 h1) (fun h1 : term73 = True => @lem2002262)). Qed.
Lemma lem2002265 : term73 = True.
Proof. exact (EQ_MP (@lem2002264) (@lem2002262)). Qed.
Lemma lem2002266 : term66 = True.
Proof. exact (TRANS (@lem2002261) (@lem2002265)). Qed.
Lemma lem2002267 : True = term66.
Proof. exact (SYM (@lem2002266)). Qed.
Lemma lem2002268 : term66.
Proof. exact (EQ_MP (@lem2002267) (@lem0)). Qed.
Lemma lem2002269 : term104.
Proof. exact (@lem2002258 (@lem2002268)). Qed.
Lemma lem2002271 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2002272 : term26 = term27.
Proof. exact (@lem2002271 term15 term15). Qed.
Lemma lem2002273 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2002274 : term29 = term15.
Proof. exact (EQ_MP (@lem2002273) (@lem940073)). Qed.
Lemma lem2002275 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002276 : term27 = term5.
Proof. exact (MK_COMB (@lem2002275) (@lem2002274)). Qed.
Lemma lem2002277 : term26 = term5.
Proof. exact (TRANS (@lem2002272) (@lem2002276)). Qed.
Lemma lem2002279 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2002280 : term21 = term32.
Proof. exact (@lem2002279 term15 term15). Qed.
Lemma lem2002281 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2002282 : term29 = term15.
Proof. exact (EQ_MP (@lem2002281) (@lem940073)). Qed.
Lemma lem2002283 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002284 : term27 = term5.
Proof. exact (MK_COMB (@lem2002283) (@lem2002282)). Qed.
Lemma lem2002285 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2002286 : term32 = term12.
Proof. exact (MK_COMB (@lem2002285) (@lem2002284)). Qed.
Lemma lem2002287 : term21 = term12.
Proof. exact (TRANS (@lem2002280) (@lem2002286)). Qed.
Lemma lem2002288 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2002289 : term105 = term47.
Proof. exact (MK_COMB (@lem2002288) (@lem2002287)). Qed.
Lemma lem2002290 : term106 = term99.
Proof. exact (MK_COMB (@lem2002289) (@lem2002277)). Qed.
Lemma lem2002292 (m : nat) : (term107 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2002293 : term99 = term2.
Proof. exact (@lem2002292 term15). Qed.
Lemma lem2002294 : term106 = term2.
Proof. exact (TRANS (@lem2002290) (@lem2002293)). Qed.
Lemma lem2002295 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2002296 : term108 = term109.
Proof. exact (MK_COMB (@lem2002295) (@lem2002294)). Qed.
Lemma lem2002297 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem2002298 : term110 = term78.
Proof. exact (MK_COMB (@lem2002296) (@lem2002297)). Qed.
Lemma lem2002300 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2002301 : term78 = term2.
Proof. exact (@lem2002300 term15). Qed.
Lemma lem2002302 : term110 = term2.
Proof. exact (TRANS (@lem2002298) (@lem2002301)). Qed.
Lemma lem2002304 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2002305 : term26 = term27.
Proof. exact (@lem2002304 term15 term15). Qed.
Lemma lem2002306 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2002307 : term29 = term15.
Proof. exact (EQ_MP (@lem2002306) (@lem940073)). Qed.
Lemma lem2002308 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002309 : term27 = term5.
Proof. exact (MK_COMB (@lem2002308) (@lem2002307)). Qed.
Lemma lem2002310 : term26 = term5.
Proof. exact (TRANS (@lem2002305) (@lem2002309)). Qed.
Lemma lem2002311 : term109 = term109.
Proof. exact (eq_refl term109). Qed.
Lemma lem2002312 : term111 = term78.
Proof. exact (MK_COMB (@lem2002311) (@lem2002310)). Qed.
Lemma lem2002314 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2002315 : term78 = term2.
Proof. exact (@lem2002314 term15). Qed.
Lemma lem2002316 : term111 = term2.
Proof. exact (TRANS (@lem2002312) (@lem2002315)). Qed.
Lemma lem2002317 : term2 = term111.
Proof. exact (SYM (@lem2002316)). Qed.
Lemma lem2002318 : term110 = term111.
Proof. exact (TRANS (@lem2002302) (@lem2002317)). Qed.
Lemma lem2002319 : term100 = term67.
Proof. exact (@lem2002269 (@lem2002318)). Qed.
Lemma lem2002320 : term99 = term67.
Proof. exact (TRANS (@lem2002235) (@lem2002319)). Qed.
Lemma lem2002322 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2002323 : term67 = term2.
Proof. exact (@lem2002322 term2). Qed.
Lemma lem2002324 : term99 = term2.
Proof. exact (TRANS (@lem2002320) (@lem2002323)). Qed.
Lemma lem2002325 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2002326 : term112 = term109.
Proof. exact (MK_COMB (@lem2002325) (@lem2002324)). Qed.
Lemma lem2002327 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2002328 (x : real) : (term97 x) = (term113 x).
Proof. exact (MK_COMB (@lem2002326) (@lem2002327 x)). Qed.
Lemma lem2002329 (x : real) : (term436 x) = (term113 x).
Proof. exact (TRANS (@lem2002226 x) (@lem2002328 x)). Qed.
Lemma lem2002330 (x : real) : (term113 x) = term2.
Proof. exact (@lem1982719 x). Qed.
Lemma lem2002331 (x : real) : (term436 x) = term2.
Proof. exact (TRANS (@lem2002329 x) (@lem2002330 x)). Qed.
Lemma lem2002332 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2002333 (x : real) : (term437 x) = term38.
Proof. exact (MK_COMB (@lem2002332) (@lem2002331 x)). Qed.
Lemma lem2002334 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem2002335 (x : real) : (term435 x) = term140.
Proof. exact (MK_COMB (@lem2002333 x) (@lem2002334)). Qed.
Lemma lem2002336 (x : real) : (term434 x) = term140.
Proof. exact (TRANS (@lem2002225 x) (@lem2002335 x)). Qed.
Lemma lem2002337 : term140 = term118.
Proof. exact (@lem1982721 term118). Qed.
Lemma lem2002339 (x : real) : (term434 x) = term118.
Proof. exact (TRANS (@lem2002336 x) (@lem2002337)). Qed.
Lemma lem2002340 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2002341 (x : real) : (term438 x) = term387.
Proof. exact (MK_COMB (@lem2002340) (@lem2002339 x)). Qed.
Lemma lem2002342 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2002343 (x : real) : (term439 x) = term389.
Proof. exact (MK_COMB (@lem2002341 x) (@lem2002342)). Qed.
Lemma lem2002344 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2002345 (x : real) : (term440 x) = term441.
Proof. exact (MK_COMB (@lem2002344) (@lem2002343 x)). Qed.
Lemma lem2002346 (x : real) : (term407 x) = (term442 x).
Proof. exact (MK_COMB (@lem2002345 x) (@lem2002207 x)). Qed.
Lemma lem2002347 (x : real) : (term356 x) = (term442 x).
Proof. exact (TRANS (@lem2002061 x) (@lem2002346 x)). Qed.
Lemma lem2002348 (x : real) : (term359 x) = (term443 x).
Proof. exact (MK_COMB (@lem2002058 x) (@lem2002347 x)). Qed.
Lemma lem2002351 (x : real) : (term361 x) = (term444 x).
Proof. exact (MK_COMB (@lem2001745 x) (@lem2002348 x)). Qed.
Lemma lem2002353 (x : real) : (term445 x) = (term316 x).
Proof. exact (eq_refl (term445 x)). Qed.
Lemma lem2002354 (x : real) : (term316 x) = (term445 x).
Proof. exact (SYM (@lem2002353 x)). Qed.
Lemma lem2002355 (x : real) : (term445 x) = (term446 x).
Proof. exact (@lem1482981 (term447 x) x). Qed.
Lemma lem2002356 (x : real) : (term316 x) = (term446 x).
Proof. exact (TRANS (@lem2002354 x) (@lem2002355 x)). Qed.
Lemma lem2002357 (x : real) : (term448 x) = (term449 x).
Proof. exact (eq_refl (term448 x)). Qed.
Lemma lem2002358 (x : real) : (term450 x) = (term450 x).
Proof. exact (eq_refl (term450 x)). Qed.
Lemma lem2002359 (x : real) : (term451 x) = (term452 x).
Proof. exact (MK_COMB (@lem2002358 x) (@lem2002357 x)). Qed.
Lemma lem2002360 (x : real) : (term453 x) = (term454 x).
Proof. exact (eq_refl (term453 x)). Qed.
Lemma lem2002361 (x : real) : (term455 x) = (term455 x).
Proof. exact (eq_refl (term455 x)). Qed.
Lemma lem2002362 (x : real) : (term456 x) = (term457 x).
Proof. exact (MK_COMB (@lem2002361 x) (@lem2002360 x)). Qed.
Lemma lem2002363 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2002364 (x : real) : (term458 x) = (term459 x).
Proof. exact (MK_COMB (@lem2002363) (@lem2002362 x)). Qed.
Lemma lem2002365 (x : real) : (term446 x) = (term460 x).
Proof. exact (MK_COMB (@lem2002364 x) (@lem2002359 x)). Qed.
Lemma lem2002366 (x : real) : (term461 x) = (term461 x).
Proof. exact (eq_refl (term461 x)). Qed.
Lemma lem2002367 (x : real) : ((term316 x) = (term446 x)) = ((term316 x) = (term460 x)).
Proof. exact (MK_COMB (@lem2002366 x) (@lem2002365 x)). Qed.
Lemma lem2002368 (x : real) : (term316 x) = (term460 x).
Proof. exact (EQ_MP (@lem2002367 x) (@lem2002356 x)). Qed.
Lemma lem2002369 (x : real) : (term462 x) = (term463 x).
Proof. exact (@lem1988291 x term2). Qed.
Lemma lem2002375 (x : real) : (term464 x) = (term465 x).
Proof. exact (@lem1982792 x term2). Qed.
Lemma lem2002377 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2002378 : term2 = term67.
Proof. exact (@lem2002377 (NUMERAL 0)). Qed.
Lemma lem2002380 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2002381 : term12 = term18.
Proof. exact (@lem2002380 term15). Qed.
Lemma lem2002382 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2002383 : term19 = term20.
Proof. exact (MK_COMB (@lem2002382) (@lem2002381)). Qed.
Lemma lem2002384 : term258 = term259.
Proof. exact (MK_COMB (@lem2002383) (@lem2002378)). Qed.
Lemma lem2002385 : term259 = term260.
Proof. exact (@lem1981613 term12 term2 term5 term5). Qed.
Lemma lem2002387 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2002388 : term26 = term27.
Proof. exact (@lem2002387 term15 term15). Qed.
Lemma lem2002389 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2002390 : term29 = term15.
Proof. exact (EQ_MP (@lem2002389) (@lem940073)). Qed.
Lemma lem2002391 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002392 : term27 = term5.
Proof. exact (MK_COMB (@lem2002391) (@lem2002390)). Qed.
Lemma lem2002393 : term26 = term5.
Proof. exact (TRANS (@lem2002388) (@lem2002392)). Qed.
Lemma lem2002395 (x : nat) : (term261 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2002396 : term258 = term2.
Proof. exact (@lem2002395 term15). Qed.
Lemma lem2002397 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2002398 : term262 = term263.
Proof. exact (MK_COMB (@lem2002397) (@lem2002396)). Qed.
Lemma lem2002399 : term260 = term67.
Proof. exact (MK_COMB (@lem2002398) (@lem2002393)). Qed.
Lemma lem2002400 : term259 = term67.
Proof. exact (TRANS (@lem2002385) (@lem2002399)). Qed.
Lemma lem2002401 : term258 = term67.
Proof. exact (TRANS (@lem2002384) (@lem2002400)). Qed.
Lemma lem2002403 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2002404 : term67 = term2.
Proof. exact (@lem2002403 term2). Qed.
Lemma lem2002405 : term258 = term2.
Proof. exact (TRANS (@lem2002401) (@lem2002404)). Qed.
Lemma lem2002406 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem2002407 (x : real) : (term465 x) = (term466 x).
Proof. exact (MK_COMB (@lem2002406 x) (@lem2002405)). Qed.
Lemma lem2002408 (x : real) : (term466 x) = x.
Proof. exact (@lem1982723 x). Qed.
Lemma lem2002409 (x : real) : (term465 x) = x.
Proof. exact (TRANS (@lem2002407 x) (@lem2002408 x)). Qed.
Lemma lem2002411 (x : real) : (term464 x) = x.
Proof. exact (TRANS (@lem2002375 x) (@lem2002409 x)). Qed.
Lemma lem2002412 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2002413 (x : real) : (term467 x) = (real_ge x).
Proof. exact (MK_COMB (@lem2002412) (@lem2002411 x)). Qed.
Lemma lem2002414 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2002415 (x : real) : (term463 x) = (term462 x).
Proof. exact (MK_COMB (@lem2002413 x) (@lem2002414)). Qed.
Lemma lem2002416 (x : real) : (term462 x) = (term462 x).
Proof. exact (TRANS (@lem2002369 x) (@lem2002415 x)). Qed.
Lemma lem2002417 (x : real) : (term468 x) = (term469 x).
Proof. exact (@lem1988291 (term470 x) term2). Qed.
Lemma lem2002429 (x : real) : (term471 x) = (term472 x).
Proof. exact (@lem1982792 (term470 x) term2). Qed.
Lemma lem2002431 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2002432 : term2 = term67.
Proof. exact (@lem2002431 (NUMERAL 0)). Qed.
Lemma lem2002434 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2002435 : term12 = term18.
Proof. exact (@lem2002434 term15). Qed.
Lemma lem2002436 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2002437 : term19 = term20.
Proof. exact (MK_COMB (@lem2002436) (@lem2002435)). Qed.
Lemma lem2002438 : term258 = term259.
Proof. exact (MK_COMB (@lem2002437) (@lem2002432)). Qed.
Lemma lem2002439 : term259 = term260.
Proof. exact (@lem1981613 term12 term2 term5 term5). Qed.
Lemma lem2002441 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2002442 : term26 = term27.
Proof. exact (@lem2002441 term15 term15). Qed.
Lemma lem2002443 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2002444 : term29 = term15.
Proof. exact (EQ_MP (@lem2002443) (@lem940073)). Qed.
Lemma lem2002445 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002446 : term27 = term5.
Proof. exact (MK_COMB (@lem2002445) (@lem2002444)). Qed.
Lemma lem2002447 : term26 = term5.
Proof. exact (TRANS (@lem2002442) (@lem2002446)). Qed.
Lemma lem2002449 (x : nat) : (term261 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2002450 : term258 = term2.
Proof. exact (@lem2002449 term15). Qed.
Lemma lem2002451 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2002452 : term262 = term263.
Proof. exact (MK_COMB (@lem2002451) (@lem2002450)). Qed.
Lemma lem2002453 : term260 = term67.
Proof. exact (MK_COMB (@lem2002452) (@lem2002447)). Qed.
Lemma lem2002454 : term259 = term67.
Proof. exact (TRANS (@lem2002439) (@lem2002453)). Qed.
Lemma lem2002455 : term258 = term67.
Proof. exact (TRANS (@lem2002438) (@lem2002454)). Qed.
Lemma lem2002457 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2002458 : term67 = term2.
Proof. exact (@lem2002457 term2). Qed.
Lemma lem2002459 : term258 = term2.
Proof. exact (TRANS (@lem2002455) (@lem2002458)). Qed.
Lemma lem2002460 (x : real) : (term473 x) = (term473 x).
Proof. exact (eq_refl (term473 x)). Qed.
Lemma lem2002461 (x : real) : (term472 x) = (term474 x).
Proof. exact (MK_COMB (@lem2002460 x) (@lem2002459)). Qed.
Lemma lem2002462 (x : real) : (term474 x) = (term470 x).
Proof. exact (@lem1982723 (term470 x)). Qed.
Lemma lem2002463 (x : real) : (term472 x) = (term470 x).
Proof. exact (TRANS (@lem2002461 x) (@lem2002462 x)). Qed.
Lemma lem2002465 (x : real) : (term471 x) = (term470 x).
Proof. exact (TRANS (@lem2002429 x) (@lem2002463 x)). Qed.
Lemma lem2002466 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2002467 (x : real) : (term475 x) = (term476 x).
Proof. exact (MK_COMB (@lem2002466) (@lem2002465 x)). Qed.
Lemma lem2002468 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2002469 (x : real) : (term469 x) = (term468 x).
Proof. exact (MK_COMB (@lem2002467 x) (@lem2002468)). Qed.
Lemma lem2002470 (x : real) : (term468 x) = (term468 x).
Proof. exact (TRANS (@lem2002417 x) (@lem2002469 x)). Qed.
Lemma lem2002471 (x : real) : (term477 x) = (term478 x).
Proof. exact (@lem1988289 (term96 x) term2). Qed.
Lemma lem2002472 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2002484 (x : real) : (term96 x) = (term97 x).
Proof. exact (@lem1982713 term12 x). Qed.
Lemma lem2002486 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2002487 : term5 = term14.
Proof. exact (@lem2002486 term15). Qed.
Lemma lem2002489 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2002490 : term12 = term18.
Proof. exact (@lem2002489 term15). Qed.
Lemma lem2002491 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2002492 : term47 = term98.
Proof. exact (MK_COMB (@lem2002491) (@lem2002490)). Qed.
Lemma lem2002493 : term99 = term100.
Proof. exact (MK_COMB (@lem2002492) (@lem2002487)). Qed.
Lemma lem2002494 : term101.
Proof. exact (@lem1981473 term12 term5 term5 term5 term2 term5). Qed.
Lemma lem2002496 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2002497 : term66 = term73.
Proof. exact (@lem2002496 (NUMERAL 0) term15). Qed.
Lemma lem2002498 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2002499 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2002500 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2002499 h1) (fun h1 : term73 = True => @lem2002498)). Qed.
Lemma lem2002501 : term73 = True.
Proof. exact (EQ_MP (@lem2002500) (@lem2002498)). Qed.
Lemma lem2002502 : term66 = True.
Proof. exact (TRANS (@lem2002497) (@lem2002501)). Qed.
Lemma lem2002503 : True = term66.
Proof. exact (SYM (@lem2002502)). Qed.
Lemma lem2002504 : term66.
Proof. exact (EQ_MP (@lem2002503) (@lem0)). Qed.
Lemma lem2002505 : term102.
Proof. exact (@lem2002494 (@lem2002504)). Qed.
Lemma lem2002507 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2002508 : term66 = term73.
Proof. exact (@lem2002507 (NUMERAL 0) term15). Qed.
Lemma lem2002509 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2002510 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2002511 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2002510 h1) (fun h1 : term73 = True => @lem2002509)). Qed.
Lemma lem2002512 : term73 = True.
Proof. exact (EQ_MP (@lem2002511) (@lem2002509)). Qed.
Lemma lem2002513 : term66 = True.
Proof. exact (TRANS (@lem2002508) (@lem2002512)). Qed.
Lemma lem2002514 : True = term66.
Proof. exact (SYM (@lem2002513)). Qed.
Lemma lem2002515 : term66.
Proof. exact (EQ_MP (@lem2002514) (@lem0)). Qed.
Lemma lem2002516 : term103.
Proof. exact (@lem2002505 (@lem2002515)). Qed.
Lemma lem2002518 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2002519 : term66 = term73.
Proof. exact (@lem2002518 (NUMERAL 0) term15). Qed.
Lemma lem2002520 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2002521 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2002522 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2002521 h1) (fun h1 : term73 = True => @lem2002520)). Qed.
Lemma lem2002523 : term73 = True.
Proof. exact (EQ_MP (@lem2002522) (@lem2002520)). Qed.
Lemma lem2002524 : term66 = True.
Proof. exact (TRANS (@lem2002519) (@lem2002523)). Qed.
Lemma lem2002525 : True = term66.
Proof. exact (SYM (@lem2002524)). Qed.
Lemma lem2002526 : term66.
Proof. exact (EQ_MP (@lem2002525) (@lem0)). Qed.
Lemma lem2002527 : term104.
Proof. exact (@lem2002516 (@lem2002526)). Qed.
Lemma lem2002529 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2002530 : term26 = term27.
Proof. exact (@lem2002529 term15 term15). Qed.
Lemma lem2002531 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2002532 : term29 = term15.
Proof. exact (EQ_MP (@lem2002531) (@lem940073)). Qed.
Lemma lem2002533 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002534 : term27 = term5.
Proof. exact (MK_COMB (@lem2002533) (@lem2002532)). Qed.
Lemma lem2002535 : term26 = term5.
Proof. exact (TRANS (@lem2002530) (@lem2002534)). Qed.
Lemma lem2002537 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2002538 : term21 = term32.
Proof. exact (@lem2002537 term15 term15). Qed.
Lemma lem2002539 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2002540 : term29 = term15.
Proof. exact (EQ_MP (@lem2002539) (@lem940073)). Qed.
Lemma lem2002541 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002542 : term27 = term5.
Proof. exact (MK_COMB (@lem2002541) (@lem2002540)). Qed.
Lemma lem2002543 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2002544 : term32 = term12.
Proof. exact (MK_COMB (@lem2002543) (@lem2002542)). Qed.
Lemma lem2002545 : term21 = term12.
Proof. exact (TRANS (@lem2002538) (@lem2002544)). Qed.
Lemma lem2002546 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2002547 : term105 = term47.
Proof. exact (MK_COMB (@lem2002546) (@lem2002545)). Qed.
Lemma lem2002548 : term106 = term99.
Proof. exact (MK_COMB (@lem2002547) (@lem2002535)). Qed.
Lemma lem2002550 (m : nat) : (term107 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2002551 : term99 = term2.
Proof. exact (@lem2002550 term15). Qed.
Lemma lem2002552 : term106 = term2.
Proof. exact (TRANS (@lem2002548) (@lem2002551)). Qed.
Lemma lem2002553 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2002554 : term108 = term109.
Proof. exact (MK_COMB (@lem2002553) (@lem2002552)). Qed.
Lemma lem2002555 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem2002556 : term110 = term78.
Proof. exact (MK_COMB (@lem2002554) (@lem2002555)). Qed.
Lemma lem2002558 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2002559 : term78 = term2.
Proof. exact (@lem2002558 term15). Qed.
Lemma lem2002560 : term110 = term2.
Proof. exact (TRANS (@lem2002556) (@lem2002559)). Qed.
Lemma lem2002562 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2002563 : term26 = term27.
Proof. exact (@lem2002562 term15 term15). Qed.
Lemma lem2002564 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2002565 : term29 = term15.
Proof. exact (EQ_MP (@lem2002564) (@lem940073)). Qed.
Lemma lem2002566 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002567 : term27 = term5.
Proof. exact (MK_COMB (@lem2002566) (@lem2002565)). Qed.
Lemma lem2002568 : term26 = term5.
Proof. exact (TRANS (@lem2002563) (@lem2002567)). Qed.
Lemma lem2002569 : term109 = term109.
Proof. exact (eq_refl term109). Qed.
Lemma lem2002570 : term111 = term78.
Proof. exact (MK_COMB (@lem2002569) (@lem2002568)). Qed.
Lemma lem2002572 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2002573 : term78 = term2.
Proof. exact (@lem2002572 term15). Qed.
Lemma lem2002574 : term111 = term2.
Proof. exact (TRANS (@lem2002570) (@lem2002573)). Qed.
Lemma lem2002575 : term2 = term111.
Proof. exact (SYM (@lem2002574)). Qed.
Lemma lem2002576 : term110 = term111.
Proof. exact (TRANS (@lem2002560) (@lem2002575)). Qed.
Lemma lem2002577 : term100 = term67.
Proof. exact (@lem2002527 (@lem2002576)). Qed.
Lemma lem2002578 : term99 = term67.
Proof. exact (TRANS (@lem2002493) (@lem2002577)). Qed.
Lemma lem2002580 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2002581 : term67 = term2.
Proof. exact (@lem2002580 term2). Qed.
Lemma lem2002582 : term99 = term2.
Proof. exact (TRANS (@lem2002578) (@lem2002581)). Qed.
Lemma lem2002583 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2002584 : term112 = term109.
Proof. exact (MK_COMB (@lem2002583) (@lem2002582)). Qed.
Lemma lem2002585 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2002586 (x : real) : (term97 x) = (term113 x).
Proof. exact (MK_COMB (@lem2002584) (@lem2002585 x)). Qed.
Lemma lem2002587 (x : real) : (term96 x) = (term113 x).
Proof. exact (TRANS (@lem2002484 x) (@lem2002586 x)). Qed.
Lemma lem2002588 (x : real) : (term113 x) = term2.
Proof. exact (@lem1982719 x). Qed.
Lemma lem2002590 (x : real) : (term96 x) = term2.
Proof. exact (TRANS (@lem2002587 x) (@lem2002588 x)). Qed.
Lemma lem2002591 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2002592 (x : real) : (term479 x) = term6.
Proof. exact (MK_COMB (@lem2002591) (@lem2002590 x)). Qed.
Lemma lem2002593 (x : real) : (term480 x) = term481.
Proof. exact (MK_COMB (@lem2002592 x) (@lem2002472)). Qed.
Lemma lem2002594 : term481 = term482.
Proof. exact (@lem1982792 term2 term2). Qed.
Lemma lem2002596 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2002597 : term2 = term67.
Proof. exact (@lem2002596 (NUMERAL 0)). Qed.
Lemma lem2002599 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2002600 : term12 = term18.
Proof. exact (@lem2002599 term15). Qed.
Lemma lem2002601 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2002602 : term19 = term20.
Proof. exact (MK_COMB (@lem2002601) (@lem2002600)). Qed.
Lemma lem2002603 : term258 = term259.
Proof. exact (MK_COMB (@lem2002602) (@lem2002597)). Qed.
Lemma lem2002604 : term259 = term260.
Proof. exact (@lem1981613 term12 term2 term5 term5). Qed.
Lemma lem2002606 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2002607 : term26 = term27.
Proof. exact (@lem2002606 term15 term15). Qed.
Lemma lem2002608 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2002609 : term29 = term15.
Proof. exact (EQ_MP (@lem2002608) (@lem940073)). Qed.
Lemma lem2002610 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002611 : term27 = term5.
Proof. exact (MK_COMB (@lem2002610) (@lem2002609)). Qed.
Lemma lem2002612 : term26 = term5.
Proof. exact (TRANS (@lem2002607) (@lem2002611)). Qed.
Lemma lem2002614 (x : nat) : (term261 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2002615 : term258 = term2.
Proof. exact (@lem2002614 term15). Qed.
Lemma lem2002616 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2002617 : term262 = term263.
Proof. exact (MK_COMB (@lem2002616) (@lem2002615)). Qed.
Lemma lem2002618 : term260 = term67.
Proof. exact (MK_COMB (@lem2002617) (@lem2002612)). Qed.
Lemma lem2002619 : term259 = term67.
Proof. exact (TRANS (@lem2002604) (@lem2002618)). Qed.
Lemma lem2002620 : term258 = term67.
Proof. exact (TRANS (@lem2002603) (@lem2002619)). Qed.
Lemma lem2002622 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2002623 : term67 = term2.
Proof. exact (@lem2002622 term2). Qed.
Lemma lem2002624 : term258 = term2.
Proof. exact (TRANS (@lem2002620) (@lem2002623)). Qed.
Lemma lem2002625 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2002626 : term482 = term483.
Proof. exact (MK_COMB (@lem2002625) (@lem2002624)). Qed.
Lemma lem2002627 : term483 = term2.
Proof. exact (@lem1982721 term2). Qed.
Lemma lem2002628 : term482 = term2.
Proof. exact (TRANS (@lem2002626) (@lem2002627)). Qed.
Lemma lem2002629 : term481 = term2.
Proof. exact (TRANS (@lem2002594) (@lem2002628)). Qed.
Lemma lem2002630 (x : real) : (term480 x) = term2.
Proof. exact (TRANS (@lem2002593 x) (@lem2002629)). Qed.
Lemma lem2002631 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2002632 (x : real) : (term484 x) = term485.
Proof. exact (MK_COMB (@lem2002631) (@lem2002630 x)). Qed.
Lemma lem2002633 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2002634 (x : real) : (term478 x) = term486.
Proof. exact (MK_COMB (@lem2002632 x) (@lem2002633)). Qed.
Lemma lem2002635 (x : real) : (term477 x) = term486.
Proof. exact (TRANS (@lem2002471 x) (@lem2002634 x)). Qed.
Lemma lem2002636 (x : real) : (term487 x) = (term488 x).
Proof. exact (@lem1988289 (real_add x x) term2). Qed.
Lemma lem2002637 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2002643 (x : real) : (real_add x x) = (term411 x).
Proof. exact (@lem1982717 x). Qed.
Lemma lem2002645 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2002646 : term5 = term14.
Proof. exact (@lem2002645 term15). Qed.
Lemma lem2002648 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2002649 : term5 = term14.
Proof. exact (@lem2002648 term15). Qed.
Lemma lem2002650 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2002651 : term273 = term274.
Proof. exact (MK_COMB (@lem2002650) (@lem2002649)). Qed.
Lemma lem2002652 : term412 = term413.
Proof. exact (MK_COMB (@lem2002651) (@lem2002646)). Qed.
Lemma lem2002653 : term414.
Proof. exact (@lem1981473 term5 term5 term5 term5 term129 term5). Qed.
Lemma lem2002655 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2002656 : term66 = term73.
Proof. exact (@lem2002655 (NUMERAL 0) term15). Qed.
Lemma lem2002657 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2002658 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2002659 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2002658 h1) (fun h1 : term73 = True => @lem2002657)). Qed.
Lemma lem2002660 : term73 = True.
Proof. exact (EQ_MP (@lem2002659) (@lem2002657)). Qed.
Lemma lem2002661 : term66 = True.
Proof. exact (TRANS (@lem2002656) (@lem2002660)). Qed.
Lemma lem2002662 : True = term66.
Proof. exact (SYM (@lem2002661)). Qed.
Lemma lem2002663 : term66.
Proof. exact (EQ_MP (@lem2002662) (@lem0)). Qed.
Lemma lem2002664 : term415.
Proof. exact (@lem2002653 (@lem2002663)). Qed.
Lemma lem2002666 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2002667 : term66 = term73.
Proof. exact (@lem2002666 (NUMERAL 0) term15). Qed.
Lemma lem2002668 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2002669 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2002670 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2002669 h1) (fun h1 : term73 = True => @lem2002668)). Qed.
Lemma lem2002671 : term73 = True.
Proof. exact (EQ_MP (@lem2002670) (@lem2002668)). Qed.
Lemma lem2002672 : term66 = True.
Proof. exact (TRANS (@lem2002667) (@lem2002671)). Qed.
Lemma lem2002673 : True = term66.
Proof. exact (SYM (@lem2002672)). Qed.
Lemma lem2002674 : term66.
Proof. exact (EQ_MP (@lem2002673) (@lem0)). Qed.
Lemma lem2002675 : term416.
Proof. exact (@lem2002664 (@lem2002674)). Qed.
Lemma lem2002677 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2002678 : term66 = term73.
Proof. exact (@lem2002677 (NUMERAL 0) term15). Qed.
Lemma lem2002679 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2002680 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2002681 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2002680 h1) (fun h1 : term73 = True => @lem2002679)). Qed.
Lemma lem2002682 : term73 = True.
Proof. exact (EQ_MP (@lem2002681) (@lem2002679)). Qed.
Lemma lem2002683 : term66 = True.
Proof. exact (TRANS (@lem2002678) (@lem2002682)). Qed.
Lemma lem2002684 : True = term66.
Proof. exact (SYM (@lem2002683)). Qed.
Lemma lem2002685 : term66.
Proof. exact (EQ_MP (@lem2002684) (@lem0)). Qed.
Lemma lem2002686 : term417.
Proof. exact (@lem2002675 (@lem2002685)). Qed.
Lemma lem2002688 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2002689 : term26 = term27.
Proof. exact (@lem2002688 term15 term15). Qed.
Lemma lem2002690 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2002691 : term29 = term15.
Proof. exact (EQ_MP (@lem2002690) (@lem940073)). Qed.
Lemma lem2002692 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002693 : term27 = term5.
Proof. exact (MK_COMB (@lem2002692) (@lem2002691)). Qed.
Lemma lem2002694 : term26 = term5.
Proof. exact (TRANS (@lem2002689) (@lem2002693)). Qed.
Lemma lem2002696 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2002697 : term26 = term27.
Proof. exact (@lem2002696 term15 term15). Qed.
Lemma lem2002698 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2002699 : term29 = term15.
Proof. exact (EQ_MP (@lem2002698) (@lem940073)). Qed.
Lemma lem2002700 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002701 : term27 = term5.
Proof. exact (MK_COMB (@lem2002700) (@lem2002699)). Qed.
Lemma lem2002702 : term26 = term5.
Proof. exact (TRANS (@lem2002697) (@lem2002701)). Qed.
Lemma lem2002703 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2002704 : term281 = term273.
Proof. exact (MK_COMB (@lem2002703) (@lem2002702)). Qed.
Lemma lem2002705 : term418 = term412.
Proof. exact (MK_COMB (@lem2002704) (@lem2002694)). Qed.
Lemma lem2002706 : term412 = term128.
Proof. exact (@lem1367770 term15 term15). Qed.
Lemma lem2002707 : term124 = term125.
Proof. exact (@lem706885). Qed.
Lemma lem2002708 : (term124 = term125) = (term126 = term127).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term125). Qed.
Lemma lem2002709 : term126 = term127.
Proof. exact (EQ_MP (@lem2002708) (@lem2002707)). Qed.
Lemma lem2002710 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002711 : term128 = term129.
Proof. exact (MK_COMB (@lem2002710) (@lem2002709)). Qed.
Lemma lem2002712 : term412 = term129.
Proof. exact (TRANS (@lem2002706) (@lem2002711)). Qed.
Lemma lem2002713 : term418 = term129.
Proof. exact (TRANS (@lem2002705) (@lem2002712)). Qed.
Lemma lem2002714 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2002715 : term419 = term420.
Proof. exact (MK_COMB (@lem2002714) (@lem2002713)). Qed.
Lemma lem2002716 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem2002717 : term421 = term422.
Proof. exact (MK_COMB (@lem2002715) (@lem2002716)). Qed.
Lemma lem2002719 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2002720 : term422 = term137.
Proof. exact (@lem2002719 term127 term15). Qed.
Lemma lem2002721 : term135 = term125.
Proof. exact (@lem996237 term125). Qed.
Lemma lem2002722 : (term135 = term125) = (term136 = term127).
Proof. exact (@lem1007663 term125 (BIT1 0) term125). Qed.
Lemma lem2002723 : term136 = term127.
Proof. exact (EQ_MP (@lem2002722) (@lem2002721)). Qed.
Lemma lem2002724 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002725 : term137 = term129.
Proof. exact (MK_COMB (@lem2002724) (@lem2002723)). Qed.
Lemma lem2002726 : term422 = term129.
Proof. exact (TRANS (@lem2002720) (@lem2002725)). Qed.
Lemma lem2002727 : term421 = term129.
Proof. exact (TRANS (@lem2002717) (@lem2002726)). Qed.
Lemma lem2002729 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2002730 : term26 = term27.
Proof. exact (@lem2002729 term15 term15). Qed.
Lemma lem2002731 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2002732 : term29 = term15.
Proof. exact (EQ_MP (@lem2002731) (@lem940073)). Qed.
Lemma lem2002733 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002734 : term27 = term5.
Proof. exact (MK_COMB (@lem2002733) (@lem2002732)). Qed.
Lemma lem2002735 : term26 = term5.
Proof. exact (TRANS (@lem2002730) (@lem2002734)). Qed.
Lemma lem2002736 : term420 = term420.
Proof. exact (eq_refl term420). Qed.
Lemma lem2002737 : term423 = term422.
Proof. exact (MK_COMB (@lem2002736) (@lem2002735)). Qed.
Lemma lem2002739 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2002740 : term422 = term137.
Proof. exact (@lem2002739 term127 term15). Qed.
Lemma lem2002741 : term135 = term125.
Proof. exact (@lem996237 term125). Qed.
Lemma lem2002742 : (term135 = term125) = (term136 = term127).
Proof. exact (@lem1007663 term125 (BIT1 0) term125). Qed.
Lemma lem2002743 : term136 = term127.
Proof. exact (EQ_MP (@lem2002742) (@lem2002741)). Qed.
Lemma lem2002744 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002745 : term137 = term129.
Proof. exact (MK_COMB (@lem2002744) (@lem2002743)). Qed.
Lemma lem2002746 : term422 = term129.
Proof. exact (TRANS (@lem2002740) (@lem2002745)). Qed.
Lemma lem2002747 : term423 = term129.
Proof. exact (TRANS (@lem2002737) (@lem2002746)). Qed.
Lemma lem2002748 : term129 = term423.
Proof. exact (SYM (@lem2002747)). Qed.
Lemma lem2002749 : term421 = term423.
Proof. exact (TRANS (@lem2002727) (@lem2002748)). Qed.
Lemma lem2002750 : term413 = term424.
Proof. exact (@lem2002686 (@lem2002749)). Qed.
Lemma lem2002751 : term412 = term424.
Proof. exact (TRANS (@lem2002652) (@lem2002750)). Qed.
Lemma lem2002753 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2002754 : term424 = term129.
Proof. exact (@lem2002753 term129). Qed.
Lemma lem2002755 : term412 = term129.
Proof. exact (TRANS (@lem2002751) (@lem2002754)). Qed.
Lemma lem2002756 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2002757 : term425 = term420.
Proof. exact (MK_COMB (@lem2002756) (@lem2002755)). Qed.
Lemma lem2002758 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2002759 (x : real) : (term411 x) = (term426 x).
Proof. exact (MK_COMB (@lem2002757) (@lem2002758 x)). Qed.
Lemma lem2002761 (x : real) : (real_add x x) = (term426 x).
Proof. exact (TRANS (@lem2002643 x) (@lem2002759 x)). Qed.
Lemma lem2002762 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2002763 (x : real) : (term489 x) = (term490 x).
Proof. exact (MK_COMB (@lem2002762) (@lem2002761 x)). Qed.
Lemma lem2002764 (x : real) : (term491 x) = (term492 x).
Proof. exact (MK_COMB (@lem2002763 x) (@lem2002637)). Qed.
Lemma lem2002765 (x : real) : (term492 x) = (term493 x).
Proof. exact (@lem1982792 (term426 x) term2). Qed.
Lemma lem2002767 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2002768 : term2 = term67.
Proof. exact (@lem2002767 (NUMERAL 0)). Qed.
Lemma lem2002770 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2002771 : term12 = term18.
Proof. exact (@lem2002770 term15). Qed.
Lemma lem2002772 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2002773 : term19 = term20.
Proof. exact (MK_COMB (@lem2002772) (@lem2002771)). Qed.
Lemma lem2002774 : term258 = term259.
Proof. exact (MK_COMB (@lem2002773) (@lem2002768)). Qed.
Lemma lem2002775 : term259 = term260.
Proof. exact (@lem1981613 term12 term2 term5 term5). Qed.
Lemma lem2002777 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2002778 : term26 = term27.
Proof. exact (@lem2002777 term15 term15). Qed.
Lemma lem2002779 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2002780 : term29 = term15.
Proof. exact (EQ_MP (@lem2002779) (@lem940073)). Qed.
Lemma lem2002781 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002782 : term27 = term5.
Proof. exact (MK_COMB (@lem2002781) (@lem2002780)). Qed.
Lemma lem2002783 : term26 = term5.
Proof. exact (TRANS (@lem2002778) (@lem2002782)). Qed.
Lemma lem2002785 (x : nat) : (term261 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2002786 : term258 = term2.
Proof. exact (@lem2002785 term15). Qed.
Lemma lem2002787 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2002788 : term262 = term263.
Proof. exact (MK_COMB (@lem2002787) (@lem2002786)). Qed.
Lemma lem2002789 : term260 = term67.
Proof. exact (MK_COMB (@lem2002788) (@lem2002783)). Qed.
Lemma lem2002790 : term259 = term67.
Proof. exact (TRANS (@lem2002775) (@lem2002789)). Qed.
Lemma lem2002791 : term258 = term67.
Proof. exact (TRANS (@lem2002774) (@lem2002790)). Qed.
Lemma lem2002793 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2002794 : term67 = term2.
Proof. exact (@lem2002793 term2). Qed.
Lemma lem2002795 : term258 = term2.
Proof. exact (TRANS (@lem2002791) (@lem2002794)). Qed.
Lemma lem2002796 (x : real) : (term428 x) = (term428 x).
Proof. exact (eq_refl (term428 x)). Qed.
Lemma lem2002797 (x : real) : (term493 x) = (term494 x).
Proof. exact (MK_COMB (@lem2002796 x) (@lem2002795)). Qed.
Lemma lem2002798 (x : real) : (term494 x) = (term426 x).
Proof. exact (@lem1982723 (term426 x)). Qed.
Lemma lem2002799 (x : real) : (term493 x) = (term426 x).
Proof. exact (TRANS (@lem2002797 x) (@lem2002798 x)). Qed.
Lemma lem2002800 (x : real) : (term492 x) = (term426 x).
Proof. exact (TRANS (@lem2002765 x) (@lem2002799 x)). Qed.
Lemma lem2002801 (x : real) : (term491 x) = (term426 x).
Proof. exact (TRANS (@lem2002764 x) (@lem2002800 x)). Qed.
Lemma lem2002802 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2002803 (x : real) : (term495 x) = (term496 x).
Proof. exact (MK_COMB (@lem2002802) (@lem2002801 x)). Qed.
Lemma lem2002804 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2002805 (x : real) : (term488 x) = (term497 x).
Proof. exact (MK_COMB (@lem2002803 x) (@lem2002804)). Qed.
Lemma lem2002806 (x : real) : (term487 x) = (term497 x).
Proof. exact (TRANS (@lem2002636 x) (@lem2002805 x)). Qed.
Lemma lem2002807 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2002808 (x : real) : (term498 x) = term499.
Proof. exact (MK_COMB (@lem2002807) (@lem2002635 x)). Qed.
Lemma lem2002809 (x : real) : (term500 x) = (term501 x).
Proof. exact (MK_COMB (@lem2002808 x) (@lem2002806 x)). Qed.
Lemma lem2002810 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2002811 (x : real) : (term502 x) = (term502 x).
Proof. exact (MK_COMB (@lem2002810) (@lem2002470 x)). Qed.
Lemma lem2002812 (x : real) : (term454 x) = (term503 x).
Proof. exact (MK_COMB (@lem2002811 x) (@lem2002809 x)). Qed.
Lemma lem2002813 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2002814 (x : real) : (term455 x) = (term455 x).
Proof. exact (MK_COMB (@lem2002813) (@lem2002416 x)). Qed.
Lemma lem2002815 (x : real) : (term457 x) = (term504 x).
Proof. exact (MK_COMB (@lem2002814 x) (@lem2002812 x)). Qed.
Lemma lem2002816 (x : real) : (term505 x) = (term506 x).
Proof. exact (@lem1988289 term2 x). Qed.
Lemma lem2002822 (x : real) : (term507 x) = (term508 x).
Proof. exact (@lem1982792 term2 x). Qed.
Lemma lem2002827 (x : real) : (term508 x) = (term57 x).
Proof. exact (@lem1982721 (term57 x)). Qed.
Lemma lem2002829 (x : real) : (term507 x) = (term57 x).
Proof. exact (TRANS (@lem2002822 x) (@lem2002827 x)). Qed.
Lemma lem2002830 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2002831 (x : real) : (term509 x) = (term510 x).
Proof. exact (MK_COMB (@lem2002830) (@lem2002829 x)). Qed.
Lemma lem2002832 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2002833 (x : real) : (term506 x) = (term511 x).
Proof. exact (MK_COMB (@lem2002831 x) (@lem2002832)). Qed.
Lemma lem2002834 (x : real) : (term505 x) = (term511 x).
Proof. exact (TRANS (@lem2002816 x) (@lem2002833 x)). Qed.
Lemma lem2002835 (x : real) : (term512 x) = (term513 x).
Proof. exact (@lem1988291 (term514 x) term2). Qed.
Lemma lem2002836 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2002837 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem2002844 (x : real) : (real_neg x) = (term57 x).
Proof. exact (@lem1982785 x). Qed.
Lemma lem2002845 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2002846 (x : real) : (term515 x) = (term287 x).
Proof. exact (MK_COMB (@lem2002845) (@lem2002844 x)). Qed.
Lemma lem2002849 (x : real) : (term514 x) = (term516 x).
Proof. exact (MK_COMB (@lem2002846 x) (@lem2002837)). Qed.
Lemma lem2002850 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2002851 (x : real) : (term517 x) = (term518 x).
Proof. exact (MK_COMB (@lem2002850) (@lem2002849 x)). Qed.
Lemma lem2002852 (x : real) : (term519 x) = (term520 x).
Proof. exact (MK_COMB (@lem2002851 x) (@lem2002836)). Qed.
Lemma lem2002853 (x : real) : (term520 x) = (term521 x).
Proof. exact (@lem1982792 (term516 x) term2). Qed.
Lemma lem2002855 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2002856 : term2 = term67.
Proof. exact (@lem2002855 (NUMERAL 0)). Qed.
Lemma lem2002858 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2002859 : term12 = term18.
Proof. exact (@lem2002858 term15). Qed.
Lemma lem2002860 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2002861 : term19 = term20.
Proof. exact (MK_COMB (@lem2002860) (@lem2002859)). Qed.
Lemma lem2002862 : term258 = term259.
Proof. exact (MK_COMB (@lem2002861) (@lem2002856)). Qed.
Lemma lem2002863 : term259 = term260.
Proof. exact (@lem1981613 term12 term2 term5 term5). Qed.
Lemma lem2002865 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2002866 : term26 = term27.
Proof. exact (@lem2002865 term15 term15). Qed.
Lemma lem2002867 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2002868 : term29 = term15.
Proof. exact (EQ_MP (@lem2002867) (@lem940073)). Qed.
Lemma lem2002869 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002870 : term27 = term5.
Proof. exact (MK_COMB (@lem2002869) (@lem2002868)). Qed.
Lemma lem2002871 : term26 = term5.
Proof. exact (TRANS (@lem2002866) (@lem2002870)). Qed.
Lemma lem2002873 (x : nat) : (term261 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2002874 : term258 = term2.
Proof. exact (@lem2002873 term15). Qed.
Lemma lem2002875 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2002876 : term262 = term263.
Proof. exact (MK_COMB (@lem2002875) (@lem2002874)). Qed.
Lemma lem2002877 : term260 = term67.
Proof. exact (MK_COMB (@lem2002876) (@lem2002871)). Qed.
Lemma lem2002878 : term259 = term67.
Proof. exact (TRANS (@lem2002863) (@lem2002877)). Qed.
Lemma lem2002879 : term258 = term67.
Proof. exact (TRANS (@lem2002862) (@lem2002878)). Qed.
Lemma lem2002881 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2002882 : term67 = term2.
Proof. exact (@lem2002881 term2). Qed.
Lemma lem2002883 : term258 = term2.
Proof. exact (TRANS (@lem2002879) (@lem2002882)). Qed.
Lemma lem2002884 (x : real) : (term522 x) = (term522 x).
Proof. exact (eq_refl (term522 x)). Qed.
Lemma lem2002885 (x : real) : (term521 x) = (term523 x).
Proof. exact (MK_COMB (@lem2002884 x) (@lem2002883)). Qed.
Lemma lem2002886 (x : real) : (term523 x) = (term516 x).
Proof. exact (@lem1982723 (term516 x)). Qed.
Lemma lem2002887 (x : real) : (term521 x) = (term516 x).
Proof. exact (TRANS (@lem2002885 x) (@lem2002886 x)). Qed.
Lemma lem2002888 (x : real) : (term520 x) = (term516 x).
Proof. exact (TRANS (@lem2002853 x) (@lem2002887 x)). Qed.
Lemma lem2002889 (x : real) : (term519 x) = (term516 x).
Proof. exact (TRANS (@lem2002852 x) (@lem2002888 x)). Qed.
Lemma lem2002890 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2002891 (x : real) : (term524 x) = (term525 x).
Proof. exact (MK_COMB (@lem2002890) (@lem2002889 x)). Qed.
Lemma lem2002892 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2002893 (x : real) : (term513 x) = (term526 x).
Proof. exact (MK_COMB (@lem2002891 x) (@lem2002892)). Qed.
Lemma lem2002894 (x : real) : (term512 x) = (term526 x).
Proof. exact (TRANS (@lem2002835 x) (@lem2002893 x)). Qed.
Lemma lem2002895 (x : real) : (term527 x) = (term528 x).
Proof. exact (@lem1988289 (term529 x) term2). Qed.
Lemma lem2002896 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2002903 (x : real) : (real_neg x) = (term57 x).
Proof. exact (@lem1982785 x). Qed.
Lemma lem2002912 (x : real) : (term287 x) = (term287 x).
Proof. exact (eq_refl (term287 x)). Qed.
Lemma lem2002913 (x : real) : (term529 x) = (term392 x).
Proof. exact (MK_COMB (@lem2002912 x) (@lem2002903 x)). Qed.
Lemma lem2002914 (x : real) : (term392 x) = (term393 x).
Proof. exact (@lem1982711 term12 term12 x). Qed.
Lemma lem2002916 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2002917 : term12 = term18.
Proof. exact (@lem2002916 term15). Qed.
Lemma lem2002919 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2002920 : term12 = term18.
Proof. exact (@lem2002919 term15). Qed.
Lemma lem2002921 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2002922 : term47 = term98.
Proof. exact (MK_COMB (@lem2002921) (@lem2002920)). Qed.
Lemma lem2002923 : term115 = term116.
Proof. exact (MK_COMB (@lem2002922) (@lem2002917)). Qed.
Lemma lem2002924 : term117.
Proof. exact (@lem1981473 term12 term5 term12 term5 term118 term5). Qed.
Lemma lem2002926 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2002927 : term66 = term73.
Proof. exact (@lem2002926 (NUMERAL 0) term15). Qed.
Lemma lem2002928 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2002929 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2002930 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2002929 h1) (fun h1 : term73 = True => @lem2002928)). Qed.
Lemma lem2002931 : term73 = True.
Proof. exact (EQ_MP (@lem2002930) (@lem2002928)). Qed.
Lemma lem2002932 : term66 = True.
Proof. exact (TRANS (@lem2002927) (@lem2002931)). Qed.
Lemma lem2002933 : True = term66.
Proof. exact (SYM (@lem2002932)). Qed.
Lemma lem2002934 : term66.
Proof. exact (EQ_MP (@lem2002933) (@lem0)). Qed.
Lemma lem2002935 : term119.
Proof. exact (@lem2002924 (@lem2002934)). Qed.
Lemma lem2002937 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2002938 : term66 = term73.
Proof. exact (@lem2002937 (NUMERAL 0) term15). Qed.
Lemma lem2002939 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2002940 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2002941 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2002940 h1) (fun h1 : term73 = True => @lem2002939)). Qed.
Lemma lem2002942 : term73 = True.
Proof. exact (EQ_MP (@lem2002941) (@lem2002939)). Qed.
Lemma lem2002943 : term66 = True.
Proof. exact (TRANS (@lem2002938) (@lem2002942)). Qed.
Lemma lem2002944 : True = term66.
Proof. exact (SYM (@lem2002943)). Qed.
Lemma lem2002945 : term66.
Proof. exact (EQ_MP (@lem2002944) (@lem0)). Qed.
Lemma lem2002946 : term120.
Proof. exact (@lem2002935 (@lem2002945)). Qed.
Lemma lem2002948 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2002949 : term66 = term73.
Proof. exact (@lem2002948 (NUMERAL 0) term15). Qed.
Lemma lem2002950 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2002951 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2002952 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2002951 h1) (fun h1 : term73 = True => @lem2002950)). Qed.
Lemma lem2002953 : term73 = True.
Proof. exact (EQ_MP (@lem2002952) (@lem2002950)). Qed.
Lemma lem2002954 : term66 = True.
Proof. exact (TRANS (@lem2002949) (@lem2002953)). Qed.
Lemma lem2002955 : True = term66.
Proof. exact (SYM (@lem2002954)). Qed.
Lemma lem2002956 : term66.
Proof. exact (EQ_MP (@lem2002955) (@lem0)). Qed.
Lemma lem2002957 : term121.
Proof. exact (@lem2002946 (@lem2002956)). Qed.
Lemma lem2002959 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2002960 : term21 = term32.
Proof. exact (@lem2002959 term15 term15). Qed.
Lemma lem2002961 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2002962 : term29 = term15.
Proof. exact (EQ_MP (@lem2002961) (@lem940073)). Qed.
Lemma lem2002963 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002964 : term27 = term5.
Proof. exact (MK_COMB (@lem2002963) (@lem2002962)). Qed.
Lemma lem2002965 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2002966 : term32 = term12.
Proof. exact (MK_COMB (@lem2002965) (@lem2002964)). Qed.
Lemma lem2002967 : term21 = term12.
Proof. exact (TRANS (@lem2002960) (@lem2002966)). Qed.
Lemma lem2002969 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2002970 : term21 = term32.
Proof. exact (@lem2002969 term15 term15). Qed.
Lemma lem2002971 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2002972 : term29 = term15.
Proof. exact (EQ_MP (@lem2002971) (@lem940073)). Qed.
Lemma lem2002973 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002974 : term27 = term5.
Proof. exact (MK_COMB (@lem2002973) (@lem2002972)). Qed.
Lemma lem2002975 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2002976 : term32 = term12.
Proof. exact (MK_COMB (@lem2002975) (@lem2002974)). Qed.
Lemma lem2002977 : term21 = term12.
Proof. exact (TRANS (@lem2002970) (@lem2002976)). Qed.
Lemma lem2002978 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2002979 : term105 = term47.
Proof. exact (MK_COMB (@lem2002978) (@lem2002977)). Qed.
Lemma lem2002980 : term122 = term115.
Proof. exact (MK_COMB (@lem2002979) (@lem2002967)). Qed.
Lemma lem2002981 : term115 = term123.
Proof. exact (@lem1367763 term15 term15). Qed.
Lemma lem2002982 : term124 = term125.
Proof. exact (@lem706885). Qed.
Lemma lem2002983 : (term124 = term125) = (term126 = term127).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term125). Qed.
Lemma lem2002984 : term126 = term127.
Proof. exact (EQ_MP (@lem2002983) (@lem2002982)). Qed.
Lemma lem2002985 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2002986 : term128 = term129.
Proof. exact (MK_COMB (@lem2002985) (@lem2002984)). Qed.
Lemma lem2002987 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2002988 : term123 = term118.
Proof. exact (MK_COMB (@lem2002987) (@lem2002986)). Qed.
Lemma lem2002989 : term115 = term118.
Proof. exact (TRANS (@lem2002981) (@lem2002988)). Qed.
Lemma lem2002990 : term122 = term118.
Proof. exact (TRANS (@lem2002980) (@lem2002989)). Qed.
Lemma lem2002991 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2002992 : term130 = term131.
Proof. exact (MK_COMB (@lem2002991) (@lem2002990)). Qed.
Lemma lem2002993 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem2002994 : term132 = term133.
Proof. exact (MK_COMB (@lem2002992) (@lem2002993)). Qed.
Lemma lem2002996 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2002997 : term133 = term134.
Proof. exact (@lem2002996 term127 term15). Qed.
Lemma lem2002998 : term135 = term125.
Proof. exact (@lem996237 term125). Qed.
Lemma lem2002999 : (term135 = term125) = (term136 = term127).
Proof. exact (@lem1007663 term125 (BIT1 0) term125). Qed.
Lemma lem2003000 : term136 = term127.
Proof. exact (EQ_MP (@lem2002999) (@lem2002998)). Qed.
Lemma lem2003001 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003002 : term137 = term129.
Proof. exact (MK_COMB (@lem2003001) (@lem2003000)). Qed.
Lemma lem2003003 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2003004 : term134 = term118.
Proof. exact (MK_COMB (@lem2003003) (@lem2003002)). Qed.
Lemma lem2003005 : term133 = term118.
Proof. exact (TRANS (@lem2002997) (@lem2003004)). Qed.
Lemma lem2003006 : term132 = term118.
Proof. exact (TRANS (@lem2002994) (@lem2003005)). Qed.
Lemma lem2003008 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2003009 : term26 = term27.
Proof. exact (@lem2003008 term15 term15). Qed.
Lemma lem2003010 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2003011 : term29 = term15.
Proof. exact (EQ_MP (@lem2003010) (@lem940073)). Qed.
Lemma lem2003012 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003013 : term27 = term5.
Proof. exact (MK_COMB (@lem2003012) (@lem2003011)). Qed.
Lemma lem2003014 : term26 = term5.
Proof. exact (TRANS (@lem2003009) (@lem2003013)). Qed.
Lemma lem2003015 : term131 = term131.
Proof. exact (eq_refl term131). Qed.
Lemma lem2003016 : term138 = term133.
Proof. exact (MK_COMB (@lem2003015) (@lem2003014)). Qed.
Lemma lem2003018 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2003019 : term133 = term134.
Proof. exact (@lem2003018 term127 term15). Qed.
Lemma lem2003020 : term135 = term125.
Proof. exact (@lem996237 term125). Qed.
Lemma lem2003021 : (term135 = term125) = (term136 = term127).
Proof. exact (@lem1007663 term125 (BIT1 0) term125). Qed.
Lemma lem2003022 : term136 = term127.
Proof. exact (EQ_MP (@lem2003021) (@lem2003020)). Qed.
Lemma lem2003023 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003024 : term137 = term129.
Proof. exact (MK_COMB (@lem2003023) (@lem2003022)). Qed.
Lemma lem2003025 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2003026 : term134 = term118.
Proof. exact (MK_COMB (@lem2003025) (@lem2003024)). Qed.
Lemma lem2003027 : term133 = term118.
Proof. exact (TRANS (@lem2003019) (@lem2003026)). Qed.
Lemma lem2003028 : term138 = term118.
Proof. exact (TRANS (@lem2003016) (@lem2003027)). Qed.
Lemma lem2003029 : term118 = term138.
Proof. exact (SYM (@lem2003028)). Qed.
Lemma lem2003030 : term132 = term138.
Proof. exact (TRANS (@lem2003006) (@lem2003029)). Qed.
Lemma lem2003031 : term116 = term139.
Proof. exact (@lem2002957 (@lem2003030)). Qed.
Lemma lem2003032 : term115 = term139.
Proof. exact (TRANS (@lem2002923) (@lem2003031)). Qed.
Lemma lem2003034 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2003035 : term139 = term118.
Proof. exact (@lem2003034 term118). Qed.
Lemma lem2003036 : term115 = term118.
Proof. exact (TRANS (@lem2003032) (@lem2003035)). Qed.
Lemma lem2003037 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2003038 : term394 = term131.
Proof. exact (MK_COMB (@lem2003037) (@lem2003036)). Qed.
Lemma lem2003039 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2003040 (x : real) : (term393 x) = (term395 x).
Proof. exact (MK_COMB (@lem2003038) (@lem2003039 x)). Qed.
Lemma lem2003041 (x : real) : (term392 x) = (term395 x).
Proof. exact (TRANS (@lem2002914 x) (@lem2003040 x)). Qed.
Lemma lem2003042 (x : real) : (term529 x) = (term395 x).
Proof. exact (TRANS (@lem2002913 x) (@lem2003041 x)). Qed.
Lemma lem2003043 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2003044 (x : real) : (term530 x) = (term531 x).
Proof. exact (MK_COMB (@lem2003043) (@lem2003042 x)). Qed.
Lemma lem2003045 (x : real) : (term532 x) = (term533 x).
Proof. exact (MK_COMB (@lem2003044 x) (@lem2002896)). Qed.
Lemma lem2003046 (x : real) : (term533 x) = (term534 x).
Proof. exact (@lem1982792 (term395 x) term2). Qed.
Lemma lem2003048 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2003049 : term2 = term67.
Proof. exact (@lem2003048 (NUMERAL 0)). Qed.
Lemma lem2003051 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2003052 : term12 = term18.
Proof. exact (@lem2003051 term15). Qed.
Lemma lem2003053 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2003054 : term19 = term20.
Proof. exact (MK_COMB (@lem2003053) (@lem2003052)). Qed.
Lemma lem2003055 : term258 = term259.
Proof. exact (MK_COMB (@lem2003054) (@lem2003049)). Qed.
Lemma lem2003056 : term259 = term260.
Proof. exact (@lem1981613 term12 term2 term5 term5). Qed.
Lemma lem2003058 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2003059 : term26 = term27.
Proof. exact (@lem2003058 term15 term15). Qed.
Lemma lem2003060 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2003061 : term29 = term15.
Proof. exact (EQ_MP (@lem2003060) (@lem940073)). Qed.
Lemma lem2003062 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003063 : term27 = term5.
Proof. exact (MK_COMB (@lem2003062) (@lem2003061)). Qed.
Lemma lem2003064 : term26 = term5.
Proof. exact (TRANS (@lem2003059) (@lem2003063)). Qed.
Lemma lem2003066 (x : nat) : (term261 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2003067 : term258 = term2.
Proof. exact (@lem2003066 term15). Qed.
Lemma lem2003068 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2003069 : term262 = term263.
Proof. exact (MK_COMB (@lem2003068) (@lem2003067)). Qed.
Lemma lem2003070 : term260 = term67.
Proof. exact (MK_COMB (@lem2003069) (@lem2003064)). Qed.
Lemma lem2003071 : term259 = term67.
Proof. exact (TRANS (@lem2003056) (@lem2003070)). Qed.
Lemma lem2003072 : term258 = term67.
Proof. exact (TRANS (@lem2003055) (@lem2003071)). Qed.
Lemma lem2003074 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2003075 : term67 = term2.
Proof. exact (@lem2003074 term2). Qed.
Lemma lem2003076 : term258 = term2.
Proof. exact (TRANS (@lem2003072) (@lem2003075)). Qed.
Lemma lem2003077 (x : real) : (term397 x) = (term397 x).
Proof. exact (eq_refl (term397 x)). Qed.
Lemma lem2003078 (x : real) : (term534 x) = (term535 x).
Proof. exact (MK_COMB (@lem2003077 x) (@lem2003076)). Qed.
Lemma lem2003079 (x : real) : (term535 x) = (term395 x).
Proof. exact (@lem1982723 (term395 x)). Qed.
Lemma lem2003080 (x : real) : (term534 x) = (term395 x).
Proof. exact (TRANS (@lem2003078 x) (@lem2003079 x)). Qed.
Lemma lem2003081 (x : real) : (term533 x) = (term395 x).
Proof. exact (TRANS (@lem2003046 x) (@lem2003080 x)). Qed.
Lemma lem2003082 (x : real) : (term532 x) = (term395 x).
Proof. exact (TRANS (@lem2003045 x) (@lem2003081 x)). Qed.
Lemma lem2003083 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2003084 (x : real) : (term536 x) = (term537 x).
Proof. exact (MK_COMB (@lem2003083) (@lem2003082 x)). Qed.
Lemma lem2003085 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2003086 (x : real) : (term528 x) = (term538 x).
Proof. exact (MK_COMB (@lem2003084 x) (@lem2003085)). Qed.
Lemma lem2003087 (x : real) : (term527 x) = (term538 x).
Proof. exact (TRANS (@lem2002895 x) (@lem2003086 x)). Qed.
Lemma lem2003088 (x : real) : (term539 x) = (term540 x).
Proof. exact (@lem1988289 (term541 x) term2). Qed.
Lemma lem2003089 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2003096 (x : real) : (real_neg x) = (term57 x).
Proof. exact (@lem1982785 x). Qed.
Lemma lem2003099 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem2003100 (x : real) : (term541 x) = (term436 x).
Proof. exact (MK_COMB (@lem2003099 x) (@lem2003096 x)). Qed.
Lemma lem2003101 (x : real) : (term436 x) = (term97 x).
Proof. exact (@lem1982715 term12 x). Qed.
Lemma lem2003103 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2003104 : term5 = term14.
Proof. exact (@lem2003103 term15). Qed.
Lemma lem2003106 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2003107 : term12 = term18.
Proof. exact (@lem2003106 term15). Qed.
Lemma lem2003108 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2003109 : term47 = term98.
Proof. exact (MK_COMB (@lem2003108) (@lem2003107)). Qed.
Lemma lem2003110 : term99 = term100.
Proof. exact (MK_COMB (@lem2003109) (@lem2003104)). Qed.
Lemma lem2003111 : term101.
Proof. exact (@lem1981473 term12 term5 term5 term5 term2 term5). Qed.
Lemma lem2003113 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2003114 : term66 = term73.
Proof. exact (@lem2003113 (NUMERAL 0) term15). Qed.
Lemma lem2003115 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2003116 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2003117 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2003116 h1) (fun h1 : term73 = True => @lem2003115)). Qed.
Lemma lem2003118 : term73 = True.
Proof. exact (EQ_MP (@lem2003117) (@lem2003115)). Qed.
Lemma lem2003119 : term66 = True.
Proof. exact (TRANS (@lem2003114) (@lem2003118)). Qed.
Lemma lem2003120 : True = term66.
Proof. exact (SYM (@lem2003119)). Qed.
Lemma lem2003121 : term66.
Proof. exact (EQ_MP (@lem2003120) (@lem0)). Qed.
Lemma lem2003122 : term102.
Proof. exact (@lem2003111 (@lem2003121)). Qed.
Lemma lem2003124 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2003125 : term66 = term73.
Proof. exact (@lem2003124 (NUMERAL 0) term15). Qed.
Lemma lem2003126 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2003127 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2003128 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2003127 h1) (fun h1 : term73 = True => @lem2003126)). Qed.
Lemma lem2003129 : term73 = True.
Proof. exact (EQ_MP (@lem2003128) (@lem2003126)). Qed.
Lemma lem2003130 : term66 = True.
Proof. exact (TRANS (@lem2003125) (@lem2003129)). Qed.
Lemma lem2003131 : True = term66.
Proof. exact (SYM (@lem2003130)). Qed.
Lemma lem2003132 : term66.
Proof. exact (EQ_MP (@lem2003131) (@lem0)). Qed.
Lemma lem2003133 : term103.
Proof. exact (@lem2003122 (@lem2003132)). Qed.
Lemma lem2003135 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2003136 : term66 = term73.
Proof. exact (@lem2003135 (NUMERAL 0) term15). Qed.
Lemma lem2003137 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2003138 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2003139 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2003138 h1) (fun h1 : term73 = True => @lem2003137)). Qed.
Lemma lem2003140 : term73 = True.
Proof. exact (EQ_MP (@lem2003139) (@lem2003137)). Qed.
Lemma lem2003141 : term66 = True.
Proof. exact (TRANS (@lem2003136) (@lem2003140)). Qed.
Lemma lem2003142 : True = term66.
Proof. exact (SYM (@lem2003141)). Qed.
Lemma lem2003143 : term66.
Proof. exact (EQ_MP (@lem2003142) (@lem0)). Qed.
Lemma lem2003144 : term104.
Proof. exact (@lem2003133 (@lem2003143)). Qed.
Lemma lem2003146 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2003147 : term26 = term27.
Proof. exact (@lem2003146 term15 term15). Qed.
Lemma lem2003148 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2003149 : term29 = term15.
Proof. exact (EQ_MP (@lem2003148) (@lem940073)). Qed.
Lemma lem2003150 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003151 : term27 = term5.
Proof. exact (MK_COMB (@lem2003150) (@lem2003149)). Qed.
Lemma lem2003152 : term26 = term5.
Proof. exact (TRANS (@lem2003147) (@lem2003151)). Qed.
Lemma lem2003154 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2003155 : term21 = term32.
Proof. exact (@lem2003154 term15 term15). Qed.
Lemma lem2003156 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2003157 : term29 = term15.
Proof. exact (EQ_MP (@lem2003156) (@lem940073)). Qed.
Lemma lem2003158 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003159 : term27 = term5.
Proof. exact (MK_COMB (@lem2003158) (@lem2003157)). Qed.
Lemma lem2003160 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2003161 : term32 = term12.
Proof. exact (MK_COMB (@lem2003160) (@lem2003159)). Qed.
Lemma lem2003162 : term21 = term12.
Proof. exact (TRANS (@lem2003155) (@lem2003161)). Qed.
Lemma lem2003163 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2003164 : term105 = term47.
Proof. exact (MK_COMB (@lem2003163) (@lem2003162)). Qed.
Lemma lem2003165 : term106 = term99.
Proof. exact (MK_COMB (@lem2003164) (@lem2003152)). Qed.
Lemma lem2003167 (m : nat) : (term107 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2003168 : term99 = term2.
Proof. exact (@lem2003167 term15). Qed.
Lemma lem2003169 : term106 = term2.
Proof. exact (TRANS (@lem2003165) (@lem2003168)). Qed.
Lemma lem2003170 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2003171 : term108 = term109.
Proof. exact (MK_COMB (@lem2003170) (@lem2003169)). Qed.
Lemma lem2003172 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem2003173 : term110 = term78.
Proof. exact (MK_COMB (@lem2003171) (@lem2003172)). Qed.
Lemma lem2003175 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2003176 : term78 = term2.
Proof. exact (@lem2003175 term15). Qed.
Lemma lem2003177 : term110 = term2.
Proof. exact (TRANS (@lem2003173) (@lem2003176)). Qed.
Lemma lem2003179 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2003180 : term26 = term27.
Proof. exact (@lem2003179 term15 term15). Qed.
Lemma lem2003181 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2003182 : term29 = term15.
Proof. exact (EQ_MP (@lem2003181) (@lem940073)). Qed.
Lemma lem2003183 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003184 : term27 = term5.
Proof. exact (MK_COMB (@lem2003183) (@lem2003182)). Qed.
Lemma lem2003185 : term26 = term5.
Proof. exact (TRANS (@lem2003180) (@lem2003184)). Qed.
Lemma lem2003186 : term109 = term109.
Proof. exact (eq_refl term109). Qed.
Lemma lem2003187 : term111 = term78.
Proof. exact (MK_COMB (@lem2003186) (@lem2003185)). Qed.
Lemma lem2003189 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2003190 : term78 = term2.
Proof. exact (@lem2003189 term15). Qed.
Lemma lem2003191 : term111 = term2.
Proof. exact (TRANS (@lem2003187) (@lem2003190)). Qed.
Lemma lem2003192 : term2 = term111.
Proof. exact (SYM (@lem2003191)). Qed.
Lemma lem2003193 : term110 = term111.
Proof. exact (TRANS (@lem2003177) (@lem2003192)). Qed.
Lemma lem2003194 : term100 = term67.
Proof. exact (@lem2003144 (@lem2003193)). Qed.
Lemma lem2003195 : term99 = term67.
Proof. exact (TRANS (@lem2003110) (@lem2003194)). Qed.
Lemma lem2003197 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2003198 : term67 = term2.
Proof. exact (@lem2003197 term2). Qed.
Lemma lem2003199 : term99 = term2.
Proof. exact (TRANS (@lem2003195) (@lem2003198)). Qed.
Lemma lem2003200 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2003201 : term112 = term109.
Proof. exact (MK_COMB (@lem2003200) (@lem2003199)). Qed.
Lemma lem2003202 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2003203 (x : real) : (term97 x) = (term113 x).
Proof. exact (MK_COMB (@lem2003201) (@lem2003202 x)). Qed.
Lemma lem2003204 (x : real) : (term436 x) = (term113 x).
Proof. exact (TRANS (@lem2003101 x) (@lem2003203 x)). Qed.
Lemma lem2003205 (x : real) : (term113 x) = term2.
Proof. exact (@lem1982719 x). Qed.
Lemma lem2003206 (x : real) : (term436 x) = term2.
Proof. exact (TRANS (@lem2003204 x) (@lem2003205 x)). Qed.
Lemma lem2003207 (x : real) : (term541 x) = term2.
Proof. exact (TRANS (@lem2003100 x) (@lem2003206 x)). Qed.
Lemma lem2003208 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2003209 (x : real) : (term542 x) = term6.
Proof. exact (MK_COMB (@lem2003208) (@lem2003207 x)). Qed.
Lemma lem2003210 (x : real) : (term543 x) = term481.
Proof. exact (MK_COMB (@lem2003209 x) (@lem2003089)). Qed.
Lemma lem2003211 : term481 = term482.
Proof. exact (@lem1982792 term2 term2). Qed.
Lemma lem2003213 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2003214 : term2 = term67.
Proof. exact (@lem2003213 (NUMERAL 0)). Qed.
Lemma lem2003216 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2003217 : term12 = term18.
Proof. exact (@lem2003216 term15). Qed.
Lemma lem2003218 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2003219 : term19 = term20.
Proof. exact (MK_COMB (@lem2003218) (@lem2003217)). Qed.
Lemma lem2003220 : term258 = term259.
Proof. exact (MK_COMB (@lem2003219) (@lem2003214)). Qed.
Lemma lem2003221 : term259 = term260.
Proof. exact (@lem1981613 term12 term2 term5 term5). Qed.
Lemma lem2003223 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2003224 : term26 = term27.
Proof. exact (@lem2003223 term15 term15). Qed.
Lemma lem2003225 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2003226 : term29 = term15.
Proof. exact (EQ_MP (@lem2003225) (@lem940073)). Qed.
Lemma lem2003227 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003228 : term27 = term5.
Proof. exact (MK_COMB (@lem2003227) (@lem2003226)). Qed.
Lemma lem2003229 : term26 = term5.
Proof. exact (TRANS (@lem2003224) (@lem2003228)). Qed.
Lemma lem2003231 (x : nat) : (term261 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2003232 : term258 = term2.
Proof. exact (@lem2003231 term15). Qed.
Lemma lem2003233 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2003234 : term262 = term263.
Proof. exact (MK_COMB (@lem2003233) (@lem2003232)). Qed.
Lemma lem2003235 : term260 = term67.
Proof. exact (MK_COMB (@lem2003234) (@lem2003229)). Qed.
Lemma lem2003236 : term259 = term67.
Proof. exact (TRANS (@lem2003221) (@lem2003235)). Qed.
Lemma lem2003237 : term258 = term67.
Proof. exact (TRANS (@lem2003220) (@lem2003236)). Qed.
Lemma lem2003239 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2003240 : term67 = term2.
Proof. exact (@lem2003239 term2). Qed.
Lemma lem2003241 : term258 = term2.
Proof. exact (TRANS (@lem2003237) (@lem2003240)). Qed.
Lemma lem2003242 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2003243 : term482 = term483.
Proof. exact (MK_COMB (@lem2003242) (@lem2003241)). Qed.
Lemma lem2003244 : term483 = term2.
Proof. exact (@lem1982721 term2). Qed.
Lemma lem2003245 : term482 = term2.
Proof. exact (TRANS (@lem2003243) (@lem2003244)). Qed.
Lemma lem2003246 : term481 = term2.
Proof. exact (TRANS (@lem2003211) (@lem2003245)). Qed.
Lemma lem2003247 (x : real) : (term543 x) = term2.
Proof. exact (TRANS (@lem2003210 x) (@lem2003246)). Qed.
Lemma lem2003248 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2003249 (x : real) : (term544 x) = term485.
Proof. exact (MK_COMB (@lem2003248) (@lem2003247 x)). Qed.
Lemma lem2003250 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2003251 (x : real) : (term540 x) = term486.
Proof. exact (MK_COMB (@lem2003249 x) (@lem2003250)). Qed.
Lemma lem2003252 (x : real) : (term539 x) = term486.
Proof. exact (TRANS (@lem2003088 x) (@lem2003251 x)). Qed.
Lemma lem2003253 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2003254 (x : real) : (term545 x) = (term546 x).
Proof. exact (MK_COMB (@lem2003253) (@lem2003087 x)). Qed.
Lemma lem2003255 (x : real) : (term547 x) = (term548 x).
Proof. exact (MK_COMB (@lem2003254 x) (@lem2003252 x)). Qed.
Lemma lem2003256 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2003257 (x : real) : (term549 x) = (term550 x).
Proof. exact (MK_COMB (@lem2003256) (@lem2002894 x)). Qed.
Lemma lem2003258 (x : real) : (term449 x) = (term551 x).
Proof. exact (MK_COMB (@lem2003257 x) (@lem2003255 x)). Qed.
Lemma lem2003259 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2003260 (x : real) : (term450 x) = (term552 x).
Proof. exact (MK_COMB (@lem2003259) (@lem2002834 x)). Qed.
Lemma lem2003261 (x : real) : (term452 x) = (term553 x).
Proof. exact (MK_COMB (@lem2003260 x) (@lem2003258 x)). Qed.
Lemma lem2003262 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2003263 (x : real) : (term459 x) = (term554 x).
Proof. exact (MK_COMB (@lem2003262) (@lem2002815 x)). Qed.
Lemma lem2003264 (x : real) : (term460 x) = (term555 x).
Proof. exact (MK_COMB (@lem2003263 x) (@lem2003261 x)). Qed.
Lemma lem2003276 (x : real) : (term316 x) = (term555 x).
Proof. exact (TRANS (@lem2002368 x) (@lem2003264 x)). Qed.
Lemma lem2003277 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2003278 (x : real) : (term362 x) = (term556 x).
Proof. exact (MK_COMB (@lem2003277) (@lem2003276 x)). Qed.
Lemma lem2003279 (x : real) : (term363 x) = (term557 x).
Proof. exact (MK_COMB (@lem2003278 x) (@lem2002351 x)). Qed.
Lemma lem2003280 (x : real) : (term236 x) = (term557 x).
Proof. exact (TRANS (@lem2001702 x) (@lem2003279 x)). Qed.
Lemma lem2003281 (x : real) : (term213 x) = (term557 x).
Proof. exact (TRANS (@lem2000709 x) (@lem2003280 x)). Qed.
Lemma lem2003283 (a : real) (x : real) (b : real) (r : real) : (term377 a x b r) = (term378 a x b r).
Proof. exact (proj1 (@lem1482705 x a b (@el real) (@el real) r)). Qed.
Lemma lem2003284 (x : real) : (term209 x) = (term558 x).
Proof. exact (@lem2003283 (real_abs x) (term4 x) term5 term2). Qed.
Lemma lem2003285 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem2003300 (x : real) : (term559 x) = (term4 x).
Proof. exact (@lem1982733 (term4 x)). Qed.
Lemma lem2003301 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2003302 (x : real) : (term560 x) = (term264 x).
Proof. exact (MK_COMB (@lem2003301) (@lem2003300 x)). Qed.
Lemma lem2003303 (x : real) : (term561 x) = (term562 x).
Proof. exact (MK_COMB (@lem2003302 x) (@lem2003285)). Qed.
Lemma lem2003304 (x : real) : (term562 x) = (term563 x).
Proof. exact (@lem1982755 (real_abs x) term5 term5). Qed.
Lemma lem2003306 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2003307 : term5 = term14.
Proof. exact (@lem2003306 term15). Qed.
Lemma lem2003309 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2003310 : term5 = term14.
Proof. exact (@lem2003309 term15). Qed.
Lemma lem2003311 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2003312 : term273 = term274.
Proof. exact (MK_COMB (@lem2003311) (@lem2003310)). Qed.
Lemma lem2003313 : term412 = term413.
Proof. exact (MK_COMB (@lem2003312) (@lem2003307)). Qed.
Lemma lem2003314 : term414.
Proof. exact (@lem1981473 term5 term5 term5 term5 term129 term5). Qed.
Lemma lem2003316 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2003317 : term66 = term73.
Proof. exact (@lem2003316 (NUMERAL 0) term15). Qed.
Lemma lem2003318 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2003319 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2003320 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2003319 h1) (fun h1 : term73 = True => @lem2003318)). Qed.
Lemma lem2003321 : term73 = True.
Proof. exact (EQ_MP (@lem2003320) (@lem2003318)). Qed.
Lemma lem2003322 : term66 = True.
Proof. exact (TRANS (@lem2003317) (@lem2003321)). Qed.
Lemma lem2003323 : True = term66.
Proof. exact (SYM (@lem2003322)). Qed.
Lemma lem2003324 : term66.
Proof. exact (EQ_MP (@lem2003323) (@lem0)). Qed.
Lemma lem2003325 : term415.
Proof. exact (@lem2003314 (@lem2003324)). Qed.
Lemma lem2003327 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2003328 : term66 = term73.
Proof. exact (@lem2003327 (NUMERAL 0) term15). Qed.
Lemma lem2003329 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2003330 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2003331 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2003330 h1) (fun h1 : term73 = True => @lem2003329)). Qed.
Lemma lem2003332 : term73 = True.
Proof. exact (EQ_MP (@lem2003331) (@lem2003329)). Qed.
Lemma lem2003333 : term66 = True.
Proof. exact (TRANS (@lem2003328) (@lem2003332)). Qed.
Lemma lem2003334 : True = term66.
Proof. exact (SYM (@lem2003333)). Qed.
Lemma lem2003335 : term66.
Proof. exact (EQ_MP (@lem2003334) (@lem0)). Qed.
Lemma lem2003336 : term416.
Proof. exact (@lem2003325 (@lem2003335)). Qed.
Lemma lem2003338 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2003339 : term66 = term73.
Proof. exact (@lem2003338 (NUMERAL 0) term15). Qed.
Lemma lem2003340 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2003341 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2003342 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2003341 h1) (fun h1 : term73 = True => @lem2003340)). Qed.
Lemma lem2003343 : term73 = True.
Proof. exact (EQ_MP (@lem2003342) (@lem2003340)). Qed.
Lemma lem2003344 : term66 = True.
Proof. exact (TRANS (@lem2003339) (@lem2003343)). Qed.
Lemma lem2003345 : True = term66.
Proof. exact (SYM (@lem2003344)). Qed.
Lemma lem2003346 : term66.
Proof. exact (EQ_MP (@lem2003345) (@lem0)). Qed.
Lemma lem2003347 : term417.
Proof. exact (@lem2003336 (@lem2003346)). Qed.
Lemma lem2003349 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2003350 : term26 = term27.
Proof. exact (@lem2003349 term15 term15). Qed.
Lemma lem2003351 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2003352 : term29 = term15.
Proof. exact (EQ_MP (@lem2003351) (@lem940073)). Qed.
Lemma lem2003353 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003354 : term27 = term5.
Proof. exact (MK_COMB (@lem2003353) (@lem2003352)). Qed.
Lemma lem2003355 : term26 = term5.
Proof. exact (TRANS (@lem2003350) (@lem2003354)). Qed.
Lemma lem2003357 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2003358 : term26 = term27.
Proof. exact (@lem2003357 term15 term15). Qed.
Lemma lem2003359 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2003360 : term29 = term15.
Proof. exact (EQ_MP (@lem2003359) (@lem940073)). Qed.
Lemma lem2003361 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003362 : term27 = term5.
Proof. exact (MK_COMB (@lem2003361) (@lem2003360)). Qed.
Lemma lem2003363 : term26 = term5.
Proof. exact (TRANS (@lem2003358) (@lem2003362)). Qed.
Lemma lem2003364 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2003365 : term281 = term273.
Proof. exact (MK_COMB (@lem2003364) (@lem2003363)). Qed.
Lemma lem2003366 : term418 = term412.
Proof. exact (MK_COMB (@lem2003365) (@lem2003355)). Qed.
Lemma lem2003367 : term412 = term128.
Proof. exact (@lem1367770 term15 term15). Qed.
Lemma lem2003368 : term124 = term125.
Proof. exact (@lem706885). Qed.
Lemma lem2003369 : (term124 = term125) = (term126 = term127).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term125). Qed.
Lemma lem2003370 : term126 = term127.
Proof. exact (EQ_MP (@lem2003369) (@lem2003368)). Qed.
Lemma lem2003371 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003372 : term128 = term129.
Proof. exact (MK_COMB (@lem2003371) (@lem2003370)). Qed.
Lemma lem2003373 : term412 = term129.
Proof. exact (TRANS (@lem2003367) (@lem2003372)). Qed.
Lemma lem2003374 : term418 = term129.
Proof. exact (TRANS (@lem2003366) (@lem2003373)). Qed.
Lemma lem2003375 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2003376 : term419 = term420.
Proof. exact (MK_COMB (@lem2003375) (@lem2003374)). Qed.
Lemma lem2003377 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem2003378 : term421 = term422.
Proof. exact (MK_COMB (@lem2003376) (@lem2003377)). Qed.
Lemma lem2003380 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2003381 : term422 = term137.
Proof. exact (@lem2003380 term127 term15). Qed.
Lemma lem2003382 : term135 = term125.
Proof. exact (@lem996237 term125). Qed.
Lemma lem2003383 : (term135 = term125) = (term136 = term127).
Proof. exact (@lem1007663 term125 (BIT1 0) term125). Qed.
Lemma lem2003384 : term136 = term127.
Proof. exact (EQ_MP (@lem2003383) (@lem2003382)). Qed.
Lemma lem2003385 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003386 : term137 = term129.
Proof. exact (MK_COMB (@lem2003385) (@lem2003384)). Qed.
Lemma lem2003387 : term422 = term129.
Proof. exact (TRANS (@lem2003381) (@lem2003386)). Qed.
Lemma lem2003388 : term421 = term129.
Proof. exact (TRANS (@lem2003378) (@lem2003387)). Qed.
Lemma lem2003390 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2003391 : term26 = term27.
Proof. exact (@lem2003390 term15 term15). Qed.
Lemma lem2003392 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2003393 : term29 = term15.
Proof. exact (EQ_MP (@lem2003392) (@lem940073)). Qed.
Lemma lem2003394 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003395 : term27 = term5.
Proof. exact (MK_COMB (@lem2003394) (@lem2003393)). Qed.
Lemma lem2003396 : term26 = term5.
Proof. exact (TRANS (@lem2003391) (@lem2003395)). Qed.
Lemma lem2003397 : term420 = term420.
Proof. exact (eq_refl term420). Qed.
Lemma lem2003398 : term423 = term422.
Proof. exact (MK_COMB (@lem2003397) (@lem2003396)). Qed.
Lemma lem2003400 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2003401 : term422 = term137.
Proof. exact (@lem2003400 term127 term15). Qed.
Lemma lem2003402 : term135 = term125.
Proof. exact (@lem996237 term125). Qed.
Lemma lem2003403 : (term135 = term125) = (term136 = term127).
Proof. exact (@lem1007663 term125 (BIT1 0) term125). Qed.
Lemma lem2003404 : term136 = term127.
Proof. exact (EQ_MP (@lem2003403) (@lem2003402)). Qed.
Lemma lem2003405 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003406 : term137 = term129.
Proof. exact (MK_COMB (@lem2003405) (@lem2003404)). Qed.
Lemma lem2003407 : term422 = term129.
Proof. exact (TRANS (@lem2003401) (@lem2003406)). Qed.
Lemma lem2003408 : term423 = term129.
Proof. exact (TRANS (@lem2003398) (@lem2003407)). Qed.
Lemma lem2003409 : term129 = term423.
Proof. exact (SYM (@lem2003408)). Qed.
Lemma lem2003410 : term421 = term423.
Proof. exact (TRANS (@lem2003388) (@lem2003409)). Qed.
Lemma lem2003411 : term413 = term424.
Proof. exact (@lem2003347 (@lem2003410)). Qed.
Lemma lem2003412 : term412 = term424.
Proof. exact (TRANS (@lem2003313) (@lem2003411)). Qed.
Lemma lem2003414 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2003415 : term424 = term129.
Proof. exact (@lem2003414 term129). Qed.
Lemma lem2003416 : term412 = term129.
Proof. exact (TRANS (@lem2003412) (@lem2003415)). Qed.
Lemma lem2003417 (x : real) : (term203 x) = (term203 x).
Proof. exact (eq_refl (term203 x)). Qed.
Lemma lem2003418 (x : real) : (term563 x) = (term564 x).
Proof. exact (MK_COMB (@lem2003417 x) (@lem2003416)). Qed.
Lemma lem2003419 (x : real) : (term562 x) = (term564 x).
Proof. exact (TRANS (@lem2003304 x) (@lem2003418 x)). Qed.
Lemma lem2003420 (x : real) : (term561 x) = (term564 x).
Proof. exact (TRANS (@lem2003303 x) (@lem2003419 x)). Qed.
Lemma lem2003425 (x : real) : (term203 x) = (term203 x).
Proof. exact (eq_refl (term203 x)). Qed.
Lemma lem2003426 (x : real) : (term565 x) = (term566 x).
Proof. exact (MK_COMB (@lem2003425 x) (@lem2003420 x)). Qed.
Lemma lem2003427 (x : real) : (term566 x) = (term567 x).
Proof. exact (@lem1982763 (real_abs x) (real_abs x) term129). Qed.
Lemma lem2003428 (x : real) : (term568 x) = (term569 x).
Proof. exact (@lem1982717 (real_abs x)). Qed.
Lemma lem2003430 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2003431 : term5 = term14.
Proof. exact (@lem2003430 term15). Qed.
Lemma lem2003433 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2003434 : term5 = term14.
Proof. exact (@lem2003433 term15). Qed.
Lemma lem2003435 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2003436 : term273 = term274.
Proof. exact (MK_COMB (@lem2003435) (@lem2003434)). Qed.
Lemma lem2003437 : term412 = term413.
Proof. exact (MK_COMB (@lem2003436) (@lem2003431)). Qed.
Lemma lem2003438 : term414.
Proof. exact (@lem1981473 term5 term5 term5 term5 term129 term5). Qed.
Lemma lem2003440 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2003441 : term66 = term73.
Proof. exact (@lem2003440 (NUMERAL 0) term15). Qed.
Lemma lem2003442 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2003443 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2003444 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2003443 h1) (fun h1 : term73 = True => @lem2003442)). Qed.
Lemma lem2003445 : term73 = True.
Proof. exact (EQ_MP (@lem2003444) (@lem2003442)). Qed.
Lemma lem2003446 : term66 = True.
Proof. exact (TRANS (@lem2003441) (@lem2003445)). Qed.
Lemma lem2003447 : True = term66.
Proof. exact (SYM (@lem2003446)). Qed.
Lemma lem2003448 : term66.
Proof. exact (EQ_MP (@lem2003447) (@lem0)). Qed.
Lemma lem2003449 : term415.
Proof. exact (@lem2003438 (@lem2003448)). Qed.
Lemma lem2003451 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2003452 : term66 = term73.
Proof. exact (@lem2003451 (NUMERAL 0) term15). Qed.
Lemma lem2003453 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2003454 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2003455 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2003454 h1) (fun h1 : term73 = True => @lem2003453)). Qed.
Lemma lem2003456 : term73 = True.
Proof. exact (EQ_MP (@lem2003455) (@lem2003453)). Qed.
Lemma lem2003457 : term66 = True.
Proof. exact (TRANS (@lem2003452) (@lem2003456)). Qed.
Lemma lem2003458 : True = term66.
Proof. exact (SYM (@lem2003457)). Qed.
Lemma lem2003459 : term66.
Proof. exact (EQ_MP (@lem2003458) (@lem0)). Qed.
Lemma lem2003460 : term416.
Proof. exact (@lem2003449 (@lem2003459)). Qed.
Lemma lem2003462 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2003463 : term66 = term73.
Proof. exact (@lem2003462 (NUMERAL 0) term15). Qed.
Lemma lem2003464 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2003465 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2003466 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2003465 h1) (fun h1 : term73 = True => @lem2003464)). Qed.
Lemma lem2003467 : term73 = True.
Proof. exact (EQ_MP (@lem2003466) (@lem2003464)). Qed.
Lemma lem2003468 : term66 = True.
Proof. exact (TRANS (@lem2003463) (@lem2003467)). Qed.
Lemma lem2003469 : True = term66.
Proof. exact (SYM (@lem2003468)). Qed.
Lemma lem2003470 : term66.
Proof. exact (EQ_MP (@lem2003469) (@lem0)). Qed.
Lemma lem2003471 : term417.
Proof. exact (@lem2003460 (@lem2003470)). Qed.
Lemma lem2003473 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2003474 : term26 = term27.
Proof. exact (@lem2003473 term15 term15). Qed.
Lemma lem2003475 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2003476 : term29 = term15.
Proof. exact (EQ_MP (@lem2003475) (@lem940073)). Qed.
Lemma lem2003477 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003478 : term27 = term5.
Proof. exact (MK_COMB (@lem2003477) (@lem2003476)). Qed.
Lemma lem2003479 : term26 = term5.
Proof. exact (TRANS (@lem2003474) (@lem2003478)). Qed.
Lemma lem2003481 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2003482 : term26 = term27.
Proof. exact (@lem2003481 term15 term15). Qed.
Lemma lem2003483 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2003484 : term29 = term15.
Proof. exact (EQ_MP (@lem2003483) (@lem940073)). Qed.
Lemma lem2003485 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003486 : term27 = term5.
Proof. exact (MK_COMB (@lem2003485) (@lem2003484)). Qed.
Lemma lem2003487 : term26 = term5.
Proof. exact (TRANS (@lem2003482) (@lem2003486)). Qed.
Lemma lem2003488 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2003489 : term281 = term273.
Proof. exact (MK_COMB (@lem2003488) (@lem2003487)). Qed.
Lemma lem2003490 : term418 = term412.
Proof. exact (MK_COMB (@lem2003489) (@lem2003479)). Qed.
Lemma lem2003491 : term412 = term128.
Proof. exact (@lem1367770 term15 term15). Qed.
Lemma lem2003492 : term124 = term125.
Proof. exact (@lem706885). Qed.
Lemma lem2003493 : (term124 = term125) = (term126 = term127).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term125). Qed.
Lemma lem2003494 : term126 = term127.
Proof. exact (EQ_MP (@lem2003493) (@lem2003492)). Qed.
Lemma lem2003495 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003496 : term128 = term129.
Proof. exact (MK_COMB (@lem2003495) (@lem2003494)). Qed.
Lemma lem2003497 : term412 = term129.
Proof. exact (TRANS (@lem2003491) (@lem2003496)). Qed.
Lemma lem2003498 : term418 = term129.
Proof. exact (TRANS (@lem2003490) (@lem2003497)). Qed.
Lemma lem2003499 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2003500 : term419 = term420.
Proof. exact (MK_COMB (@lem2003499) (@lem2003498)). Qed.
Lemma lem2003501 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem2003502 : term421 = term422.
Proof. exact (MK_COMB (@lem2003500) (@lem2003501)). Qed.
Lemma lem2003504 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2003505 : term422 = term137.
Proof. exact (@lem2003504 term127 term15). Qed.
Lemma lem2003506 : term135 = term125.
Proof. exact (@lem996237 term125). Qed.
Lemma lem2003507 : (term135 = term125) = (term136 = term127).
Proof. exact (@lem1007663 term125 (BIT1 0) term125). Qed.
Lemma lem2003508 : term136 = term127.
Proof. exact (EQ_MP (@lem2003507) (@lem2003506)). Qed.
Lemma lem2003509 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003510 : term137 = term129.
Proof. exact (MK_COMB (@lem2003509) (@lem2003508)). Qed.
Lemma lem2003511 : term422 = term129.
Proof. exact (TRANS (@lem2003505) (@lem2003510)). Qed.
Lemma lem2003512 : term421 = term129.
Proof. exact (TRANS (@lem2003502) (@lem2003511)). Qed.
Lemma lem2003514 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2003515 : term26 = term27.
Proof. exact (@lem2003514 term15 term15). Qed.
Lemma lem2003516 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2003517 : term29 = term15.
Proof. exact (EQ_MP (@lem2003516) (@lem940073)). Qed.
Lemma lem2003518 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003519 : term27 = term5.
Proof. exact (MK_COMB (@lem2003518) (@lem2003517)). Qed.
Lemma lem2003520 : term26 = term5.
Proof. exact (TRANS (@lem2003515) (@lem2003519)). Qed.
Lemma lem2003521 : term420 = term420.
Proof. exact (eq_refl term420). Qed.
Lemma lem2003522 : term423 = term422.
Proof. exact (MK_COMB (@lem2003521) (@lem2003520)). Qed.
Lemma lem2003524 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2003525 : term422 = term137.
Proof. exact (@lem2003524 term127 term15). Qed.
Lemma lem2003526 : term135 = term125.
Proof. exact (@lem996237 term125). Qed.
Lemma lem2003527 : (term135 = term125) = (term136 = term127).
Proof. exact (@lem1007663 term125 (BIT1 0) term125). Qed.
Lemma lem2003528 : term136 = term127.
Proof. exact (EQ_MP (@lem2003527) (@lem2003526)). Qed.
Lemma lem2003529 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003530 : term137 = term129.
Proof. exact (MK_COMB (@lem2003529) (@lem2003528)). Qed.
Lemma lem2003531 : term422 = term129.
Proof. exact (TRANS (@lem2003525) (@lem2003530)). Qed.
Lemma lem2003532 : term423 = term129.
Proof. exact (TRANS (@lem2003522) (@lem2003531)). Qed.
Lemma lem2003533 : term129 = term423.
Proof. exact (SYM (@lem2003532)). Qed.
Lemma lem2003534 : term421 = term423.
Proof. exact (TRANS (@lem2003512) (@lem2003533)). Qed.
Lemma lem2003535 : term413 = term424.
Proof. exact (@lem2003471 (@lem2003534)). Qed.
Lemma lem2003536 : term412 = term424.
Proof. exact (TRANS (@lem2003437) (@lem2003535)). Qed.
Lemma lem2003538 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2003539 : term424 = term129.
Proof. exact (@lem2003538 term129). Qed.
Lemma lem2003540 : term412 = term129.
Proof. exact (TRANS (@lem2003536) (@lem2003539)). Qed.
Lemma lem2003541 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2003542 : term425 = term420.
Proof. exact (MK_COMB (@lem2003541) (@lem2003540)). Qed.
Lemma lem2003543 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem2003544 (x : real) : (term569 x) = (term570 x).
Proof. exact (MK_COMB (@lem2003542) (@lem2003543 x)). Qed.
Lemma lem2003545 (x : real) : (term568 x) = (term570 x).
Proof. exact (TRANS (@lem2003428 x) (@lem2003544 x)). Qed.
Lemma lem2003546 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2003547 (x : real) : (term571 x) = (term572 x).
Proof. exact (MK_COMB (@lem2003546) (@lem2003545 x)). Qed.
Lemma lem2003548 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem2003549 (x : real) : (term567 x) = (term573 x).
Proof. exact (MK_COMB (@lem2003547 x) (@lem2003548)). Qed.
Lemma lem2003550 (x : real) : (term566 x) = (term573 x).
Proof. exact (TRANS (@lem2003427 x) (@lem2003549 x)). Qed.
Lemma lem2003551 (x : real) : (term565 x) = (term573 x).
Proof. exact (TRANS (@lem2003426 x) (@lem2003550 x)). Qed.
Lemma lem2003552 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2003553 (x : real) : (term574 x) = (term575 x).
Proof. exact (MK_COMB (@lem2003552) (@lem2003551 x)). Qed.
Lemma lem2003554 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2003555 (x : real) : (term576 x) = (term577 x).
Proof. exact (MK_COMB (@lem2003553 x) (@lem2003554)). Qed.
Lemma lem2003556 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem2003570 (x : real) : (term10 x) = (term11 x).
Proof. exact (@lem1982781 (real_abs x) term12 term5). Qed.
Lemma lem2003572 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2003573 : term5 = term14.
Proof. exact (@lem2003572 term15). Qed.
Lemma lem2003575 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2003576 : term12 = term18.
Proof. exact (@lem2003575 term15). Qed.
Lemma lem2003577 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2003578 : term19 = term20.
Proof. exact (MK_COMB (@lem2003577) (@lem2003576)). Qed.
Lemma lem2003579 : term21 = term22.
Proof. exact (MK_COMB (@lem2003578) (@lem2003573)). Qed.
Lemma lem2003580 : term22 = term23.
Proof. exact (@lem1981613 term12 term5 term5 term5). Qed.
Lemma lem2003582 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2003583 : term26 = term27.
Proof. exact (@lem2003582 term15 term15). Qed.
Lemma lem2003584 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2003585 : term29 = term15.
Proof. exact (EQ_MP (@lem2003584) (@lem940073)). Qed.
Lemma lem2003586 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003587 : term27 = term5.
Proof. exact (MK_COMB (@lem2003586) (@lem2003585)). Qed.
Lemma lem2003588 : term26 = term5.
Proof. exact (TRANS (@lem2003583) (@lem2003587)). Qed.
Lemma lem2003590 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2003591 : term21 = term32.
Proof. exact (@lem2003590 term15 term15). Qed.
Lemma lem2003592 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2003593 : term29 = term15.
Proof. exact (EQ_MP (@lem2003592) (@lem940073)). Qed.
Lemma lem2003594 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003595 : term27 = term5.
Proof. exact (MK_COMB (@lem2003594) (@lem2003593)). Qed.
Lemma lem2003596 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2003597 : term32 = term12.
Proof. exact (MK_COMB (@lem2003596) (@lem2003595)). Qed.
Lemma lem2003598 : term21 = term12.
Proof. exact (TRANS (@lem2003591) (@lem2003597)). Qed.
Lemma lem2003599 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2003600 : term33 = term34.
Proof. exact (MK_COMB (@lem2003599) (@lem2003598)). Qed.
Lemma lem2003601 : term23 = term18.
Proof. exact (MK_COMB (@lem2003600) (@lem2003588)). Qed.
Lemma lem2003602 : term22 = term18.
Proof. exact (TRANS (@lem2003580) (@lem2003601)). Qed.
Lemma lem2003603 : term21 = term18.
Proof. exact (TRANS (@lem2003579) (@lem2003602)). Qed.
Lemma lem2003605 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2003606 : term18 = term12.
Proof. exact (@lem2003605 term12). Qed.
Lemma lem2003607 : term21 = term12.
Proof. exact (TRANS (@lem2003603) (@lem2003606)). Qed.
Lemma lem2003610 (x : real) : (term36 x) = (term36 x).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem2003611 (x : real) : (term11 x) = (term37 x).
Proof. exact (MK_COMB (@lem2003610 x) (@lem2003607)). Qed.
Lemma lem2003613 (x : real) : (term10 x) = (term37 x).
Proof. exact (TRANS (@lem2003570 x) (@lem2003611 x)). Qed.
Lemma lem2003614 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2003615 (x : real) : (term578 x) = (term327 x).
Proof. exact (MK_COMB (@lem2003614) (@lem2003613 x)). Qed.
Lemma lem2003616 (x : real) : (term579 x) = (term580 x).
Proof. exact (MK_COMB (@lem2003615 x) (@lem2003556)). Qed.
Lemma lem2003617 (x : real) : (term580 x) = (term581 x).
Proof. exact (@lem1982755 (term181 x) term12 term5). Qed.
Lemma lem2003619 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2003620 : term5 = term14.
Proof. exact (@lem2003619 term15). Qed.
Lemma lem2003622 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2003623 : term12 = term18.
Proof. exact (@lem2003622 term15). Qed.
Lemma lem2003624 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2003625 : term47 = term98.
Proof. exact (MK_COMB (@lem2003624) (@lem2003623)). Qed.
Lemma lem2003626 : term99 = term100.
Proof. exact (MK_COMB (@lem2003625) (@lem2003620)). Qed.
Lemma lem2003627 : term101.
Proof. exact (@lem1981473 term12 term5 term5 term5 term2 term5). Qed.
Lemma lem2003629 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2003630 : term66 = term73.
Proof. exact (@lem2003629 (NUMERAL 0) term15). Qed.
Lemma lem2003631 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2003632 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2003633 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2003632 h1) (fun h1 : term73 = True => @lem2003631)). Qed.
Lemma lem2003634 : term73 = True.
Proof. exact (EQ_MP (@lem2003633) (@lem2003631)). Qed.
Lemma lem2003635 : term66 = True.
Proof. exact (TRANS (@lem2003630) (@lem2003634)). Qed.
Lemma lem2003636 : True = term66.
Proof. exact (SYM (@lem2003635)). Qed.
Lemma lem2003637 : term66.
Proof. exact (EQ_MP (@lem2003636) (@lem0)). Qed.
Lemma lem2003638 : term102.
Proof. exact (@lem2003627 (@lem2003637)). Qed.
Lemma lem2003640 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2003641 : term66 = term73.
Proof. exact (@lem2003640 (NUMERAL 0) term15). Qed.
Lemma lem2003642 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2003643 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2003644 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2003643 h1) (fun h1 : term73 = True => @lem2003642)). Qed.
Lemma lem2003645 : term73 = True.
Proof. exact (EQ_MP (@lem2003644) (@lem2003642)). Qed.
Lemma lem2003646 : term66 = True.
Proof. exact (TRANS (@lem2003641) (@lem2003645)). Qed.
Lemma lem2003647 : True = term66.
Proof. exact (SYM (@lem2003646)). Qed.
Lemma lem2003648 : term66.
Proof. exact (EQ_MP (@lem2003647) (@lem0)). Qed.
Lemma lem2003649 : term103.
Proof. exact (@lem2003638 (@lem2003648)). Qed.
Lemma lem2003651 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2003652 : term66 = term73.
Proof. exact (@lem2003651 (NUMERAL 0) term15). Qed.
Lemma lem2003653 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2003654 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2003655 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2003654 h1) (fun h1 : term73 = True => @lem2003653)). Qed.
Lemma lem2003656 : term73 = True.
Proof. exact (EQ_MP (@lem2003655) (@lem2003653)). Qed.
Lemma lem2003657 : term66 = True.
Proof. exact (TRANS (@lem2003652) (@lem2003656)). Qed.
Lemma lem2003658 : True = term66.
Proof. exact (SYM (@lem2003657)). Qed.
Lemma lem2003659 : term66.
Proof. exact (EQ_MP (@lem2003658) (@lem0)). Qed.
Lemma lem2003660 : term104.
Proof. exact (@lem2003649 (@lem2003659)). Qed.
Lemma lem2003662 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2003663 : term26 = term27.
Proof. exact (@lem2003662 term15 term15). Qed.
Lemma lem2003664 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2003665 : term29 = term15.
Proof. exact (EQ_MP (@lem2003664) (@lem940073)). Qed.
Lemma lem2003666 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003667 : term27 = term5.
Proof. exact (MK_COMB (@lem2003666) (@lem2003665)). Qed.
Lemma lem2003668 : term26 = term5.
Proof. exact (TRANS (@lem2003663) (@lem2003667)). Qed.
Lemma lem2003670 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2003671 : term21 = term32.
Proof. exact (@lem2003670 term15 term15). Qed.
Lemma lem2003672 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2003673 : term29 = term15.
Proof. exact (EQ_MP (@lem2003672) (@lem940073)). Qed.
Lemma lem2003674 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003675 : term27 = term5.
Proof. exact (MK_COMB (@lem2003674) (@lem2003673)). Qed.
Lemma lem2003676 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2003677 : term32 = term12.
Proof. exact (MK_COMB (@lem2003676) (@lem2003675)). Qed.
Lemma lem2003678 : term21 = term12.
Proof. exact (TRANS (@lem2003671) (@lem2003677)). Qed.
Lemma lem2003679 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2003680 : term105 = term47.
Proof. exact (MK_COMB (@lem2003679) (@lem2003678)). Qed.
Lemma lem2003681 : term106 = term99.
Proof. exact (MK_COMB (@lem2003680) (@lem2003668)). Qed.
Lemma lem2003683 (m : nat) : (term107 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2003684 : term99 = term2.
Proof. exact (@lem2003683 term15). Qed.
Lemma lem2003685 : term106 = term2.
Proof. exact (TRANS (@lem2003681) (@lem2003684)). Qed.
Lemma lem2003686 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2003687 : term108 = term109.
Proof. exact (MK_COMB (@lem2003686) (@lem2003685)). Qed.
Lemma lem2003688 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem2003689 : term110 = term78.
Proof. exact (MK_COMB (@lem2003687) (@lem2003688)). Qed.
Lemma lem2003691 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2003692 : term78 = term2.
Proof. exact (@lem2003691 term15). Qed.
Lemma lem2003693 : term110 = term2.
Proof. exact (TRANS (@lem2003689) (@lem2003692)). Qed.
Lemma lem2003695 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2003696 : term26 = term27.
Proof. exact (@lem2003695 term15 term15). Qed.
Lemma lem2003697 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2003698 : term29 = term15.
Proof. exact (EQ_MP (@lem2003697) (@lem940073)). Qed.
Lemma lem2003699 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003700 : term27 = term5.
Proof. exact (MK_COMB (@lem2003699) (@lem2003698)). Qed.
Lemma lem2003701 : term26 = term5.
Proof. exact (TRANS (@lem2003696) (@lem2003700)). Qed.
Lemma lem2003702 : term109 = term109.
Proof. exact (eq_refl term109). Qed.
Lemma lem2003703 : term111 = term78.
Proof. exact (MK_COMB (@lem2003702) (@lem2003701)). Qed.
Lemma lem2003705 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2003706 : term78 = term2.
Proof. exact (@lem2003705 term15). Qed.
Lemma lem2003707 : term111 = term2.
Proof. exact (TRANS (@lem2003703) (@lem2003706)). Qed.
Lemma lem2003708 : term2 = term111.
Proof. exact (SYM (@lem2003707)). Qed.
Lemma lem2003709 : term110 = term111.
Proof. exact (TRANS (@lem2003693) (@lem2003708)). Qed.
Lemma lem2003710 : term100 = term67.
Proof. exact (@lem2003660 (@lem2003709)). Qed.
Lemma lem2003711 : term99 = term67.
Proof. exact (TRANS (@lem2003626) (@lem2003710)). Qed.
Lemma lem2003713 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2003714 : term67 = term2.
Proof. exact (@lem2003713 term2). Qed.
Lemma lem2003715 : term99 = term2.
Proof. exact (TRANS (@lem2003711) (@lem2003714)). Qed.
Lemma lem2003716 (x : real) : (term36 x) = (term36 x).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem2003717 (x : real) : (term581 x) = (term582 x).
Proof. exact (MK_COMB (@lem2003716 x) (@lem2003715)). Qed.
Lemma lem2003718 (x : real) : (term580 x) = (term582 x).
Proof. exact (TRANS (@lem2003617 x) (@lem2003717 x)). Qed.
Lemma lem2003719 (x : real) : (term582 x) = (term181 x).
Proof. exact (@lem1982723 (term181 x)). Qed.
Lemma lem2003720 (x : real) : (term580 x) = (term181 x).
Proof. exact (TRANS (@lem2003718 x) (@lem2003719 x)). Qed.
Lemma lem2003721 (x : real) : (term579 x) = (term181 x).
Proof. exact (TRANS (@lem2003616 x) (@lem2003720 x)). Qed.
Lemma lem2003726 (x : real) : (term203 x) = (term203 x).
Proof. exact (eq_refl (term203 x)). Qed.
Lemma lem2003727 (x : real) : (term583 x) = (term584 x).
Proof. exact (MK_COMB (@lem2003726 x) (@lem2003721 x)). Qed.
Lemma lem2003728 (x : real) : (term584 x) = (term585 x).
Proof. exact (@lem1982715 term12 (real_abs x)). Qed.
Lemma lem2003730 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2003731 : term5 = term14.
Proof. exact (@lem2003730 term15). Qed.
Lemma lem2003733 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2003734 : term12 = term18.
Proof. exact (@lem2003733 term15). Qed.
Lemma lem2003735 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2003736 : term47 = term98.
Proof. exact (MK_COMB (@lem2003735) (@lem2003734)). Qed.
Lemma lem2003737 : term99 = term100.
Proof. exact (MK_COMB (@lem2003736) (@lem2003731)). Qed.
Lemma lem2003738 : term101.
Proof. exact (@lem1981473 term12 term5 term5 term5 term2 term5). Qed.
Lemma lem2003740 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2003741 : term66 = term73.
Proof. exact (@lem2003740 (NUMERAL 0) term15). Qed.
Lemma lem2003742 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2003743 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2003744 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2003743 h1) (fun h1 : term73 = True => @lem2003742)). Qed.
Lemma lem2003745 : term73 = True.
Proof. exact (EQ_MP (@lem2003744) (@lem2003742)). Qed.
Lemma lem2003746 : term66 = True.
Proof. exact (TRANS (@lem2003741) (@lem2003745)). Qed.
Lemma lem2003747 : True = term66.
Proof. exact (SYM (@lem2003746)). Qed.
Lemma lem2003748 : term66.
Proof. exact (EQ_MP (@lem2003747) (@lem0)). Qed.
Lemma lem2003749 : term102.
Proof. exact (@lem2003738 (@lem2003748)). Qed.
Lemma lem2003751 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2003752 : term66 = term73.
Proof. exact (@lem2003751 (NUMERAL 0) term15). Qed.
Lemma lem2003753 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2003754 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2003755 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2003754 h1) (fun h1 : term73 = True => @lem2003753)). Qed.
Lemma lem2003756 : term73 = True.
Proof. exact (EQ_MP (@lem2003755) (@lem2003753)). Qed.
Lemma lem2003757 : term66 = True.
Proof. exact (TRANS (@lem2003752) (@lem2003756)). Qed.
Lemma lem2003758 : True = term66.
Proof. exact (SYM (@lem2003757)). Qed.
Lemma lem2003759 : term66.
Proof. exact (EQ_MP (@lem2003758) (@lem0)). Qed.
Lemma lem2003760 : term103.
Proof. exact (@lem2003749 (@lem2003759)). Qed.
Lemma lem2003762 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2003763 : term66 = term73.
Proof. exact (@lem2003762 (NUMERAL 0) term15). Qed.
Lemma lem2003764 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2003765 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2003766 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2003765 h1) (fun h1 : term73 = True => @lem2003764)). Qed.
Lemma lem2003767 : term73 = True.
Proof. exact (EQ_MP (@lem2003766) (@lem2003764)). Qed.
Lemma lem2003768 : term66 = True.
Proof. exact (TRANS (@lem2003763) (@lem2003767)). Qed.
Lemma lem2003769 : True = term66.
Proof. exact (SYM (@lem2003768)). Qed.
Lemma lem2003770 : term66.
Proof. exact (EQ_MP (@lem2003769) (@lem0)). Qed.
Lemma lem2003771 : term104.
Proof. exact (@lem2003760 (@lem2003770)). Qed.
Lemma lem2003773 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2003774 : term26 = term27.
Proof. exact (@lem2003773 term15 term15). Qed.
Lemma lem2003775 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2003776 : term29 = term15.
Proof. exact (EQ_MP (@lem2003775) (@lem940073)). Qed.
Lemma lem2003777 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003778 : term27 = term5.
Proof. exact (MK_COMB (@lem2003777) (@lem2003776)). Qed.
Lemma lem2003779 : term26 = term5.
Proof. exact (TRANS (@lem2003774) (@lem2003778)). Qed.
Lemma lem2003781 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2003782 : term21 = term32.
Proof. exact (@lem2003781 term15 term15). Qed.
Lemma lem2003783 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2003784 : term29 = term15.
Proof. exact (EQ_MP (@lem2003783) (@lem940073)). Qed.
Lemma lem2003785 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003786 : term27 = term5.
Proof. exact (MK_COMB (@lem2003785) (@lem2003784)). Qed.
Lemma lem2003787 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2003788 : term32 = term12.
Proof. exact (MK_COMB (@lem2003787) (@lem2003786)). Qed.
Lemma lem2003789 : term21 = term12.
Proof. exact (TRANS (@lem2003782) (@lem2003788)). Qed.
Lemma lem2003790 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2003791 : term105 = term47.
Proof. exact (MK_COMB (@lem2003790) (@lem2003789)). Qed.
Lemma lem2003792 : term106 = term99.
Proof. exact (MK_COMB (@lem2003791) (@lem2003779)). Qed.
Lemma lem2003794 (m : nat) : (term107 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2003795 : term99 = term2.
Proof. exact (@lem2003794 term15). Qed.
Lemma lem2003796 : term106 = term2.
Proof. exact (TRANS (@lem2003792) (@lem2003795)). Qed.
Lemma lem2003797 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2003798 : term108 = term109.
Proof. exact (MK_COMB (@lem2003797) (@lem2003796)). Qed.
Lemma lem2003799 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem2003800 : term110 = term78.
Proof. exact (MK_COMB (@lem2003798) (@lem2003799)). Qed.
Lemma lem2003802 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2003803 : term78 = term2.
Proof. exact (@lem2003802 term15). Qed.
Lemma lem2003804 : term110 = term2.
Proof. exact (TRANS (@lem2003800) (@lem2003803)). Qed.
Lemma lem2003806 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2003807 : term26 = term27.
Proof. exact (@lem2003806 term15 term15). Qed.
Lemma lem2003808 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2003809 : term29 = term15.
Proof. exact (EQ_MP (@lem2003808) (@lem940073)). Qed.
Lemma lem2003810 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003811 : term27 = term5.
Proof. exact (MK_COMB (@lem2003810) (@lem2003809)). Qed.
Lemma lem2003812 : term26 = term5.
Proof. exact (TRANS (@lem2003807) (@lem2003811)). Qed.
Lemma lem2003813 : term109 = term109.
Proof. exact (eq_refl term109). Qed.
Lemma lem2003814 : term111 = term78.
Proof. exact (MK_COMB (@lem2003813) (@lem2003812)). Qed.
Lemma lem2003816 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2003817 : term78 = term2.
Proof. exact (@lem2003816 term15). Qed.
Lemma lem2003818 : term111 = term2.
Proof. exact (TRANS (@lem2003814) (@lem2003817)). Qed.
Lemma lem2003819 : term2 = term111.
Proof. exact (SYM (@lem2003818)). Qed.
Lemma lem2003820 : term110 = term111.
Proof. exact (TRANS (@lem2003804) (@lem2003819)). Qed.
Lemma lem2003821 : term100 = term67.
Proof. exact (@lem2003771 (@lem2003820)). Qed.
Lemma lem2003822 : term99 = term67.
Proof. exact (TRANS (@lem2003737) (@lem2003821)). Qed.
Lemma lem2003824 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2003825 : term67 = term2.
Proof. exact (@lem2003824 term2). Qed.
Lemma lem2003826 : term99 = term2.
Proof. exact (TRANS (@lem2003822) (@lem2003825)). Qed.
Lemma lem2003827 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2003828 : term112 = term109.
Proof. exact (MK_COMB (@lem2003827) (@lem2003826)). Qed.
Lemma lem2003829 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem2003830 (x : real) : (term585 x) = (term586 x).
Proof. exact (MK_COMB (@lem2003828) (@lem2003829 x)). Qed.
Lemma lem2003831 (x : real) : (term584 x) = (term586 x).
Proof. exact (TRANS (@lem2003728 x) (@lem2003830 x)). Qed.
Lemma lem2003832 (x : real) : (term586 x) = term2.
Proof. exact (@lem1982719 (real_abs x)). Qed.
Lemma lem2003833 (x : real) : (term584 x) = term2.
Proof. exact (TRANS (@lem2003831 x) (@lem2003832 x)). Qed.
Lemma lem2003834 (x : real) : (term583 x) = term2.
Proof. exact (TRANS (@lem2003727 x) (@lem2003833 x)). Qed.
Lemma lem2003835 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2003836 (x : real) : (term587 x) = term485.
Proof. exact (MK_COMB (@lem2003835) (@lem2003834 x)). Qed.
Lemma lem2003837 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2003838 (x : real) : (term588 x) = term486.
Proof. exact (MK_COMB (@lem2003836 x) (@lem2003837)). Qed.
Lemma lem2003839 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2003840 (x : real) : (term589 x) = term499.
Proof. exact (MK_COMB (@lem2003839) (@lem2003838 x)). Qed.
Lemma lem2003841 (x : real) : (term558 x) = (term590 x).
Proof. exact (MK_COMB (@lem2003840 x) (@lem2003555 x)). Qed.
Lemma lem2003842 (x : real) : (term209 x) = (term590 x).
Proof. exact (TRANS (@lem2003284 x) (@lem2003841 x)). Qed.
Lemma lem2003843 (x : real) : (term591 x) = (term590 x).
Proof. exact (eq_refl (term591 x)). Qed.
Lemma lem2003844 (x : real) : (term590 x) = (term591 x).
Proof. exact (SYM (@lem2003843 x)). Qed.
Lemma lem2003845 (x : real) : (term591 x) = (term592 x).
Proof. exact (@lem1482981 term593 x). Qed.
Lemma lem2003846 (x : real) : (term590 x) = (term592 x).
Proof. exact (TRANS (@lem2003844 x) (@lem2003845 x)). Qed.
Lemma lem2003847 (x : real) : (term594 x) = (term595 x).
Proof. exact (eq_refl (term594 x)). Qed.
Lemma lem2003848 (x : real) : (term450 x) = (term450 x).
Proof. exact (eq_refl (term450 x)). Qed.
Lemma lem2003849 (x : real) : (term596 x) = (term597 x).
Proof. exact (MK_COMB (@lem2003848 x) (@lem2003847 x)). Qed.
Lemma lem2003850 (x : real) : (term598 x) = (term599 x).
Proof. exact (eq_refl (term598 x)). Qed.
Lemma lem2003851 (x : real) : (term455 x) = (term455 x).
Proof. exact (eq_refl (term455 x)). Qed.
Lemma lem2003852 (x : real) : (term600 x) = (term601 x).
Proof. exact (MK_COMB (@lem2003851 x) (@lem2003850 x)). Qed.
Lemma lem2003853 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2003854 (x : real) : (term602 x) = (term603 x).
Proof. exact (MK_COMB (@lem2003853) (@lem2003852 x)). Qed.
Lemma lem2003855 (x : real) : (term592 x) = (term604 x).
Proof. exact (MK_COMB (@lem2003854 x) (@lem2003849 x)). Qed.
Lemma lem2003856 (x : real) : (term605 x) = (term605 x).
Proof. exact (eq_refl (term605 x)). Qed.
Lemma lem2003857 (x : real) : ((term590 x) = (term592 x)) = ((term590 x) = (term604 x)).
Proof. exact (MK_COMB (@lem2003856 x) (@lem2003855 x)). Qed.
Lemma lem2003858 (x : real) : (term590 x) = (term604 x).
Proof. exact (EQ_MP (@lem2003857 x) (@lem2003846 x)). Qed.
Lemma lem2003859 : term486 = term606.
Proof. exact (@lem1988289 term2 term2). Qed.
Lemma lem2003865 : term481 = term482.
Proof. exact (@lem1982792 term2 term2). Qed.
Lemma lem2003867 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2003868 : term2 = term67.
Proof. exact (@lem2003867 (NUMERAL 0)). Qed.
Lemma lem2003870 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2003871 : term12 = term18.
Proof. exact (@lem2003870 term15). Qed.
Lemma lem2003872 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2003873 : term19 = term20.
Proof. exact (MK_COMB (@lem2003872) (@lem2003871)). Qed.
Lemma lem2003874 : term258 = term259.
Proof. exact (MK_COMB (@lem2003873) (@lem2003868)). Qed.
Lemma lem2003875 : term259 = term260.
Proof. exact (@lem1981613 term12 term2 term5 term5). Qed.
Lemma lem2003877 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2003878 : term26 = term27.
Proof. exact (@lem2003877 term15 term15). Qed.
Lemma lem2003879 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2003880 : term29 = term15.
Proof. exact (EQ_MP (@lem2003879) (@lem940073)). Qed.
Lemma lem2003881 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003882 : term27 = term5.
Proof. exact (MK_COMB (@lem2003881) (@lem2003880)). Qed.
Lemma lem2003883 : term26 = term5.
Proof. exact (TRANS (@lem2003878) (@lem2003882)). Qed.
Lemma lem2003885 (x : nat) : (term261 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2003886 : term258 = term2.
Proof. exact (@lem2003885 term15). Qed.
Lemma lem2003887 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2003888 : term262 = term263.
Proof. exact (MK_COMB (@lem2003887) (@lem2003886)). Qed.
Lemma lem2003889 : term260 = term67.
Proof. exact (MK_COMB (@lem2003888) (@lem2003883)). Qed.
Lemma lem2003890 : term259 = term67.
Proof. exact (TRANS (@lem2003875) (@lem2003889)). Qed.
Lemma lem2003891 : term258 = term67.
Proof. exact (TRANS (@lem2003874) (@lem2003890)). Qed.
Lemma lem2003893 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2003894 : term67 = term2.
Proof. exact (@lem2003893 term2). Qed.
Lemma lem2003895 : term258 = term2.
Proof. exact (TRANS (@lem2003891) (@lem2003894)). Qed.
Lemma lem2003896 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2003897 : term482 = term483.
Proof. exact (MK_COMB (@lem2003896) (@lem2003895)). Qed.
Lemma lem2003898 : term483 = term2.
Proof. exact (@lem1982721 term2). Qed.
Lemma lem2003899 : term482 = term2.
Proof. exact (TRANS (@lem2003897) (@lem2003898)). Qed.
Lemma lem2003901 : term481 = term2.
Proof. exact (TRANS (@lem2003865) (@lem2003899)). Qed.
Lemma lem2003902 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2003903 : term607 = term485.
Proof. exact (MK_COMB (@lem2003902) (@lem2003901)). Qed.
Lemma lem2003904 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2003905 : term606 = term486.
Proof. exact (MK_COMB (@lem2003903) (@lem2003904)). Qed.
Lemma lem2003906 : term486 = term486.
Proof. exact (TRANS (@lem2003859) (@lem2003905)). Qed.
Lemma lem2003907 (x : real) : (term608 x) = (term609 x).
Proof. exact (@lem1988289 (term610 x) term2). Qed.
Lemma lem2003925 (x : real) : (term611 x) = (term612 x).
Proof. exact (@lem1982792 (term610 x) term2). Qed.
Lemma lem2003927 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2003928 : term2 = term67.
Proof. exact (@lem2003927 (NUMERAL 0)). Qed.
Lemma lem2003930 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2003931 : term12 = term18.
Proof. exact (@lem2003930 term15). Qed.
Lemma lem2003932 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2003933 : term19 = term20.
Proof. exact (MK_COMB (@lem2003932) (@lem2003931)). Qed.
Lemma lem2003934 : term258 = term259.
Proof. exact (MK_COMB (@lem2003933) (@lem2003928)). Qed.
Lemma lem2003935 : term259 = term260.
Proof. exact (@lem1981613 term12 term2 term5 term5). Qed.
Lemma lem2003937 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2003938 : term26 = term27.
Proof. exact (@lem2003937 term15 term15). Qed.
Lemma lem2003939 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2003940 : term29 = term15.
Proof. exact (EQ_MP (@lem2003939) (@lem940073)). Qed.
Lemma lem2003941 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2003942 : term27 = term5.
Proof. exact (MK_COMB (@lem2003941) (@lem2003940)). Qed.
Lemma lem2003943 : term26 = term5.
Proof. exact (TRANS (@lem2003938) (@lem2003942)). Qed.
Lemma lem2003945 (x : nat) : (term261 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2003946 : term258 = term2.
Proof. exact (@lem2003945 term15). Qed.
Lemma lem2003947 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2003948 : term262 = term263.
Proof. exact (MK_COMB (@lem2003947) (@lem2003946)). Qed.
Lemma lem2003949 : term260 = term67.
Proof. exact (MK_COMB (@lem2003948) (@lem2003943)). Qed.
Lemma lem2003950 : term259 = term67.
Proof. exact (TRANS (@lem2003935) (@lem2003949)). Qed.
Lemma lem2003951 : term258 = term67.
Proof. exact (TRANS (@lem2003934) (@lem2003950)). Qed.
Lemma lem2003953 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2003954 : term67 = term2.
Proof. exact (@lem2003953 term2). Qed.
Lemma lem2003955 : term258 = term2.
Proof. exact (TRANS (@lem2003951) (@lem2003954)). Qed.
Lemma lem2003956 (x : real) : (term613 x) = (term613 x).
Proof. exact (eq_refl (term613 x)). Qed.
Lemma lem2003957 (x : real) : (term612 x) = (term614 x).
Proof. exact (MK_COMB (@lem2003956 x) (@lem2003955)). Qed.
Lemma lem2003958 (x : real) : (term614 x) = (term610 x).
Proof. exact (@lem1982723 (term610 x)). Qed.
Lemma lem2003959 (x : real) : (term612 x) = (term610 x).
Proof. exact (TRANS (@lem2003957 x) (@lem2003958 x)). Qed.
Lemma lem2003961 (x : real) : (term611 x) = (term610 x).
Proof. exact (TRANS (@lem2003925 x) (@lem2003959 x)). Qed.
Lemma lem2003962 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2003963 (x : real) : (term615 x) = (term616 x).
Proof. exact (MK_COMB (@lem2003962) (@lem2003961 x)). Qed.
Lemma lem2003964 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2003965 (x : real) : (term609 x) = (term608 x).
Proof. exact (MK_COMB (@lem2003963 x) (@lem2003964)). Qed.
Lemma lem2003966 (x : real) : (term608 x) = (term608 x).
Proof. exact (TRANS (@lem2003907 x) (@lem2003965 x)). Qed.
Lemma lem2003967 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2003968 : term499 = term499.
Proof. exact (MK_COMB (@lem2003967) (@lem2003906)). Qed.
Lemma lem2003969 (x : real) : (term599 x) = (term599 x).
Proof. exact (MK_COMB (@lem2003968) (@lem2003966 x)). Qed.
Lemma lem2003970 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2003971 (x : real) : (term455 x) = (term455 x).
Proof. exact (MK_COMB (@lem2003970) (@lem2002416 x)). Qed.
Lemma lem2003972 (x : real) : (term601 x) = (term601 x).
Proof. exact (MK_COMB (@lem2003971 x) (@lem2003969 x)). Qed.
Lemma lem2003973 (x : real) : (term617 x) = (term618 x).
Proof. exact (@lem1988289 (term619 x) term2). Qed.
Lemma lem2003974 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2003975 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem2003982 (x : real) : (real_neg x) = (term57 x).
Proof. exact (@lem1982785 x). Qed.
Lemma lem2003985 : term420 = term420.
Proof. exact (eq_refl term420). Qed.
Lemma lem2003986 (x : real) : (term620 x) = (term621 x).
Proof. exact (MK_COMB (@lem2003985) (@lem2003982 x)). Qed.
Lemma lem2003987 (x : real) : (term621 x) = (term622 x).
Proof. exact (@lem1982749 term129 term12 x). Qed.
Lemma lem2003989 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2003990 : term12 = term18.
Proof. exact (@lem2003989 term15). Qed.
Lemma lem2003992 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2003993 : term129 = term424.
Proof. exact (@lem2003992 term127). Qed.
Lemma lem2003994 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2003995 : term420 = term623.
Proof. exact (MK_COMB (@lem2003994) (@lem2003993)). Qed.
Lemma lem2003996 : term624 = term625.
Proof. exact (MK_COMB (@lem2003995) (@lem2003990)). Qed.
Lemma lem2003997 : term625 = term626.
Proof. exact (@lem1981613 term129 term12 term5 term5). Qed.
Lemma lem2003999 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2004000 : term26 = term27.
Proof. exact (@lem2003999 term15 term15). Qed.
Lemma lem2004001 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2004002 : term29 = term15.
Proof. exact (EQ_MP (@lem2004001) (@lem940073)). Qed.
Lemma lem2004003 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2004004 : term27 = term5.
Proof. exact (MK_COMB (@lem2004003) (@lem2004002)). Qed.
Lemma lem2004005 : term26 = term5.
Proof. exact (TRANS (@lem2004000) (@lem2004004)). Qed.
Lemma lem2004007 (m : nat) (n : nat) : (term627 m n) = (term31 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem2004008 : term624 = term134.
Proof. exact (@lem2004007 term127 term15). Qed.
Lemma lem2004009 : term135 = term125.
Proof. exact (@lem996237 term125). Qed.
Lemma lem2004010 : (term135 = term125) = (term136 = term127).
Proof. exact (@lem1007663 term125 (BIT1 0) term125). Qed.
Lemma lem2004011 : term136 = term127.
Proof. exact (EQ_MP (@lem2004010) (@lem2004009)). Qed.
Lemma lem2004012 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2004013 : term137 = term129.
Proof. exact (MK_COMB (@lem2004012) (@lem2004011)). Qed.
Lemma lem2004014 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2004015 : term134 = term118.
Proof. exact (MK_COMB (@lem2004014) (@lem2004013)). Qed.
Lemma lem2004016 : term624 = term118.
Proof. exact (TRANS (@lem2004008) (@lem2004015)). Qed.
Lemma lem2004017 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2004018 : term628 = term629.
Proof. exact (MK_COMB (@lem2004017) (@lem2004016)). Qed.
Lemma lem2004019 : term626 = term139.
Proof. exact (MK_COMB (@lem2004018) (@lem2004005)). Qed.
Lemma lem2004020 : term625 = term139.
Proof. exact (TRANS (@lem2003997) (@lem2004019)). Qed.
Lemma lem2004021 : term624 = term139.
Proof. exact (TRANS (@lem2003996) (@lem2004020)). Qed.
Lemma lem2004023 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2004024 : term139 = term118.
Proof. exact (@lem2004023 term118). Qed.
Lemma lem2004025 : term624 = term118.
Proof. exact (TRANS (@lem2004021) (@lem2004024)). Qed.
Lemma lem2004026 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2004027 : term630 = term131.
Proof. exact (MK_COMB (@lem2004026) (@lem2004025)). Qed.
Lemma lem2004028 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2004029 (x : real) : (term622 x) = (term395 x).
Proof. exact (MK_COMB (@lem2004027) (@lem2004028 x)). Qed.
Lemma lem2004030 (x : real) : (term621 x) = (term395 x).
Proof. exact (TRANS (@lem2003987 x) (@lem2004029 x)). Qed.
Lemma lem2004031 (x : real) : (term620 x) = (term395 x).
Proof. exact (TRANS (@lem2003986 x) (@lem2004030 x)). Qed.
Lemma lem2004032 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2004033 (x : real) : (term631 x) = (term397 x).
Proof. exact (MK_COMB (@lem2004032) (@lem2004031 x)). Qed.
Lemma lem2004036 (x : real) : (term619 x) = (term632 x).
Proof. exact (MK_COMB (@lem2004033 x) (@lem2003975)). Qed.
Lemma lem2004037 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2004038 (x : real) : (term633 x) = (term634 x).
Proof. exact (MK_COMB (@lem2004037) (@lem2004036 x)). Qed.
Lemma lem2004039 (x : real) : (term635 x) = (term636 x).
Proof. exact (MK_COMB (@lem2004038 x) (@lem2003974)). Qed.
Lemma lem2004040 (x : real) : (term636 x) = (term637 x).
Proof. exact (@lem1982792 (term632 x) term2). Qed.
Lemma lem2004042 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2004043 : term2 = term67.
Proof. exact (@lem2004042 (NUMERAL 0)). Qed.
Lemma lem2004045 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2004046 : term12 = term18.
Proof. exact (@lem2004045 term15). Qed.
Lemma lem2004047 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2004048 : term19 = term20.
Proof. exact (MK_COMB (@lem2004047) (@lem2004046)). Qed.
Lemma lem2004049 : term258 = term259.
Proof. exact (MK_COMB (@lem2004048) (@lem2004043)). Qed.
Lemma lem2004050 : term259 = term260.
Proof. exact (@lem1981613 term12 term2 term5 term5). Qed.
Lemma lem2004052 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2004053 : term26 = term27.
Proof. exact (@lem2004052 term15 term15). Qed.
Lemma lem2004054 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2004055 : term29 = term15.
Proof. exact (EQ_MP (@lem2004054) (@lem940073)). Qed.
Lemma lem2004056 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2004057 : term27 = term5.
Proof. exact (MK_COMB (@lem2004056) (@lem2004055)). Qed.
Lemma lem2004058 : term26 = term5.
Proof. exact (TRANS (@lem2004053) (@lem2004057)). Qed.
Lemma lem2004060 (x : nat) : (term261 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2004061 : term258 = term2.
Proof. exact (@lem2004060 term15). Qed.
Lemma lem2004062 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2004063 : term262 = term263.
Proof. exact (MK_COMB (@lem2004062) (@lem2004061)). Qed.
Lemma lem2004064 : term260 = term67.
Proof. exact (MK_COMB (@lem2004063) (@lem2004058)). Qed.
Lemma lem2004065 : term259 = term67.
Proof. exact (TRANS (@lem2004050) (@lem2004064)). Qed.
Lemma lem2004066 : term258 = term67.
Proof. exact (TRANS (@lem2004049) (@lem2004065)). Qed.
Lemma lem2004068 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2004069 : term67 = term2.
Proof. exact (@lem2004068 term2). Qed.
Lemma lem2004070 : term258 = term2.
Proof. exact (TRANS (@lem2004066) (@lem2004069)). Qed.
Lemma lem2004071 (x : real) : (term638 x) = (term638 x).
Proof. exact (eq_refl (term638 x)). Qed.
Lemma lem2004072 (x : real) : (term637 x) = (term639 x).
Proof. exact (MK_COMB (@lem2004071 x) (@lem2004070)). Qed.
Lemma lem2004073 (x : real) : (term639 x) = (term632 x).
Proof. exact (@lem1982723 (term632 x)). Qed.
Lemma lem2004074 (x : real) : (term637 x) = (term632 x).
Proof. exact (TRANS (@lem2004072 x) (@lem2004073 x)). Qed.
Lemma lem2004075 (x : real) : (term636 x) = (term632 x).
Proof. exact (TRANS (@lem2004040 x) (@lem2004074 x)). Qed.
Lemma lem2004076 (x : real) : (term635 x) = (term632 x).
Proof. exact (TRANS (@lem2004039 x) (@lem2004075 x)). Qed.
Lemma lem2004077 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2004078 (x : real) : (term640 x) = (term641 x).
Proof. exact (MK_COMB (@lem2004077) (@lem2004076 x)). Qed.
Lemma lem2004079 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2004080 (x : real) : (term618 x) = (term642 x).
Proof. exact (MK_COMB (@lem2004078 x) (@lem2004079)). Qed.
Lemma lem2004081 (x : real) : (term617 x) = (term642 x).
Proof. exact (TRANS (@lem2003973 x) (@lem2004080 x)). Qed.
Lemma lem2004082 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2004083 : term499 = term499.
Proof. exact (MK_COMB (@lem2004082) (@lem2003906)). Qed.
Lemma lem2004084 (x : real) : (term595 x) = (term643 x).
Proof. exact (MK_COMB (@lem2004083) (@lem2004081 x)). Qed.
Lemma lem2004085 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2004086 (x : real) : (term450 x) = (term552 x).
Proof. exact (MK_COMB (@lem2004085) (@lem2002834 x)). Qed.
Lemma lem2004087 (x : real) : (term597 x) = (term644 x).
Proof. exact (MK_COMB (@lem2004086 x) (@lem2004084 x)). Qed.
Lemma lem2004088 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2004089 (x : real) : (term603 x) = (term603 x).
Proof. exact (MK_COMB (@lem2004088) (@lem2003972 x)). Qed.
Lemma lem2004090 (x : real) : (term604 x) = (term645 x).
Proof. exact (MK_COMB (@lem2004089 x) (@lem2004087 x)). Qed.
Lemma lem2004101 (x : real) : (term590 x) = (term645 x).
Proof. exact (TRANS (@lem2003858 x) (@lem2004090 x)). Qed.
Lemma lem2004102 (x : real) : (term209 x) = (term645 x).
Proof. exact (TRANS (@lem2003842 x) (@lem2004101 x)). Qed.
Lemma lem2004103 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2004104 (x : real) : (term215 x) = (term646 x).
Proof. exact (MK_COMB (@lem2004103) (@lem2003281 x)). Qed.
Lemma lem2004105 (x : real) : (term216 x) = (term647 x).
Proof. exact (MK_COMB (@lem2004104 x) (@lem2004102 x)). Qed.
Lemma lem2004106 (x : real) (h1 : term647 x) : term647 x.
Proof. exact (h1). Qed.
Lemma lem2004107 (x : real) (h1 : term557 x) : term557 x.
Proof. exact (h1). Qed.
Lemma lem2004108 (x : real) (h1 : term555 x) : term555 x.
Proof. exact (h1). Qed.
Lemma lem2004109 (x : real) (h1 : term504 x) : term504 x.
Proof. exact (h1). Qed.
Lemma lem2004110 (x : real) (h1 : term504 x) : term503 x.
Proof. exact (proj2 (@lem2004109 x h1)). Qed.
Lemma lem2004112 (x : real) (h1 : term504 x) : term501 x.
Proof. exact (proj2 (@lem2004110 x h1)). Qed.
Lemma lem2004115 (x : real) (h1 : term504 x) : term486.
Proof. exact (proj1 (@lem2004112 x h1)). Qed.
Lemma lem2004117 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2004118 : term486 = term648.
Proof. exact (@lem2004117 term2 term2). Qed.
Lemma lem2004120 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2004121 : term2 = term67.
Proof. exact (@lem2004120 (NUMERAL 0)). Qed.
Lemma lem2004123 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2004124 : term2 = term67.
Proof. exact (@lem2004123 (NUMERAL 0)). Qed.
Lemma lem2004125 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2004126 : term68 = term69.
Proof. exact (MK_COMB (@lem2004125) (@lem2004124)). Qed.
Lemma lem2004127 : term648 = term649.
Proof. exact (MK_COMB (@lem2004126) (@lem2004121)). Qed.
Lemma lem2004128 : term650.
Proof. exact (@lem1980255 term2 term5 term2 term5). Qed.
Lemma lem2004130 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2004131 : term66 = term73.
Proof. exact (@lem2004130 (NUMERAL 0) term15). Qed.
Lemma lem2004132 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2004133 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2004134 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2004133 h1) (fun h1 : term73 = True => @lem2004132)). Qed.
Lemma lem2004135 : term73 = True.
Proof. exact (EQ_MP (@lem2004134) (@lem2004132)). Qed.
Lemma lem2004136 : term66 = True.
Proof. exact (TRANS (@lem2004131) (@lem2004135)). Qed.
Lemma lem2004137 : True = term66.
Proof. exact (SYM (@lem2004136)). Qed.
Lemma lem2004138 : term66.
Proof. exact (EQ_MP (@lem2004137) (@lem0)). Qed.
Lemma lem2004139 : term651.
Proof. exact (@lem2004128 (@lem2004138)). Qed.
Lemma lem2004141 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2004142 : term66 = term73.
Proof. exact (@lem2004141 (NUMERAL 0) term15). Qed.
Lemma lem2004143 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2004144 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2004145 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2004144 h1) (fun h1 : term73 = True => @lem2004143)). Qed.
Lemma lem2004146 : term73 = True.
Proof. exact (EQ_MP (@lem2004145) (@lem2004143)). Qed.
Lemma lem2004147 : term66 = True.
Proof. exact (TRANS (@lem2004142) (@lem2004146)). Qed.
Lemma lem2004148 : True = term66.
Proof. exact (SYM (@lem2004147)). Qed.
Lemma lem2004149 : term66.
Proof. exact (EQ_MP (@lem2004148) (@lem0)). Qed.
Lemma lem2004150 : term649 = term652.
Proof. exact (@lem2004139 (@lem2004149)). Qed.
Lemma lem2004152 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2004153 : term78 = term2.
Proof. exact (@lem2004152 term15). Qed.
Lemma lem2004155 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2004156 : term78 = term2.
Proof. exact (@lem2004155 term15). Qed.
Lemma lem2004157 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2004158 : term79 = term68.
Proof. exact (MK_COMB (@lem2004157) (@lem2004156)). Qed.
Lemma lem2004159 : term652 = term648.
Proof. exact (MK_COMB (@lem2004158) (@lem2004153)). Qed.
Lemma lem2004161 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2004162 : term648 = term653.
Proof. exact (@lem2004161 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2004163 : term653 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2004164 : term648 = False.
Proof. exact (TRANS (@lem2004162) (@lem2004163)). Qed.
Lemma lem2004165 : term652 = False.
Proof. exact (TRANS (@lem2004159) (@lem2004164)). Qed.
Lemma lem2004166 : term649 = False.
Proof. exact (TRANS (@lem2004150) (@lem2004165)). Qed.
Lemma lem2004167 : term648 = False.
Proof. exact (TRANS (@lem2004127) (@lem2004166)). Qed.
Lemma lem2004168 : term486 = False.
Proof. exact (TRANS (@lem2004118) (@lem2004167)). Qed.
Lemma lem2004169 (x : real) (h1 : term504 x) : False.
Proof. exact (EQ_MP (@lem2004168) (@lem2004115 x h1)). Qed.
Lemma lem2004170 (x : real) (h1 : term553 x) : term553 x.
Proof. exact (h1). Qed.
Lemma lem2004171 (x : real) (h1 : term553 x) : term551 x.
Proof. exact (proj2 (@lem2004170 x h1)). Qed.
Lemma lem2004173 (x : real) (h1 : term553 x) : term548 x.
Proof. exact (proj2 (@lem2004171 x h1)). Qed.
Lemma lem2004175 (x : real) (h1 : term553 x) : term486.
Proof. exact (proj2 (@lem2004173 x h1)). Qed.
Lemma lem2004178 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2004179 : term486 = term648.
Proof. exact (@lem2004178 term2 term2). Qed.
Lemma lem2004181 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2004182 : term2 = term67.
Proof. exact (@lem2004181 (NUMERAL 0)). Qed.
Lemma lem2004184 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2004185 : term2 = term67.
Proof. exact (@lem2004184 (NUMERAL 0)). Qed.
Lemma lem2004186 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2004187 : term68 = term69.
Proof. exact (MK_COMB (@lem2004186) (@lem2004185)). Qed.
Lemma lem2004188 : term648 = term649.
Proof. exact (MK_COMB (@lem2004187) (@lem2004182)). Qed.
Lemma lem2004189 : term650.
Proof. exact (@lem1980255 term2 term5 term2 term5). Qed.
Lemma lem2004191 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2004192 : term66 = term73.
Proof. exact (@lem2004191 (NUMERAL 0) term15). Qed.
Lemma lem2004193 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2004194 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2004195 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2004194 h1) (fun h1 : term73 = True => @lem2004193)). Qed.
Lemma lem2004196 : term73 = True.
Proof. exact (EQ_MP (@lem2004195) (@lem2004193)). Qed.
Lemma lem2004197 : term66 = True.
Proof. exact (TRANS (@lem2004192) (@lem2004196)). Qed.
Lemma lem2004198 : True = term66.
Proof. exact (SYM (@lem2004197)). Qed.
Lemma lem2004199 : term66.
Proof. exact (EQ_MP (@lem2004198) (@lem0)). Qed.
Lemma lem2004200 : term651.
Proof. exact (@lem2004189 (@lem2004199)). Qed.
Lemma lem2004202 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2004203 : term66 = term73.
Proof. exact (@lem2004202 (NUMERAL 0) term15). Qed.
Lemma lem2004204 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2004205 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2004206 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2004205 h1) (fun h1 : term73 = True => @lem2004204)). Qed.
Lemma lem2004207 : term73 = True.
Proof. exact (EQ_MP (@lem2004206) (@lem2004204)). Qed.
Lemma lem2004208 : term66 = True.
Proof. exact (TRANS (@lem2004203) (@lem2004207)). Qed.
Lemma lem2004209 : True = term66.
Proof. exact (SYM (@lem2004208)). Qed.
Lemma lem2004210 : term66.
Proof. exact (EQ_MP (@lem2004209) (@lem0)). Qed.
Lemma lem2004211 : term649 = term652.
Proof. exact (@lem2004200 (@lem2004210)). Qed.
Lemma lem2004213 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2004214 : term78 = term2.
Proof. exact (@lem2004213 term15). Qed.
Lemma lem2004216 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2004217 : term78 = term2.
Proof. exact (@lem2004216 term15). Qed.
Lemma lem2004218 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2004219 : term79 = term68.
Proof. exact (MK_COMB (@lem2004218) (@lem2004217)). Qed.
Lemma lem2004220 : term652 = term648.
Proof. exact (MK_COMB (@lem2004219) (@lem2004214)). Qed.
Lemma lem2004222 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2004223 : term648 = term653.
Proof. exact (@lem2004222 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2004224 : term653 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2004225 : term648 = False.
Proof. exact (TRANS (@lem2004223) (@lem2004224)). Qed.
Lemma lem2004226 : term652 = False.
Proof. exact (TRANS (@lem2004220) (@lem2004225)). Qed.
Lemma lem2004227 : term649 = False.
Proof. exact (TRANS (@lem2004211) (@lem2004226)). Qed.
Lemma lem2004228 : term648 = False.
Proof. exact (TRANS (@lem2004188) (@lem2004227)). Qed.
Lemma lem2004229 : term486 = False.
Proof. exact (TRANS (@lem2004179) (@lem2004228)). Qed.
Lemma lem2004230 (x : real) (h1 : term553 x) : False.
Proof. exact (EQ_MP (@lem2004229) (@lem2004175 x h1)). Qed.
Lemma lem2004231 (x : real) (h1 : term555 x) : False.
Proof. exact (or_elim (@lem2004108 x h1) (fun h0 : term504 x => @lem2004169 x h0) (fun h0 : term553 x => @lem2004230 x h0)). Qed.
Lemma lem2004232 (x : real) (h1 : term444 x) : term444 x.
Proof. exact (h1). Qed.
Lemma lem2004233 (x : real) (h1 : term444 x) : term443 x.
Proof. exact (proj2 (@lem2004232 x h1)). Qed.
Lemma lem2004237 (x : real) (h1 : term444 x) : term442 x.
Proof. exact (proj2 (@lem2004233 x h1)). Qed.
Lemma lem2004242 (x : real) (h1 : term444 x) : term389.
Proof. exact (proj1 (@lem2004237 x h1)). Qed.
Lemma lem2004244 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2004245 : term389 = term654.
Proof. exact (@lem2004244 term2 term118). Qed.
Lemma lem2004247 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2004248 : term118 = term139.
Proof. exact (@lem2004247 term127). Qed.
Lemma lem2004250 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2004251 : term2 = term67.
Proof. exact (@lem2004250 (NUMERAL 0)). Qed.
Lemma lem2004252 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2004253 : term68 = term69.
Proof. exact (MK_COMB (@lem2004252) (@lem2004251)). Qed.
Lemma lem2004254 : term654 = term655.
Proof. exact (MK_COMB (@lem2004253) (@lem2004248)). Qed.
Lemma lem2004255 : term656.
Proof. exact (@lem1980255 term2 term5 term118 term5). Qed.
Lemma lem2004257 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2004258 : term66 = term73.
Proof. exact (@lem2004257 (NUMERAL 0) term15). Qed.
Lemma lem2004259 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2004260 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2004261 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2004260 h1) (fun h1 : term73 = True => @lem2004259)). Qed.
Lemma lem2004262 : term73 = True.
Proof. exact (EQ_MP (@lem2004261) (@lem2004259)). Qed.
Lemma lem2004263 : term66 = True.
Proof. exact (TRANS (@lem2004258) (@lem2004262)). Qed.
Lemma lem2004264 : True = term66.
Proof. exact (SYM (@lem2004263)). Qed.
Lemma lem2004265 : term66.
Proof. exact (EQ_MP (@lem2004264) (@lem0)). Qed.
Lemma lem2004266 : term657.
Proof. exact (@lem2004255 (@lem2004265)). Qed.
Lemma lem2004268 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2004269 : term66 = term73.
Proof. exact (@lem2004268 (NUMERAL 0) term15). Qed.
Lemma lem2004270 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2004271 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2004272 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2004271 h1) (fun h1 : term73 = True => @lem2004270)). Qed.
Lemma lem2004273 : term73 = True.
Proof. exact (EQ_MP (@lem2004272) (@lem2004270)). Qed.
Lemma lem2004274 : term66 = True.
Proof. exact (TRANS (@lem2004269) (@lem2004273)). Qed.
Lemma lem2004275 : True = term66.
Proof. exact (SYM (@lem2004274)). Qed.
Lemma lem2004276 : term66.
Proof. exact (EQ_MP (@lem2004275) (@lem0)). Qed.
Lemma lem2004277 : term655 = term658.
Proof. exact (@lem2004266 (@lem2004276)). Qed.
Lemma lem2004279 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2004280 : term133 = term134.
Proof. exact (@lem2004279 term127 term15). Qed.
Lemma lem2004281 : term135 = term125.
Proof. exact (@lem996237 term125). Qed.
Lemma lem2004282 : (term135 = term125) = (term136 = term127).
Proof. exact (@lem1007663 term125 (BIT1 0) term125). Qed.
Lemma lem2004283 : term136 = term127.
Proof. exact (EQ_MP (@lem2004282) (@lem2004281)). Qed.
Lemma lem2004284 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2004285 : term137 = term129.
Proof. exact (MK_COMB (@lem2004284) (@lem2004283)). Qed.
Lemma lem2004286 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2004287 : term134 = term118.
Proof. exact (MK_COMB (@lem2004286) (@lem2004285)). Qed.
Lemma lem2004288 : term133 = term118.
Proof. exact (TRANS (@lem2004280) (@lem2004287)). Qed.
Lemma lem2004290 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2004291 : term78 = term2.
Proof. exact (@lem2004290 term15). Qed.
Lemma lem2004292 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2004293 : term79 = term68.
Proof. exact (MK_COMB (@lem2004292) (@lem2004291)). Qed.
Lemma lem2004294 : term658 = term654.
Proof. exact (MK_COMB (@lem2004293) (@lem2004288)). Qed.
Lemma lem2004296 (m : nat) (n : nat) : (term659 m n) = False.
Proof. exact (proj1 (@lem1365720 m n)). Qed.
Lemma lem2004297 : term654 = False.
Proof. exact (@lem2004296 (NUMERAL 0) term127). Qed.
Lemma lem2004298 : term658 = False.
Proof. exact (TRANS (@lem2004294) (@lem2004297)). Qed.
Lemma lem2004299 : term655 = False.
Proof. exact (TRANS (@lem2004277) (@lem2004298)). Qed.
Lemma lem2004300 : term654 = False.
Proof. exact (TRANS (@lem2004254) (@lem2004299)). Qed.
Lemma lem2004301 : term389 = False.
Proof. exact (TRANS (@lem2004245) (@lem2004300)). Qed.
Lemma lem2004302 (x : real) (h1 : term444 x) : False.
Proof. exact (EQ_MP (@lem2004301) (@lem2004242 x h1)). Qed.
Lemma lem2004303 (x : real) (h1 : term557 x) : False.
Proof. exact (or_elim (@lem2004107 x h1) (fun h0 : term555 x => @lem2004231 x h0) (fun h0 : term444 x => @lem2004302 x h0)). Qed.
Lemma lem2004304 (x : real) (h1 : term645 x) : term645 x.
Proof. exact (h1). Qed.
Lemma lem2004305 (x : real) (h1 : term601 x) : term601 x.
Proof. exact (h1). Qed.
Lemma lem2004306 (x : real) (h1 : term601 x) : term599 x.
Proof. exact (proj2 (@lem2004305 x h1)). Qed.
Lemma lem2004309 (x : real) (h1 : term601 x) : term486.
Proof. exact (proj1 (@lem2004306 x h1)). Qed.
Lemma lem2004311 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2004312 : term486 = term648.
Proof. exact (@lem2004311 term2 term2). Qed.
Lemma lem2004314 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2004315 : term2 = term67.
Proof. exact (@lem2004314 (NUMERAL 0)). Qed.
Lemma lem2004317 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2004318 : term2 = term67.
Proof. exact (@lem2004317 (NUMERAL 0)). Qed.
Lemma lem2004319 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2004320 : term68 = term69.
Proof. exact (MK_COMB (@lem2004319) (@lem2004318)). Qed.
Lemma lem2004321 : term648 = term649.
Proof. exact (MK_COMB (@lem2004320) (@lem2004315)). Qed.
Lemma lem2004322 : term650.
Proof. exact (@lem1980255 term2 term5 term2 term5). Qed.
Lemma lem2004324 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2004325 : term66 = term73.
Proof. exact (@lem2004324 (NUMERAL 0) term15). Qed.
Lemma lem2004326 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2004327 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2004328 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2004327 h1) (fun h1 : term73 = True => @lem2004326)). Qed.
Lemma lem2004329 : term73 = True.
Proof. exact (EQ_MP (@lem2004328) (@lem2004326)). Qed.
Lemma lem2004330 : term66 = True.
Proof. exact (TRANS (@lem2004325) (@lem2004329)). Qed.
Lemma lem2004331 : True = term66.
Proof. exact (SYM (@lem2004330)). Qed.
Lemma lem2004332 : term66.
Proof. exact (EQ_MP (@lem2004331) (@lem0)). Qed.
Lemma lem2004333 : term651.
Proof. exact (@lem2004322 (@lem2004332)). Qed.
Lemma lem2004335 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2004336 : term66 = term73.
Proof. exact (@lem2004335 (NUMERAL 0) term15). Qed.
Lemma lem2004337 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2004338 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2004339 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2004338 h1) (fun h1 : term73 = True => @lem2004337)). Qed.
Lemma lem2004340 : term73 = True.
Proof. exact (EQ_MP (@lem2004339) (@lem2004337)). Qed.
Lemma lem2004341 : term66 = True.
Proof. exact (TRANS (@lem2004336) (@lem2004340)). Qed.
Lemma lem2004342 : True = term66.
Proof. exact (SYM (@lem2004341)). Qed.
Lemma lem2004343 : term66.
Proof. exact (EQ_MP (@lem2004342) (@lem0)). Qed.
Lemma lem2004344 : term649 = term652.
Proof. exact (@lem2004333 (@lem2004343)). Qed.
Lemma lem2004346 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2004347 : term78 = term2.
Proof. exact (@lem2004346 term15). Qed.
Lemma lem2004349 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2004350 : term78 = term2.
Proof. exact (@lem2004349 term15). Qed.
Lemma lem2004351 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2004352 : term79 = term68.
Proof. exact (MK_COMB (@lem2004351) (@lem2004350)). Qed.
Lemma lem2004353 : term652 = term648.
Proof. exact (MK_COMB (@lem2004352) (@lem2004347)). Qed.
Lemma lem2004355 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2004356 : term648 = term653.
Proof. exact (@lem2004355 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2004357 : term653 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2004358 : term648 = False.
Proof. exact (TRANS (@lem2004356) (@lem2004357)). Qed.
Lemma lem2004359 : term652 = False.
Proof. exact (TRANS (@lem2004353) (@lem2004358)). Qed.
Lemma lem2004360 : term649 = False.
Proof. exact (TRANS (@lem2004344) (@lem2004359)). Qed.
Lemma lem2004361 : term648 = False.
Proof. exact (TRANS (@lem2004321) (@lem2004360)). Qed.
Lemma lem2004362 : term486 = False.
Proof. exact (TRANS (@lem2004312) (@lem2004361)). Qed.
Lemma lem2004363 (x : real) (h1 : term601 x) : False.
Proof. exact (EQ_MP (@lem2004362) (@lem2004309 x h1)). Qed.
Lemma lem2004364 (x : real) (h1 : term644 x) : term644 x.
Proof. exact (h1). Qed.
Lemma lem2004365 (x : real) (h1 : term644 x) : term643 x.
Proof. exact (proj2 (@lem2004364 x h1)). Qed.
Lemma lem2004368 (x : real) (h1 : term644 x) : term486.
Proof. exact (proj1 (@lem2004365 x h1)). Qed.
Lemma lem2004370 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2004371 : term486 = term648.
Proof. exact (@lem2004370 term2 term2). Qed.
Lemma lem2004373 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2004374 : term2 = term67.
Proof. exact (@lem2004373 (NUMERAL 0)). Qed.
Lemma lem2004376 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2004377 : term2 = term67.
Proof. exact (@lem2004376 (NUMERAL 0)). Qed.
Lemma lem2004378 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2004379 : term68 = term69.
Proof. exact (MK_COMB (@lem2004378) (@lem2004377)). Qed.
Lemma lem2004380 : term648 = term649.
Proof. exact (MK_COMB (@lem2004379) (@lem2004374)). Qed.
Lemma lem2004381 : term650.
Proof. exact (@lem1980255 term2 term5 term2 term5). Qed.
Lemma lem2004383 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2004384 : term66 = term73.
Proof. exact (@lem2004383 (NUMERAL 0) term15). Qed.
Lemma lem2004385 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2004386 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2004387 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2004386 h1) (fun h1 : term73 = True => @lem2004385)). Qed.
Lemma lem2004388 : term73 = True.
Proof. exact (EQ_MP (@lem2004387) (@lem2004385)). Qed.
Lemma lem2004389 : term66 = True.
Proof. exact (TRANS (@lem2004384) (@lem2004388)). Qed.
Lemma lem2004390 : True = term66.
Proof. exact (SYM (@lem2004389)). Qed.
Lemma lem2004391 : term66.
Proof. exact (EQ_MP (@lem2004390) (@lem0)). Qed.
Lemma lem2004392 : term651.
Proof. exact (@lem2004381 (@lem2004391)). Qed.
Lemma lem2004394 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2004395 : term66 = term73.
Proof. exact (@lem2004394 (NUMERAL 0) term15). Qed.
Lemma lem2004396 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2004397 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2004398 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2004397 h1) (fun h1 : term73 = True => @lem2004396)). Qed.
Lemma lem2004399 : term73 = True.
Proof. exact (EQ_MP (@lem2004398) (@lem2004396)). Qed.
Lemma lem2004400 : term66 = True.
Proof. exact (TRANS (@lem2004395) (@lem2004399)). Qed.
Lemma lem2004401 : True = term66.
Proof. exact (SYM (@lem2004400)). Qed.
Lemma lem2004402 : term66.
Proof. exact (EQ_MP (@lem2004401) (@lem0)). Qed.
Lemma lem2004403 : term649 = term652.
Proof. exact (@lem2004392 (@lem2004402)). Qed.
Lemma lem2004405 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2004406 : term78 = term2.
Proof. exact (@lem2004405 term15). Qed.
Lemma lem2004408 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2004409 : term78 = term2.
Proof. exact (@lem2004408 term15). Qed.
Lemma lem2004410 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2004411 : term79 = term68.
Proof. exact (MK_COMB (@lem2004410) (@lem2004409)). Qed.
Lemma lem2004412 : term652 = term648.
Proof. exact (MK_COMB (@lem2004411) (@lem2004406)). Qed.
Lemma lem2004414 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2004415 : term648 = term653.
Proof. exact (@lem2004414 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2004416 : term653 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2004417 : term648 = False.
Proof. exact (TRANS (@lem2004415) (@lem2004416)). Qed.
Lemma lem2004418 : term652 = False.
Proof. exact (TRANS (@lem2004412) (@lem2004417)). Qed.
Lemma lem2004419 : term649 = False.
Proof. exact (TRANS (@lem2004403) (@lem2004418)). Qed.
Lemma lem2004420 : term648 = False.
Proof. exact (TRANS (@lem2004380) (@lem2004419)). Qed.
Lemma lem2004421 : term486 = False.
Proof. exact (TRANS (@lem2004371) (@lem2004420)). Qed.
Lemma lem2004422 (x : real) (h1 : term644 x) : False.
Proof. exact (EQ_MP (@lem2004421) (@lem2004368 x h1)). Qed.
Lemma lem2004423 (x : real) (h1 : term645 x) : False.
Proof. exact (or_elim (@lem2004304 x h1) (fun h0 : term601 x => @lem2004363 x h0) (fun h0 : term644 x => @lem2004422 x h0)). Qed.
Lemma lem2004424 (x : real) (h1 : term647 x) : False.
Proof. exact (or_elim (@lem2004106 x h1) (fun h0 : term557 x => @lem2004303 x h0) (fun h0 : term645 x => @lem2004423 x h0)). Qed.
Lemma lem2004425 (x : real) (h1 : term216 x) : term216 x.
Proof. exact (h1). Qed.
Lemma lem2004426 (x : real) (h1 : term216 x) : term647 x.
Proof. exact (EQ_MP (@lem2004105 x) (@lem2004425 x h1)). Qed.
Lemma lem2004427 (x : real) (h1 : term216 x) : (term647 x) = False.
Proof. exact (prop_ext (fun h2 : term647 x => @lem2004424 x h2) (fun h2 : False => @lem2004426 x h1)). Qed.
Lemma lem2004428 (x : real) (h1 : term216 x) : False.
Proof. exact (EQ_MP (@lem2004427 x h1) (@lem2004426 x h1)). Qed.
Lemma lem2004429 (x : real) (h1 : term169 x) : term169 x.
Proof. exact (h1). Qed.
Lemma lem2004430 (x : real) (h1 : term169 x) : term216 x.
Proof. exact (EQ_MP (@lem2000636 x) (@lem2004429 x h1)). Qed.
Lemma lem2004431 (x : real) (h1 : term169 x) : (term216 x) = False.
Proof. exact (prop_ext (fun h2 : term216 x => @lem2004428 x h2) (fun h2 : False => @lem2004430 x h1)). Qed.
Lemma lem2004432 (x : real) (h1 : term169 x) : False.
Proof. exact (EQ_MP (@lem2004431 x h1) (@lem2004430 x h1)). Qed.
Lemma lem2004433 (x : real) : term660 x.
Proof. exact (fun h0 : term169 x => @lem2004432 x h0). Qed.
Lemma lem2004434 (x : real) : term661 x.
Proof. exact (@lem1386578 ((term171 x) = (term3 x))). Qed.
Lemma lem2004438 (x : real) : term662 x.
Proof. exact (@lem1594900 x). Qed.
Lemma lem2004439 (x : real) : (term662 x) = (term663 x).
Proof. exact (eq_refl (term662 x)). Qed.
Lemma lem2004440 (x : real) : term663 x.
Proof. exact (EQ_MP (@lem2004439 x) (@lem2004438 x)). Qed.
Lemma lem2004441 (x : real) (y : real) : term664 x y.
Proof. exact (@lem2004440 x y). Qed.
Lemma lem2004442 (x : real) (y : real) : (term664 x y) = ((term665 x y) = (term666 x y)).
Proof. exact (eq_refl (term664 x y)). Qed.
Lemma lem2004445 (x : real) (y : real) : (term665 x y) = (term666 x y).
Proof. exact (EQ_MP (@lem2004442 x y) (@lem2004441 x y)). Qed.
Lemma lem2004446 (x : real) : (term667 x) = (term668 x).
Proof. exact (@lem2004445 x (term3 x)). Qed.
Lemma lem2004448 (x : real) : (term171 x) = (term3 x).
Proof. exact (@lem2004434 x (@lem2004433 x)). Qed.
Lemma lem2004449 (x : real) : (term669 x) = (term669 x).
Proof. exact (eq_refl (term669 x)). Qed.
Lemma lem2004450 (x : real) : (term668 x) = (term670 x).
Proof. exact (MK_COMB (@lem2004449 x) (@lem2004448 x)). Qed.
Lemma lem2004451 (x : real) : (term667 x) = (term670 x).
Proof. exact (TRANS (@lem2004446 x) (@lem2004450 x)). Qed.
Lemma lem2004452 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2004453 (x : real) : (term671 x) = (term672 x).
Proof. exact (MK_COMB (@lem2004452) (@lem2004451 x)). Qed.
Lemma lem2004454 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem2004455 (x : real) : (term673 x) = (term674 x).
Proof. exact (MK_COMB (@lem2004453 x) (@lem2004454)). Qed.
Lemma lem2004456 (x : real) : (term674 x) = (term673 x).
Proof. exact (SYM (@lem2004455 x)). Qed.
Lemma lem2004458 (x : real) (y : real) (z : real) : term165 x y z.
Proof. exact (fun h0 : term166 z => @lem2000422 x y z h0). Qed.
Lemma lem2004459 (x : real) : term675 x.
Proof. exact (@lem2004458 (real_abs x) term5 (term3 x)). Qed.
Lemma lem2004461 (x : real) : (term159 x) = True.
Proof. exact (EQ_MP (@lem2000410 x) (@lem2000409 x)). Qed.
Lemma lem2004462 (x : real) : True = (term159 x).
Proof. exact (SYM (@lem2004461 x)). Qed.
Lemma lem2004463 (x : real) : term159 x.
Proof. exact (EQ_MP (@lem2004462 x) (@lem0)). Qed.
Lemma lem2004464 (x : real) : (term674 x) = (term676 x).
Proof. exact (@lem2004459 x (@lem2004463 x)). Qed.
Lemma lem2004465 (x : real) : (term676 x) = (term674 x).
Proof. exact (SYM (@lem2004464 x)). Qed.
Lemma lem2004476 (x : real) : (term677 x) = (term678 x).
Proof. exact (@lem1988295 (real_abs x) (term679 x)). Qed.
Lemma lem2004485 (x : real) : (term3 x) = (term4 x).
Proof. exact (@lem1982761 (real_abs x) term5). Qed.
Lemma lem2004488 : term200 = term200.
Proof. exact (eq_refl term200). Qed.
Lemma lem2004489 (x : real) : (term679 x) = (term559 x).
Proof. exact (MK_COMB (@lem2004488) (@lem2004485 x)). Qed.
Lemma lem2004490 (x : real) : (term559 x) = (term4 x).
Proof. exact (@lem1982733 (term4 x)). Qed.
Lemma lem2004491 (x : real) : (term679 x) = (term4 x).
Proof. exact (TRANS (@lem2004489 x) (@lem2004490 x)). Qed.
Lemma lem2004496 (x : real) : (term680 x) = (term680 x).
Proof. exact (eq_refl (term680 x)). Qed.
Lemma lem2004497 (x : real) : (term681 x) = (term682 x).
Proof. exact (MK_COMB (@lem2004496 x) (@lem2004491 x)). Qed.
Lemma lem2004498 (x : real) : (term682 x) = (term683 x).
Proof. exact (@lem1982792 (real_abs x) (term4 x)). Qed.
Lemma lem2004499 (x : real) : (term10 x) = (term11 x).
Proof. exact (@lem1982781 (real_abs x) term12 term5). Qed.
Lemma lem2004501 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2004502 : term5 = term14.
Proof. exact (@lem2004501 term15). Qed.
Lemma lem2004504 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2004505 : term12 = term18.
Proof. exact (@lem2004504 term15). Qed.
Lemma lem2004506 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2004507 : term19 = term20.
Proof. exact (MK_COMB (@lem2004506) (@lem2004505)). Qed.
Lemma lem2004508 : term21 = term22.
Proof. exact (MK_COMB (@lem2004507) (@lem2004502)). Qed.
Lemma lem2004509 : term22 = term23.
Proof. exact (@lem1981613 term12 term5 term5 term5). Qed.
Lemma lem2004511 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2004512 : term26 = term27.
Proof. exact (@lem2004511 term15 term15). Qed.
Lemma lem2004513 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2004514 : term29 = term15.
Proof. exact (EQ_MP (@lem2004513) (@lem940073)). Qed.
Lemma lem2004515 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2004516 : term27 = term5.
Proof. exact (MK_COMB (@lem2004515) (@lem2004514)). Qed.
Lemma lem2004517 : term26 = term5.
Proof. exact (TRANS (@lem2004512) (@lem2004516)). Qed.
Lemma lem2004519 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2004520 : term21 = term32.
Proof. exact (@lem2004519 term15 term15). Qed.
Lemma lem2004521 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2004522 : term29 = term15.
Proof. exact (EQ_MP (@lem2004521) (@lem940073)). Qed.
Lemma lem2004523 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2004524 : term27 = term5.
Proof. exact (MK_COMB (@lem2004523) (@lem2004522)). Qed.
Lemma lem2004525 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2004526 : term32 = term12.
Proof. exact (MK_COMB (@lem2004525) (@lem2004524)). Qed.
Lemma lem2004527 : term21 = term12.
Proof. exact (TRANS (@lem2004520) (@lem2004526)). Qed.
Lemma lem2004528 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2004529 : term33 = term34.
Proof. exact (MK_COMB (@lem2004528) (@lem2004527)). Qed.
Lemma lem2004530 : term23 = term18.
Proof. exact (MK_COMB (@lem2004529) (@lem2004517)). Qed.
Lemma lem2004531 : term22 = term18.
Proof. exact (TRANS (@lem2004509) (@lem2004530)). Qed.
Lemma lem2004532 : term21 = term18.
Proof. exact (TRANS (@lem2004508) (@lem2004531)). Qed.
Lemma lem2004534 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2004535 : term18 = term12.
Proof. exact (@lem2004534 term12). Qed.
Lemma lem2004536 : term21 = term12.
Proof. exact (TRANS (@lem2004532) (@lem2004535)). Qed.
Lemma lem2004539 (x : real) : (term36 x) = (term36 x).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem2004540 (x : real) : (term11 x) = (term37 x).
Proof. exact (MK_COMB (@lem2004539 x) (@lem2004536)). Qed.
Lemma lem2004541 (x : real) : (term10 x) = (term37 x).
Proof. exact (TRANS (@lem2004499 x) (@lem2004540 x)). Qed.
Lemma lem2004542 (x : real) : (term203 x) = (term203 x).
Proof. exact (eq_refl (term203 x)). Qed.
Lemma lem2004543 (x : real) : (term683 x) = (term684 x).
Proof. exact (MK_COMB (@lem2004542 x) (@lem2004541 x)). Qed.
Lemma lem2004544 (x : real) : (term684 x) = (term685 x).
Proof. exact (@lem1982763 (real_abs x) (term181 x) term12). Qed.
Lemma lem2004545 (x : real) : (term584 x) = (term585 x).
Proof. exact (@lem1982715 term12 (real_abs x)). Qed.
Lemma lem2004547 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2004548 : term5 = term14.
Proof. exact (@lem2004547 term15). Qed.
Lemma lem2004550 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2004551 : term12 = term18.
Proof. exact (@lem2004550 term15). Qed.
Lemma lem2004552 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2004553 : term47 = term98.
Proof. exact (MK_COMB (@lem2004552) (@lem2004551)). Qed.
Lemma lem2004554 : term99 = term100.
Proof. exact (MK_COMB (@lem2004553) (@lem2004548)). Qed.
Lemma lem2004555 : term101.
Proof. exact (@lem1981473 term12 term5 term5 term5 term2 term5). Qed.
Lemma lem2004557 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2004558 : term66 = term73.
Proof. exact (@lem2004557 (NUMERAL 0) term15). Qed.
Lemma lem2004559 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2004560 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2004561 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2004560 h1) (fun h1 : term73 = True => @lem2004559)). Qed.
Lemma lem2004562 : term73 = True.
Proof. exact (EQ_MP (@lem2004561) (@lem2004559)). Qed.
Lemma lem2004563 : term66 = True.
Proof. exact (TRANS (@lem2004558) (@lem2004562)). Qed.
Lemma lem2004564 : True = term66.
Proof. exact (SYM (@lem2004563)). Qed.
Lemma lem2004565 : term66.
Proof. exact (EQ_MP (@lem2004564) (@lem0)). Qed.
Lemma lem2004566 : term102.
Proof. exact (@lem2004555 (@lem2004565)). Qed.
Lemma lem2004568 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2004569 : term66 = term73.
Proof. exact (@lem2004568 (NUMERAL 0) term15). Qed.
Lemma lem2004570 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2004571 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2004572 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2004571 h1) (fun h1 : term73 = True => @lem2004570)). Qed.
Lemma lem2004573 : term73 = True.
Proof. exact (EQ_MP (@lem2004572) (@lem2004570)). Qed.
Lemma lem2004574 : term66 = True.
Proof. exact (TRANS (@lem2004569) (@lem2004573)). Qed.
Lemma lem2004575 : True = term66.
Proof. exact (SYM (@lem2004574)). Qed.
Lemma lem2004576 : term66.
Proof. exact (EQ_MP (@lem2004575) (@lem0)). Qed.
Lemma lem2004577 : term103.
Proof. exact (@lem2004566 (@lem2004576)). Qed.
Lemma lem2004579 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2004580 : term66 = term73.
Proof. exact (@lem2004579 (NUMERAL 0) term15). Qed.
Lemma lem2004581 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2004582 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2004583 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2004582 h1) (fun h1 : term73 = True => @lem2004581)). Qed.
Lemma lem2004584 : term73 = True.
Proof. exact (EQ_MP (@lem2004583) (@lem2004581)). Qed.
Lemma lem2004585 : term66 = True.
Proof. exact (TRANS (@lem2004580) (@lem2004584)). Qed.
Lemma lem2004586 : True = term66.
Proof. exact (SYM (@lem2004585)). Qed.
Lemma lem2004587 : term66.
Proof. exact (EQ_MP (@lem2004586) (@lem0)). Qed.
Lemma lem2004588 : term104.
Proof. exact (@lem2004577 (@lem2004587)). Qed.
Lemma lem2004590 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2004591 : term26 = term27.
Proof. exact (@lem2004590 term15 term15). Qed.
Lemma lem2004592 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2004593 : term29 = term15.
Proof. exact (EQ_MP (@lem2004592) (@lem940073)). Qed.
Lemma lem2004594 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2004595 : term27 = term5.
Proof. exact (MK_COMB (@lem2004594) (@lem2004593)). Qed.
Lemma lem2004596 : term26 = term5.
Proof. exact (TRANS (@lem2004591) (@lem2004595)). Qed.
Lemma lem2004598 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2004599 : term21 = term32.
Proof. exact (@lem2004598 term15 term15). Qed.
Lemma lem2004600 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2004601 : term29 = term15.
Proof. exact (EQ_MP (@lem2004600) (@lem940073)). Qed.
Lemma lem2004602 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2004603 : term27 = term5.
Proof. exact (MK_COMB (@lem2004602) (@lem2004601)). Qed.
Lemma lem2004604 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2004605 : term32 = term12.
Proof. exact (MK_COMB (@lem2004604) (@lem2004603)). Qed.
Lemma lem2004606 : term21 = term12.
Proof. exact (TRANS (@lem2004599) (@lem2004605)). Qed.
Lemma lem2004607 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2004608 : term105 = term47.
Proof. exact (MK_COMB (@lem2004607) (@lem2004606)). Qed.
Lemma lem2004609 : term106 = term99.
Proof. exact (MK_COMB (@lem2004608) (@lem2004596)). Qed.
Lemma lem2004611 (m : nat) : (term107 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2004612 : term99 = term2.
Proof. exact (@lem2004611 term15). Qed.
Lemma lem2004613 : term106 = term2.
Proof. exact (TRANS (@lem2004609) (@lem2004612)). Qed.
Lemma lem2004614 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2004615 : term108 = term109.
Proof. exact (MK_COMB (@lem2004614) (@lem2004613)). Qed.
Lemma lem2004616 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem2004617 : term110 = term78.
Proof. exact (MK_COMB (@lem2004615) (@lem2004616)). Qed.
Lemma lem2004619 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2004620 : term78 = term2.
Proof. exact (@lem2004619 term15). Qed.
Lemma lem2004621 : term110 = term2.
Proof. exact (TRANS (@lem2004617) (@lem2004620)). Qed.
Lemma lem2004623 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2004624 : term26 = term27.
Proof. exact (@lem2004623 term15 term15). Qed.
Lemma lem2004625 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2004626 : term29 = term15.
Proof. exact (EQ_MP (@lem2004625) (@lem940073)). Qed.
Lemma lem2004627 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2004628 : term27 = term5.
Proof. exact (MK_COMB (@lem2004627) (@lem2004626)). Qed.
Lemma lem2004629 : term26 = term5.
Proof. exact (TRANS (@lem2004624) (@lem2004628)). Qed.
Lemma lem2004630 : term109 = term109.
Proof. exact (eq_refl term109). Qed.
Lemma lem2004631 : term111 = term78.
Proof. exact (MK_COMB (@lem2004630) (@lem2004629)). Qed.
Lemma lem2004633 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2004634 : term78 = term2.
Proof. exact (@lem2004633 term15). Qed.
Lemma lem2004635 : term111 = term2.
Proof. exact (TRANS (@lem2004631) (@lem2004634)). Qed.
Lemma lem2004636 : term2 = term111.
Proof. exact (SYM (@lem2004635)). Qed.
Lemma lem2004637 : term110 = term111.
Proof. exact (TRANS (@lem2004621) (@lem2004636)). Qed.
Lemma lem2004638 : term100 = term67.
Proof. exact (@lem2004588 (@lem2004637)). Qed.
Lemma lem2004639 : term99 = term67.
Proof. exact (TRANS (@lem2004554) (@lem2004638)). Qed.
Lemma lem2004641 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2004642 : term67 = term2.
Proof. exact (@lem2004641 term2). Qed.
Lemma lem2004643 : term99 = term2.
Proof. exact (TRANS (@lem2004639) (@lem2004642)). Qed.
Lemma lem2004644 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2004645 : term112 = term109.
Proof. exact (MK_COMB (@lem2004644) (@lem2004643)). Qed.
Lemma lem2004646 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem2004647 (x : real) : (term585 x) = (term586 x).
Proof. exact (MK_COMB (@lem2004645) (@lem2004646 x)). Qed.
Lemma lem2004648 (x : real) : (term584 x) = (term586 x).
Proof. exact (TRANS (@lem2004545 x) (@lem2004647 x)). Qed.
Lemma lem2004649 (x : real) : (term586 x) = term2.
Proof. exact (@lem1982719 (real_abs x)). Qed.
Lemma lem2004650 (x : real) : (term584 x) = term2.
Proof. exact (TRANS (@lem2004648 x) (@lem2004649 x)). Qed.
Lemma lem2004651 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2004652 (x : real) : (term686 x) = term38.
Proof. exact (MK_COMB (@lem2004651) (@lem2004650 x)). Qed.
Lemma lem2004653 : term12 = term12.
Proof. exact (eq_refl term12). Qed.
Lemma lem2004654 (x : real) : (term685 x) = term687.
Proof. exact (MK_COMB (@lem2004652 x) (@lem2004653)). Qed.
Lemma lem2004655 (x : real) : (term684 x) = term687.
Proof. exact (TRANS (@lem2004544 x) (@lem2004654 x)). Qed.
Lemma lem2004656 : term687 = term12.
Proof. exact (@lem1982721 term12). Qed.
Lemma lem2004657 (x : real) : (term684 x) = term12.
Proof. exact (TRANS (@lem2004655 x) (@lem2004656)). Qed.
Lemma lem2004658 (x : real) : (term683 x) = term12.
Proof. exact (TRANS (@lem2004543 x) (@lem2004657 x)). Qed.
Lemma lem2004659 (x : real) : (term682 x) = term12.
Proof. exact (TRANS (@lem2004498 x) (@lem2004658 x)). Qed.
Lemma lem2004660 (x : real) : (term681 x) = term12.
Proof. exact (TRANS (@lem2004497 x) (@lem2004659 x)). Qed.
Lemma lem2004661 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2004662 (x : real) : (term688 x) = term689.
Proof. exact (MK_COMB (@lem2004661) (@lem2004660 x)). Qed.
Lemma lem2004663 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2004664 (x : real) : (term678 x) = term690.
Proof. exact (MK_COMB (@lem2004662 x) (@lem2004663)). Qed.
Lemma lem2004674 (x : real) : (term677 x) = term690.
Proof. exact (TRANS (@lem2004476 x) (@lem2004664 x)). Qed.
Lemma lem2004678 (h1 : term690) : term690.
Proof. exact (h1). Qed.
Lemma lem2004680 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2004681 : term690 = term691.
Proof. exact (@lem2004680 term2 term12). Qed.
Lemma lem2004683 (x : nat) : (term16 x) = (term17 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2004684 : term12 = term18.
Proof. exact (@lem2004683 term15). Qed.
Lemma lem2004686 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2004687 : term2 = term67.
Proof. exact (@lem2004686 (NUMERAL 0)). Qed.
Lemma lem2004688 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2004689 : term145 = term146.
Proof. exact (MK_COMB (@lem2004688) (@lem2004687)). Qed.
Lemma lem2004690 : term691 = term692.
Proof. exact (MK_COMB (@lem2004689) (@lem2004684)). Qed.
Lemma lem2004691 : term693.
Proof. exact (@lem1980026 term2 term5 term12 term5). Qed.
Lemma lem2004693 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2004694 : term66 = term73.
Proof. exact (@lem2004693 (NUMERAL 0) term15). Qed.
Lemma lem2004695 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2004696 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2004697 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2004696 h1) (fun h1 : term73 = True => @lem2004695)). Qed.
Lemma lem2004698 : term73 = True.
Proof. exact (EQ_MP (@lem2004697) (@lem2004695)). Qed.
Lemma lem2004699 : term66 = True.
Proof. exact (TRANS (@lem2004694) (@lem2004698)). Qed.
Lemma lem2004700 : True = term66.
Proof. exact (SYM (@lem2004699)). Qed.
Lemma lem2004701 : term66.
Proof. exact (EQ_MP (@lem2004700) (@lem0)). Qed.
Lemma lem2004702 : term694.
Proof. exact (@lem2004691 (@lem2004701)). Qed.
Lemma lem2004704 (m : nat) (n : nat) : (term72 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2004705 : term66 = term73.
Proof. exact (@lem2004704 (NUMERAL 0) term15). Qed.
Lemma lem2004706 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2004707 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2004708 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2004707 h1) (fun h1 : term73 = True => @lem2004706)). Qed.
Lemma lem2004709 : term73 = True.
Proof. exact (EQ_MP (@lem2004708) (@lem2004706)). Qed.
Lemma lem2004710 : term66 = True.
Proof. exact (TRANS (@lem2004705) (@lem2004709)). Qed.
Lemma lem2004711 : True = term66.
Proof. exact (SYM (@lem2004710)). Qed.
Lemma lem2004712 : term66.
Proof. exact (EQ_MP (@lem2004711) (@lem0)). Qed.
Lemma lem2004713 : term692 = term695.
Proof. exact (@lem2004702 (@lem2004712)). Qed.
Lemma lem2004715 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2004716 : term21 = term32.
Proof. exact (@lem2004715 term15 term15). Qed.
Lemma lem2004717 : (term28 = (BIT1 0)) = (term29 = term15).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2004718 : term29 = term15.
Proof. exact (EQ_MP (@lem2004717) (@lem940073)). Qed.
Lemma lem2004719 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2004720 : term27 = term5.
Proof. exact (MK_COMB (@lem2004719) (@lem2004718)). Qed.
Lemma lem2004721 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2004722 : term32 = term12.
Proof. exact (MK_COMB (@lem2004721) (@lem2004720)). Qed.
Lemma lem2004723 : term21 = term12.
Proof. exact (TRANS (@lem2004716) (@lem2004722)). Qed.
Lemma lem2004725 (x : nat) : (term77 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2004726 : term78 = term2.
Proof. exact (@lem2004725 term15). Qed.
Lemma lem2004727 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2004728 : term151 = term145.
Proof. exact (MK_COMB (@lem2004727) (@lem2004726)). Qed.
Lemma lem2004729 : term695 = term691.
Proof. exact (MK_COMB (@lem2004728) (@lem2004723)). Qed.
Lemma lem2004731 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2004732 : term691 = term696.
Proof. exact (@lem2004731 (NUMERAL 0) term15). Qed.
Lemma lem2004733 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2004734 (h1 : term74 = (BIT1 0)) : (term15 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2004735 : (term74 = (BIT1 0)) = ((term15 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem2004734 h1) (fun h1 : (term15 = (NUMERAL 0)) = False => @lem2004733)). Qed.
Lemma lem2004736 : (term15 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2004735) (@lem2004733)). Qed.
Lemma lem2004737 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2004738 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2004739 : term156 = (and True).
Proof. exact (MK_COMB (@lem2004738) (@lem2004737)). Qed.
Lemma lem2004740 : term696 = (True /\ False).
Proof. exact (MK_COMB (@lem2004739) (@lem2004736)). Qed.
Lemma lem2004742 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2004743 : term696 = False.
Proof. exact (TRANS (@lem2004740) (@lem2004742)). Qed.
Lemma lem2004744 : term691 = False.
Proof. exact (TRANS (@lem2004732) (@lem2004743)). Qed.
Lemma lem2004745 : term695 = False.
Proof. exact (TRANS (@lem2004729) (@lem2004744)). Qed.
Lemma lem2004746 : term692 = False.
Proof. exact (TRANS (@lem2004713) (@lem2004745)). Qed.
Lemma lem2004747 : term691 = False.
Proof. exact (TRANS (@lem2004690) (@lem2004746)). Qed.
Lemma lem2004748 : term690 = False.
Proof. exact (TRANS (@lem2004681) (@lem2004747)). Qed.
Lemma lem2004749 (h1 : term690) : False.
Proof. exact (EQ_MP (@lem2004748) (@lem2004678 h1)). Qed.
Lemma lem2004751 (h1 : term690) : term690.
Proof. exact (h1). Qed.
Lemma lem2004752 (h1 : term690) : term690 = False.
Proof. exact (prop_ext (fun h2 : term690 => @lem2004749 h1) (fun h2 : False => @lem2004751 h1)). Qed.
Lemma lem2004753 (h1 : term690) : False.
Proof. exact (EQ_MP (@lem2004752 h1) (@lem2004751 h1)). Qed.
Lemma lem2004754 (x : real) (h1 : term677 x) : term677 x.
Proof. exact (h1). Qed.
Lemma lem2004755 (x : real) (h1 : term677 x) : term690.
Proof. exact (EQ_MP (@lem2004674 x) (@lem2004754 x h1)). Qed.
Lemma lem2004756 (x : real) (h1 : term677 x) : term690 = False.
Proof. exact (prop_ext (fun h2 : term690 => @lem2004753 h2) (fun h2 : False => @lem2004755 x h1)). Qed.
Lemma lem2004757 (x : real) (h1 : term677 x) : False.
Proof. exact (EQ_MP (@lem2004756 x h1) (@lem2004755 x h1)). Qed.
Lemma lem2004758 (x : real) : term697 x.
Proof. exact (fun h0 : term677 x => @lem2004757 x h0). Qed.
Lemma lem2004759 (x : real) : term698 x.
Proof. exact (@lem1386578 (term676 x)). Qed.
Lemma lem2004762 (x : real) : term676 x.
Proof. exact (@lem2004759 x (@lem2004758 x)). Qed.
Lemma lem2004763 (x : real) : term674 x.
Proof. exact (EQ_MP (@lem2004465 x) (@lem2004762 x)). Qed.
Lemma lem2004764 (x : real) : term673 x.
Proof. exact (EQ_MP (@lem2004456 x) (@lem2004763 x)). Qed.
Lemma lem2004769 : term699.
Proof. exact (fun x : real => @lem2004764 x). Qed.
