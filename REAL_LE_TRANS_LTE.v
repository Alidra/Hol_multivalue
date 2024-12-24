Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_TRANS_LTE_term_abbrevs.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1367765_spec.
Require Import thm1367771_spec.
Require Import thm1386578_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19367_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980255_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981223_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982711_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982725_spec.
Require Import thm1982733_spec.
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1982796_spec.
Require Import thm1982797_spec.
Require Import thm1988285_spec.
Require Import thm1988287_spec.
Require Import thm1988295_spec.
Require Import thm1988297_spec.
Require Import thm1988332_spec.
Require Import thm1988348_spec.
Require Import thm32_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm940532_spec.
Require Import thm996237_spec.
Require Import thm996238_spec.
Lemma lem1989804 (y : real) (x : real) (z : real) : (term0 y x z) = (term1 y x z).
Proof. exact (@lem17362 (real_lt y z) (real_le x z)). Qed.
Lemma lem1989805 (P : real -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1989806 (y : real) (x : real) : (term4 y x) = (term5 y x).
Proof. exact (@lem1989805 (term6 y x)). Qed.
Lemma lem1989807 (y : real) (x : real) (z : real) : (term7 y x z) = (term8 y x z).
Proof. exact (eq_refl (term7 y x z)). Qed.
Lemma lem1989808 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1989809 (y : real) (x : real) (z : real) : (term9 y x z) = (term0 y x z).
Proof. exact (MK_COMB (@lem1989808) (@lem1989807 y x z)). Qed.
Lemma lem1989810 (y : real) (x : real) (z : real) : (term9 y x z) = (term1 y x z).
Proof. exact (TRANS (@lem1989809 y x z) (@lem1989804 y x z)). Qed.
Lemma lem1989811 (y : real) (x : real) : (term10 y x) = (term11 y x).
Proof. exact (fun_ext (fun z : real => @lem1989810 y x z)). Qed.
Lemma lem1989812 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1989813 (y : real) (x : real) : (term5 y x) = (term12 y x).
Proof. exact (MK_COMB (@lem1989812) (@lem1989811 y x)). Qed.
Lemma lem1989814 (y : real) (x : real) : (term4 y x) = (term12 y x).
Proof. exact (TRANS (@lem1989806 y x) (@lem1989813 y x)). Qed.
Lemma lem1989816 (x : real) (y : real) : (term13 x y) = (term13 x y).
Proof. exact (eq_refl (term13 x y)). Qed.
Lemma lem1989817 (y : real) (x : real) : (term14 y x) = (term15 y x).
Proof. exact (MK_COMB (@lem1989816 x y) (@lem1989814 y x)). Qed.
Lemma lem1989818 (y : real) (x : real) : (term16 y x) = (term14 y x).
Proof. exact (@lem17362 (real_le x y) (term17 y x)). Qed.
Lemma lem1989820 (y : real) (x : real) : (term16 y x) = (term15 y x).
Proof. exact (TRANS (@lem1989818 y x) (@lem1989817 y x)). Qed.
Lemma lem1989827 (y : real) (x : real) (z : real) : (term1 y x z) = (term1 y x z).
Proof. exact (eq_refl (term1 y x z)). Qed.
Lemma lem1989828 (y : real) (x : real) : (term11 y x) = (term11 y x).
Proof. exact (fun_ext (fun z : real => @lem1989827 y x z)). Qed.
Lemma lem1989829 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1989830 (y : real) (x : real) : (term12 y x) = (term12 y x).
Proof. exact (MK_COMB (@lem1989829) (@lem1989828 y x)). Qed.
Lemma lem1989833 (x : real) (y : real) : (term13 x y) = (term13 x y).
Proof. exact (eq_refl (term13 x y)). Qed.
Lemma lem1989834 (y : real) (x : real) : (term15 y x) = (term15 y x).
Proof. exact (MK_COMB (@lem1989833 x y) (@lem1989830 y x)). Qed.
Lemma lem1989835 (y : real) (x : real) : (term16 y x) = (term15 y x).
Proof. exact (TRANS (@lem1989820 y x) (@lem1989834 y x)). Qed.
Lemma lem1989836 (y : real) (x : real) : (real_le x y) = (term18 y x).
Proof. exact (@lem1988287 y x). Qed.
Lemma lem1989842 (y : real) (x : real) : (real_sub y x) = (term19 y x).
Proof. exact (@lem1982792 y x). Qed.
Lemma lem1989847 (x : real) (y : real) : (term19 y x) = (term20 x y).
Proof. exact (@lem1982761 (term21 x) y). Qed.
Lemma lem1989849 (x : real) (y : real) : (real_sub y x) = (term20 x y).
Proof. exact (TRANS (@lem1989842 y x) (@lem1989847 x y)). Qed.
Lemma lem1989850 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1989851 (x : real) (y : real) : (term22 y x) = (term23 x y).
Proof. exact (MK_COMB (@lem1989850) (@lem1989849 x y)). Qed.
Lemma lem1989852 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1989853 (x : real) (y : real) : (term18 y x) = (term25 x y).
Proof. exact (MK_COMB (@lem1989851 x y) (@lem1989852)). Qed.
Lemma lem1989854 (x : real) (y : real) : (real_le x y) = (term25 x y).
Proof. exact (TRANS (@lem1989836 y x) (@lem1989853 x y)). Qed.
Lemma lem1989855 (z : real) (y : real) : (real_lt y z) = (term26 z y).
Proof. exact (@lem1988285 z y). Qed.
Lemma lem1989861 (z : real) (y : real) : (real_sub z y) = (term19 z y).
Proof. exact (@lem1982792 z y). Qed.
Lemma lem1989866 (y : real) (z : real) : (term19 z y) = (term20 y z).
Proof. exact (@lem1982761 (term21 y) z). Qed.
Lemma lem1989868 (y : real) (z : real) : (real_sub z y) = (term20 y z).
Proof. exact (TRANS (@lem1989861 z y) (@lem1989866 y z)). Qed.
Lemma lem1989869 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1989870 (y : real) (z : real) : (term27 z y) = (term28 y z).
Proof. exact (MK_COMB (@lem1989869) (@lem1989868 y z)). Qed.
Lemma lem1989871 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1989872 (y : real) (z : real) : (term26 z y) = (term29 y z).
Proof. exact (MK_COMB (@lem1989870 y z) (@lem1989871)). Qed.
Lemma lem1989873 (y : real) (z : real) : (real_lt y z) = (term29 y z).
Proof. exact (TRANS (@lem1989855 z y) (@lem1989872 y z)). Qed.
Lemma lem1989874 (x : real) (z : real) : (term30 x z) = (term26 x z).
Proof. exact (@lem1988297 x z). Qed.
Lemma lem1989887 (x : real) (z : real) : (real_sub x z) = (term19 x z).
Proof. exact (@lem1982792 x z). Qed.
Lemma lem1989888 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1989889 (x : real) (z : real) : (term27 x z) = (term31 x z).
Proof. exact (MK_COMB (@lem1989888) (@lem1989887 x z)). Qed.
Lemma lem1989890 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1989891 (x : real) (z : real) : (term26 x z) = (term32 x z).
Proof. exact (MK_COMB (@lem1989889 x z) (@lem1989890)). Qed.
Lemma lem1989892 (x : real) (z : real) : (term30 x z) = (term32 x z).
Proof. exact (TRANS (@lem1989874 x z) (@lem1989891 x z)). Qed.
Lemma lem1989893 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1989894 (y : real) (z : real) : (term33 y z) = (term34 y z).
Proof. exact (MK_COMB (@lem1989893) (@lem1989873 y z)). Qed.
Lemma lem1989895 (y : real) (x : real) (z : real) : (term1 y x z) = (term35 y x z).
Proof. exact (MK_COMB (@lem1989894 y z) (@lem1989892 x z)). Qed.
Lemma lem1989896 (y : real) (x : real) : (term11 y x) = (term36 y x).
Proof. exact (fun_ext (fun z : real => @lem1989895 y x z)). Qed.
Lemma lem1989897 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1989898 (y : real) (x : real) : (term12 y x) = (term37 y x).
Proof. exact (MK_COMB (@lem1989897) (@lem1989896 y x)). Qed.
Lemma lem1989899 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1989900 (x : real) (y : real) : (term13 x y) = (term38 x y).
Proof. exact (MK_COMB (@lem1989899) (@lem1989854 x y)). Qed.
Lemma lem1989901 (y : real) (x : real) : (term15 y x) = (term39 y x).
Proof. exact (MK_COMB (@lem1989900 x y) (@lem1989898 y x)). Qed.
Lemma lem1989902 (y : real) (x : real) : (term16 y x) = (term39 y x).
Proof. exact (TRANS (@lem1989835 y x) (@lem1989901 y x)). Qed.
Lemma lem1989953 {A : Type'} (P : Prop) (Q : A -> Prop) : (term40 A P Q) = (term41 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1989954 (P : Prop) (Q : real -> Prop) : (term42 P Q) = (term43 P Q).
Proof. exact (@lem1989953 real P Q). Qed.
Lemma lem1989955 (y : real) (x : real) : (term44 y x) = (term45 y x).
Proof. exact (@lem1989954 (term25 x y) (term36 y x)). Qed.
Lemma lem1989956 (y : real) (x : real) (z : real) : (term46 y x z) = (term35 y x z).
Proof. exact (eq_refl (term46 y x z)). Qed.
Lemma lem1989957 (y : real) (x : real) : (term47 y x) = (term36 y x).
Proof. exact (fun_ext (fun z : real => @lem1989956 y x z)). Qed.
Lemma lem1989958 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1989959 (y : real) (x : real) : (term48 y x) = (term37 y x).
Proof. exact (MK_COMB (@lem1989958) (@lem1989957 y x)). Qed.
Lemma lem1989960 (x : real) (y : real) : (term38 x y) = (term38 x y).
Proof. exact (eq_refl (term38 x y)). Qed.
Lemma lem1989961 (y : real) (x : real) : (term44 y x) = (term39 y x).
Proof. exact (MK_COMB (@lem1989960 x y) (@lem1989959 y x)). Qed.
Lemma lem1989962 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1989963 (y : real) (x : real) : (term49 y x) = (term50 y x).
Proof. exact (MK_COMB (@lem1989962) (@lem1989961 y x)). Qed.
Lemma lem1989964 (y : real) (x : real) (z : real) : (term46 y x z) = (term35 y x z).
Proof. exact (eq_refl (term46 y x z)). Qed.
Lemma lem1989965 (x : real) (y : real) : (term38 x y) = (term38 x y).
Proof. exact (eq_refl (term38 x y)). Qed.
Lemma lem1989966 (y : real) (x : real) (z : real) : (term51 y x z) = (term52 y x z).
Proof. exact (MK_COMB (@lem1989965 x y) (@lem1989964 y x z)). Qed.
Lemma lem1989967 (y : real) (x : real) : (term53 y x) = (term54 y x).
Proof. exact (fun_ext (fun z : real => @lem1989966 y x z)). Qed.
Lemma lem1989968 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1989969 (y : real) (x : real) : (term45 y x) = (term55 y x).
Proof. exact (MK_COMB (@lem1989968) (@lem1989967 y x)). Qed.
Lemma lem1989970 (y : real) (x : real) : ((term44 y x) = (term45 y x)) = ((term39 y x) = (term55 y x)).
Proof. exact (MK_COMB (@lem1989963 y x) (@lem1989969 y x)). Qed.
Lemma lem1989972 (y : real) (x : real) : (term39 y x) = (term55 y x).
Proof. exact (EQ_MP (@lem1989970 y x) (@lem1989955 y x)). Qed.
Lemma lem1989975 (y : real) (x : real) : (term16 y x) = (term55 y x).
Proof. exact (TRANS (@lem1989902 y x) (@lem1989972 y x)). Qed.
Lemma lem1989988 (y : real) (x : real) (z : real) : (term52 y x z) = (term52 y x z).
Proof. exact (eq_refl (term52 y x z)). Qed.
Lemma lem1989989 (y : real) (x : real) : (term54 y x) = (term54 y x).
Proof. exact (fun_ext (fun z : real => @lem1989988 y x z)). Qed.
Lemma lem1989990 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1989991 (y : real) (x : real) : (term55 y x) = (term55 y x).
Proof. exact (MK_COMB (@lem1989990) (@lem1989989 y x)). Qed.
Lemma lem1989992 (y : real) (x : real) : (term16 y x) = (term55 y x).
Proof. exact (TRANS (@lem1989975 y x) (@lem1989991 y x)). Qed.
Lemma lem1989996 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term52 y x z.
Proof. exact (h1). Qed.
Lemma lem1989997 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term35 y x z.
Proof. exact (proj2 (@lem1989996 y x z h1)). Qed.
Lemma lem1989998 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term25 x y.
Proof. exact (proj1 (@lem1989996 y x z h1)). Qed.
Lemma lem1989999 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term32 x z.
Proof. exact (proj2 (@lem1989997 y x z h1)). Qed.
Lemma lem1990000 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term29 y z.
Proof. exact (proj1 (@lem1989997 y x z h1)). Qed.
Lemma lem1990002 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1990003 : term56 = term57.
Proof. exact (@lem1990002 term24 term58). Qed.
Lemma lem1990005 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1990006 : term58 = term60.
Proof. exact (@lem1990005 term61). Qed.
Lemma lem1990008 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1990009 : term24 = term62.
Proof. exact (@lem1990008 (NUMERAL 0)). Qed.
Lemma lem1990010 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1990011 : term63 = term64.
Proof. exact (MK_COMB (@lem1990010) (@lem1990009)). Qed.
Lemma lem1990012 : term57 = term65.
Proof. exact (MK_COMB (@lem1990011) (@lem1990006)). Qed.
Lemma lem1990013 : term66.
Proof. exact (@lem1980255 term24 term58 term58 term58). Qed.
Lemma lem1990015 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1990016 : term57 = term68.
Proof. exact (@lem1990015 (NUMERAL 0) term61). Qed.
Lemma lem1990017 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1990018 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1990019 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1990018 h1) (fun h1 : term68 = True => @lem1990017)). Qed.
Lemma lem1990020 : term68 = True.
Proof. exact (EQ_MP (@lem1990019) (@lem1990017)). Qed.
Lemma lem1990021 : term57 = True.
Proof. exact (TRANS (@lem1990016) (@lem1990020)). Qed.
Lemma lem1990022 : True = term57.
Proof. exact (SYM (@lem1990021)). Qed.
Lemma lem1990023 : term57.
Proof. exact (EQ_MP (@lem1990022) (@lem0)). Qed.
Lemma lem1990024 : term70.
Proof. exact (@lem1990013 (@lem1990023)). Qed.
Lemma lem1990026 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1990027 : term57 = term68.
Proof. exact (@lem1990026 (NUMERAL 0) term61). Qed.
Lemma lem1990028 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1990029 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1990030 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1990029 h1) (fun h1 : term68 = True => @lem1990028)). Qed.
Lemma lem1990031 : term68 = True.
Proof. exact (EQ_MP (@lem1990030) (@lem1990028)). Qed.
Lemma lem1990032 : term57 = True.
Proof. exact (TRANS (@lem1990027) (@lem1990031)). Qed.
Lemma lem1990033 : True = term57.
Proof. exact (SYM (@lem1990032)). Qed.
Lemma lem1990034 : term57.
Proof. exact (EQ_MP (@lem1990033) (@lem0)). Qed.
Lemma lem1990035 : term65 = term71.
Proof. exact (@lem1990024 (@lem1990034)). Qed.
Lemma lem1990037 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1990038 : term74 = term75.
Proof. exact (@lem1990037 term61 term61). Qed.
Lemma lem1990039 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1990040 : term77 = term61.
Proof. exact (EQ_MP (@lem1990039) (@lem940073)). Qed.
Lemma lem1990041 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1990042 : term75 = term58.
Proof. exact (MK_COMB (@lem1990041) (@lem1990040)). Qed.
Lemma lem1990043 : term74 = term58.
Proof. exact (TRANS (@lem1990038) (@lem1990042)). Qed.
Lemma lem1990045 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1990046 : term79 = term24.
Proof. exact (@lem1990045 term61). Qed.
Lemma lem1990047 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1990048 : term80 = term63.
Proof. exact (MK_COMB (@lem1990047) (@lem1990046)). Qed.
Lemma lem1990049 : term71 = term57.
Proof. exact (MK_COMB (@lem1990048) (@lem1990043)). Qed.
Lemma lem1990051 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1990052 : term57 = term68.
Proof. exact (@lem1990051 (NUMERAL 0) term61). Qed.
Lemma lem1990053 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1990054 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1990055 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1990054 h1) (fun h1 : term68 = True => @lem1990053)). Qed.
Lemma lem1990056 : term68 = True.
Proof. exact (EQ_MP (@lem1990055) (@lem1990053)). Qed.
Lemma lem1990057 : term57 = True.
Proof. exact (TRANS (@lem1990052) (@lem1990056)). Qed.
Lemma lem1990058 : term71 = True.
Proof. exact (TRANS (@lem1990049) (@lem1990057)). Qed.
Lemma lem1990059 : term65 = True.
Proof. exact (TRANS (@lem1990035) (@lem1990058)). Qed.
Lemma lem1990060 : term57 = True.
Proof. exact (TRANS (@lem1990012) (@lem1990059)). Qed.
Lemma lem1990061 : term56 = True.
Proof. exact (TRANS (@lem1990003) (@lem1990060)). Qed.
Lemma lem1990062 : True = term56.
Proof. exact (SYM (@lem1990061)). Qed.
Lemma lem1990063 : term56.
Proof. exact (EQ_MP (@lem1990062) (@lem0)). Qed.
Lemma lem1990064 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term81 x y.
Proof. exact (conj (@lem1990063) (@lem1989998 y x z h1)). Qed.
Lemma lem1990066 (x : real) (y : real) : term82 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem1990067 (x : real) (y : real) : term83 x y.
Proof. exact (@lem1990066 term58 (term20 x y)). Qed.
Lemma lem1990068 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term84 x y.
Proof. exact (@lem1990067 x y (@lem1990064 y x z h1)). Qed.
Lemma lem1990069 (x : real) (y : real) : (term85 x y) = (term20 x y).
Proof. exact (@lem1982733 (term20 x y)). Qed.
Lemma lem1990070 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1990071 (x : real) (y : real) : (term86 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem1990070) (@lem1990069 x y)). Qed.
Lemma lem1990072 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1990073 (x : real) (y : real) : (term84 x y) = (term25 x y).
Proof. exact (MK_COMB (@lem1990071 x y) (@lem1990072)). Qed.
Lemma lem1990074 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term25 x y.
Proof. exact (EQ_MP (@lem1990073 x y) (@lem1990068 y x z h1)). Qed.
Lemma lem1990076 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1990077 : term56 = term57.
Proof. exact (@lem1990076 term24 term58). Qed.
Lemma lem1990079 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1990080 : term58 = term60.
Proof. exact (@lem1990079 term61). Qed.
Lemma lem1990082 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1990083 : term24 = term62.
Proof. exact (@lem1990082 (NUMERAL 0)). Qed.
Lemma lem1990084 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1990085 : term63 = term64.
Proof. exact (MK_COMB (@lem1990084) (@lem1990083)). Qed.
Lemma lem1990086 : term57 = term65.
Proof. exact (MK_COMB (@lem1990085) (@lem1990080)). Qed.
Lemma lem1990087 : term66.
Proof. exact (@lem1980255 term24 term58 term58 term58). Qed.
Lemma lem1990089 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1990090 : term57 = term68.
Proof. exact (@lem1990089 (NUMERAL 0) term61). Qed.
Lemma lem1990091 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1990092 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1990093 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1990092 h1) (fun h1 : term68 = True => @lem1990091)). Qed.
Lemma lem1990094 : term68 = True.
Proof. exact (EQ_MP (@lem1990093) (@lem1990091)). Qed.
Lemma lem1990095 : term57 = True.
Proof. exact (TRANS (@lem1990090) (@lem1990094)). Qed.
Lemma lem1990096 : True = term57.
Proof. exact (SYM (@lem1990095)). Qed.
Lemma lem1990097 : term57.
Proof. exact (EQ_MP (@lem1990096) (@lem0)). Qed.
Lemma lem1990098 : term70.
Proof. exact (@lem1990087 (@lem1990097)). Qed.
Lemma lem1990100 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1990101 : term57 = term68.
Proof. exact (@lem1990100 (NUMERAL 0) term61). Qed.
Lemma lem1990102 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1990103 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1990104 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1990103 h1) (fun h1 : term68 = True => @lem1990102)). Qed.
Lemma lem1990105 : term68 = True.
Proof. exact (EQ_MP (@lem1990104) (@lem1990102)). Qed.
Lemma lem1990106 : term57 = True.
Proof. exact (TRANS (@lem1990101) (@lem1990105)). Qed.
Lemma lem1990107 : True = term57.
Proof. exact (SYM (@lem1990106)). Qed.
Lemma lem1990108 : term57.
Proof. exact (EQ_MP (@lem1990107) (@lem0)). Qed.
Lemma lem1990109 : term65 = term71.
Proof. exact (@lem1990098 (@lem1990108)). Qed.
Lemma lem1990111 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1990112 : term74 = term75.
Proof. exact (@lem1990111 term61 term61). Qed.
Lemma lem1990113 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1990114 : term77 = term61.
Proof. exact (EQ_MP (@lem1990113) (@lem940073)). Qed.
Lemma lem1990115 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1990116 : term75 = term58.
Proof. exact (MK_COMB (@lem1990115) (@lem1990114)). Qed.
Lemma lem1990117 : term74 = term58.
Proof. exact (TRANS (@lem1990112) (@lem1990116)). Qed.
Lemma lem1990119 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1990120 : term79 = term24.
Proof. exact (@lem1990119 term61). Qed.
Lemma lem1990121 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1990122 : term80 = term63.
Proof. exact (MK_COMB (@lem1990121) (@lem1990120)). Qed.
Lemma lem1990123 : term71 = term57.
Proof. exact (MK_COMB (@lem1990122) (@lem1990117)). Qed.
Lemma lem1990125 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1990126 : term57 = term68.
Proof. exact (@lem1990125 (NUMERAL 0) term61). Qed.
Lemma lem1990127 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1990128 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1990129 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1990128 h1) (fun h1 : term68 = True => @lem1990127)). Qed.
Lemma lem1990130 : term68 = True.
Proof. exact (EQ_MP (@lem1990129) (@lem1990127)). Qed.
Lemma lem1990131 : term57 = True.
Proof. exact (TRANS (@lem1990126) (@lem1990130)). Qed.
Lemma lem1990132 : term71 = True.
Proof. exact (TRANS (@lem1990123) (@lem1990131)). Qed.
Lemma lem1990133 : term65 = True.
Proof. exact (TRANS (@lem1990109) (@lem1990132)). Qed.
Lemma lem1990134 : term57 = True.
Proof. exact (TRANS (@lem1990086) (@lem1990133)). Qed.
Lemma lem1990135 : term56 = True.
Proof. exact (TRANS (@lem1990077) (@lem1990134)). Qed.
Lemma lem1990136 : True = term56.
Proof. exact (SYM (@lem1990135)). Qed.
Lemma lem1990137 : term56.
Proof. exact (EQ_MP (@lem1990136) (@lem0)). Qed.
Lemma lem1990138 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term87 y z.
Proof. exact (conj (@lem1990137) (@lem1990000 y x z h1)). Qed.
Lemma lem1990140 (x : real) (y : real) : term88 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem1990141 (y : real) (z : real) : term89 y z.
Proof. exact (@lem1990140 term58 (term20 y z)). Qed.
Lemma lem1990142 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term90 y z.
Proof. exact (@lem1990141 y z (@lem1990138 y x z h1)). Qed.
Lemma lem1990143 (y : real) (z : real) : (term85 y z) = (term20 y z).
Proof. exact (@lem1982733 (term20 y z)). Qed.
Lemma lem1990144 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1990145 (y : real) (z : real) : (term91 y z) = (term28 y z).
Proof. exact (MK_COMB (@lem1990144) (@lem1990143 y z)). Qed.
Lemma lem1990146 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1990147 (y : real) (z : real) : (term90 y z) = (term29 y z).
Proof. exact (MK_COMB (@lem1990145 y z) (@lem1990146)). Qed.
Lemma lem1990148 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term29 y z.
Proof. exact (EQ_MP (@lem1990147 y z) (@lem1990142 y x z h1)). Qed.
Lemma lem1990150 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1990151 : term56 = term57.
Proof. exact (@lem1990150 term24 term58). Qed.
Lemma lem1990153 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1990154 : term58 = term60.
Proof. exact (@lem1990153 term61). Qed.
Lemma lem1990156 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1990157 : term24 = term62.
Proof. exact (@lem1990156 (NUMERAL 0)). Qed.
Lemma lem1990158 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1990159 : term63 = term64.
Proof. exact (MK_COMB (@lem1990158) (@lem1990157)). Qed.
Lemma lem1990160 : term57 = term65.
Proof. exact (MK_COMB (@lem1990159) (@lem1990154)). Qed.
Lemma lem1990161 : term66.
Proof. exact (@lem1980255 term24 term58 term58 term58). Qed.
Lemma lem1990163 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1990164 : term57 = term68.
Proof. exact (@lem1990163 (NUMERAL 0) term61). Qed.
Lemma lem1990165 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1990166 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1990167 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1990166 h1) (fun h1 : term68 = True => @lem1990165)). Qed.
Lemma lem1990168 : term68 = True.
Proof. exact (EQ_MP (@lem1990167) (@lem1990165)). Qed.
Lemma lem1990169 : term57 = True.
Proof. exact (TRANS (@lem1990164) (@lem1990168)). Qed.
Lemma lem1990170 : True = term57.
Proof. exact (SYM (@lem1990169)). Qed.
Lemma lem1990171 : term57.
Proof. exact (EQ_MP (@lem1990170) (@lem0)). Qed.
Lemma lem1990172 : term70.
Proof. exact (@lem1990161 (@lem1990171)). Qed.
Lemma lem1990174 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1990175 : term57 = term68.
Proof. exact (@lem1990174 (NUMERAL 0) term61). Qed.
Lemma lem1990176 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1990177 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1990178 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1990177 h1) (fun h1 : term68 = True => @lem1990176)). Qed.
Lemma lem1990179 : term68 = True.
Proof. exact (EQ_MP (@lem1990178) (@lem1990176)). Qed.
Lemma lem1990180 : term57 = True.
Proof. exact (TRANS (@lem1990175) (@lem1990179)). Qed.
Lemma lem1990181 : True = term57.
Proof. exact (SYM (@lem1990180)). Qed.
Lemma lem1990182 : term57.
Proof. exact (EQ_MP (@lem1990181) (@lem0)). Qed.
Lemma lem1990183 : term65 = term71.
Proof. exact (@lem1990172 (@lem1990182)). Qed.
Lemma lem1990185 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1990186 : term74 = term75.
Proof. exact (@lem1990185 term61 term61). Qed.
Lemma lem1990187 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1990188 : term77 = term61.
Proof. exact (EQ_MP (@lem1990187) (@lem940073)). Qed.
Lemma lem1990189 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1990190 : term75 = term58.
Proof. exact (MK_COMB (@lem1990189) (@lem1990188)). Qed.
Lemma lem1990191 : term74 = term58.
Proof. exact (TRANS (@lem1990186) (@lem1990190)). Qed.
Lemma lem1990193 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1990194 : term79 = term24.
Proof. exact (@lem1990193 term61). Qed.
Lemma lem1990195 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1990196 : term80 = term63.
Proof. exact (MK_COMB (@lem1990195) (@lem1990194)). Qed.
Lemma lem1990197 : term71 = term57.
Proof. exact (MK_COMB (@lem1990196) (@lem1990191)). Qed.
Lemma lem1990199 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1990200 : term57 = term68.
Proof. exact (@lem1990199 (NUMERAL 0) term61). Qed.
Lemma lem1990201 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1990202 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1990203 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1990202 h1) (fun h1 : term68 = True => @lem1990201)). Qed.
Lemma lem1990204 : term68 = True.
Proof. exact (EQ_MP (@lem1990203) (@lem1990201)). Qed.
Lemma lem1990205 : term57 = True.
Proof. exact (TRANS (@lem1990200) (@lem1990204)). Qed.
Lemma lem1990206 : term71 = True.
Proof. exact (TRANS (@lem1990197) (@lem1990205)). Qed.
Lemma lem1990207 : term65 = True.
Proof. exact (TRANS (@lem1990183) (@lem1990206)). Qed.
Lemma lem1990208 : term57 = True.
Proof. exact (TRANS (@lem1990160) (@lem1990207)). Qed.
Lemma lem1990209 : term56 = True.
Proof. exact (TRANS (@lem1990151) (@lem1990208)). Qed.
Lemma lem1990210 : True = term56.
Proof. exact (SYM (@lem1990209)). Qed.
Lemma lem1990211 : term56.
Proof. exact (EQ_MP (@lem1990210) (@lem0)). Qed.
Lemma lem1990212 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term92 x z.
Proof. exact (conj (@lem1990211) (@lem1989999 y x z h1)). Qed.
Lemma lem1990214 (x : real) (y : real) : term88 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem1990215 (x : real) (z : real) : term93 x z.
Proof. exact (@lem1990214 term58 (term19 x z)). Qed.
Lemma lem1990216 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term94 x z.
Proof. exact (@lem1990215 x z (@lem1990212 y x z h1)). Qed.
Lemma lem1990217 (x : real) (z : real) : (term95 x z) = (term19 x z).
Proof. exact (@lem1982733 (term19 x z)). Qed.
Lemma lem1990218 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1990219 (x : real) (z : real) : (term96 x z) = (term31 x z).
Proof. exact (MK_COMB (@lem1990218) (@lem1990217 x z)). Qed.
Lemma lem1990220 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1990221 (x : real) (z : real) : (term94 x z) = (term32 x z).
Proof. exact (MK_COMB (@lem1990219 x z) (@lem1990220)). Qed.
Lemma lem1990222 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term32 x z.
Proof. exact (EQ_MP (@lem1990221 x z) (@lem1990216 y x z h1)). Qed.
Lemma lem1990223 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term97 x y z.
Proof. exact (conj (@lem1990222 y x z h1) (@lem1990148 y x z h1)). Qed.
Lemma lem1990225 (x : real) (y : real) : term98 x y.
Proof. exact (proj2 (@lem1988348 x y)). Qed.
Lemma lem1990226 (x : real) (y : real) (z : real) : term99 x y z.
Proof. exact (@lem1990225 (term19 x z) (term20 y z)). Qed.
Lemma lem1990227 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term100 x y z.
Proof. exact (@lem1990226 x y z (@lem1990223 y x z h1)). Qed.
Lemma lem1990228 (x : real) (y : real) (z : real) : (term101 x y z) = (term102 x y z).
Proof. exact (@lem1982755 x (term21 z) (term20 y z)). Qed.
Lemma lem1990229 (y : real) (z : real) : (term103 y z) = (term104 y z).
Proof. exact (@lem1982757 (term21 y) (term21 z) z). Qed.
Lemma lem1990230 (z : real) : (term105 z) = (term106 z).
Proof. exact (@lem1982713 term107 z). Qed.
Lemma lem1990232 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1990233 : term58 = term60.
Proof. exact (@lem1990232 term61). Qed.
Lemma lem1990235 (x : nat) : (term108 x) = (term109 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1990236 : term107 = term110.
Proof. exact (@lem1990235 term61). Qed.
Lemma lem1990237 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1990238 : term111 = term112.
Proof. exact (MK_COMB (@lem1990237) (@lem1990236)). Qed.
Lemma lem1990239 : term113 = term114.
Proof. exact (MK_COMB (@lem1990238) (@lem1990233)). Qed.
Lemma lem1990240 : term115.
Proof. exact (@lem1981473 term107 term58 term58 term58 term24 term58). Qed.
Lemma lem1990242 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1990243 : term57 = term68.
Proof. exact (@lem1990242 (NUMERAL 0) term61). Qed.
Lemma lem1990244 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1990245 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1990246 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1990245 h1) (fun h1 : term68 = True => @lem1990244)). Qed.
Lemma lem1990247 : term68 = True.
Proof. exact (EQ_MP (@lem1990246) (@lem1990244)). Qed.
Lemma lem1990248 : term57 = True.
Proof. exact (TRANS (@lem1990243) (@lem1990247)). Qed.
Lemma lem1990249 : True = term57.
Proof. exact (SYM (@lem1990248)). Qed.
Lemma lem1990250 : term57.
Proof. exact (EQ_MP (@lem1990249) (@lem0)). Qed.
Lemma lem1990251 : term116.
Proof. exact (@lem1990240 (@lem1990250)). Qed.
Lemma lem1990253 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1990254 : term57 = term68.
Proof. exact (@lem1990253 (NUMERAL 0) term61). Qed.
Lemma lem1990255 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1990256 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1990257 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1990256 h1) (fun h1 : term68 = True => @lem1990255)). Qed.
Lemma lem1990258 : term68 = True.
Proof. exact (EQ_MP (@lem1990257) (@lem1990255)). Qed.
Lemma lem1990259 : term57 = True.
Proof. exact (TRANS (@lem1990254) (@lem1990258)). Qed.
Lemma lem1990260 : True = term57.
Proof. exact (SYM (@lem1990259)). Qed.
Lemma lem1990261 : term57.
Proof. exact (EQ_MP (@lem1990260) (@lem0)). Qed.
Lemma lem1990262 : term117.
Proof. exact (@lem1990251 (@lem1990261)). Qed.
Lemma lem1990264 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1990265 : term57 = term68.
Proof. exact (@lem1990264 (NUMERAL 0) term61). Qed.
Lemma lem1990266 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1990267 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1990268 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1990267 h1) (fun h1 : term68 = True => @lem1990266)). Qed.
Lemma lem1990269 : term68 = True.
Proof. exact (EQ_MP (@lem1990268) (@lem1990266)). Qed.
Lemma lem1990270 : term57 = True.
Proof. exact (TRANS (@lem1990265) (@lem1990269)). Qed.
Lemma lem1990271 : True = term57.
Proof. exact (SYM (@lem1990270)). Qed.
Lemma lem1990272 : term57.
Proof. exact (EQ_MP (@lem1990271) (@lem0)). Qed.
Lemma lem1990273 : term118.
Proof. exact (@lem1990262 (@lem1990272)). Qed.
Lemma lem1990275 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1990276 : term74 = term75.
Proof. exact (@lem1990275 term61 term61). Qed.
Lemma lem1990277 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1990278 : term77 = term61.
Proof. exact (EQ_MP (@lem1990277) (@lem940073)). Qed.
Lemma lem1990279 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1990280 : term75 = term58.
Proof. exact (MK_COMB (@lem1990279) (@lem1990278)). Qed.
Lemma lem1990281 : term74 = term58.
Proof. exact (TRANS (@lem1990276) (@lem1990280)). Qed.
Lemma lem1990283 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1990284 : term121 = term122.
Proof. exact (@lem1990283 term61 term61). Qed.
Lemma lem1990285 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1990286 : term77 = term61.
Proof. exact (EQ_MP (@lem1990285) (@lem940073)). Qed.
Lemma lem1990287 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1990288 : term75 = term58.
Proof. exact (MK_COMB (@lem1990287) (@lem1990286)). Qed.
Lemma lem1990289 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1990290 : term122 = term107.
Proof. exact (MK_COMB (@lem1990289) (@lem1990288)). Qed.
Lemma lem1990291 : term121 = term107.
Proof. exact (TRANS (@lem1990284) (@lem1990290)). Qed.
Lemma lem1990292 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1990293 : term123 = term111.
Proof. exact (MK_COMB (@lem1990292) (@lem1990291)). Qed.
Lemma lem1990294 : term124 = term113.
Proof. exact (MK_COMB (@lem1990293) (@lem1990281)). Qed.
Lemma lem1990296 (m : nat) : (term125 m) = term24.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1990297 : term113 = term24.
Proof. exact (@lem1990296 term61). Qed.
Lemma lem1990298 : term124 = term24.
Proof. exact (TRANS (@lem1990294) (@lem1990297)). Qed.
Lemma lem1990299 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1990300 : term126 = term127.
Proof. exact (MK_COMB (@lem1990299) (@lem1990298)). Qed.
Lemma lem1990301 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1990302 : term128 = term79.
Proof. exact (MK_COMB (@lem1990300) (@lem1990301)). Qed.
Lemma lem1990304 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1990305 : term79 = term24.
Proof. exact (@lem1990304 term61). Qed.
Lemma lem1990306 : term128 = term24.
Proof. exact (TRANS (@lem1990302) (@lem1990305)). Qed.
Lemma lem1990308 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1990309 : term74 = term75.
Proof. exact (@lem1990308 term61 term61). Qed.
Lemma lem1990310 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1990311 : term77 = term61.
Proof. exact (EQ_MP (@lem1990310) (@lem940073)). Qed.
Lemma lem1990312 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1990313 : term75 = term58.
Proof. exact (MK_COMB (@lem1990312) (@lem1990311)). Qed.
Lemma lem1990314 : term74 = term58.
Proof. exact (TRANS (@lem1990309) (@lem1990313)). Qed.
Lemma lem1990315 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem1990316 : term129 = term79.
Proof. exact (MK_COMB (@lem1990315) (@lem1990314)). Qed.
Lemma lem1990318 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1990319 : term79 = term24.
Proof. exact (@lem1990318 term61). Qed.
Lemma lem1990320 : term129 = term24.
Proof. exact (TRANS (@lem1990316) (@lem1990319)). Qed.
Lemma lem1990321 : term24 = term129.
Proof. exact (SYM (@lem1990320)). Qed.
Lemma lem1990322 : term128 = term129.
Proof. exact (TRANS (@lem1990306) (@lem1990321)). Qed.
Lemma lem1990323 : term114 = term62.
Proof. exact (@lem1990273 (@lem1990322)). Qed.
Lemma lem1990324 : term113 = term62.
Proof. exact (TRANS (@lem1990239) (@lem1990323)). Qed.
Lemma lem1990326 (x : real) : (term130 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem1990327 : term62 = term24.
Proof. exact (@lem1990326 term24). Qed.
Lemma lem1990328 : term113 = term24.
Proof. exact (TRANS (@lem1990324) (@lem1990327)). Qed.
Lemma lem1990329 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1990330 : term131 = term127.
Proof. exact (MK_COMB (@lem1990329) (@lem1990328)). Qed.
Lemma lem1990331 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1990332 (z : real) : (term106 z) = (term132 z).
Proof. exact (MK_COMB (@lem1990330) (@lem1990331 z)). Qed.
Lemma lem1990333 (z : real) : (term105 z) = (term132 z).
Proof. exact (TRANS (@lem1990230 z) (@lem1990332 z)). Qed.
Lemma lem1990334 (z : real) : (term132 z) = term24.
Proof. exact (@lem1982719 z). Qed.
Lemma lem1990335 (z : real) : (term105 z) = term24.
Proof. exact (TRANS (@lem1990333 z) (@lem1990334 z)). Qed.
Lemma lem1990336 (y : real) : (term133 y) = (term133 y).
Proof. exact (eq_refl (term133 y)). Qed.
Lemma lem1990337 (z : real) (y : real) : (term104 y z) = (term134 y).
Proof. exact (MK_COMB (@lem1990336 y) (@lem1990335 z)). Qed.
Lemma lem1990338 (z : real) (y : real) : (term103 y z) = (term134 y).
Proof. exact (TRANS (@lem1990229 y z) (@lem1990337 z y)). Qed.
Lemma lem1990339 (y : real) : (term134 y) = (term21 y).
Proof. exact (@lem1982723 (term21 y)). Qed.
Lemma lem1990340 (z : real) (y : real) : (term103 y z) = (term21 y).
Proof. exact (TRANS (@lem1990338 z y) (@lem1990339 y)). Qed.
Lemma lem1990341 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1990342 (z : real) (x : real) (y : real) : (term102 x y z) = (term19 x y).
Proof. exact (MK_COMB (@lem1990341 x) (@lem1990340 z y)). Qed.
Lemma lem1990343 (z : real) (x : real) (y : real) : (term101 x y z) = (term19 x y).
Proof. exact (TRANS (@lem1990228 x y z) (@lem1990342 z x y)). Qed.
Lemma lem1990344 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1990345 (z : real) (x : real) (y : real) : (term135 x y z) = (term31 x y).
Proof. exact (MK_COMB (@lem1990344) (@lem1990343 z x y)). Qed.
Lemma lem1990346 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1990347 (z : real) (x : real) (y : real) : (term100 x y z) = (term32 x y).
Proof. exact (MK_COMB (@lem1990345 z x y) (@lem1990346)). Qed.
Lemma lem1990348 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term32 x y.
Proof. exact (EQ_MP (@lem1990347 z x y) (@lem1990227 y x z h1)). Qed.
Lemma lem1990350 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1990351 : term56 = term57.
Proof. exact (@lem1990350 term24 term58). Qed.
Lemma lem1990353 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1990354 : term58 = term60.
Proof. exact (@lem1990353 term61). Qed.
Lemma lem1990356 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1990357 : term24 = term62.
Proof. exact (@lem1990356 (NUMERAL 0)). Qed.
Lemma lem1990358 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1990359 : term63 = term64.
Proof. exact (MK_COMB (@lem1990358) (@lem1990357)). Qed.
Lemma lem1990360 : term57 = term65.
Proof. exact (MK_COMB (@lem1990359) (@lem1990354)). Qed.
Lemma lem1990361 : term66.
Proof. exact (@lem1980255 term24 term58 term58 term58). Qed.
Lemma lem1990363 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1990364 : term57 = term68.
Proof. exact (@lem1990363 (NUMERAL 0) term61). Qed.
Lemma lem1990365 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1990366 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1990367 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1990366 h1) (fun h1 : term68 = True => @lem1990365)). Qed.
Lemma lem1990368 : term68 = True.
Proof. exact (EQ_MP (@lem1990367) (@lem1990365)). Qed.
Lemma lem1990369 : term57 = True.
Proof. exact (TRANS (@lem1990364) (@lem1990368)). Qed.
Lemma lem1990370 : True = term57.
Proof. exact (SYM (@lem1990369)). Qed.
Lemma lem1990371 : term57.
Proof. exact (EQ_MP (@lem1990370) (@lem0)). Qed.
Lemma lem1990372 : term70.
Proof. exact (@lem1990361 (@lem1990371)). Qed.
Lemma lem1990374 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1990375 : term57 = term68.
Proof. exact (@lem1990374 (NUMERAL 0) term61). Qed.
Lemma lem1990376 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1990377 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1990378 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1990377 h1) (fun h1 : term68 = True => @lem1990376)). Qed.
Lemma lem1990379 : term68 = True.
Proof. exact (EQ_MP (@lem1990378) (@lem1990376)). Qed.
Lemma lem1990380 : term57 = True.
Proof. exact (TRANS (@lem1990375) (@lem1990379)). Qed.
Lemma lem1990381 : True = term57.
Proof. exact (SYM (@lem1990380)). Qed.
Lemma lem1990382 : term57.
Proof. exact (EQ_MP (@lem1990381) (@lem0)). Qed.
Lemma lem1990383 : term65 = term71.
Proof. exact (@lem1990372 (@lem1990382)). Qed.
Lemma lem1990385 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1990386 : term74 = term75.
Proof. exact (@lem1990385 term61 term61). Qed.
Lemma lem1990387 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1990388 : term77 = term61.
Proof. exact (EQ_MP (@lem1990387) (@lem940073)). Qed.
Lemma lem1990389 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1990390 : term75 = term58.
Proof. exact (MK_COMB (@lem1990389) (@lem1990388)). Qed.
Lemma lem1990391 : term74 = term58.
Proof. exact (TRANS (@lem1990386) (@lem1990390)). Qed.
Lemma lem1990393 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1990394 : term79 = term24.
Proof. exact (@lem1990393 term61). Qed.
Lemma lem1990395 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1990396 : term80 = term63.
Proof. exact (MK_COMB (@lem1990395) (@lem1990394)). Qed.
Lemma lem1990397 : term71 = term57.
Proof. exact (MK_COMB (@lem1990396) (@lem1990391)). Qed.
Lemma lem1990399 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1990400 : term57 = term68.
Proof. exact (@lem1990399 (NUMERAL 0) term61). Qed.
Lemma lem1990401 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1990402 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1990403 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1990402 h1) (fun h1 : term68 = True => @lem1990401)). Qed.
Lemma lem1990404 : term68 = True.
Proof. exact (EQ_MP (@lem1990403) (@lem1990401)). Qed.
Lemma lem1990405 : term57 = True.
Proof. exact (TRANS (@lem1990400) (@lem1990404)). Qed.
Lemma lem1990406 : term71 = True.
Proof. exact (TRANS (@lem1990397) (@lem1990405)). Qed.
Lemma lem1990407 : term65 = True.
Proof. exact (TRANS (@lem1990383) (@lem1990406)). Qed.
Lemma lem1990408 : term57 = True.
Proof. exact (TRANS (@lem1990360) (@lem1990407)). Qed.
Lemma lem1990409 : term56 = True.
Proof. exact (TRANS (@lem1990351) (@lem1990408)). Qed.
Lemma lem1990410 : True = term56.
Proof. exact (SYM (@lem1990409)). Qed.
Lemma lem1990411 : term56.
Proof. exact (EQ_MP (@lem1990410) (@lem0)). Qed.
Lemma lem1990412 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term92 x y.
Proof. exact (conj (@lem1990411) (@lem1990348 y x z h1)). Qed.
Lemma lem1990414 (x : real) (y : real) : term88 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem1990415 (x : real) (y : real) : term93 x y.
Proof. exact (@lem1990414 term58 (term19 x y)). Qed.
Lemma lem1990416 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term94 x y.
Proof. exact (@lem1990415 x y (@lem1990412 y x z h1)). Qed.
Lemma lem1990417 (x : real) (y : real) : (term95 x y) = (term19 x y).
Proof. exact (@lem1982733 (term19 x y)). Qed.
Lemma lem1990418 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1990419 (x : real) (y : real) : (term96 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1990418) (@lem1990417 x y)). Qed.
Lemma lem1990420 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1990421 (x : real) (y : real) : (term94 x y) = (term32 x y).
Proof. exact (MK_COMB (@lem1990419 x y) (@lem1990420)). Qed.
Lemma lem1990422 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term32 x y.
Proof. exact (EQ_MP (@lem1990421 x y) (@lem1990416 y x z h1)). Qed.
Lemma lem1990423 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term136 x y.
Proof. exact (conj (@lem1990422 y x z h1) (@lem1990074 y x z h1)). Qed.
Lemma lem1990425 (x : real) (y : real) : term137 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem1990426 (x : real) (y : real) : term138 x y.
Proof. exact (@lem1990425 (term19 x y) (term20 x y)). Qed.
Lemma lem1990427 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term139 x y.
Proof. exact (@lem1990426 x y (@lem1990423 y x z h1)). Qed.
Lemma lem1990428 (x : real) (y : real) : (term140 x y) = (term141 x y).
Proof. exact (@lem1982753 x (term21 x) (term21 y) y). Qed.
Lemma lem1990429 (x : real) : (term142 x) = (term106 x).
Proof. exact (@lem1982715 term107 x). Qed.
Lemma lem1990431 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1990432 : term58 = term60.
Proof. exact (@lem1990431 term61). Qed.
Lemma lem1990434 (x : nat) : (term108 x) = (term109 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1990435 : term107 = term110.
Proof. exact (@lem1990434 term61). Qed.
Lemma lem1990436 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1990437 : term111 = term112.
Proof. exact (MK_COMB (@lem1990436) (@lem1990435)). Qed.
Lemma lem1990438 : term113 = term114.
Proof. exact (MK_COMB (@lem1990437) (@lem1990432)). Qed.
Lemma lem1990439 : term115.
Proof. exact (@lem1981473 term107 term58 term58 term58 term24 term58). Qed.
Lemma lem1990441 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1990442 : term57 = term68.
Proof. exact (@lem1990441 (NUMERAL 0) term61). Qed.
Lemma lem1990443 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1990444 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1990445 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1990444 h1) (fun h1 : term68 = True => @lem1990443)). Qed.
Lemma lem1990446 : term68 = True.
Proof. exact (EQ_MP (@lem1990445) (@lem1990443)). Qed.
Lemma lem1990447 : term57 = True.
Proof. exact (TRANS (@lem1990442) (@lem1990446)). Qed.
Lemma lem1990448 : True = term57.
Proof. exact (SYM (@lem1990447)). Qed.
Lemma lem1990449 : term57.
Proof. exact (EQ_MP (@lem1990448) (@lem0)). Qed.
Lemma lem1990450 : term116.
Proof. exact (@lem1990439 (@lem1990449)). Qed.
Lemma lem1990452 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1990453 : term57 = term68.
Proof. exact (@lem1990452 (NUMERAL 0) term61). Qed.
Lemma lem1990454 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1990455 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1990456 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1990455 h1) (fun h1 : term68 = True => @lem1990454)). Qed.
Lemma lem1990457 : term68 = True.
Proof. exact (EQ_MP (@lem1990456) (@lem1990454)). Qed.
Lemma lem1990458 : term57 = True.
Proof. exact (TRANS (@lem1990453) (@lem1990457)). Qed.
Lemma lem1990459 : True = term57.
Proof. exact (SYM (@lem1990458)). Qed.
Lemma lem1990460 : term57.
Proof. exact (EQ_MP (@lem1990459) (@lem0)). Qed.
Lemma lem1990461 : term117.
Proof. exact (@lem1990450 (@lem1990460)). Qed.
Lemma lem1990463 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1990464 : term57 = term68.
Proof. exact (@lem1990463 (NUMERAL 0) term61). Qed.
Lemma lem1990465 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1990466 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1990467 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1990466 h1) (fun h1 : term68 = True => @lem1990465)). Qed.
Lemma lem1990468 : term68 = True.
Proof. exact (EQ_MP (@lem1990467) (@lem1990465)). Qed.
Lemma lem1990469 : term57 = True.
Proof. exact (TRANS (@lem1990464) (@lem1990468)). Qed.
Lemma lem1990470 : True = term57.
Proof. exact (SYM (@lem1990469)). Qed.
Lemma lem1990471 : term57.
Proof. exact (EQ_MP (@lem1990470) (@lem0)). Qed.
Lemma lem1990472 : term118.
Proof. exact (@lem1990461 (@lem1990471)). Qed.
Lemma lem1990474 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1990475 : term74 = term75.
Proof. exact (@lem1990474 term61 term61). Qed.
Lemma lem1990476 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1990477 : term77 = term61.
Proof. exact (EQ_MP (@lem1990476) (@lem940073)). Qed.
Lemma lem1990478 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1990479 : term75 = term58.
Proof. exact (MK_COMB (@lem1990478) (@lem1990477)). Qed.
Lemma lem1990480 : term74 = term58.
Proof. exact (TRANS (@lem1990475) (@lem1990479)). Qed.
Lemma lem1990482 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1990483 : term121 = term122.
Proof. exact (@lem1990482 term61 term61). Qed.
Lemma lem1990484 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1990485 : term77 = term61.
Proof. exact (EQ_MP (@lem1990484) (@lem940073)). Qed.
Lemma lem1990486 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1990487 : term75 = term58.
Proof. exact (MK_COMB (@lem1990486) (@lem1990485)). Qed.
Lemma lem1990488 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1990489 : term122 = term107.
Proof. exact (MK_COMB (@lem1990488) (@lem1990487)). Qed.
Lemma lem1990490 : term121 = term107.
Proof. exact (TRANS (@lem1990483) (@lem1990489)). Qed.
Lemma lem1990491 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1990492 : term123 = term111.
Proof. exact (MK_COMB (@lem1990491) (@lem1990490)). Qed.
Lemma lem1990493 : term124 = term113.
Proof. exact (MK_COMB (@lem1990492) (@lem1990480)). Qed.
Lemma lem1990495 (m : nat) : (term125 m) = term24.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1990496 : term113 = term24.
Proof. exact (@lem1990495 term61). Qed.
Lemma lem1990497 : term124 = term24.
Proof. exact (TRANS (@lem1990493) (@lem1990496)). Qed.
Lemma lem1990498 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1990499 : term126 = term127.
Proof. exact (MK_COMB (@lem1990498) (@lem1990497)). Qed.
Lemma lem1990500 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1990501 : term128 = term79.
Proof. exact (MK_COMB (@lem1990499) (@lem1990500)). Qed.
Lemma lem1990503 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1990504 : term79 = term24.
Proof. exact (@lem1990503 term61). Qed.
Lemma lem1990505 : term128 = term24.
Proof. exact (TRANS (@lem1990501) (@lem1990504)). Qed.
Lemma lem1990507 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1990508 : term74 = term75.
Proof. exact (@lem1990507 term61 term61). Qed.
Lemma lem1990509 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1990510 : term77 = term61.
Proof. exact (EQ_MP (@lem1990509) (@lem940073)). Qed.
Lemma lem1990511 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1990512 : term75 = term58.
Proof. exact (MK_COMB (@lem1990511) (@lem1990510)). Qed.
Lemma lem1990513 : term74 = term58.
Proof. exact (TRANS (@lem1990508) (@lem1990512)). Qed.
Lemma lem1990514 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem1990515 : term129 = term79.
Proof. exact (MK_COMB (@lem1990514) (@lem1990513)). Qed.
Lemma lem1990517 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1990518 : term79 = term24.
Proof. exact (@lem1990517 term61). Qed.
Lemma lem1990519 : term129 = term24.
Proof. exact (TRANS (@lem1990515) (@lem1990518)). Qed.
Lemma lem1990520 : term24 = term129.
Proof. exact (SYM (@lem1990519)). Qed.
Lemma lem1990521 : term128 = term129.
Proof. exact (TRANS (@lem1990505) (@lem1990520)). Qed.
Lemma lem1990522 : term114 = term62.
Proof. exact (@lem1990472 (@lem1990521)). Qed.
Lemma lem1990523 : term113 = term62.
Proof. exact (TRANS (@lem1990438) (@lem1990522)). Qed.
Lemma lem1990525 (x : real) : (term130 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem1990526 : term62 = term24.
Proof. exact (@lem1990525 term24). Qed.
Lemma lem1990527 : term113 = term24.
Proof. exact (TRANS (@lem1990523) (@lem1990526)). Qed.
Lemma lem1990528 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1990529 : term131 = term127.
Proof. exact (MK_COMB (@lem1990528) (@lem1990527)). Qed.
Lemma lem1990530 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1990531 (x : real) : (term106 x) = (term132 x).
Proof. exact (MK_COMB (@lem1990529) (@lem1990530 x)). Qed.
Lemma lem1990532 (x : real) : (term142 x) = (term132 x).
Proof. exact (TRANS (@lem1990429 x) (@lem1990531 x)). Qed.
Lemma lem1990533 (x : real) : (term132 x) = term24.
Proof. exact (@lem1982719 x). Qed.
Lemma lem1990534 (x : real) : (term142 x) = term24.
Proof. exact (TRANS (@lem1990532 x) (@lem1990533 x)). Qed.
Lemma lem1990535 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1990536 (x : real) : (term143 x) = term144.
Proof. exact (MK_COMB (@lem1990535) (@lem1990534 x)). Qed.
Lemma lem1990537 (y : real) : (term105 y) = (term106 y).
Proof. exact (@lem1982713 term107 y). Qed.
Lemma lem1990539 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1990540 : term58 = term60.
Proof. exact (@lem1990539 term61). Qed.
Lemma lem1990542 (x : nat) : (term108 x) = (term109 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1990543 : term107 = term110.
Proof. exact (@lem1990542 term61). Qed.
Lemma lem1990544 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1990545 : term111 = term112.
Proof. exact (MK_COMB (@lem1990544) (@lem1990543)). Qed.
Lemma lem1990546 : term113 = term114.
Proof. exact (MK_COMB (@lem1990545) (@lem1990540)). Qed.
Lemma lem1990547 : term115.
Proof. exact (@lem1981473 term107 term58 term58 term58 term24 term58). Qed.
Lemma lem1990549 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1990550 : term57 = term68.
Proof. exact (@lem1990549 (NUMERAL 0) term61). Qed.
Lemma lem1990551 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1990552 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1990553 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1990552 h1) (fun h1 : term68 = True => @lem1990551)). Qed.
Lemma lem1990554 : term68 = True.
Proof. exact (EQ_MP (@lem1990553) (@lem1990551)). Qed.
Lemma lem1990555 : term57 = True.
Proof. exact (TRANS (@lem1990550) (@lem1990554)). Qed.
Lemma lem1990556 : True = term57.
Proof. exact (SYM (@lem1990555)). Qed.
Lemma lem1990557 : term57.
Proof. exact (EQ_MP (@lem1990556) (@lem0)). Qed.
Lemma lem1990558 : term116.
Proof. exact (@lem1990547 (@lem1990557)). Qed.
Lemma lem1990560 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1990561 : term57 = term68.
Proof. exact (@lem1990560 (NUMERAL 0) term61). Qed.
Lemma lem1990562 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1990563 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1990564 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1990563 h1) (fun h1 : term68 = True => @lem1990562)). Qed.
Lemma lem1990565 : term68 = True.
Proof. exact (EQ_MP (@lem1990564) (@lem1990562)). Qed.
Lemma lem1990566 : term57 = True.
Proof. exact (TRANS (@lem1990561) (@lem1990565)). Qed.
Lemma lem1990567 : True = term57.
Proof. exact (SYM (@lem1990566)). Qed.
Lemma lem1990568 : term57.
Proof. exact (EQ_MP (@lem1990567) (@lem0)). Qed.
Lemma lem1990569 : term117.
Proof. exact (@lem1990558 (@lem1990568)). Qed.
Lemma lem1990571 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1990572 : term57 = term68.
Proof. exact (@lem1990571 (NUMERAL 0) term61). Qed.
Lemma lem1990573 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1990574 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1990575 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1990574 h1) (fun h1 : term68 = True => @lem1990573)). Qed.
Lemma lem1990576 : term68 = True.
Proof. exact (EQ_MP (@lem1990575) (@lem1990573)). Qed.
Lemma lem1990577 : term57 = True.
Proof. exact (TRANS (@lem1990572) (@lem1990576)). Qed.
Lemma lem1990578 : True = term57.
Proof. exact (SYM (@lem1990577)). Qed.
Lemma lem1990579 : term57.
Proof. exact (EQ_MP (@lem1990578) (@lem0)). Qed.
Lemma lem1990580 : term118.
Proof. exact (@lem1990569 (@lem1990579)). Qed.
Lemma lem1990582 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1990583 : term74 = term75.
Proof. exact (@lem1990582 term61 term61). Qed.
Lemma lem1990584 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1990585 : term77 = term61.
Proof. exact (EQ_MP (@lem1990584) (@lem940073)). Qed.
Lemma lem1990586 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1990587 : term75 = term58.
Proof. exact (MK_COMB (@lem1990586) (@lem1990585)). Qed.
Lemma lem1990588 : term74 = term58.
Proof. exact (TRANS (@lem1990583) (@lem1990587)). Qed.
Lemma lem1990590 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1990591 : term121 = term122.
Proof. exact (@lem1990590 term61 term61). Qed.
Lemma lem1990592 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1990593 : term77 = term61.
Proof. exact (EQ_MP (@lem1990592) (@lem940073)). Qed.
Lemma lem1990594 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1990595 : term75 = term58.
Proof. exact (MK_COMB (@lem1990594) (@lem1990593)). Qed.
Lemma lem1990596 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1990597 : term122 = term107.
Proof. exact (MK_COMB (@lem1990596) (@lem1990595)). Qed.
Lemma lem1990598 : term121 = term107.
Proof. exact (TRANS (@lem1990591) (@lem1990597)). Qed.
Lemma lem1990599 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1990600 : term123 = term111.
Proof. exact (MK_COMB (@lem1990599) (@lem1990598)). Qed.
Lemma lem1990601 : term124 = term113.
Proof. exact (MK_COMB (@lem1990600) (@lem1990588)). Qed.
Lemma lem1990603 (m : nat) : (term125 m) = term24.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1990604 : term113 = term24.
Proof. exact (@lem1990603 term61). Qed.
Lemma lem1990605 : term124 = term24.
Proof. exact (TRANS (@lem1990601) (@lem1990604)). Qed.
Lemma lem1990606 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1990607 : term126 = term127.
Proof. exact (MK_COMB (@lem1990606) (@lem1990605)). Qed.
Lemma lem1990608 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1990609 : term128 = term79.
Proof. exact (MK_COMB (@lem1990607) (@lem1990608)). Qed.
Lemma lem1990611 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1990612 : term79 = term24.
Proof. exact (@lem1990611 term61). Qed.
Lemma lem1990613 : term128 = term24.
Proof. exact (TRANS (@lem1990609) (@lem1990612)). Qed.
Lemma lem1990615 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1990616 : term74 = term75.
Proof. exact (@lem1990615 term61 term61). Qed.
Lemma lem1990617 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1990618 : term77 = term61.
Proof. exact (EQ_MP (@lem1990617) (@lem940073)). Qed.
Lemma lem1990619 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1990620 : term75 = term58.
Proof. exact (MK_COMB (@lem1990619) (@lem1990618)). Qed.
Lemma lem1990621 : term74 = term58.
Proof. exact (TRANS (@lem1990616) (@lem1990620)). Qed.
Lemma lem1990622 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem1990623 : term129 = term79.
Proof. exact (MK_COMB (@lem1990622) (@lem1990621)). Qed.
Lemma lem1990625 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1990626 : term79 = term24.
Proof. exact (@lem1990625 term61). Qed.
Lemma lem1990627 : term129 = term24.
Proof. exact (TRANS (@lem1990623) (@lem1990626)). Qed.
Lemma lem1990628 : term24 = term129.
Proof. exact (SYM (@lem1990627)). Qed.
Lemma lem1990629 : term128 = term129.
Proof. exact (TRANS (@lem1990613) (@lem1990628)). Qed.
Lemma lem1990630 : term114 = term62.
Proof. exact (@lem1990580 (@lem1990629)). Qed.
Lemma lem1990631 : term113 = term62.
Proof. exact (TRANS (@lem1990546) (@lem1990630)). Qed.
Lemma lem1990633 (x : real) : (term130 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem1990634 : term62 = term24.
Proof. exact (@lem1990633 term24). Qed.
Lemma lem1990635 : term113 = term24.
Proof. exact (TRANS (@lem1990631) (@lem1990634)). Qed.
Lemma lem1990636 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1990637 : term131 = term127.
Proof. exact (MK_COMB (@lem1990636) (@lem1990635)). Qed.
Lemma lem1990638 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1990639 (y : real) : (term106 y) = (term132 y).
Proof. exact (MK_COMB (@lem1990637) (@lem1990638 y)). Qed.
Lemma lem1990640 (y : real) : (term105 y) = (term132 y).
Proof. exact (TRANS (@lem1990537 y) (@lem1990639 y)). Qed.
Lemma lem1990641 (y : real) : (term132 y) = term24.
Proof. exact (@lem1982719 y). Qed.
Lemma lem1990642 (y : real) : (term105 y) = term24.
Proof. exact (TRANS (@lem1990640 y) (@lem1990641 y)). Qed.
Lemma lem1990643 (x : real) (y : real) : (term141 x y) = term145.
Proof. exact (MK_COMB (@lem1990536 x) (@lem1990642 y)). Qed.
Lemma lem1990644 (x : real) (y : real) : (term140 x y) = term145.
Proof. exact (TRANS (@lem1990428 x y) (@lem1990643 x y)). Qed.
Lemma lem1990645 : term145 = term24.
Proof. exact (@lem1982721 term24). Qed.
Lemma lem1990646 (x : real) (y : real) : (term140 x y) = term24.
Proof. exact (TRANS (@lem1990644 x y) (@lem1990645)). Qed.
Lemma lem1990647 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1990648 (x : real) (y : real) : (term146 x y) = term147.
Proof. exact (MK_COMB (@lem1990647) (@lem1990646 x y)). Qed.
Lemma lem1990649 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1990650 (x : real) (y : real) : (term139 x y) = term148.
Proof. exact (MK_COMB (@lem1990648 x y) (@lem1990649)). Qed.
Lemma lem1990651 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term148.
Proof. exact (EQ_MP (@lem1990650 x y) (@lem1990427 y x z h1)). Qed.
Lemma lem1990653 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1990654 : term148 = term149.
Proof. exact (@lem1990653 term24 term24). Qed.
Lemma lem1990656 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1990657 : term24 = term62.
Proof. exact (@lem1990656 (NUMERAL 0)). Qed.
Lemma lem1990659 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1990660 : term24 = term62.
Proof. exact (@lem1990659 (NUMERAL 0)). Qed.
Lemma lem1990661 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1990662 : term63 = term64.
Proof. exact (MK_COMB (@lem1990661) (@lem1990660)). Qed.
Lemma lem1990663 : term149 = term150.
Proof. exact (MK_COMB (@lem1990662) (@lem1990657)). Qed.
Lemma lem1990664 : term151.
Proof. exact (@lem1980255 term24 term58 term24 term58). Qed.
Lemma lem1990666 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1990667 : term57 = term68.
Proof. exact (@lem1990666 (NUMERAL 0) term61). Qed.
Lemma lem1990668 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1990669 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1990670 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1990669 h1) (fun h1 : term68 = True => @lem1990668)). Qed.
Lemma lem1990671 : term68 = True.
Proof. exact (EQ_MP (@lem1990670) (@lem1990668)). Qed.
Lemma lem1990672 : term57 = True.
Proof. exact (TRANS (@lem1990667) (@lem1990671)). Qed.
Lemma lem1990673 : True = term57.
Proof. exact (SYM (@lem1990672)). Qed.
Lemma lem1990674 : term57.
Proof. exact (EQ_MP (@lem1990673) (@lem0)). Qed.
Lemma lem1990675 : term152.
Proof. exact (@lem1990664 (@lem1990674)). Qed.
Lemma lem1990677 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1990678 : term57 = term68.
Proof. exact (@lem1990677 (NUMERAL 0) term61). Qed.
Lemma lem1990679 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1990680 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1990681 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1990680 h1) (fun h1 : term68 = True => @lem1990679)). Qed.
Lemma lem1990682 : term68 = True.
Proof. exact (EQ_MP (@lem1990681) (@lem1990679)). Qed.
Lemma lem1990683 : term57 = True.
Proof. exact (TRANS (@lem1990678) (@lem1990682)). Qed.
Lemma lem1990684 : True = term57.
Proof. exact (SYM (@lem1990683)). Qed.
Lemma lem1990685 : term57.
Proof. exact (EQ_MP (@lem1990684) (@lem0)). Qed.
Lemma lem1990686 : term150 = term153.
Proof. exact (@lem1990675 (@lem1990685)). Qed.
Lemma lem1990688 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1990689 : term79 = term24.
Proof. exact (@lem1990688 term61). Qed.
Lemma lem1990691 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1990692 : term79 = term24.
Proof. exact (@lem1990691 term61). Qed.
Lemma lem1990693 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1990694 : term80 = term63.
Proof. exact (MK_COMB (@lem1990693) (@lem1990692)). Qed.
Lemma lem1990695 : term153 = term149.
Proof. exact (MK_COMB (@lem1990694) (@lem1990689)). Qed.
Lemma lem1990697 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1990698 : term149 = term154.
Proof. exact (@lem1990697 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1990699 : term154 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1990700 : term149 = False.
Proof. exact (TRANS (@lem1990698) (@lem1990699)). Qed.
Lemma lem1990701 : term153 = False.
Proof. exact (TRANS (@lem1990695) (@lem1990700)). Qed.
Lemma lem1990702 : term150 = False.
Proof. exact (TRANS (@lem1990686) (@lem1990701)). Qed.
Lemma lem1990703 : term149 = False.
Proof. exact (TRANS (@lem1990663) (@lem1990702)). Qed.
Lemma lem1990704 : term148 = False.
Proof. exact (TRANS (@lem1990654) (@lem1990703)). Qed.
Lemma lem1990705 (y : real) (x : real) (z : real) (h1 : term52 y x z) : False.
Proof. exact (EQ_MP (@lem1990704) (@lem1990651 y x z h1)). Qed.
Lemma lem1990707 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term52 y x z.
Proof. exact (h1). Qed.
Lemma lem1990708 (y : real) (x : real) (z : real) (h1 : term52 y x z) : (term52 y x z) = False.
Proof. exact (prop_ext (fun h2 : term52 y x z => @lem1990705 y x z h1) (fun h2 : False => @lem1990707 y x z h1)). Qed.
Lemma lem1990709 (y : real) (x : real) (z : real) (h1 : term52 y x z) : False.
Proof. exact (EQ_MP (@lem1990708 y x z h1) (@lem1990707 y x z h1)). Qed.
Lemma lem1990710 (y : real) (x : real) (h1 : term55 y x) : term55 y x.
Proof. exact (h1). Qed.
Lemma lem1990711 (y : real) (x : real) (h1 : term55 y x) : False.
Proof. exact (ex_elim (@lem1990710 y x h1) (fun z : real => fun h0 : term54 y x z => @lem1990709 y x z h0)). Qed.
Lemma lem1990712 (y : real) (x : real) (h1 : term16 y x) : term16 y x.
Proof. exact (h1). Qed.
Lemma lem1990713 (y : real) (x : real) (h1 : term16 y x) : term55 y x.
Proof. exact (EQ_MP (@lem1989992 y x) (@lem1990712 y x h1)). Qed.
Lemma lem1990714 (y : real) (x : real) (h1 : term16 y x) : (term55 y x) = False.
Proof. exact (prop_ext (fun h2 : term55 y x => @lem1990711 y x h2) (fun h2 : False => @lem1990713 y x h1)). Qed.
Lemma lem1990715 (y : real) (x : real) (h1 : term16 y x) : False.
Proof. exact (EQ_MP (@lem1990714 y x h1) (@lem1990713 y x h1)). Qed.
Lemma lem1990716 (y : real) (x : real) : term155 y x.
Proof. exact (fun h0 : term16 y x => @lem1990715 y x h0). Qed.
Lemma lem1990717 (y : real) (x : real) : term156 y x.
Proof. exact (@lem1386578 (term157 y x)). Qed.
Lemma lem1990720 (y : real) (x : real) : term157 y x.
Proof. exact (@lem1990717 y x (@lem1990716 y x)). Qed.
Lemma lem1990721 (y : real) (x : real) (h1 : term17 y x) : term17 y x.
Proof. exact (h1). Qed.
Lemma lem1990722 (y : real) (x : real) (h1 : term17 y x) : term158 x y.
Proof. exact (@lem1990721 y x h1 (term159 x y)). Qed.
Lemma lem1990723 (x : real) (y : real) : (term158 x y) = (term160 x y).
Proof. exact (eq_refl (term158 x y)). Qed.
Lemma lem1990724 (y : real) (x : real) (h1 : term17 y x) : term160 x y.
Proof. exact (EQ_MP (@lem1990723 x y) (@lem1990722 y x h1)). Qed.
Lemma lem1990739 (x : real) (y : real) : (term160 x y) = (term161 x y).
Proof. exact (@lem17265 (term162 x y) (term163 x y)). Qed.
Lemma lem1990740 (x : real) (y : real) : (term30 x y) = (term30 x y).
Proof. exact (eq_refl (term30 x y)). Qed.
Lemma lem1990741 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1990742 (x : real) (y : real) : (term164 x y) = (term165 x y).
Proof. exact (MK_COMB (@lem1990741) (@lem1990739 x y)). Qed.
Lemma lem1990743 (x : real) (y : real) : (term166 x y) = (term167 x y).
Proof. exact (MK_COMB (@lem1990742 x y) (@lem1990740 x y)). Qed.
Lemma lem1990744 (x : real) (y : real) : (term168 x y) = (term166 x y).
Proof. exact (@lem17362 (term160 x y) (real_le x y)). Qed.
Lemma lem1990760 (x : real) (y : real) : (term168 x y) = (term167 x y).
Proof. exact (TRANS (@lem1990744 x y) (@lem1990743 x y)). Qed.
Lemma lem1990761 (x : real) (y : real) : (term169 x y) = (term170 x y).
Proof. exact (@lem1988295 y (term159 x y)). Qed.
Lemma lem1990763 (x : real) (y : real) : (real_div x y) = (term171 x y).
Proof. exact (EQ_MP (@lem1982797 x y) (@lem1982796 x y)). Qed.
Lemma lem1990764 (x : real) (y : real) : (term172 x y) = (term173 x y).
Proof. exact (@lem1990763 (real_sub x y) term174). Qed.
Lemma lem1990769 (n : nat) : (term175 n) = (term176 n).
Proof. exact (proj1 (@lem1981223 n (@el nat))). Qed.
Lemma lem1990771 : term177 = term178.
Proof. exact (@lem1990769 term179). Qed.
Lemma lem1990784 (x : real) (y : real) : (real_sub x y) = (term19 x y).
Proof. exact (@lem1982792 x y). Qed.
Lemma lem1990785 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1990786 (x : real) (y : real) : (term180 x y) = (term181 x y).
Proof. exact (MK_COMB (@lem1990785) (@lem1990784 x y)). Qed.
Lemma lem1990787 (x : real) (y : real) : (term173 x y) = (term182 x y).
Proof. exact (MK_COMB (@lem1990786 x y) (@lem1990771)). Qed.
Lemma lem1990788 (x : real) (y : real) : (term182 x y) = (term183 x y).
Proof. exact (@lem1982725 term178 (term19 x y)). Qed.
Lemma lem1990789 (x : real) (y : real) : (term183 x y) = (term184 x y).
Proof. exact (@lem1982781 x term178 (term21 y)). Qed.
Lemma lem1990790 (y : real) : (term185 y) = (term186 y).
Proof. exact (@lem1982749 term178 term107 y). Qed.
Lemma lem1990792 (x : nat) : (term108 x) = (term109 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1990793 : term107 = term110.
Proof. exact (@lem1990792 term61). Qed.
Lemma lem1990796 : term187 = term187.
Proof. exact (eq_refl term187). Qed.
Lemma lem1990797 : term188 = term189.
Proof. exact (MK_COMB (@lem1990796) (@lem1990793)). Qed.
Lemma lem1990798 : term189 = term190.
Proof. exact (@lem1981613 term58 term107 term174 term58). Qed.
Lemma lem1990800 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1990801 : term191 = term192.
Proof. exact (@lem1990800 term179 term61). Qed.
Lemma lem1990802 : term193 = term194.
Proof. exact (@lem996237 term194). Qed.
Lemma lem1990803 : (term193 = term194) = (term195 = term179).
Proof. exact (@lem1007663 term194 (BIT1 0) term194). Qed.
Lemma lem1990804 : term195 = term179.
Proof. exact (EQ_MP (@lem1990803) (@lem1990802)). Qed.
Lemma lem1990805 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1990806 : term192 = term174.
Proof. exact (MK_COMB (@lem1990805) (@lem1990804)). Qed.
Lemma lem1990807 : term191 = term174.
Proof. exact (TRANS (@lem1990801) (@lem1990806)). Qed.
Lemma lem1990809 (m : nat) (n : nat) : (term196 m n) = (term120 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1990810 : term197 = term122.
Proof. exact (@lem1990809 term61 term61). Qed.
Lemma lem1990811 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1990812 : term77 = term61.
Proof. exact (EQ_MP (@lem1990811) (@lem940073)). Qed.
Lemma lem1990813 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1990814 : term75 = term58.
Proof. exact (MK_COMB (@lem1990813) (@lem1990812)). Qed.
Lemma lem1990815 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1990816 : term122 = term107.
Proof. exact (MK_COMB (@lem1990815) (@lem1990814)). Qed.
Lemma lem1990817 : term197 = term107.
Proof. exact (TRANS (@lem1990810) (@lem1990816)). Qed.
Lemma lem1990818 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem1990819 : term198 = term199.
Proof. exact (MK_COMB (@lem1990818) (@lem1990817)). Qed.
Lemma lem1990820 : term190 = term200.
Proof. exact (MK_COMB (@lem1990819) (@lem1990807)). Qed.
Lemma lem1990821 : term189 = term200.
Proof. exact (TRANS (@lem1990798) (@lem1990820)). Qed.
Lemma lem1990824 : term188 = term200.
Proof. exact (TRANS (@lem1990797) (@lem1990821)). Qed.
Lemma lem1990825 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1990826 : term201 = term202.
Proof. exact (MK_COMB (@lem1990825) (@lem1990824)). Qed.
Lemma lem1990827 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1990828 (y : real) : (term186 y) = (term203 y).
Proof. exact (MK_COMB (@lem1990826) (@lem1990827 y)). Qed.
Lemma lem1990829 (y : real) : (term185 y) = (term203 y).
Proof. exact (TRANS (@lem1990790 y) (@lem1990828 y)). Qed.
Lemma lem1990832 (x : real) : (term204 x) = (term204 x).
Proof. exact (eq_refl (term204 x)). Qed.
Lemma lem1990833 (x : real) (y : real) : (term184 x y) = (term205 x y).
Proof. exact (MK_COMB (@lem1990832 x) (@lem1990829 y)). Qed.
Lemma lem1990834 (x : real) (y : real) : (term183 x y) = (term205 x y).
Proof. exact (TRANS (@lem1990789 x y) (@lem1990833 x y)). Qed.
Lemma lem1990835 (x : real) (y : real) : (term182 x y) = (term205 x y).
Proof. exact (TRANS (@lem1990788 x y) (@lem1990834 x y)). Qed.
Lemma lem1990836 (x : real) (y : real) : (term173 x y) = (term205 x y).
Proof. exact (TRANS (@lem1990787 x y) (@lem1990835 x y)). Qed.
Lemma lem1990837 (x : real) (y : real) : (term172 x y) = (term205 x y).
Proof. exact (TRANS (@lem1990764 x y) (@lem1990836 x y)). Qed.
Lemma lem1990840 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1990841 (x : real) (y : real) : (term159 x y) = (term206 x y).
Proof. exact (MK_COMB (@lem1990840 y) (@lem1990837 x y)). Qed.
Lemma lem1990842 (x : real) (y : real) : (term206 x y) = (term207 x y).
Proof. exact (@lem1982757 (term208 x) y (term203 y)). Qed.
Lemma lem1990843 (y : real) : (term209 y) = (term210 y).
Proof. exact (@lem1982715 term200 y). Qed.
Lemma lem1990845 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1990846 : term58 = term60.
Proof. exact (@lem1990845 term61). Qed.
Lemma lem1990849 : term211 = term211.
Proof. exact (eq_refl term211). Qed.
Lemma lem1990850 : term212 = term213.
Proof. exact (MK_COMB (@lem1990849) (@lem1990846)). Qed.
Lemma lem1990851 : term214.
Proof. exact (@lem1981473 term107 term174 term58 term58 term58 term174). Qed.
Lemma lem1990853 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1990854 : term215 = term216.
Proof. exact (@lem1990853 (NUMERAL 0) term179). Qed.
Lemma lem1990855 : term217 = term194.
Proof. exact (@lem912803). Qed.
Lemma lem1990856 (h1 : term217 = term194) : term216 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term194 h1). Qed.
Lemma lem1990857 : (term217 = term194) = (term216 = True).
Proof. exact (prop_ext (fun h1 : term217 = term194 => @lem1990856 h1) (fun h1 : term216 = True => @lem1990855)). Qed.
Lemma lem1990858 : term216 = True.
Proof. exact (EQ_MP (@lem1990857) (@lem1990855)). Qed.
Lemma lem1990859 : term215 = True.
Proof. exact (TRANS (@lem1990854) (@lem1990858)). Qed.
Lemma lem1990860 : True = term215.
Proof. exact (SYM (@lem1990859)). Qed.
Lemma lem1990861 : term215.
Proof. exact (EQ_MP (@lem1990860) (@lem0)). Qed.
Lemma lem1990862 : term218.
Proof. exact (@lem1990851 (@lem1990861)). Qed.
Lemma lem1990864 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1990865 : term57 = term68.
Proof. exact (@lem1990864 (NUMERAL 0) term61). Qed.
Lemma lem1990866 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1990867 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1990868 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1990867 h1) (fun h1 : term68 = True => @lem1990866)). Qed.
Lemma lem1990869 : term68 = True.
Proof. exact (EQ_MP (@lem1990868) (@lem1990866)). Qed.
Lemma lem1990870 : term57 = True.
Proof. exact (TRANS (@lem1990865) (@lem1990869)). Qed.
Lemma lem1990871 : True = term57.
Proof. exact (SYM (@lem1990870)). Qed.
Lemma lem1990872 : term57.
Proof. exact (EQ_MP (@lem1990871) (@lem0)). Qed.
Lemma lem1990873 : term219.
Proof. exact (@lem1990862 (@lem1990872)). Qed.
Lemma lem1990875 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1990876 : term215 = term216.
Proof. exact (@lem1990875 (NUMERAL 0) term179). Qed.
Lemma lem1990877 : term217 = term194.
Proof. exact (@lem912803). Qed.
Lemma lem1990878 (h1 : term217 = term194) : term216 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term194 h1). Qed.
Lemma lem1990879 : (term217 = term194) = (term216 = True).
Proof. exact (prop_ext (fun h1 : term217 = term194 => @lem1990878 h1) (fun h1 : term216 = True => @lem1990877)). Qed.
Lemma lem1990880 : term216 = True.
Proof. exact (EQ_MP (@lem1990879) (@lem1990877)). Qed.
Lemma lem1990881 : term215 = True.
Proof. exact (TRANS (@lem1990876) (@lem1990880)). Qed.
Lemma lem1990882 : True = term215.
Proof. exact (SYM (@lem1990881)). Qed.
Lemma lem1990883 : term215.
Proof. exact (EQ_MP (@lem1990882) (@lem0)). Qed.
Lemma lem1990884 : term220.
Proof. exact (@lem1990873 (@lem1990883)). Qed.
Lemma lem1990886 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1990887 : term221 = term222.
Proof. exact (@lem1990886 term61 term179). Qed.
Lemma lem1990888 : term223 = term194.
Proof. exact (@lem996238 term194). Qed.
Lemma lem1990889 : (term223 = term194) = (term224 = term179).
Proof. exact (@lem1007663 (BIT1 0) term194 term194). Qed.
Lemma lem1990890 : term224 = term179.
Proof. exact (EQ_MP (@lem1990889) (@lem1990888)). Qed.
Lemma lem1990891 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1990892 : term222 = term174.
Proof. exact (MK_COMB (@lem1990891) (@lem1990890)). Qed.
Lemma lem1990893 : term221 = term174.
Proof. exact (TRANS (@lem1990887) (@lem1990892)). Qed.
Lemma lem1990895 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1990896 : term121 = term122.
Proof. exact (@lem1990895 term61 term61). Qed.
Lemma lem1990897 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1990898 : term77 = term61.
Proof. exact (EQ_MP (@lem1990897) (@lem940073)). Qed.
Lemma lem1990899 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1990900 : term75 = term58.
Proof. exact (MK_COMB (@lem1990899) (@lem1990898)). Qed.
Lemma lem1990901 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1990902 : term122 = term107.
Proof. exact (MK_COMB (@lem1990901) (@lem1990900)). Qed.
Lemma lem1990903 : term121 = term107.
Proof. exact (TRANS (@lem1990896) (@lem1990902)). Qed.
Lemma lem1990904 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1990905 : term123 = term111.
Proof. exact (MK_COMB (@lem1990904) (@lem1990903)). Qed.
Lemma lem1990906 : term225 = term226.
Proof. exact (MK_COMB (@lem1990905) (@lem1990893)). Qed.
Lemma lem1990909 : term227 = term58.
Proof. exact (@lem1367765 term61 term61). Qed.
Lemma lem1990910 : term228 = term194.
Proof. exact (@lem706885). Qed.
Lemma lem1990911 : (term228 = term194) = (term229 = term179).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term194). Qed.
Lemma lem1990912 : term229 = term179.
Proof. exact (EQ_MP (@lem1990911) (@lem1990910)). Qed.
Lemma lem1990913 : term179 = term229.
Proof. exact (SYM (@lem1990912)). Qed.
Lemma lem1990914 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1990915 : term174 = term230.
Proof. exact (MK_COMB (@lem1990914) (@lem1990913)). Qed.
Lemma lem1990916 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem1990917 : term226 = term227.
Proof. exact (MK_COMB (@lem1990916) (@lem1990915)). Qed.
Lemma lem1990918 : term226 = term58.
Proof. exact (TRANS (@lem1990917) (@lem1990909)). Qed.
Lemma lem1990919 : term225 = term58.
Proof. exact (TRANS (@lem1990906) (@lem1990918)). Qed.
Lemma lem1990920 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1990921 : term231 = term232.
Proof. exact (MK_COMB (@lem1990920) (@lem1990919)). Qed.
Lemma lem1990922 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem1990923 : term233 = term221.
Proof. exact (MK_COMB (@lem1990921) (@lem1990922)). Qed.
Lemma lem1990925 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1990926 : term221 = term222.
Proof. exact (@lem1990925 term61 term179). Qed.
Lemma lem1990927 : term223 = term194.
Proof. exact (@lem996238 term194). Qed.
Lemma lem1990928 : (term223 = term194) = (term224 = term179).
Proof. exact (@lem1007663 (BIT1 0) term194 term194). Qed.
Lemma lem1990929 : term224 = term179.
Proof. exact (EQ_MP (@lem1990928) (@lem1990927)). Qed.
Lemma lem1990930 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1990931 : term222 = term174.
Proof. exact (MK_COMB (@lem1990930) (@lem1990929)). Qed.
Lemma lem1990932 : term221 = term174.
Proof. exact (TRANS (@lem1990926) (@lem1990931)). Qed.
Lemma lem1990933 : term233 = term174.
Proof. exact (TRANS (@lem1990923) (@lem1990932)). Qed.
Lemma lem1990935 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1990936 : term191 = term192.
Proof. exact (@lem1990935 term179 term61). Qed.
Lemma lem1990937 : term193 = term194.
Proof. exact (@lem996237 term194). Qed.
Lemma lem1990938 : (term193 = term194) = (term195 = term179).
Proof. exact (@lem1007663 term194 (BIT1 0) term194). Qed.
Lemma lem1990939 : term195 = term179.
Proof. exact (EQ_MP (@lem1990938) (@lem1990937)). Qed.
Lemma lem1990940 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1990941 : term192 = term174.
Proof. exact (MK_COMB (@lem1990940) (@lem1990939)). Qed.
Lemma lem1990942 : term191 = term174.
Proof. exact (TRANS (@lem1990936) (@lem1990941)). Qed.
Lemma lem1990943 : term232 = term232.
Proof. exact (eq_refl term232). Qed.
Lemma lem1990944 : term234 = term221.
Proof. exact (MK_COMB (@lem1990943) (@lem1990942)). Qed.
Lemma lem1990946 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1990947 : term221 = term222.
Proof. exact (@lem1990946 term61 term179). Qed.
Lemma lem1990948 : term223 = term194.
Proof. exact (@lem996238 term194). Qed.
Lemma lem1990949 : (term223 = term194) = (term224 = term179).
Proof. exact (@lem1007663 (BIT1 0) term194 term194). Qed.
Lemma lem1990950 : term224 = term179.
Proof. exact (EQ_MP (@lem1990949) (@lem1990948)). Qed.
Lemma lem1990951 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1990952 : term222 = term174.
Proof. exact (MK_COMB (@lem1990951) (@lem1990950)). Qed.
Lemma lem1990953 : term221 = term174.
Proof. exact (TRANS (@lem1990947) (@lem1990952)). Qed.
Lemma lem1990954 : term234 = term174.
Proof. exact (TRANS (@lem1990944) (@lem1990953)). Qed.
Lemma lem1990955 : term174 = term234.
Proof. exact (SYM (@lem1990954)). Qed.
Lemma lem1990956 : term233 = term234.
Proof. exact (TRANS (@lem1990933) (@lem1990955)). Qed.
Lemma lem1990957 : term213 = term178.
Proof. exact (@lem1990884 (@lem1990956)). Qed.
Lemma lem1990960 : term212 = term178.
Proof. exact (TRANS (@lem1990850) (@lem1990957)). Qed.
Lemma lem1990961 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1990962 : term235 = term187.
Proof. exact (MK_COMB (@lem1990961) (@lem1990960)). Qed.
Lemma lem1990963 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1990964 (y : real) : (term210 y) = (term208 y).
Proof. exact (MK_COMB (@lem1990962) (@lem1990963 y)). Qed.
Lemma lem1990965 (y : real) : (term209 y) = (term208 y).
Proof. exact (TRANS (@lem1990843 y) (@lem1990964 y)). Qed.
Lemma lem1990966 (x : real) : (term204 x) = (term204 x).
Proof. exact (eq_refl (term204 x)). Qed.
Lemma lem1990967 (x : real) (y : real) : (term207 x y) = (term236 x y).
Proof. exact (MK_COMB (@lem1990966 x) (@lem1990965 y)). Qed.
Lemma lem1990968 (x : real) (y : real) : (term206 x y) = (term236 x y).
Proof. exact (TRANS (@lem1990842 x y) (@lem1990967 x y)). Qed.
Lemma lem1990969 (x : real) (y : real) : (term159 x y) = (term236 x y).
Proof. exact (TRANS (@lem1990841 x y) (@lem1990968 x y)). Qed.
Lemma lem1990972 (y : real) : (real_sub y) = (real_sub y).
Proof. exact (eq_refl (real_sub y)). Qed.
Lemma lem1990973 (x : real) (y : real) : (term237 x y) = (term238 x y).
Proof. exact (MK_COMB (@lem1990972 y) (@lem1990969 x y)). Qed.
Lemma lem1990974 (x : real) (y : real) : (term238 x y) = (term239 x y).
Proof. exact (@lem1982792 y (term236 x y)). Qed.
Lemma lem1990975 (x : real) (y : real) : (term240 x y) = (term241 x y).
Proof. exact (@lem1982781 (term208 x) term107 (term208 y)). Qed.
Lemma lem1990976 (y : real) : (term242 y) = (term243 y).
Proof. exact (@lem1982749 term107 term178 y). Qed.
Lemma lem1990977 : term178 = term178.
Proof. exact (eq_refl term178). Qed.
Lemma lem1990979 (x : nat) : (term108 x) = (term109 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1990980 : term107 = term110.
Proof. exact (@lem1990979 term61). Qed.
Lemma lem1990981 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1990982 : term244 = term245.
Proof. exact (MK_COMB (@lem1990981) (@lem1990980)). Qed.
Lemma lem1990983 : term246 = term247.
Proof. exact (MK_COMB (@lem1990982) (@lem1990977)). Qed.
Lemma lem1990984 : term247 = term248.
Proof. exact (@lem1981613 term107 term58 term58 term174). Qed.
Lemma lem1990986 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1990987 : term221 = term222.
Proof. exact (@lem1990986 term61 term179). Qed.
Lemma lem1990988 : term223 = term194.
Proof. exact (@lem996238 term194). Qed.
Lemma lem1990989 : (term223 = term194) = (term224 = term179).
Proof. exact (@lem1007663 (BIT1 0) term194 term194). Qed.
Lemma lem1990990 : term224 = term179.
Proof. exact (EQ_MP (@lem1990989) (@lem1990988)). Qed.
Lemma lem1990991 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1990992 : term222 = term174.
Proof. exact (MK_COMB (@lem1990991) (@lem1990990)). Qed.
Lemma lem1990993 : term221 = term174.
Proof. exact (TRANS (@lem1990987) (@lem1990992)). Qed.
Lemma lem1990995 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1990996 : term121 = term122.
Proof. exact (@lem1990995 term61 term61). Qed.
Lemma lem1990997 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1990998 : term77 = term61.
Proof. exact (EQ_MP (@lem1990997) (@lem940073)). Qed.
Lemma lem1990999 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991000 : term75 = term58.
Proof. exact (MK_COMB (@lem1990999) (@lem1990998)). Qed.
Lemma lem1991001 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1991002 : term122 = term107.
Proof. exact (MK_COMB (@lem1991001) (@lem1991000)). Qed.
Lemma lem1991003 : term121 = term107.
Proof. exact (TRANS (@lem1990996) (@lem1991002)). Qed.
Lemma lem1991004 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem1991005 : term249 = term199.
Proof. exact (MK_COMB (@lem1991004) (@lem1991003)). Qed.
Lemma lem1991006 : term248 = term200.
Proof. exact (MK_COMB (@lem1991005) (@lem1990993)). Qed.
Lemma lem1991007 : term247 = term200.
Proof. exact (TRANS (@lem1990984) (@lem1991006)). Qed.
Lemma lem1991010 : term246 = term200.
Proof. exact (TRANS (@lem1990983) (@lem1991007)). Qed.
Lemma lem1991011 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1991012 : term250 = term202.
Proof. exact (MK_COMB (@lem1991011) (@lem1991010)). Qed.
Lemma lem1991013 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1991014 (y : real) : (term243 y) = (term203 y).
Proof. exact (MK_COMB (@lem1991012) (@lem1991013 y)). Qed.
Lemma lem1991015 (y : real) : (term242 y) = (term203 y).
Proof. exact (TRANS (@lem1990976 y) (@lem1991014 y)). Qed.
Lemma lem1991016 (x : real) : (term242 x) = (term243 x).
Proof. exact (@lem1982749 term107 term178 x). Qed.
Lemma lem1991017 : term178 = term178.
Proof. exact (eq_refl term178). Qed.
Lemma lem1991019 (x : nat) : (term108 x) = (term109 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1991020 : term107 = term110.
Proof. exact (@lem1991019 term61). Qed.
Lemma lem1991021 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1991022 : term244 = term245.
Proof. exact (MK_COMB (@lem1991021) (@lem1991020)). Qed.
Lemma lem1991023 : term246 = term247.
Proof. exact (MK_COMB (@lem1991022) (@lem1991017)). Qed.
Lemma lem1991024 : term247 = term248.
Proof. exact (@lem1981613 term107 term58 term58 term174). Qed.
Lemma lem1991026 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1991027 : term221 = term222.
Proof. exact (@lem1991026 term61 term179). Qed.
Lemma lem1991028 : term223 = term194.
Proof. exact (@lem996238 term194). Qed.
Lemma lem1991029 : (term223 = term194) = (term224 = term179).
Proof. exact (@lem1007663 (BIT1 0) term194 term194). Qed.
Lemma lem1991030 : term224 = term179.
Proof. exact (EQ_MP (@lem1991029) (@lem1991028)). Qed.
Lemma lem1991031 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991032 : term222 = term174.
Proof. exact (MK_COMB (@lem1991031) (@lem1991030)). Qed.
Lemma lem1991033 : term221 = term174.
Proof. exact (TRANS (@lem1991027) (@lem1991032)). Qed.
Lemma lem1991035 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1991036 : term121 = term122.
Proof. exact (@lem1991035 term61 term61). Qed.
Lemma lem1991037 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1991038 : term77 = term61.
Proof. exact (EQ_MP (@lem1991037) (@lem940073)). Qed.
Lemma lem1991039 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991040 : term75 = term58.
Proof. exact (MK_COMB (@lem1991039) (@lem1991038)). Qed.
Lemma lem1991041 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1991042 : term122 = term107.
Proof. exact (MK_COMB (@lem1991041) (@lem1991040)). Qed.
Lemma lem1991043 : term121 = term107.
Proof. exact (TRANS (@lem1991036) (@lem1991042)). Qed.
Lemma lem1991044 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem1991045 : term249 = term199.
Proof. exact (MK_COMB (@lem1991044) (@lem1991043)). Qed.
Lemma lem1991046 : term248 = term200.
Proof. exact (MK_COMB (@lem1991045) (@lem1991033)). Qed.
Lemma lem1991047 : term247 = term200.
Proof. exact (TRANS (@lem1991024) (@lem1991046)). Qed.
Lemma lem1991050 : term246 = term200.
Proof. exact (TRANS (@lem1991023) (@lem1991047)). Qed.
Lemma lem1991051 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1991052 : term250 = term202.
Proof. exact (MK_COMB (@lem1991051) (@lem1991050)). Qed.
Lemma lem1991053 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1991054 (x : real) : (term243 x) = (term203 x).
Proof. exact (MK_COMB (@lem1991052) (@lem1991053 x)). Qed.
Lemma lem1991055 (x : real) : (term242 x) = (term203 x).
Proof. exact (TRANS (@lem1991016 x) (@lem1991054 x)). Qed.
Lemma lem1991056 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1991057 (x : real) : (term251 x) = (term252 x).
Proof. exact (MK_COMB (@lem1991056) (@lem1991055 x)). Qed.
Lemma lem1991058 (x : real) (y : real) : (term241 x y) = (term253 x y).
Proof. exact (MK_COMB (@lem1991057 x) (@lem1991015 y)). Qed.
Lemma lem1991059 (x : real) (y : real) : (term240 x y) = (term253 x y).
Proof. exact (TRANS (@lem1990975 x y) (@lem1991058 x y)). Qed.
Lemma lem1991060 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1991061 (x : real) (y : real) : (term239 x y) = (term254 x y).
Proof. exact (MK_COMB (@lem1991060 y) (@lem1991059 x y)). Qed.
Lemma lem1991062 (x : real) (y : real) : (term254 x y) = (term255 x y).
Proof. exact (@lem1982757 (term203 x) y (term203 y)). Qed.
Lemma lem1991063 (y : real) : (term209 y) = (term210 y).
Proof. exact (@lem1982715 term200 y). Qed.
Lemma lem1991065 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1991066 : term58 = term60.
Proof. exact (@lem1991065 term61). Qed.
Lemma lem1991069 : term211 = term211.
Proof. exact (eq_refl term211). Qed.
Lemma lem1991070 : term212 = term213.
Proof. exact (MK_COMB (@lem1991069) (@lem1991066)). Qed.
Lemma lem1991071 : term214.
Proof. exact (@lem1981473 term107 term174 term58 term58 term58 term174). Qed.
Lemma lem1991073 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1991074 : term215 = term216.
Proof. exact (@lem1991073 (NUMERAL 0) term179). Qed.
Lemma lem1991075 : term217 = term194.
Proof. exact (@lem912803). Qed.
Lemma lem1991076 (h1 : term217 = term194) : term216 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term194 h1). Qed.
Lemma lem1991077 : (term217 = term194) = (term216 = True).
Proof. exact (prop_ext (fun h1 : term217 = term194 => @lem1991076 h1) (fun h1 : term216 = True => @lem1991075)). Qed.
Lemma lem1991078 : term216 = True.
Proof. exact (EQ_MP (@lem1991077) (@lem1991075)). Qed.
Lemma lem1991079 : term215 = True.
Proof. exact (TRANS (@lem1991074) (@lem1991078)). Qed.
Lemma lem1991080 : True = term215.
Proof. exact (SYM (@lem1991079)). Qed.
Lemma lem1991081 : term215.
Proof. exact (EQ_MP (@lem1991080) (@lem0)). Qed.
Lemma lem1991082 : term218.
Proof. exact (@lem1991071 (@lem1991081)). Qed.
Lemma lem1991084 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1991085 : term57 = term68.
Proof. exact (@lem1991084 (NUMERAL 0) term61). Qed.
Lemma lem1991086 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1991087 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1991088 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1991087 h1) (fun h1 : term68 = True => @lem1991086)). Qed.
Lemma lem1991089 : term68 = True.
Proof. exact (EQ_MP (@lem1991088) (@lem1991086)). Qed.
Lemma lem1991090 : term57 = True.
Proof. exact (TRANS (@lem1991085) (@lem1991089)). Qed.
Lemma lem1991091 : True = term57.
Proof. exact (SYM (@lem1991090)). Qed.
Lemma lem1991092 : term57.
Proof. exact (EQ_MP (@lem1991091) (@lem0)). Qed.
Lemma lem1991093 : term219.
Proof. exact (@lem1991082 (@lem1991092)). Qed.
Lemma lem1991095 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1991096 : term215 = term216.
Proof. exact (@lem1991095 (NUMERAL 0) term179). Qed.
Lemma lem1991097 : term217 = term194.
Proof. exact (@lem912803). Qed.
Lemma lem1991098 (h1 : term217 = term194) : term216 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term194 h1). Qed.
Lemma lem1991099 : (term217 = term194) = (term216 = True).
Proof. exact (prop_ext (fun h1 : term217 = term194 => @lem1991098 h1) (fun h1 : term216 = True => @lem1991097)). Qed.
Lemma lem1991100 : term216 = True.
Proof. exact (EQ_MP (@lem1991099) (@lem1991097)). Qed.
Lemma lem1991101 : term215 = True.
Proof. exact (TRANS (@lem1991096) (@lem1991100)). Qed.
Lemma lem1991102 : True = term215.
Proof. exact (SYM (@lem1991101)). Qed.
Lemma lem1991103 : term215.
Proof. exact (EQ_MP (@lem1991102) (@lem0)). Qed.
Lemma lem1991104 : term220.
Proof. exact (@lem1991093 (@lem1991103)). Qed.
Lemma lem1991106 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1991107 : term221 = term222.
Proof. exact (@lem1991106 term61 term179). Qed.
Lemma lem1991108 : term223 = term194.
Proof. exact (@lem996238 term194). Qed.
Lemma lem1991109 : (term223 = term194) = (term224 = term179).
Proof. exact (@lem1007663 (BIT1 0) term194 term194). Qed.
Lemma lem1991110 : term224 = term179.
Proof. exact (EQ_MP (@lem1991109) (@lem1991108)). Qed.
Lemma lem1991111 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991112 : term222 = term174.
Proof. exact (MK_COMB (@lem1991111) (@lem1991110)). Qed.
Lemma lem1991113 : term221 = term174.
Proof. exact (TRANS (@lem1991107) (@lem1991112)). Qed.
Lemma lem1991115 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1991116 : term121 = term122.
Proof. exact (@lem1991115 term61 term61). Qed.
Lemma lem1991117 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1991118 : term77 = term61.
Proof. exact (EQ_MP (@lem1991117) (@lem940073)). Qed.
Lemma lem1991119 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991120 : term75 = term58.
Proof. exact (MK_COMB (@lem1991119) (@lem1991118)). Qed.
Lemma lem1991121 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1991122 : term122 = term107.
Proof. exact (MK_COMB (@lem1991121) (@lem1991120)). Qed.
Lemma lem1991123 : term121 = term107.
Proof. exact (TRANS (@lem1991116) (@lem1991122)). Qed.
Lemma lem1991124 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1991125 : term123 = term111.
Proof. exact (MK_COMB (@lem1991124) (@lem1991123)). Qed.
Lemma lem1991126 : term225 = term226.
Proof. exact (MK_COMB (@lem1991125) (@lem1991113)). Qed.
Lemma lem1991129 : term227 = term58.
Proof. exact (@lem1367765 term61 term61). Qed.
Lemma lem1991130 : term228 = term194.
Proof. exact (@lem706885). Qed.
Lemma lem1991131 : (term228 = term194) = (term229 = term179).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term194). Qed.
Lemma lem1991132 : term229 = term179.
Proof. exact (EQ_MP (@lem1991131) (@lem1991130)). Qed.
Lemma lem1991133 : term179 = term229.
Proof. exact (SYM (@lem1991132)). Qed.
Lemma lem1991134 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991135 : term174 = term230.
Proof. exact (MK_COMB (@lem1991134) (@lem1991133)). Qed.
Lemma lem1991136 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem1991137 : term226 = term227.
Proof. exact (MK_COMB (@lem1991136) (@lem1991135)). Qed.
Lemma lem1991138 : term226 = term58.
Proof. exact (TRANS (@lem1991137) (@lem1991129)). Qed.
Lemma lem1991139 : term225 = term58.
Proof. exact (TRANS (@lem1991126) (@lem1991138)). Qed.
Lemma lem1991140 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1991141 : term231 = term232.
Proof. exact (MK_COMB (@lem1991140) (@lem1991139)). Qed.
Lemma lem1991142 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem1991143 : term233 = term221.
Proof. exact (MK_COMB (@lem1991141) (@lem1991142)). Qed.
Lemma lem1991145 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1991146 : term221 = term222.
Proof. exact (@lem1991145 term61 term179). Qed.
Lemma lem1991147 : term223 = term194.
Proof. exact (@lem996238 term194). Qed.
Lemma lem1991148 : (term223 = term194) = (term224 = term179).
Proof. exact (@lem1007663 (BIT1 0) term194 term194). Qed.
Lemma lem1991149 : term224 = term179.
Proof. exact (EQ_MP (@lem1991148) (@lem1991147)). Qed.
Lemma lem1991150 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991151 : term222 = term174.
Proof. exact (MK_COMB (@lem1991150) (@lem1991149)). Qed.
Lemma lem1991152 : term221 = term174.
Proof. exact (TRANS (@lem1991146) (@lem1991151)). Qed.
Lemma lem1991153 : term233 = term174.
Proof. exact (TRANS (@lem1991143) (@lem1991152)). Qed.
Lemma lem1991155 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1991156 : term191 = term192.
Proof. exact (@lem1991155 term179 term61). Qed.
Lemma lem1991157 : term193 = term194.
Proof. exact (@lem996237 term194). Qed.
Lemma lem1991158 : (term193 = term194) = (term195 = term179).
Proof. exact (@lem1007663 term194 (BIT1 0) term194). Qed.
Lemma lem1991159 : term195 = term179.
Proof. exact (EQ_MP (@lem1991158) (@lem1991157)). Qed.
Lemma lem1991160 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991161 : term192 = term174.
Proof. exact (MK_COMB (@lem1991160) (@lem1991159)). Qed.
Lemma lem1991162 : term191 = term174.
Proof. exact (TRANS (@lem1991156) (@lem1991161)). Qed.
Lemma lem1991163 : term232 = term232.
Proof. exact (eq_refl term232). Qed.
Lemma lem1991164 : term234 = term221.
Proof. exact (MK_COMB (@lem1991163) (@lem1991162)). Qed.
Lemma lem1991166 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1991167 : term221 = term222.
Proof. exact (@lem1991166 term61 term179). Qed.
Lemma lem1991168 : term223 = term194.
Proof. exact (@lem996238 term194). Qed.
Lemma lem1991169 : (term223 = term194) = (term224 = term179).
Proof. exact (@lem1007663 (BIT1 0) term194 term194). Qed.
Lemma lem1991170 : term224 = term179.
Proof. exact (EQ_MP (@lem1991169) (@lem1991168)). Qed.
Lemma lem1991171 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991172 : term222 = term174.
Proof. exact (MK_COMB (@lem1991171) (@lem1991170)). Qed.
Lemma lem1991173 : term221 = term174.
Proof. exact (TRANS (@lem1991167) (@lem1991172)). Qed.
Lemma lem1991174 : term234 = term174.
Proof. exact (TRANS (@lem1991164) (@lem1991173)). Qed.
Lemma lem1991175 : term174 = term234.
Proof. exact (SYM (@lem1991174)). Qed.
Lemma lem1991176 : term233 = term234.
Proof. exact (TRANS (@lem1991153) (@lem1991175)). Qed.
Lemma lem1991177 : term213 = term178.
Proof. exact (@lem1991104 (@lem1991176)). Qed.
Lemma lem1991180 : term212 = term178.
Proof. exact (TRANS (@lem1991070) (@lem1991177)). Qed.
Lemma lem1991181 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1991182 : term235 = term187.
Proof. exact (MK_COMB (@lem1991181) (@lem1991180)). Qed.
Lemma lem1991183 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1991184 (y : real) : (term210 y) = (term208 y).
Proof. exact (MK_COMB (@lem1991182) (@lem1991183 y)). Qed.
Lemma lem1991185 (y : real) : (term209 y) = (term208 y).
Proof. exact (TRANS (@lem1991063 y) (@lem1991184 y)). Qed.
Lemma lem1991186 (x : real) : (term252 x) = (term252 x).
Proof. exact (eq_refl (term252 x)). Qed.
Lemma lem1991187 (x : real) (y : real) : (term255 x y) = (term256 x y).
Proof. exact (MK_COMB (@lem1991186 x) (@lem1991185 y)). Qed.
Lemma lem1991188 (x : real) (y : real) : (term254 x y) = (term256 x y).
Proof. exact (TRANS (@lem1991062 x y) (@lem1991187 x y)). Qed.
Lemma lem1991189 (x : real) (y : real) : (term239 x y) = (term256 x y).
Proof. exact (TRANS (@lem1991061 x y) (@lem1991188 x y)). Qed.
Lemma lem1991190 (x : real) (y : real) : (term238 x y) = (term256 x y).
Proof. exact (TRANS (@lem1990974 x y) (@lem1991189 x y)). Qed.
Lemma lem1991191 (x : real) (y : real) : (term237 x y) = (term256 x y).
Proof. exact (TRANS (@lem1990973 x y) (@lem1991190 x y)). Qed.
Lemma lem1991192 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1991193 (x : real) (y : real) : (term257 x y) = (term258 x y).
Proof. exact (MK_COMB (@lem1991192) (@lem1991191 x y)). Qed.
Lemma lem1991194 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1991195 (x : real) (y : real) : (term170 x y) = (term259 x y).
Proof. exact (MK_COMB (@lem1991193 x y) (@lem1991194)). Qed.
Lemma lem1991196 (x : real) (y : real) : (term169 x y) = (term259 x y).
Proof. exact (TRANS (@lem1990761 x y) (@lem1991195 x y)). Qed.
Lemma lem1991197 (y : real) (x : real) : (term163 x y) = (term260 y x).
Proof. exact (@lem1988287 (term159 x y) x). Qed.
Lemma lem1991198 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1991200 (x : real) (y : real) : (real_div x y) = (term171 x y).
Proof. exact (EQ_MP (@lem1982797 x y) (@lem1982796 x y)). Qed.
Lemma lem1991201 (x : real) (y : real) : (term172 x y) = (term173 x y).
Proof. exact (@lem1991200 (real_sub x y) term174). Qed.
Lemma lem1991206 (n : nat) : (term175 n) = (term176 n).
Proof. exact (proj1 (@lem1981223 n (@el nat))). Qed.
Lemma lem1991208 : term177 = term178.
Proof. exact (@lem1991206 term179). Qed.
Lemma lem1991221 (x : real) (y : real) : (real_sub x y) = (term19 x y).
Proof. exact (@lem1982792 x y). Qed.
Lemma lem1991222 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1991223 (x : real) (y : real) : (term180 x y) = (term181 x y).
Proof. exact (MK_COMB (@lem1991222) (@lem1991221 x y)). Qed.
Lemma lem1991224 (x : real) (y : real) : (term173 x y) = (term182 x y).
Proof. exact (MK_COMB (@lem1991223 x y) (@lem1991208)). Qed.
Lemma lem1991225 (x : real) (y : real) : (term182 x y) = (term183 x y).
Proof. exact (@lem1982725 term178 (term19 x y)). Qed.
Lemma lem1991226 (x : real) (y : real) : (term183 x y) = (term184 x y).
Proof. exact (@lem1982781 x term178 (term21 y)). Qed.
Lemma lem1991227 (y : real) : (term185 y) = (term186 y).
Proof. exact (@lem1982749 term178 term107 y). Qed.
Lemma lem1991229 (x : nat) : (term108 x) = (term109 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1991230 : term107 = term110.
Proof. exact (@lem1991229 term61). Qed.
Lemma lem1991233 : term187 = term187.
Proof. exact (eq_refl term187). Qed.
Lemma lem1991234 : term188 = term189.
Proof. exact (MK_COMB (@lem1991233) (@lem1991230)). Qed.
Lemma lem1991235 : term189 = term190.
Proof. exact (@lem1981613 term58 term107 term174 term58). Qed.
Lemma lem1991237 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1991238 : term191 = term192.
Proof. exact (@lem1991237 term179 term61). Qed.
Lemma lem1991239 : term193 = term194.
Proof. exact (@lem996237 term194). Qed.
Lemma lem1991240 : (term193 = term194) = (term195 = term179).
Proof. exact (@lem1007663 term194 (BIT1 0) term194). Qed.
Lemma lem1991241 : term195 = term179.
Proof. exact (EQ_MP (@lem1991240) (@lem1991239)). Qed.
Lemma lem1991242 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991243 : term192 = term174.
Proof. exact (MK_COMB (@lem1991242) (@lem1991241)). Qed.
Lemma lem1991244 : term191 = term174.
Proof. exact (TRANS (@lem1991238) (@lem1991243)). Qed.
Lemma lem1991246 (m : nat) (n : nat) : (term196 m n) = (term120 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1991247 : term197 = term122.
Proof. exact (@lem1991246 term61 term61). Qed.
Lemma lem1991248 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1991249 : term77 = term61.
Proof. exact (EQ_MP (@lem1991248) (@lem940073)). Qed.
Lemma lem1991250 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991251 : term75 = term58.
Proof. exact (MK_COMB (@lem1991250) (@lem1991249)). Qed.
Lemma lem1991252 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1991253 : term122 = term107.
Proof. exact (MK_COMB (@lem1991252) (@lem1991251)). Qed.
Lemma lem1991254 : term197 = term107.
Proof. exact (TRANS (@lem1991247) (@lem1991253)). Qed.
Lemma lem1991255 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem1991256 : term198 = term199.
Proof. exact (MK_COMB (@lem1991255) (@lem1991254)). Qed.
Lemma lem1991257 : term190 = term200.
Proof. exact (MK_COMB (@lem1991256) (@lem1991244)). Qed.
Lemma lem1991258 : term189 = term200.
Proof. exact (TRANS (@lem1991235) (@lem1991257)). Qed.
Lemma lem1991261 : term188 = term200.
Proof. exact (TRANS (@lem1991234) (@lem1991258)). Qed.
Lemma lem1991262 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1991263 : term201 = term202.
Proof. exact (MK_COMB (@lem1991262) (@lem1991261)). Qed.
Lemma lem1991264 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1991265 (y : real) : (term186 y) = (term203 y).
Proof. exact (MK_COMB (@lem1991263) (@lem1991264 y)). Qed.
Lemma lem1991266 (y : real) : (term185 y) = (term203 y).
Proof. exact (TRANS (@lem1991227 y) (@lem1991265 y)). Qed.
Lemma lem1991269 (x : real) : (term204 x) = (term204 x).
Proof. exact (eq_refl (term204 x)). Qed.
Lemma lem1991270 (x : real) (y : real) : (term184 x y) = (term205 x y).
Proof. exact (MK_COMB (@lem1991269 x) (@lem1991266 y)). Qed.
Lemma lem1991271 (x : real) (y : real) : (term183 x y) = (term205 x y).
Proof. exact (TRANS (@lem1991226 x y) (@lem1991270 x y)). Qed.
Lemma lem1991272 (x : real) (y : real) : (term182 x y) = (term205 x y).
Proof. exact (TRANS (@lem1991225 x y) (@lem1991271 x y)). Qed.
Lemma lem1991273 (x : real) (y : real) : (term173 x y) = (term205 x y).
Proof. exact (TRANS (@lem1991224 x y) (@lem1991272 x y)). Qed.
Lemma lem1991274 (x : real) (y : real) : (term172 x y) = (term205 x y).
Proof. exact (TRANS (@lem1991201 x y) (@lem1991273 x y)). Qed.
Lemma lem1991277 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1991278 (x : real) (y : real) : (term159 x y) = (term206 x y).
Proof. exact (MK_COMB (@lem1991277 y) (@lem1991274 x y)). Qed.
Lemma lem1991279 (x : real) (y : real) : (term206 x y) = (term207 x y).
Proof. exact (@lem1982757 (term208 x) y (term203 y)). Qed.
Lemma lem1991280 (y : real) : (term209 y) = (term210 y).
Proof. exact (@lem1982715 term200 y). Qed.
Lemma lem1991282 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1991283 : term58 = term60.
Proof. exact (@lem1991282 term61). Qed.
Lemma lem1991286 : term211 = term211.
Proof. exact (eq_refl term211). Qed.
Lemma lem1991287 : term212 = term213.
Proof. exact (MK_COMB (@lem1991286) (@lem1991283)). Qed.
Lemma lem1991288 : term214.
Proof. exact (@lem1981473 term107 term174 term58 term58 term58 term174). Qed.
Lemma lem1991290 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1991291 : term215 = term216.
Proof. exact (@lem1991290 (NUMERAL 0) term179). Qed.
Lemma lem1991292 : term217 = term194.
Proof. exact (@lem912803). Qed.
Lemma lem1991293 (h1 : term217 = term194) : term216 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term194 h1). Qed.
Lemma lem1991294 : (term217 = term194) = (term216 = True).
Proof. exact (prop_ext (fun h1 : term217 = term194 => @lem1991293 h1) (fun h1 : term216 = True => @lem1991292)). Qed.
Lemma lem1991295 : term216 = True.
Proof. exact (EQ_MP (@lem1991294) (@lem1991292)). Qed.
Lemma lem1991296 : term215 = True.
Proof. exact (TRANS (@lem1991291) (@lem1991295)). Qed.
Lemma lem1991297 : True = term215.
Proof. exact (SYM (@lem1991296)). Qed.
Lemma lem1991298 : term215.
Proof. exact (EQ_MP (@lem1991297) (@lem0)). Qed.
Lemma lem1991299 : term218.
Proof. exact (@lem1991288 (@lem1991298)). Qed.
Lemma lem1991301 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1991302 : term57 = term68.
Proof. exact (@lem1991301 (NUMERAL 0) term61). Qed.
Lemma lem1991303 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1991304 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1991305 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1991304 h1) (fun h1 : term68 = True => @lem1991303)). Qed.
Lemma lem1991306 : term68 = True.
Proof. exact (EQ_MP (@lem1991305) (@lem1991303)). Qed.
Lemma lem1991307 : term57 = True.
Proof. exact (TRANS (@lem1991302) (@lem1991306)). Qed.
Lemma lem1991308 : True = term57.
Proof. exact (SYM (@lem1991307)). Qed.
Lemma lem1991309 : term57.
Proof. exact (EQ_MP (@lem1991308) (@lem0)). Qed.
Lemma lem1991310 : term219.
Proof. exact (@lem1991299 (@lem1991309)). Qed.
Lemma lem1991312 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1991313 : term215 = term216.
Proof. exact (@lem1991312 (NUMERAL 0) term179). Qed.
Lemma lem1991314 : term217 = term194.
Proof. exact (@lem912803). Qed.
Lemma lem1991315 (h1 : term217 = term194) : term216 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term194 h1). Qed.
Lemma lem1991316 : (term217 = term194) = (term216 = True).
Proof. exact (prop_ext (fun h1 : term217 = term194 => @lem1991315 h1) (fun h1 : term216 = True => @lem1991314)). Qed.
Lemma lem1991317 : term216 = True.
Proof. exact (EQ_MP (@lem1991316) (@lem1991314)). Qed.
Lemma lem1991318 : term215 = True.
Proof. exact (TRANS (@lem1991313) (@lem1991317)). Qed.
Lemma lem1991319 : True = term215.
Proof. exact (SYM (@lem1991318)). Qed.
Lemma lem1991320 : term215.
Proof. exact (EQ_MP (@lem1991319) (@lem0)). Qed.
Lemma lem1991321 : term220.
Proof. exact (@lem1991310 (@lem1991320)). Qed.
Lemma lem1991323 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1991324 : term221 = term222.
Proof. exact (@lem1991323 term61 term179). Qed.
Lemma lem1991325 : term223 = term194.
Proof. exact (@lem996238 term194). Qed.
Lemma lem1991326 : (term223 = term194) = (term224 = term179).
Proof. exact (@lem1007663 (BIT1 0) term194 term194). Qed.
Lemma lem1991327 : term224 = term179.
Proof. exact (EQ_MP (@lem1991326) (@lem1991325)). Qed.
Lemma lem1991328 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991329 : term222 = term174.
Proof. exact (MK_COMB (@lem1991328) (@lem1991327)). Qed.
Lemma lem1991330 : term221 = term174.
Proof. exact (TRANS (@lem1991324) (@lem1991329)). Qed.
Lemma lem1991332 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1991333 : term121 = term122.
Proof. exact (@lem1991332 term61 term61). Qed.
Lemma lem1991334 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1991335 : term77 = term61.
Proof. exact (EQ_MP (@lem1991334) (@lem940073)). Qed.
Lemma lem1991336 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991337 : term75 = term58.
Proof. exact (MK_COMB (@lem1991336) (@lem1991335)). Qed.
Lemma lem1991338 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1991339 : term122 = term107.
Proof. exact (MK_COMB (@lem1991338) (@lem1991337)). Qed.
Lemma lem1991340 : term121 = term107.
Proof. exact (TRANS (@lem1991333) (@lem1991339)). Qed.
Lemma lem1991341 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1991342 : term123 = term111.
Proof. exact (MK_COMB (@lem1991341) (@lem1991340)). Qed.
Lemma lem1991343 : term225 = term226.
Proof. exact (MK_COMB (@lem1991342) (@lem1991330)). Qed.
Lemma lem1991346 : term227 = term58.
Proof. exact (@lem1367765 term61 term61). Qed.
Lemma lem1991347 : term228 = term194.
Proof. exact (@lem706885). Qed.
Lemma lem1991348 : (term228 = term194) = (term229 = term179).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term194). Qed.
Lemma lem1991349 : term229 = term179.
Proof. exact (EQ_MP (@lem1991348) (@lem1991347)). Qed.
Lemma lem1991350 : term179 = term229.
Proof. exact (SYM (@lem1991349)). Qed.
Lemma lem1991351 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991352 : term174 = term230.
Proof. exact (MK_COMB (@lem1991351) (@lem1991350)). Qed.
Lemma lem1991353 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem1991354 : term226 = term227.
Proof. exact (MK_COMB (@lem1991353) (@lem1991352)). Qed.
Lemma lem1991355 : term226 = term58.
Proof. exact (TRANS (@lem1991354) (@lem1991346)). Qed.
Lemma lem1991356 : term225 = term58.
Proof. exact (TRANS (@lem1991343) (@lem1991355)). Qed.
Lemma lem1991357 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1991358 : term231 = term232.
Proof. exact (MK_COMB (@lem1991357) (@lem1991356)). Qed.
Lemma lem1991359 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem1991360 : term233 = term221.
Proof. exact (MK_COMB (@lem1991358) (@lem1991359)). Qed.
Lemma lem1991362 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1991363 : term221 = term222.
Proof. exact (@lem1991362 term61 term179). Qed.
Lemma lem1991364 : term223 = term194.
Proof. exact (@lem996238 term194). Qed.
Lemma lem1991365 : (term223 = term194) = (term224 = term179).
Proof. exact (@lem1007663 (BIT1 0) term194 term194). Qed.
Lemma lem1991366 : term224 = term179.
Proof. exact (EQ_MP (@lem1991365) (@lem1991364)). Qed.
Lemma lem1991367 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991368 : term222 = term174.
Proof. exact (MK_COMB (@lem1991367) (@lem1991366)). Qed.
Lemma lem1991369 : term221 = term174.
Proof. exact (TRANS (@lem1991363) (@lem1991368)). Qed.
Lemma lem1991370 : term233 = term174.
Proof. exact (TRANS (@lem1991360) (@lem1991369)). Qed.
Lemma lem1991372 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1991373 : term191 = term192.
Proof. exact (@lem1991372 term179 term61). Qed.
Lemma lem1991374 : term193 = term194.
Proof. exact (@lem996237 term194). Qed.
Lemma lem1991375 : (term193 = term194) = (term195 = term179).
Proof. exact (@lem1007663 term194 (BIT1 0) term194). Qed.
Lemma lem1991376 : term195 = term179.
Proof. exact (EQ_MP (@lem1991375) (@lem1991374)). Qed.
Lemma lem1991377 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991378 : term192 = term174.
Proof. exact (MK_COMB (@lem1991377) (@lem1991376)). Qed.
Lemma lem1991379 : term191 = term174.
Proof. exact (TRANS (@lem1991373) (@lem1991378)). Qed.
Lemma lem1991380 : term232 = term232.
Proof. exact (eq_refl term232). Qed.
Lemma lem1991381 : term234 = term221.
Proof. exact (MK_COMB (@lem1991380) (@lem1991379)). Qed.
Lemma lem1991383 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1991384 : term221 = term222.
Proof. exact (@lem1991383 term61 term179). Qed.
Lemma lem1991385 : term223 = term194.
Proof. exact (@lem996238 term194). Qed.
Lemma lem1991386 : (term223 = term194) = (term224 = term179).
Proof. exact (@lem1007663 (BIT1 0) term194 term194). Qed.
Lemma lem1991387 : term224 = term179.
Proof. exact (EQ_MP (@lem1991386) (@lem1991385)). Qed.
Lemma lem1991388 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991389 : term222 = term174.
Proof. exact (MK_COMB (@lem1991388) (@lem1991387)). Qed.
Lemma lem1991390 : term221 = term174.
Proof. exact (TRANS (@lem1991384) (@lem1991389)). Qed.
Lemma lem1991391 : term234 = term174.
Proof. exact (TRANS (@lem1991381) (@lem1991390)). Qed.
Lemma lem1991392 : term174 = term234.
Proof. exact (SYM (@lem1991391)). Qed.
Lemma lem1991393 : term233 = term234.
Proof. exact (TRANS (@lem1991370) (@lem1991392)). Qed.
Lemma lem1991394 : term213 = term178.
Proof. exact (@lem1991321 (@lem1991393)). Qed.
Lemma lem1991397 : term212 = term178.
Proof. exact (TRANS (@lem1991287) (@lem1991394)). Qed.
Lemma lem1991398 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1991399 : term235 = term187.
Proof. exact (MK_COMB (@lem1991398) (@lem1991397)). Qed.
Lemma lem1991400 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1991401 (y : real) : (term210 y) = (term208 y).
Proof. exact (MK_COMB (@lem1991399) (@lem1991400 y)). Qed.
Lemma lem1991402 (y : real) : (term209 y) = (term208 y).
Proof. exact (TRANS (@lem1991280 y) (@lem1991401 y)). Qed.
Lemma lem1991403 (x : real) : (term204 x) = (term204 x).
Proof. exact (eq_refl (term204 x)). Qed.
Lemma lem1991404 (x : real) (y : real) : (term207 x y) = (term236 x y).
Proof. exact (MK_COMB (@lem1991403 x) (@lem1991402 y)). Qed.
Lemma lem1991405 (x : real) (y : real) : (term206 x y) = (term236 x y).
Proof. exact (TRANS (@lem1991279 x y) (@lem1991404 x y)). Qed.
Lemma lem1991406 (x : real) (y : real) : (term159 x y) = (term236 x y).
Proof. exact (TRANS (@lem1991278 x y) (@lem1991405 x y)). Qed.
Lemma lem1991407 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1991408 (x : real) (y : real) : (term261 x y) = (term262 x y).
Proof. exact (MK_COMB (@lem1991407) (@lem1991406 x y)). Qed.
Lemma lem1991409 (y : real) (x : real) : (term263 y x) = (term264 y x).
Proof. exact (MK_COMB (@lem1991408 x y) (@lem1991198 x)). Qed.
Lemma lem1991410 (y : real) (x : real) : (term264 y x) = (term265 y x).
Proof. exact (@lem1982792 (term236 x y) x). Qed.
Lemma lem1991414 (x : real) (y : real) : (term265 y x) = (term266 x y).
Proof. exact (@lem1982759 (term208 x) (term21 x) (term208 y)). Qed.
Lemma lem1991415 (x : real) : (term267 x) = (term268 x).
Proof. exact (@lem1982711 term178 term107 x). Qed.
Lemma lem1991417 (x : nat) : (term108 x) = (term109 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1991418 : term107 = term110.
Proof. exact (@lem1991417 term61). Qed.
Lemma lem1991421 : term269 = term269.
Proof. exact (eq_refl term269). Qed.
Lemma lem1991422 : term270 = term271.
Proof. exact (MK_COMB (@lem1991421) (@lem1991418)). Qed.
Lemma lem1991423 : term272.
Proof. exact (@lem1981473 term58 term174 term107 term58 term107 term174). Qed.
Lemma lem1991425 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1991426 : term215 = term216.
Proof. exact (@lem1991425 (NUMERAL 0) term179). Qed.
Lemma lem1991427 : term217 = term194.
Proof. exact (@lem912803). Qed.
Lemma lem1991428 (h1 : term217 = term194) : term216 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term194 h1). Qed.
Lemma lem1991429 : (term217 = term194) = (term216 = True).
Proof. exact (prop_ext (fun h1 : term217 = term194 => @lem1991428 h1) (fun h1 : term216 = True => @lem1991427)). Qed.
Lemma lem1991430 : term216 = True.
Proof. exact (EQ_MP (@lem1991429) (@lem1991427)). Qed.
Lemma lem1991431 : term215 = True.
Proof. exact (TRANS (@lem1991426) (@lem1991430)). Qed.
Lemma lem1991432 : True = term215.
Proof. exact (SYM (@lem1991431)). Qed.
Lemma lem1991433 : term215.
Proof. exact (EQ_MP (@lem1991432) (@lem0)). Qed.
Lemma lem1991434 : term273.
Proof. exact (@lem1991423 (@lem1991433)). Qed.
Lemma lem1991436 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1991437 : term57 = term68.
Proof. exact (@lem1991436 (NUMERAL 0) term61). Qed.
Lemma lem1991438 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1991439 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1991440 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1991439 h1) (fun h1 : term68 = True => @lem1991438)). Qed.
Lemma lem1991441 : term68 = True.
Proof. exact (EQ_MP (@lem1991440) (@lem1991438)). Qed.
Lemma lem1991442 : term57 = True.
Proof. exact (TRANS (@lem1991437) (@lem1991441)). Qed.
Lemma lem1991443 : True = term57.
Proof. exact (SYM (@lem1991442)). Qed.
Lemma lem1991444 : term57.
Proof. exact (EQ_MP (@lem1991443) (@lem0)). Qed.
Lemma lem1991445 : term274.
Proof. exact (@lem1991434 (@lem1991444)). Qed.
Lemma lem1991447 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1991448 : term215 = term216.
Proof. exact (@lem1991447 (NUMERAL 0) term179). Qed.
Lemma lem1991449 : term217 = term194.
Proof. exact (@lem912803). Qed.
Lemma lem1991450 (h1 : term217 = term194) : term216 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term194 h1). Qed.
Lemma lem1991451 : (term217 = term194) = (term216 = True).
Proof. exact (prop_ext (fun h1 : term217 = term194 => @lem1991450 h1) (fun h1 : term216 = True => @lem1991449)). Qed.
Lemma lem1991452 : term216 = True.
Proof. exact (EQ_MP (@lem1991451) (@lem1991449)). Qed.
Lemma lem1991453 : term215 = True.
Proof. exact (TRANS (@lem1991448) (@lem1991452)). Qed.
Lemma lem1991454 : True = term215.
Proof. exact (SYM (@lem1991453)). Qed.
Lemma lem1991455 : term215.
Proof. exact (EQ_MP (@lem1991454) (@lem0)). Qed.
Lemma lem1991456 : term275.
Proof. exact (@lem1991445 (@lem1991455)). Qed.
Lemma lem1991458 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1991459 : term276 = term277.
Proof. exact (@lem1991458 term61 term179). Qed.
Lemma lem1991460 : term223 = term194.
Proof. exact (@lem996238 term194). Qed.
Lemma lem1991461 : (term223 = term194) = (term224 = term179).
Proof. exact (@lem1007663 (BIT1 0) term194 term194). Qed.
Lemma lem1991462 : term224 = term179.
Proof. exact (EQ_MP (@lem1991461) (@lem1991460)). Qed.
Lemma lem1991463 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991464 : term222 = term174.
Proof. exact (MK_COMB (@lem1991463) (@lem1991462)). Qed.
Lemma lem1991465 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1991466 : term277 = term278.
Proof. exact (MK_COMB (@lem1991465) (@lem1991464)). Qed.
Lemma lem1991467 : term276 = term278.
Proof. exact (TRANS (@lem1991459) (@lem1991466)). Qed.
Lemma lem1991469 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1991470 : term74 = term75.
Proof. exact (@lem1991469 term61 term61). Qed.
Lemma lem1991471 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1991472 : term77 = term61.
Proof. exact (EQ_MP (@lem1991471) (@lem940073)). Qed.
Lemma lem1991473 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991474 : term75 = term58.
Proof. exact (MK_COMB (@lem1991473) (@lem1991472)). Qed.
Lemma lem1991475 : term74 = term58.
Proof. exact (TRANS (@lem1991470) (@lem1991474)). Qed.
Lemma lem1991476 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1991477 : term279 = term280.
Proof. exact (MK_COMB (@lem1991476) (@lem1991475)). Qed.
Lemma lem1991478 : term281 = term282.
Proof. exact (MK_COMB (@lem1991477) (@lem1991467)). Qed.
Lemma lem1991481 : term283 = term107.
Proof. exact (@lem1367771 term61 term61). Qed.
Lemma lem1991482 : term228 = term194.
Proof. exact (@lem706885). Qed.
Lemma lem1991483 : (term228 = term194) = (term229 = term179).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term194). Qed.
Lemma lem1991484 : term229 = term179.
Proof. exact (EQ_MP (@lem1991483) (@lem1991482)). Qed.
Lemma lem1991485 : term179 = term229.
Proof. exact (SYM (@lem1991484)). Qed.
Lemma lem1991486 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991487 : term174 = term230.
Proof. exact (MK_COMB (@lem1991486) (@lem1991485)). Qed.
Lemma lem1991488 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1991489 : term278 = term284.
Proof. exact (MK_COMB (@lem1991488) (@lem1991487)). Qed.
Lemma lem1991490 : term280 = term280.
Proof. exact (eq_refl term280). Qed.
Lemma lem1991491 : term282 = term283.
Proof. exact (MK_COMB (@lem1991490) (@lem1991489)). Qed.
Lemma lem1991492 : term282 = term107.
Proof. exact (TRANS (@lem1991491) (@lem1991481)). Qed.
Lemma lem1991493 : term281 = term107.
Proof. exact (TRANS (@lem1991478) (@lem1991492)). Qed.
Lemma lem1991494 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1991495 : term285 = term244.
Proof. exact (MK_COMB (@lem1991494) (@lem1991493)). Qed.
Lemma lem1991496 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem1991497 : term286 = term276.
Proof. exact (MK_COMB (@lem1991495) (@lem1991496)). Qed.
Lemma lem1991499 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1991500 : term276 = term277.
Proof. exact (@lem1991499 term61 term179). Qed.
Lemma lem1991501 : term223 = term194.
Proof. exact (@lem996238 term194). Qed.
Lemma lem1991502 : (term223 = term194) = (term224 = term179).
Proof. exact (@lem1007663 (BIT1 0) term194 term194). Qed.
Lemma lem1991503 : term224 = term179.
Proof. exact (EQ_MP (@lem1991502) (@lem1991501)). Qed.
Lemma lem1991504 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991505 : term222 = term174.
Proof. exact (MK_COMB (@lem1991504) (@lem1991503)). Qed.
Lemma lem1991506 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1991507 : term277 = term278.
Proof. exact (MK_COMB (@lem1991506) (@lem1991505)). Qed.
Lemma lem1991508 : term276 = term278.
Proof. exact (TRANS (@lem1991500) (@lem1991507)). Qed.
Lemma lem1991509 : term286 = term278.
Proof. exact (TRANS (@lem1991497) (@lem1991508)). Qed.
Lemma lem1991511 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1991512 : term191 = term192.
Proof. exact (@lem1991511 term179 term61). Qed.
Lemma lem1991513 : term193 = term194.
Proof. exact (@lem996237 term194). Qed.
Lemma lem1991514 : (term193 = term194) = (term195 = term179).
Proof. exact (@lem1007663 term194 (BIT1 0) term194). Qed.
Lemma lem1991515 : term195 = term179.
Proof. exact (EQ_MP (@lem1991514) (@lem1991513)). Qed.
Lemma lem1991516 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991517 : term192 = term174.
Proof. exact (MK_COMB (@lem1991516) (@lem1991515)). Qed.
Lemma lem1991518 : term191 = term174.
Proof. exact (TRANS (@lem1991512) (@lem1991517)). Qed.
Lemma lem1991519 : term244 = term244.
Proof. exact (eq_refl term244). Qed.
Lemma lem1991520 : term287 = term276.
Proof. exact (MK_COMB (@lem1991519) (@lem1991518)). Qed.
Lemma lem1991522 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1991523 : term276 = term277.
Proof. exact (@lem1991522 term61 term179). Qed.
Lemma lem1991524 : term223 = term194.
Proof. exact (@lem996238 term194). Qed.
Lemma lem1991525 : (term223 = term194) = (term224 = term179).
Proof. exact (@lem1007663 (BIT1 0) term194 term194). Qed.
Lemma lem1991526 : term224 = term179.
Proof. exact (EQ_MP (@lem1991525) (@lem1991524)). Qed.
Lemma lem1991527 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991528 : term222 = term174.
Proof. exact (MK_COMB (@lem1991527) (@lem1991526)). Qed.
Lemma lem1991529 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1991530 : term277 = term278.
Proof. exact (MK_COMB (@lem1991529) (@lem1991528)). Qed.
Lemma lem1991531 : term276 = term278.
Proof. exact (TRANS (@lem1991523) (@lem1991530)). Qed.
Lemma lem1991532 : term287 = term278.
Proof. exact (TRANS (@lem1991520) (@lem1991531)). Qed.
Lemma lem1991533 : term278 = term287.
Proof. exact (SYM (@lem1991532)). Qed.
Lemma lem1991534 : term286 = term287.
Proof. exact (TRANS (@lem1991509) (@lem1991533)). Qed.
Lemma lem1991535 : term271 = term200.
Proof. exact (@lem1991456 (@lem1991534)). Qed.
Lemma lem1991538 : term270 = term200.
Proof. exact (TRANS (@lem1991422) (@lem1991535)). Qed.
Lemma lem1991539 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1991540 : term288 = term202.
Proof. exact (MK_COMB (@lem1991539) (@lem1991538)). Qed.
Lemma lem1991541 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1991542 (x : real) : (term268 x) = (term203 x).
Proof. exact (MK_COMB (@lem1991540) (@lem1991541 x)). Qed.
Lemma lem1991543 (x : real) : (term267 x) = (term203 x).
Proof. exact (TRANS (@lem1991415 x) (@lem1991542 x)). Qed.
Lemma lem1991544 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1991545 (x : real) : (term289 x) = (term252 x).
Proof. exact (MK_COMB (@lem1991544) (@lem1991543 x)). Qed.
Lemma lem1991546 (y : real) : (term208 y) = (term208 y).
Proof. exact (eq_refl (term208 y)). Qed.
Lemma lem1991547 (x : real) (y : real) : (term266 x y) = (term256 x y).
Proof. exact (MK_COMB (@lem1991545 x) (@lem1991546 y)). Qed.
Lemma lem1991549 (x : real) (y : real) : (term265 y x) = (term256 x y).
Proof. exact (TRANS (@lem1991414 x y) (@lem1991547 x y)). Qed.
Lemma lem1991550 (x : real) (y : real) : (term264 y x) = (term256 x y).
Proof. exact (TRANS (@lem1991410 y x) (@lem1991549 x y)). Qed.
Lemma lem1991551 (x : real) (y : real) : (term263 y x) = (term256 x y).
Proof. exact (TRANS (@lem1991409 y x) (@lem1991550 x y)). Qed.
Lemma lem1991552 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1991553 (x : real) (y : real) : (term290 y x) = (term258 x y).
Proof. exact (MK_COMB (@lem1991552) (@lem1991551 x y)). Qed.
Lemma lem1991554 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1991555 (x : real) (y : real) : (term260 y x) = (term259 x y).
Proof. exact (MK_COMB (@lem1991553 x y) (@lem1991554)). Qed.
Lemma lem1991556 (x : real) (y : real) : (term163 x y) = (term259 x y).
Proof. exact (TRANS (@lem1991197 y x) (@lem1991555 x y)). Qed.
Lemma lem1991557 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1991558 (x : real) (y : real) : (term291 x y) = (term292 x y).
Proof. exact (MK_COMB (@lem1991557) (@lem1991196 x y)). Qed.
Lemma lem1991559 (x : real) (y : real) : (term161 x y) = (term293 x y).
Proof. exact (MK_COMB (@lem1991558 x y) (@lem1991556 x y)). Qed.
Lemma lem1991560 (x : real) (y : real) : (term30 x y) = (term26 x y).
Proof. exact (@lem1988297 x y). Qed.
Lemma lem1991573 (x : real) (y : real) : (real_sub x y) = (term19 x y).
Proof. exact (@lem1982792 x y). Qed.
Lemma lem1991574 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1991575 (x : real) (y : real) : (term27 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1991574) (@lem1991573 x y)). Qed.
Lemma lem1991576 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1991577 (x : real) (y : real) : (term26 x y) = (term32 x y).
Proof. exact (MK_COMB (@lem1991575 x y) (@lem1991576)). Qed.
Lemma lem1991578 (x : real) (y : real) : (term30 x y) = (term32 x y).
Proof. exact (TRANS (@lem1991560 x y) (@lem1991577 x y)). Qed.
Lemma lem1991579 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1991580 (x : real) (y : real) : (term165 x y) = (term294 x y).
Proof. exact (MK_COMB (@lem1991579) (@lem1991559 x y)). Qed.
Lemma lem1991581 (x : real) (y : real) : (term167 x y) = (term295 x y).
Proof. exact (MK_COMB (@lem1991580 x y) (@lem1991578 x y)). Qed.
Lemma lem1991588 (x : real) (y : real) : (term168 x y) = (term295 x y).
Proof. exact (TRANS (@lem1990760 x y) (@lem1991581 x y)). Qed.
Lemma lem1991605 (x : real) (y : real) : (term295 x y) = (term296 x y).
Proof. exact (@lem19367 (term259 x y) (term259 x y) (term32 x y)). Qed.
Lemma lem1991606 (x : real) (y : real) : (term168 x y) = (term296 x y).
Proof. exact (TRANS (@lem1991588 x y) (@lem1991605 x y)). Qed.
Lemma lem1991616 (x : real) (y : real) (h1 : term296 x y) : term296 x y.
Proof. exact (h1). Qed.
Lemma lem1991617 (x : real) (y : real) (h1 : term297 x y) : term297 x y.
Proof. exact (h1). Qed.
Lemma lem1991618 (x : real) (y : real) (h1 : term297 x y) : term32 x y.
Proof. exact (proj2 (@lem1991617 x y h1)). Qed.
Lemma lem1991619 (x : real) (y : real) (h1 : term297 x y) : term259 x y.
Proof. exact (proj1 (@lem1991617 x y h1)). Qed.
Lemma lem1991621 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1991622 : term56 = term57.
Proof. exact (@lem1991621 term24 term58). Qed.
Lemma lem1991624 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1991625 : term58 = term60.
Proof. exact (@lem1991624 term61). Qed.
Lemma lem1991627 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1991628 : term24 = term62.
Proof. exact (@lem1991627 (NUMERAL 0)). Qed.
Lemma lem1991629 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1991630 : term63 = term64.
Proof. exact (MK_COMB (@lem1991629) (@lem1991628)). Qed.
Lemma lem1991631 : term57 = term65.
Proof. exact (MK_COMB (@lem1991630) (@lem1991625)). Qed.
Lemma lem1991632 : term66.
Proof. exact (@lem1980255 term24 term58 term58 term58). Qed.
Lemma lem1991634 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1991635 : term57 = term68.
Proof. exact (@lem1991634 (NUMERAL 0) term61). Qed.
Lemma lem1991636 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1991637 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1991638 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1991637 h1) (fun h1 : term68 = True => @lem1991636)). Qed.
Lemma lem1991639 : term68 = True.
Proof. exact (EQ_MP (@lem1991638) (@lem1991636)). Qed.
Lemma lem1991640 : term57 = True.
Proof. exact (TRANS (@lem1991635) (@lem1991639)). Qed.
Lemma lem1991641 : True = term57.
Proof. exact (SYM (@lem1991640)). Qed.
Lemma lem1991642 : term57.
Proof. exact (EQ_MP (@lem1991641) (@lem0)). Qed.
Lemma lem1991643 : term70.
Proof. exact (@lem1991632 (@lem1991642)). Qed.
Lemma lem1991645 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1991646 : term57 = term68.
Proof. exact (@lem1991645 (NUMERAL 0) term61). Qed.
Lemma lem1991647 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1991648 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1991649 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1991648 h1) (fun h1 : term68 = True => @lem1991647)). Qed.
Lemma lem1991650 : term68 = True.
Proof. exact (EQ_MP (@lem1991649) (@lem1991647)). Qed.
Lemma lem1991651 : term57 = True.
Proof. exact (TRANS (@lem1991646) (@lem1991650)). Qed.
Lemma lem1991652 : True = term57.
Proof. exact (SYM (@lem1991651)). Qed.
Lemma lem1991653 : term57.
Proof. exact (EQ_MP (@lem1991652) (@lem0)). Qed.
Lemma lem1991654 : term65 = term71.
Proof. exact (@lem1991643 (@lem1991653)). Qed.
Lemma lem1991656 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1991657 : term74 = term75.
Proof. exact (@lem1991656 term61 term61). Qed.
Lemma lem1991658 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1991659 : term77 = term61.
Proof. exact (EQ_MP (@lem1991658) (@lem940073)). Qed.
Lemma lem1991660 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991661 : term75 = term58.
Proof. exact (MK_COMB (@lem1991660) (@lem1991659)). Qed.
Lemma lem1991662 : term74 = term58.
Proof. exact (TRANS (@lem1991657) (@lem1991661)). Qed.
Lemma lem1991664 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1991665 : term79 = term24.
Proof. exact (@lem1991664 term61). Qed.
Lemma lem1991666 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1991667 : term80 = term63.
Proof. exact (MK_COMB (@lem1991666) (@lem1991665)). Qed.
Lemma lem1991668 : term71 = term57.
Proof. exact (MK_COMB (@lem1991667) (@lem1991662)). Qed.
Lemma lem1991670 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1991671 : term57 = term68.
Proof. exact (@lem1991670 (NUMERAL 0) term61). Qed.
Lemma lem1991672 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1991673 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1991674 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1991673 h1) (fun h1 : term68 = True => @lem1991672)). Qed.
Lemma lem1991675 : term68 = True.
Proof. exact (EQ_MP (@lem1991674) (@lem1991672)). Qed.
Lemma lem1991676 : term57 = True.
Proof. exact (TRANS (@lem1991671) (@lem1991675)). Qed.
Lemma lem1991677 : term71 = True.
Proof. exact (TRANS (@lem1991668) (@lem1991676)). Qed.
Lemma lem1991678 : term65 = True.
Proof. exact (TRANS (@lem1991654) (@lem1991677)). Qed.
Lemma lem1991679 : term57 = True.
Proof. exact (TRANS (@lem1991631) (@lem1991678)). Qed.
Lemma lem1991680 : term56 = True.
Proof. exact (TRANS (@lem1991622) (@lem1991679)). Qed.
Lemma lem1991681 : True = term56.
Proof. exact (SYM (@lem1991680)). Qed.
Lemma lem1991682 : term56.
Proof. exact (EQ_MP (@lem1991681) (@lem0)). Qed.
Lemma lem1991683 (x : real) (y : real) (h1 : term297 x y) : term298 x y.
Proof. exact (conj (@lem1991682) (@lem1991619 x y h1)). Qed.
Lemma lem1991685 (x : real) (y : real) : term82 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem1991686 (x : real) (y : real) : term299 x y.
Proof. exact (@lem1991685 term58 (term256 x y)). Qed.
Lemma lem1991687 (x : real) (y : real) (h1 : term297 x y) : term300 x y.
Proof. exact (@lem1991686 x y (@lem1991683 x y h1)). Qed.
Lemma lem1991688 (x : real) (y : real) : (term301 x y) = (term256 x y).
Proof. exact (@lem1982733 (term256 x y)). Qed.
Lemma lem1991689 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1991690 (x : real) (y : real) : (term302 x y) = (term258 x y).
Proof. exact (MK_COMB (@lem1991689) (@lem1991688 x y)). Qed.
Lemma lem1991691 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1991692 (x : real) (y : real) : (term300 x y) = (term259 x y).
Proof. exact (MK_COMB (@lem1991690 x y) (@lem1991691)). Qed.
Lemma lem1991693 (x : real) (y : real) (h1 : term297 x y) : term259 x y.
Proof. exact (EQ_MP (@lem1991692 x y) (@lem1991687 x y h1)). Qed.
Lemma lem1991695 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1991696 : term303 = term304.
Proof. exact (@lem1991695 term24 term178). Qed.
Lemma lem1991697 : term178 = term178.
Proof. exact (eq_refl term178). Qed.
Lemma lem1991699 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1991700 : term24 = term62.
Proof. exact (@lem1991699 (NUMERAL 0)). Qed.
Lemma lem1991701 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1991702 : term63 = term64.
Proof. exact (MK_COMB (@lem1991701) (@lem1991700)). Qed.
Lemma lem1991703 : term304 = term305.
Proof. exact (MK_COMB (@lem1991702) (@lem1991697)). Qed.
Lemma lem1991704 : term306.
Proof. exact (@lem1980255 term24 term174 term58 term58). Qed.
Lemma lem1991706 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1991707 : term57 = term68.
Proof. exact (@lem1991706 (NUMERAL 0) term61). Qed.
Lemma lem1991708 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1991709 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1991710 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1991709 h1) (fun h1 : term68 = True => @lem1991708)). Qed.
Lemma lem1991711 : term68 = True.
Proof. exact (EQ_MP (@lem1991710) (@lem1991708)). Qed.
Lemma lem1991712 : term57 = True.
Proof. exact (TRANS (@lem1991707) (@lem1991711)). Qed.
Lemma lem1991713 : True = term57.
Proof. exact (SYM (@lem1991712)). Qed.
Lemma lem1991714 : term57.
Proof. exact (EQ_MP (@lem1991713) (@lem0)). Qed.
Lemma lem1991715 : term307.
Proof. exact (@lem1991704 (@lem1991714)). Qed.
Lemma lem1991717 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1991718 : term215 = term216.
Proof. exact (@lem1991717 (NUMERAL 0) term179). Qed.
Lemma lem1991719 : term217 = term194.
Proof. exact (@lem912803). Qed.
Lemma lem1991720 (h1 : term217 = term194) : term216 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term194 h1). Qed.
Lemma lem1991721 : (term217 = term194) = (term216 = True).
Proof. exact (prop_ext (fun h1 : term217 = term194 => @lem1991720 h1) (fun h1 : term216 = True => @lem1991719)). Qed.
Lemma lem1991722 : term216 = True.
Proof. exact (EQ_MP (@lem1991721) (@lem1991719)). Qed.
Lemma lem1991723 : term215 = True.
Proof. exact (TRANS (@lem1991718) (@lem1991722)). Qed.
Lemma lem1991724 : True = term215.
Proof. exact (SYM (@lem1991723)). Qed.
Lemma lem1991725 : term215.
Proof. exact (EQ_MP (@lem1991724) (@lem0)). Qed.
Lemma lem1991726 : term305 = term308.
Proof. exact (@lem1991715 (@lem1991725)). Qed.
Lemma lem1991728 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1991729 : term74 = term75.
Proof. exact (@lem1991728 term61 term61). Qed.
Lemma lem1991730 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1991731 : term77 = term61.
Proof. exact (EQ_MP (@lem1991730) (@lem940073)). Qed.
Lemma lem1991732 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991733 : term75 = term58.
Proof. exact (MK_COMB (@lem1991732) (@lem1991731)). Qed.
Lemma lem1991734 : term74 = term58.
Proof. exact (TRANS (@lem1991729) (@lem1991733)). Qed.
Lemma lem1991736 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1991737 : term309 = term24.
Proof. exact (@lem1991736 term179). Qed.
Lemma lem1991738 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1991739 : term310 = term63.
Proof. exact (MK_COMB (@lem1991738) (@lem1991737)). Qed.
Lemma lem1991740 : term308 = term57.
Proof. exact (MK_COMB (@lem1991739) (@lem1991734)). Qed.
Lemma lem1991742 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1991743 : term57 = term68.
Proof. exact (@lem1991742 (NUMERAL 0) term61). Qed.
Lemma lem1991744 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1991745 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1991746 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1991745 h1) (fun h1 : term68 = True => @lem1991744)). Qed.
Lemma lem1991747 : term68 = True.
Proof. exact (EQ_MP (@lem1991746) (@lem1991744)). Qed.
Lemma lem1991748 : term57 = True.
Proof. exact (TRANS (@lem1991743) (@lem1991747)). Qed.
Lemma lem1991749 : term308 = True.
Proof. exact (TRANS (@lem1991740) (@lem1991748)). Qed.
Lemma lem1991750 : term305 = True.
Proof. exact (TRANS (@lem1991726) (@lem1991749)). Qed.
Lemma lem1991751 : term304 = True.
Proof. exact (TRANS (@lem1991703) (@lem1991750)). Qed.
Lemma lem1991752 : term303 = True.
Proof. exact (TRANS (@lem1991696) (@lem1991751)). Qed.
Lemma lem1991753 : True = term303.
Proof. exact (SYM (@lem1991752)). Qed.
Lemma lem1991754 : term303.
Proof. exact (EQ_MP (@lem1991753) (@lem0)). Qed.
Lemma lem1991755 (x : real) (y : real) (h1 : term297 x y) : term311 x y.
Proof. exact (conj (@lem1991754) (@lem1991618 x y h1)). Qed.
Lemma lem1991757 (x : real) (y : real) : term88 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem1991758 (x : real) (y : real) : term312 x y.
Proof. exact (@lem1991757 term178 (term19 x y)). Qed.
Lemma lem1991759 (x : real) (y : real) (h1 : term297 x y) : term313 x y.
Proof. exact (@lem1991758 x y (@lem1991755 x y h1)). Qed.
Lemma lem1991760 (x : real) (y : real) : (term183 x y) = (term184 x y).
Proof. exact (@lem1982781 x term178 (term21 y)). Qed.
Lemma lem1991761 (y : real) : (term185 y) = (term186 y).
Proof. exact (@lem1982749 term178 term107 y). Qed.
Lemma lem1991763 (x : nat) : (term108 x) = (term109 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1991764 : term107 = term110.
Proof. exact (@lem1991763 term61). Qed.
Lemma lem1991767 : term187 = term187.
Proof. exact (eq_refl term187). Qed.
Lemma lem1991768 : term188 = term189.
Proof. exact (MK_COMB (@lem1991767) (@lem1991764)). Qed.
Lemma lem1991769 : term189 = term190.
Proof. exact (@lem1981613 term58 term107 term174 term58). Qed.
Lemma lem1991771 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1991772 : term191 = term192.
Proof. exact (@lem1991771 term179 term61). Qed.
Lemma lem1991773 : term193 = term194.
Proof. exact (@lem996237 term194). Qed.
Lemma lem1991774 : (term193 = term194) = (term195 = term179).
Proof. exact (@lem1007663 term194 (BIT1 0) term194). Qed.
Lemma lem1991775 : term195 = term179.
Proof. exact (EQ_MP (@lem1991774) (@lem1991773)). Qed.
Lemma lem1991776 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991777 : term192 = term174.
Proof. exact (MK_COMB (@lem1991776) (@lem1991775)). Qed.
Lemma lem1991778 : term191 = term174.
Proof. exact (TRANS (@lem1991772) (@lem1991777)). Qed.
Lemma lem1991780 (m : nat) (n : nat) : (term196 m n) = (term120 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1991781 : term197 = term122.
Proof. exact (@lem1991780 term61 term61). Qed.
Lemma lem1991782 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1991783 : term77 = term61.
Proof. exact (EQ_MP (@lem1991782) (@lem940073)). Qed.
Lemma lem1991784 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991785 : term75 = term58.
Proof. exact (MK_COMB (@lem1991784) (@lem1991783)). Qed.
Lemma lem1991786 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1991787 : term122 = term107.
Proof. exact (MK_COMB (@lem1991786) (@lem1991785)). Qed.
Lemma lem1991788 : term197 = term107.
Proof. exact (TRANS (@lem1991781) (@lem1991787)). Qed.
Lemma lem1991789 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem1991790 : term198 = term199.
Proof. exact (MK_COMB (@lem1991789) (@lem1991788)). Qed.
Lemma lem1991791 : term190 = term200.
Proof. exact (MK_COMB (@lem1991790) (@lem1991778)). Qed.
Lemma lem1991792 : term189 = term200.
Proof. exact (TRANS (@lem1991769) (@lem1991791)). Qed.
Lemma lem1991795 : term188 = term200.
Proof. exact (TRANS (@lem1991768) (@lem1991792)). Qed.
Lemma lem1991796 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1991797 : term201 = term202.
Proof. exact (MK_COMB (@lem1991796) (@lem1991795)). Qed.
Lemma lem1991798 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1991799 (y : real) : (term186 y) = (term203 y).
Proof. exact (MK_COMB (@lem1991797) (@lem1991798 y)). Qed.
Lemma lem1991800 (y : real) : (term185 y) = (term203 y).
Proof. exact (TRANS (@lem1991761 y) (@lem1991799 y)). Qed.
Lemma lem1991803 (x : real) : (term204 x) = (term204 x).
Proof. exact (eq_refl (term204 x)). Qed.
Lemma lem1991804 (x : real) (y : real) : (term184 x y) = (term205 x y).
Proof. exact (MK_COMB (@lem1991803 x) (@lem1991800 y)). Qed.
Lemma lem1991805 (x : real) (y : real) : (term183 x y) = (term205 x y).
Proof. exact (TRANS (@lem1991760 x y) (@lem1991804 x y)). Qed.
Lemma lem1991806 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1991807 (x : real) (y : real) : (term314 x y) = (term315 x y).
Proof. exact (MK_COMB (@lem1991806) (@lem1991805 x y)). Qed.
Lemma lem1991808 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1991809 (x : real) (y : real) : (term313 x y) = (term316 x y).
Proof. exact (MK_COMB (@lem1991807 x y) (@lem1991808)). Qed.
Lemma lem1991810 (x : real) (y : real) (h1 : term297 x y) : term316 x y.
Proof. exact (EQ_MP (@lem1991809 x y) (@lem1991759 x y h1)). Qed.
Lemma lem1991811 (x : real) (y : real) (h1 : term297 x y) : term317 x y.
Proof. exact (conj (@lem1991810 x y h1) (@lem1991693 x y h1)). Qed.
Lemma lem1991813 (x : real) (y : real) : term137 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem1991814 (x : real) (y : real) : term318 x y.
Proof. exact (@lem1991813 (term205 x y) (term256 x y)). Qed.
Lemma lem1991815 (x : real) (y : real) (h1 : term297 x y) : term319 x y.
Proof. exact (@lem1991814 x y (@lem1991811 x y h1)). Qed.
Lemma lem1991816 (x : real) (y : real) : (term320 x y) = (term321 x y).
Proof. exact (@lem1982753 (term208 x) (term203 x) (term203 y) (term208 y)). Qed.
Lemma lem1991817 (x : real) : (term322 x) = (term323 x).
Proof. exact (@lem1982711 term178 term200 x). Qed.
Lemma lem1991823 : term324.
Proof. exact (@lem1981473 term58 term174 term107 term174 term24 term58). Qed.
Lemma lem1991825 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1991826 : term215 = term216.
Proof. exact (@lem1991825 (NUMERAL 0) term179). Qed.
Lemma lem1991827 : term217 = term194.
Proof. exact (@lem912803). Qed.
Lemma lem1991828 (h1 : term217 = term194) : term216 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term194 h1). Qed.
Lemma lem1991829 : (term217 = term194) = (term216 = True).
Proof. exact (prop_ext (fun h1 : term217 = term194 => @lem1991828 h1) (fun h1 : term216 = True => @lem1991827)). Qed.
Lemma lem1991830 : term216 = True.
Proof. exact (EQ_MP (@lem1991829) (@lem1991827)). Qed.
Lemma lem1991831 : term215 = True.
Proof. exact (TRANS (@lem1991826) (@lem1991830)). Qed.
Lemma lem1991832 : True = term215.
Proof. exact (SYM (@lem1991831)). Qed.
Lemma lem1991833 : term215.
Proof. exact (EQ_MP (@lem1991832) (@lem0)). Qed.
Lemma lem1991834 : term325.
Proof. exact (@lem1991823 (@lem1991833)). Qed.
Lemma lem1991836 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1991837 : term215 = term216.
Proof. exact (@lem1991836 (NUMERAL 0) term179). Qed.
Lemma lem1991838 : term217 = term194.
Proof. exact (@lem912803). Qed.
Lemma lem1991839 (h1 : term217 = term194) : term216 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term194 h1). Qed.
Lemma lem1991840 : (term217 = term194) = (term216 = True).
Proof. exact (prop_ext (fun h1 : term217 = term194 => @lem1991839 h1) (fun h1 : term216 = True => @lem1991838)). Qed.
Lemma lem1991841 : term216 = True.
Proof. exact (EQ_MP (@lem1991840) (@lem1991838)). Qed.
Lemma lem1991842 : term215 = True.
Proof. exact (TRANS (@lem1991837) (@lem1991841)). Qed.
Lemma lem1991843 : True = term215.
Proof. exact (SYM (@lem1991842)). Qed.
Lemma lem1991844 : term215.
Proof. exact (EQ_MP (@lem1991843) (@lem0)). Qed.
Lemma lem1991845 : term326.
Proof. exact (@lem1991834 (@lem1991844)). Qed.
Lemma lem1991847 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1991848 : term57 = term68.
Proof. exact (@lem1991847 (NUMERAL 0) term61). Qed.
Lemma lem1991849 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1991850 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1991851 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1991850 h1) (fun h1 : term68 = True => @lem1991849)). Qed.
Lemma lem1991852 : term68 = True.
Proof. exact (EQ_MP (@lem1991851) (@lem1991849)). Qed.
Lemma lem1991853 : term57 = True.
Proof. exact (TRANS (@lem1991848) (@lem1991852)). Qed.
Lemma lem1991854 : True = term57.
Proof. exact (SYM (@lem1991853)). Qed.
Lemma lem1991855 : term57.
Proof. exact (EQ_MP (@lem1991854) (@lem0)). Qed.
Lemma lem1991856 : term327.
Proof. exact (@lem1991845 (@lem1991855)). Qed.
Lemma lem1991858 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1991859 : term276 = term277.
Proof. exact (@lem1991858 term61 term179). Qed.
Lemma lem1991860 : term223 = term194.
Proof. exact (@lem996238 term194). Qed.
Lemma lem1991861 : (term223 = term194) = (term224 = term179).
Proof. exact (@lem1007663 (BIT1 0) term194 term194). Qed.
Lemma lem1991862 : term224 = term179.
Proof. exact (EQ_MP (@lem1991861) (@lem1991860)). Qed.
Lemma lem1991863 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991864 : term222 = term174.
Proof. exact (MK_COMB (@lem1991863) (@lem1991862)). Qed.
Lemma lem1991865 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1991866 : term277 = term278.
Proof. exact (MK_COMB (@lem1991865) (@lem1991864)). Qed.
Lemma lem1991867 : term276 = term278.
Proof. exact (TRANS (@lem1991859) (@lem1991866)). Qed.
Lemma lem1991869 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1991870 : term221 = term222.
Proof. exact (@lem1991869 term61 term179). Qed.
Lemma lem1991871 : term223 = term194.
Proof. exact (@lem996238 term194). Qed.
Lemma lem1991872 : (term223 = term194) = (term224 = term179).
Proof. exact (@lem1007663 (BIT1 0) term194 term194). Qed.
Lemma lem1991873 : term224 = term179.
Proof. exact (EQ_MP (@lem1991872) (@lem1991871)). Qed.
Lemma lem1991874 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991875 : term222 = term174.
Proof. exact (MK_COMB (@lem1991874) (@lem1991873)). Qed.
Lemma lem1991876 : term221 = term174.
Proof. exact (TRANS (@lem1991870) (@lem1991875)). Qed.
Lemma lem1991877 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1991878 : term328 = term329.
Proof. exact (MK_COMB (@lem1991877) (@lem1991876)). Qed.
Lemma lem1991879 : term330 = term331.
Proof. exact (MK_COMB (@lem1991878) (@lem1991867)). Qed.
Lemma lem1991881 (m : nat) : (term332 m) = term24.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1991882 : term331 = term24.
Proof. exact (@lem1991881 term179). Qed.
Lemma lem1991883 : term330 = term24.
Proof. exact (TRANS (@lem1991879) (@lem1991882)). Qed.
Lemma lem1991884 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1991885 : term333 = term127.
Proof. exact (MK_COMB (@lem1991884) (@lem1991883)). Qed.
Lemma lem1991886 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1991887 : term334 = term79.
Proof. exact (MK_COMB (@lem1991885) (@lem1991886)). Qed.
Lemma lem1991889 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1991890 : term79 = term24.
Proof. exact (@lem1991889 term61). Qed.
Lemma lem1991891 : term334 = term24.
Proof. exact (TRANS (@lem1991887) (@lem1991890)). Qed.
Lemma lem1991893 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1991894 : term335 = term336.
Proof. exact (@lem1991893 term179 term179). Qed.
Lemma lem1991895 : (term76 = (BIT1 0)) = (term337 = term338).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1991896 : term337 = term338.
Proof. exact (EQ_MP (@lem1991895) (@lem940073)). Qed.
Lemma lem1991897 : (term337 = term338) = (term339 = term340).
Proof. exact (@lem1008952 term194 term338). Qed.
Lemma lem1991898 : term339 = term340.
Proof. exact (EQ_MP (@lem1991897) (@lem1991896)). Qed.
Lemma lem1991899 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991900 : term336 = term341.
Proof. exact (MK_COMB (@lem1991899) (@lem1991898)). Qed.
Lemma lem1991901 : term335 = term341.
Proof. exact (TRANS (@lem1991894) (@lem1991900)). Qed.
Lemma lem1991902 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem1991903 : term342 = term343.
Proof. exact (MK_COMB (@lem1991902) (@lem1991901)). Qed.
Lemma lem1991905 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1991906 : term343 = term24.
Proof. exact (@lem1991905 term340). Qed.
Lemma lem1991907 : term342 = term24.
Proof. exact (TRANS (@lem1991903) (@lem1991906)). Qed.
Lemma lem1991908 : term24 = term342.
Proof. exact (SYM (@lem1991907)). Qed.
Lemma lem1991909 : term334 = term342.
Proof. exact (TRANS (@lem1991891) (@lem1991908)). Qed.
Lemma lem1991911 : term344 = term62.
Proof. exact (@lem1991856 (@lem1991909)). Qed.
Lemma lem1991913 (x : real) : (term130 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem1991914 : term62 = term24.
Proof. exact (@lem1991913 term24). Qed.
Lemma lem1991915 : term344 = term24.
Proof. exact (TRANS (@lem1991911) (@lem1991914)). Qed.
Lemma lem1991916 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1991917 : term345 = term127.
Proof. exact (MK_COMB (@lem1991916) (@lem1991915)). Qed.
Lemma lem1991918 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1991919 (x : real) : (term323 x) = (term132 x).
Proof. exact (MK_COMB (@lem1991917) (@lem1991918 x)). Qed.
Lemma lem1991920 (x : real) : (term322 x) = (term132 x).
Proof. exact (TRANS (@lem1991817 x) (@lem1991919 x)). Qed.
Lemma lem1991921 (x : real) : (term132 x) = term24.
Proof. exact (@lem1982719 x). Qed.
Lemma lem1991922 (x : real) : (term322 x) = term24.
Proof. exact (TRANS (@lem1991920 x) (@lem1991921 x)). Qed.
Lemma lem1991923 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1991924 (x : real) : (term346 x) = term144.
Proof. exact (MK_COMB (@lem1991923) (@lem1991922 x)). Qed.
Lemma lem1991925 (y : real) : (term347 y) = (term348 y).
Proof. exact (@lem1982711 term200 term178 y). Qed.
Lemma lem1991931 : term349.
Proof. exact (@lem1981473 term107 term174 term58 term174 term24 term58). Qed.
Lemma lem1991933 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1991934 : term215 = term216.
Proof. exact (@lem1991933 (NUMERAL 0) term179). Qed.
Lemma lem1991935 : term217 = term194.
Proof. exact (@lem912803). Qed.
Lemma lem1991936 (h1 : term217 = term194) : term216 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term194 h1). Qed.
Lemma lem1991937 : (term217 = term194) = (term216 = True).
Proof. exact (prop_ext (fun h1 : term217 = term194 => @lem1991936 h1) (fun h1 : term216 = True => @lem1991935)). Qed.
Lemma lem1991938 : term216 = True.
Proof. exact (EQ_MP (@lem1991937) (@lem1991935)). Qed.
Lemma lem1991939 : term215 = True.
Proof. exact (TRANS (@lem1991934) (@lem1991938)). Qed.
Lemma lem1991940 : True = term215.
Proof. exact (SYM (@lem1991939)). Qed.
Lemma lem1991941 : term215.
Proof. exact (EQ_MP (@lem1991940) (@lem0)). Qed.
Lemma lem1991942 : term350.
Proof. exact (@lem1991931 (@lem1991941)). Qed.
Lemma lem1991944 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1991945 : term215 = term216.
Proof. exact (@lem1991944 (NUMERAL 0) term179). Qed.
Lemma lem1991946 : term217 = term194.
Proof. exact (@lem912803). Qed.
Lemma lem1991947 (h1 : term217 = term194) : term216 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term194 h1). Qed.
Lemma lem1991948 : (term217 = term194) = (term216 = True).
Proof. exact (prop_ext (fun h1 : term217 = term194 => @lem1991947 h1) (fun h1 : term216 = True => @lem1991946)). Qed.
Lemma lem1991949 : term216 = True.
Proof. exact (EQ_MP (@lem1991948) (@lem1991946)). Qed.
Lemma lem1991950 : term215 = True.
Proof. exact (TRANS (@lem1991945) (@lem1991949)). Qed.
Lemma lem1991951 : True = term215.
Proof. exact (SYM (@lem1991950)). Qed.
Lemma lem1991952 : term215.
Proof. exact (EQ_MP (@lem1991951) (@lem0)). Qed.
Lemma lem1991953 : term351.
Proof. exact (@lem1991942 (@lem1991952)). Qed.
Lemma lem1991955 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1991956 : term57 = term68.
Proof. exact (@lem1991955 (NUMERAL 0) term61). Qed.
Lemma lem1991957 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1991958 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1991959 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1991958 h1) (fun h1 : term68 = True => @lem1991957)). Qed.
Lemma lem1991960 : term68 = True.
Proof. exact (EQ_MP (@lem1991959) (@lem1991957)). Qed.
Lemma lem1991961 : term57 = True.
Proof. exact (TRANS (@lem1991956) (@lem1991960)). Qed.
Lemma lem1991962 : True = term57.
Proof. exact (SYM (@lem1991961)). Qed.
Lemma lem1991963 : term57.
Proof. exact (EQ_MP (@lem1991962) (@lem0)). Qed.
Lemma lem1991964 : term352.
Proof. exact (@lem1991953 (@lem1991963)). Qed.
Lemma lem1991966 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1991967 : term221 = term222.
Proof. exact (@lem1991966 term61 term179). Qed.
Lemma lem1991968 : term223 = term194.
Proof. exact (@lem996238 term194). Qed.
Lemma lem1991969 : (term223 = term194) = (term224 = term179).
Proof. exact (@lem1007663 (BIT1 0) term194 term194). Qed.
Lemma lem1991970 : term224 = term179.
Proof. exact (EQ_MP (@lem1991969) (@lem1991968)). Qed.
Lemma lem1991971 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991972 : term222 = term174.
Proof. exact (MK_COMB (@lem1991971) (@lem1991970)). Qed.
Lemma lem1991973 : term221 = term174.
Proof. exact (TRANS (@lem1991967) (@lem1991972)). Qed.
Lemma lem1991975 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1991976 : term276 = term277.
Proof. exact (@lem1991975 term61 term179). Qed.
Lemma lem1991977 : term223 = term194.
Proof. exact (@lem996238 term194). Qed.
Lemma lem1991978 : (term223 = term194) = (term224 = term179).
Proof. exact (@lem1007663 (BIT1 0) term194 term194). Qed.
Lemma lem1991979 : term224 = term179.
Proof. exact (EQ_MP (@lem1991978) (@lem1991977)). Qed.
Lemma lem1991980 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1991981 : term222 = term174.
Proof. exact (MK_COMB (@lem1991980) (@lem1991979)). Qed.
Lemma lem1991982 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1991983 : term277 = term278.
Proof. exact (MK_COMB (@lem1991982) (@lem1991981)). Qed.
Lemma lem1991984 : term276 = term278.
Proof. exact (TRANS (@lem1991976) (@lem1991983)). Qed.
Lemma lem1991985 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1991986 : term353 = term354.
Proof. exact (MK_COMB (@lem1991985) (@lem1991984)). Qed.
Lemma lem1991987 : term355 = term356.
Proof. exact (MK_COMB (@lem1991986) (@lem1991973)). Qed.
Lemma lem1991989 (m : nat) : (term125 m) = term24.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1991990 : term356 = term24.
Proof. exact (@lem1991989 term179). Qed.
Lemma lem1991991 : term355 = term24.
Proof. exact (TRANS (@lem1991987) (@lem1991990)). Qed.
Lemma lem1991992 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1991993 : term357 = term127.
Proof. exact (MK_COMB (@lem1991992) (@lem1991991)). Qed.
Lemma lem1991994 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1991995 : term358 = term79.
Proof. exact (MK_COMB (@lem1991993) (@lem1991994)). Qed.
Lemma lem1991997 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1991998 : term79 = term24.
Proof. exact (@lem1991997 term61). Qed.
Lemma lem1991999 : term358 = term24.
Proof. exact (TRANS (@lem1991995) (@lem1991998)). Qed.
Lemma lem1992001 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1992002 : term335 = term336.
Proof. exact (@lem1992001 term179 term179). Qed.
Lemma lem1992003 : (term76 = (BIT1 0)) = (term337 = term338).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1992004 : term337 = term338.
Proof. exact (EQ_MP (@lem1992003) (@lem940073)). Qed.
Lemma lem1992005 : (term337 = term338) = (term339 = term340).
Proof. exact (@lem1008952 term194 term338). Qed.
Lemma lem1992006 : term339 = term340.
Proof. exact (EQ_MP (@lem1992005) (@lem1992004)). Qed.
Lemma lem1992007 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1992008 : term336 = term341.
Proof. exact (MK_COMB (@lem1992007) (@lem1992006)). Qed.
Lemma lem1992009 : term335 = term341.
Proof. exact (TRANS (@lem1992002) (@lem1992008)). Qed.
Lemma lem1992010 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem1992011 : term342 = term343.
Proof. exact (MK_COMB (@lem1992010) (@lem1992009)). Qed.
Lemma lem1992013 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1992014 : term343 = term24.
Proof. exact (@lem1992013 term340). Qed.
Lemma lem1992015 : term342 = term24.
Proof. exact (TRANS (@lem1992011) (@lem1992014)). Qed.
Lemma lem1992016 : term24 = term342.
Proof. exact (SYM (@lem1992015)). Qed.
Lemma lem1992017 : term358 = term342.
Proof. exact (TRANS (@lem1991999) (@lem1992016)). Qed.
Lemma lem1992019 : term359 = term62.
Proof. exact (@lem1991964 (@lem1992017)). Qed.
Lemma lem1992021 (x : real) : (term130 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem1992022 : term62 = term24.
Proof. exact (@lem1992021 term24). Qed.
Lemma lem1992023 : term359 = term24.
Proof. exact (TRANS (@lem1992019) (@lem1992022)). Qed.
Lemma lem1992024 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1992025 : term360 = term127.
Proof. exact (MK_COMB (@lem1992024) (@lem1992023)). Qed.
Lemma lem1992026 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1992027 (y : real) : (term348 y) = (term132 y).
Proof. exact (MK_COMB (@lem1992025) (@lem1992026 y)). Qed.
Lemma lem1992028 (y : real) : (term347 y) = (term132 y).
Proof. exact (TRANS (@lem1991925 y) (@lem1992027 y)). Qed.
Lemma lem1992029 (y : real) : (term132 y) = term24.
Proof. exact (@lem1982719 y). Qed.
Lemma lem1992030 (y : real) : (term347 y) = term24.
Proof. exact (TRANS (@lem1992028 y) (@lem1992029 y)). Qed.
Lemma lem1992031 (x : real) (y : real) : (term321 x y) = term145.
Proof. exact (MK_COMB (@lem1991924 x) (@lem1992030 y)). Qed.
Lemma lem1992032 (x : real) (y : real) : (term320 x y) = term145.
Proof. exact (TRANS (@lem1991816 x y) (@lem1992031 x y)). Qed.
Lemma lem1992033 : term145 = term24.
Proof. exact (@lem1982721 term24). Qed.
Lemma lem1992034 (x : real) (y : real) : (term320 x y) = term24.
Proof. exact (TRANS (@lem1992032 x y) (@lem1992033)). Qed.
Lemma lem1992035 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1992036 (x : real) (y : real) : (term361 x y) = term147.
Proof. exact (MK_COMB (@lem1992035) (@lem1992034 x y)). Qed.
Lemma lem1992037 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1992038 (x : real) (y : real) : (term319 x y) = term148.
Proof. exact (MK_COMB (@lem1992036 x y) (@lem1992037)). Qed.
Lemma lem1992039 (x : real) (y : real) (h1 : term297 x y) : term148.
Proof. exact (EQ_MP (@lem1992038 x y) (@lem1991815 x y h1)). Qed.
Lemma lem1992041 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1992042 : term148 = term149.
Proof. exact (@lem1992041 term24 term24). Qed.
Lemma lem1992044 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1992045 : term24 = term62.
Proof. exact (@lem1992044 (NUMERAL 0)). Qed.
Lemma lem1992047 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1992048 : term24 = term62.
Proof. exact (@lem1992047 (NUMERAL 0)). Qed.
Lemma lem1992049 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1992050 : term63 = term64.
Proof. exact (MK_COMB (@lem1992049) (@lem1992048)). Qed.
Lemma lem1992051 : term149 = term150.
Proof. exact (MK_COMB (@lem1992050) (@lem1992045)). Qed.
Lemma lem1992052 : term151.
Proof. exact (@lem1980255 term24 term58 term24 term58). Qed.
Lemma lem1992054 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1992055 : term57 = term68.
Proof. exact (@lem1992054 (NUMERAL 0) term61). Qed.
Lemma lem1992056 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1992057 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1992058 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1992057 h1) (fun h1 : term68 = True => @lem1992056)). Qed.
Lemma lem1992059 : term68 = True.
Proof. exact (EQ_MP (@lem1992058) (@lem1992056)). Qed.
Lemma lem1992060 : term57 = True.
Proof. exact (TRANS (@lem1992055) (@lem1992059)). Qed.
Lemma lem1992061 : True = term57.
Proof. exact (SYM (@lem1992060)). Qed.
Lemma lem1992062 : term57.
Proof. exact (EQ_MP (@lem1992061) (@lem0)). Qed.
Lemma lem1992063 : term152.
Proof. exact (@lem1992052 (@lem1992062)). Qed.
Lemma lem1992065 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1992066 : term57 = term68.
Proof. exact (@lem1992065 (NUMERAL 0) term61). Qed.
Lemma lem1992067 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1992068 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1992069 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1992068 h1) (fun h1 : term68 = True => @lem1992067)). Qed.
Lemma lem1992070 : term68 = True.
Proof. exact (EQ_MP (@lem1992069) (@lem1992067)). Qed.
Lemma lem1992071 : term57 = True.
Proof. exact (TRANS (@lem1992066) (@lem1992070)). Qed.
Lemma lem1992072 : True = term57.
Proof. exact (SYM (@lem1992071)). Qed.
Lemma lem1992073 : term57.
Proof. exact (EQ_MP (@lem1992072) (@lem0)). Qed.
Lemma lem1992074 : term150 = term153.
Proof. exact (@lem1992063 (@lem1992073)). Qed.
Lemma lem1992076 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1992077 : term79 = term24.
Proof. exact (@lem1992076 term61). Qed.
Lemma lem1992079 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1992080 : term79 = term24.
Proof. exact (@lem1992079 term61). Qed.
Lemma lem1992081 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1992082 : term80 = term63.
Proof. exact (MK_COMB (@lem1992081) (@lem1992080)). Qed.
Lemma lem1992083 : term153 = term149.
Proof. exact (MK_COMB (@lem1992082) (@lem1992077)). Qed.
Lemma lem1992085 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1992086 : term149 = term154.
Proof. exact (@lem1992085 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1992087 : term154 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1992088 : term149 = False.
Proof. exact (TRANS (@lem1992086) (@lem1992087)). Qed.
Lemma lem1992089 : term153 = False.
Proof. exact (TRANS (@lem1992083) (@lem1992088)). Qed.
Lemma lem1992090 : term150 = False.
Proof. exact (TRANS (@lem1992074) (@lem1992089)). Qed.
Lemma lem1992091 : term149 = False.
Proof. exact (TRANS (@lem1992051) (@lem1992090)). Qed.
Lemma lem1992092 : term148 = False.
Proof. exact (TRANS (@lem1992042) (@lem1992091)). Qed.
Lemma lem1992093 (x : real) (y : real) (h1 : term297 x y) : False.
Proof. exact (EQ_MP (@lem1992092) (@lem1992039 x y h1)). Qed.
Lemma lem1992094 (x : real) (y : real) (h1 : term297 x y) : term297 x y.
Proof. exact (h1). Qed.
Lemma lem1992095 (x : real) (y : real) (h1 : term297 x y) : term32 x y.
Proof. exact (proj2 (@lem1992094 x y h1)). Qed.
Lemma lem1992096 (x : real) (y : real) (h1 : term297 x y) : term259 x y.
Proof. exact (proj1 (@lem1992094 x y h1)). Qed.
Lemma lem1992098 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1992099 : term56 = term57.
Proof. exact (@lem1992098 term24 term58). Qed.
Lemma lem1992101 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1992102 : term58 = term60.
Proof. exact (@lem1992101 term61). Qed.
Lemma lem1992104 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1992105 : term24 = term62.
Proof. exact (@lem1992104 (NUMERAL 0)). Qed.
Lemma lem1992106 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1992107 : term63 = term64.
Proof. exact (MK_COMB (@lem1992106) (@lem1992105)). Qed.
Lemma lem1992108 : term57 = term65.
Proof. exact (MK_COMB (@lem1992107) (@lem1992102)). Qed.
Lemma lem1992109 : term66.
Proof. exact (@lem1980255 term24 term58 term58 term58). Qed.
Lemma lem1992111 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1992112 : term57 = term68.
Proof. exact (@lem1992111 (NUMERAL 0) term61). Qed.
Lemma lem1992113 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1992114 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1992115 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1992114 h1) (fun h1 : term68 = True => @lem1992113)). Qed.
Lemma lem1992116 : term68 = True.
Proof. exact (EQ_MP (@lem1992115) (@lem1992113)). Qed.
Lemma lem1992117 : term57 = True.
Proof. exact (TRANS (@lem1992112) (@lem1992116)). Qed.
Lemma lem1992118 : True = term57.
Proof. exact (SYM (@lem1992117)). Qed.
Lemma lem1992119 : term57.
Proof. exact (EQ_MP (@lem1992118) (@lem0)). Qed.
Lemma lem1992120 : term70.
Proof. exact (@lem1992109 (@lem1992119)). Qed.
Lemma lem1992122 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1992123 : term57 = term68.
Proof. exact (@lem1992122 (NUMERAL 0) term61). Qed.
Lemma lem1992124 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1992125 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1992126 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1992125 h1) (fun h1 : term68 = True => @lem1992124)). Qed.
Lemma lem1992127 : term68 = True.
Proof. exact (EQ_MP (@lem1992126) (@lem1992124)). Qed.
Lemma lem1992128 : term57 = True.
Proof. exact (TRANS (@lem1992123) (@lem1992127)). Qed.
Lemma lem1992129 : True = term57.
Proof. exact (SYM (@lem1992128)). Qed.
Lemma lem1992130 : term57.
Proof. exact (EQ_MP (@lem1992129) (@lem0)). Qed.
Lemma lem1992131 : term65 = term71.
Proof. exact (@lem1992120 (@lem1992130)). Qed.
Lemma lem1992133 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1992134 : term74 = term75.
Proof. exact (@lem1992133 term61 term61). Qed.
Lemma lem1992135 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1992136 : term77 = term61.
Proof. exact (EQ_MP (@lem1992135) (@lem940073)). Qed.
Lemma lem1992137 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1992138 : term75 = term58.
Proof. exact (MK_COMB (@lem1992137) (@lem1992136)). Qed.
Lemma lem1992139 : term74 = term58.
Proof. exact (TRANS (@lem1992134) (@lem1992138)). Qed.
Lemma lem1992141 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1992142 : term79 = term24.
Proof. exact (@lem1992141 term61). Qed.
Lemma lem1992143 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1992144 : term80 = term63.
Proof. exact (MK_COMB (@lem1992143) (@lem1992142)). Qed.
Lemma lem1992145 : term71 = term57.
Proof. exact (MK_COMB (@lem1992144) (@lem1992139)). Qed.
Lemma lem1992147 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1992148 : term57 = term68.
Proof. exact (@lem1992147 (NUMERAL 0) term61). Qed.
Lemma lem1992149 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1992150 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1992151 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1992150 h1) (fun h1 : term68 = True => @lem1992149)). Qed.
Lemma lem1992152 : term68 = True.
Proof. exact (EQ_MP (@lem1992151) (@lem1992149)). Qed.
Lemma lem1992153 : term57 = True.
Proof. exact (TRANS (@lem1992148) (@lem1992152)). Qed.
Lemma lem1992154 : term71 = True.
Proof. exact (TRANS (@lem1992145) (@lem1992153)). Qed.
Lemma lem1992155 : term65 = True.
Proof. exact (TRANS (@lem1992131) (@lem1992154)). Qed.
Lemma lem1992156 : term57 = True.
Proof. exact (TRANS (@lem1992108) (@lem1992155)). Qed.
Lemma lem1992157 : term56 = True.
Proof. exact (TRANS (@lem1992099) (@lem1992156)). Qed.
Lemma lem1992158 : True = term56.
Proof. exact (SYM (@lem1992157)). Qed.
Lemma lem1992159 : term56.
Proof. exact (EQ_MP (@lem1992158) (@lem0)). Qed.
Lemma lem1992160 (x : real) (y : real) (h1 : term297 x y) : term298 x y.
Proof. exact (conj (@lem1992159) (@lem1992096 x y h1)). Qed.
Lemma lem1992162 (x : real) (y : real) : term82 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem1992163 (x : real) (y : real) : term299 x y.
Proof. exact (@lem1992162 term58 (term256 x y)). Qed.
Lemma lem1992164 (x : real) (y : real) (h1 : term297 x y) : term300 x y.
Proof. exact (@lem1992163 x y (@lem1992160 x y h1)). Qed.
Lemma lem1992165 (x : real) (y : real) : (term301 x y) = (term256 x y).
Proof. exact (@lem1982733 (term256 x y)). Qed.
Lemma lem1992166 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1992167 (x : real) (y : real) : (term302 x y) = (term258 x y).
Proof. exact (MK_COMB (@lem1992166) (@lem1992165 x y)). Qed.
Lemma lem1992168 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1992169 (x : real) (y : real) : (term300 x y) = (term259 x y).
Proof. exact (MK_COMB (@lem1992167 x y) (@lem1992168)). Qed.
Lemma lem1992170 (x : real) (y : real) (h1 : term297 x y) : term259 x y.
Proof. exact (EQ_MP (@lem1992169 x y) (@lem1992164 x y h1)). Qed.
Lemma lem1992172 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1992173 : term303 = term304.
Proof. exact (@lem1992172 term24 term178). Qed.
Lemma lem1992174 : term178 = term178.
Proof. exact (eq_refl term178). Qed.
Lemma lem1992176 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1992177 : term24 = term62.
Proof. exact (@lem1992176 (NUMERAL 0)). Qed.
Lemma lem1992178 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1992179 : term63 = term64.
Proof. exact (MK_COMB (@lem1992178) (@lem1992177)). Qed.
Lemma lem1992180 : term304 = term305.
Proof. exact (MK_COMB (@lem1992179) (@lem1992174)). Qed.
Lemma lem1992181 : term306.
Proof. exact (@lem1980255 term24 term174 term58 term58). Qed.
Lemma lem1992183 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1992184 : term57 = term68.
Proof. exact (@lem1992183 (NUMERAL 0) term61). Qed.
Lemma lem1992185 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1992186 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1992187 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1992186 h1) (fun h1 : term68 = True => @lem1992185)). Qed.
Lemma lem1992188 : term68 = True.
Proof. exact (EQ_MP (@lem1992187) (@lem1992185)). Qed.
Lemma lem1992189 : term57 = True.
Proof. exact (TRANS (@lem1992184) (@lem1992188)). Qed.
Lemma lem1992190 : True = term57.
Proof. exact (SYM (@lem1992189)). Qed.
Lemma lem1992191 : term57.
Proof. exact (EQ_MP (@lem1992190) (@lem0)). Qed.
Lemma lem1992192 : term307.
Proof. exact (@lem1992181 (@lem1992191)). Qed.
Lemma lem1992194 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1992195 : term215 = term216.
Proof. exact (@lem1992194 (NUMERAL 0) term179). Qed.
Lemma lem1992196 : term217 = term194.
Proof. exact (@lem912803). Qed.
Lemma lem1992197 (h1 : term217 = term194) : term216 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term194 h1). Qed.
Lemma lem1992198 : (term217 = term194) = (term216 = True).
Proof. exact (prop_ext (fun h1 : term217 = term194 => @lem1992197 h1) (fun h1 : term216 = True => @lem1992196)). Qed.
Lemma lem1992199 : term216 = True.
Proof. exact (EQ_MP (@lem1992198) (@lem1992196)). Qed.
Lemma lem1992200 : term215 = True.
Proof. exact (TRANS (@lem1992195) (@lem1992199)). Qed.
Lemma lem1992201 : True = term215.
Proof. exact (SYM (@lem1992200)). Qed.
Lemma lem1992202 : term215.
Proof. exact (EQ_MP (@lem1992201) (@lem0)). Qed.
Lemma lem1992203 : term305 = term308.
Proof. exact (@lem1992192 (@lem1992202)). Qed.
Lemma lem1992205 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1992206 : term74 = term75.
Proof. exact (@lem1992205 term61 term61). Qed.
Lemma lem1992207 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1992208 : term77 = term61.
Proof. exact (EQ_MP (@lem1992207) (@lem940073)). Qed.
Lemma lem1992209 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1992210 : term75 = term58.
Proof. exact (MK_COMB (@lem1992209) (@lem1992208)). Qed.
Lemma lem1992211 : term74 = term58.
Proof. exact (TRANS (@lem1992206) (@lem1992210)). Qed.
Lemma lem1992213 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1992214 : term309 = term24.
Proof. exact (@lem1992213 term179). Qed.
Lemma lem1992215 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1992216 : term310 = term63.
Proof. exact (MK_COMB (@lem1992215) (@lem1992214)). Qed.
Lemma lem1992217 : term308 = term57.
Proof. exact (MK_COMB (@lem1992216) (@lem1992211)). Qed.
Lemma lem1992219 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1992220 : term57 = term68.
Proof. exact (@lem1992219 (NUMERAL 0) term61). Qed.
Lemma lem1992221 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1992222 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1992223 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1992222 h1) (fun h1 : term68 = True => @lem1992221)). Qed.
Lemma lem1992224 : term68 = True.
Proof. exact (EQ_MP (@lem1992223) (@lem1992221)). Qed.
Lemma lem1992225 : term57 = True.
Proof. exact (TRANS (@lem1992220) (@lem1992224)). Qed.
Lemma lem1992226 : term308 = True.
Proof. exact (TRANS (@lem1992217) (@lem1992225)). Qed.
Lemma lem1992227 : term305 = True.
Proof. exact (TRANS (@lem1992203) (@lem1992226)). Qed.
Lemma lem1992228 : term304 = True.
Proof. exact (TRANS (@lem1992180) (@lem1992227)). Qed.
Lemma lem1992229 : term303 = True.
Proof. exact (TRANS (@lem1992173) (@lem1992228)). Qed.
Lemma lem1992230 : True = term303.
Proof. exact (SYM (@lem1992229)). Qed.
Lemma lem1992231 : term303.
Proof. exact (EQ_MP (@lem1992230) (@lem0)). Qed.
Lemma lem1992232 (x : real) (y : real) (h1 : term297 x y) : term311 x y.
Proof. exact (conj (@lem1992231) (@lem1992095 x y h1)). Qed.
Lemma lem1992234 (x : real) (y : real) : term88 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem1992235 (x : real) (y : real) : term312 x y.
Proof. exact (@lem1992234 term178 (term19 x y)). Qed.
Lemma lem1992236 (x : real) (y : real) (h1 : term297 x y) : term313 x y.
Proof. exact (@lem1992235 x y (@lem1992232 x y h1)). Qed.
Lemma lem1992237 (x : real) (y : real) : (term183 x y) = (term184 x y).
Proof. exact (@lem1982781 x term178 (term21 y)). Qed.
Lemma lem1992238 (y : real) : (term185 y) = (term186 y).
Proof. exact (@lem1982749 term178 term107 y). Qed.
Lemma lem1992240 (x : nat) : (term108 x) = (term109 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1992241 : term107 = term110.
Proof. exact (@lem1992240 term61). Qed.
Lemma lem1992244 : term187 = term187.
Proof. exact (eq_refl term187). Qed.
Lemma lem1992245 : term188 = term189.
Proof. exact (MK_COMB (@lem1992244) (@lem1992241)). Qed.
Lemma lem1992246 : term189 = term190.
Proof. exact (@lem1981613 term58 term107 term174 term58). Qed.
Lemma lem1992248 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1992249 : term191 = term192.
Proof. exact (@lem1992248 term179 term61). Qed.
Lemma lem1992250 : term193 = term194.
Proof. exact (@lem996237 term194). Qed.
Lemma lem1992251 : (term193 = term194) = (term195 = term179).
Proof. exact (@lem1007663 term194 (BIT1 0) term194). Qed.
Lemma lem1992252 : term195 = term179.
Proof. exact (EQ_MP (@lem1992251) (@lem1992250)). Qed.
Lemma lem1992253 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1992254 : term192 = term174.
Proof. exact (MK_COMB (@lem1992253) (@lem1992252)). Qed.
Lemma lem1992255 : term191 = term174.
Proof. exact (TRANS (@lem1992249) (@lem1992254)). Qed.
Lemma lem1992257 (m : nat) (n : nat) : (term196 m n) = (term120 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1992258 : term197 = term122.
Proof. exact (@lem1992257 term61 term61). Qed.
Lemma lem1992259 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1992260 : term77 = term61.
Proof. exact (EQ_MP (@lem1992259) (@lem940073)). Qed.
Lemma lem1992261 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1992262 : term75 = term58.
Proof. exact (MK_COMB (@lem1992261) (@lem1992260)). Qed.
Lemma lem1992263 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1992264 : term122 = term107.
Proof. exact (MK_COMB (@lem1992263) (@lem1992262)). Qed.
Lemma lem1992265 : term197 = term107.
Proof. exact (TRANS (@lem1992258) (@lem1992264)). Qed.
Lemma lem1992266 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem1992267 : term198 = term199.
Proof. exact (MK_COMB (@lem1992266) (@lem1992265)). Qed.
Lemma lem1992268 : term190 = term200.
Proof. exact (MK_COMB (@lem1992267) (@lem1992255)). Qed.
Lemma lem1992269 : term189 = term200.
Proof. exact (TRANS (@lem1992246) (@lem1992268)). Qed.
Lemma lem1992272 : term188 = term200.
Proof. exact (TRANS (@lem1992245) (@lem1992269)). Qed.
Lemma lem1992273 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1992274 : term201 = term202.
Proof. exact (MK_COMB (@lem1992273) (@lem1992272)). Qed.
Lemma lem1992275 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1992276 (y : real) : (term186 y) = (term203 y).
Proof. exact (MK_COMB (@lem1992274) (@lem1992275 y)). Qed.
Lemma lem1992277 (y : real) : (term185 y) = (term203 y).
Proof. exact (TRANS (@lem1992238 y) (@lem1992276 y)). Qed.
Lemma lem1992280 (x : real) : (term204 x) = (term204 x).
Proof. exact (eq_refl (term204 x)). Qed.
Lemma lem1992281 (x : real) (y : real) : (term184 x y) = (term205 x y).
Proof. exact (MK_COMB (@lem1992280 x) (@lem1992277 y)). Qed.
Lemma lem1992282 (x : real) (y : real) : (term183 x y) = (term205 x y).
Proof. exact (TRANS (@lem1992237 x y) (@lem1992281 x y)). Qed.
Lemma lem1992283 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1992284 (x : real) (y : real) : (term314 x y) = (term315 x y).
Proof. exact (MK_COMB (@lem1992283) (@lem1992282 x y)). Qed.
Lemma lem1992285 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1992286 (x : real) (y : real) : (term313 x y) = (term316 x y).
Proof. exact (MK_COMB (@lem1992284 x y) (@lem1992285)). Qed.
Lemma lem1992287 (x : real) (y : real) (h1 : term297 x y) : term316 x y.
Proof. exact (EQ_MP (@lem1992286 x y) (@lem1992236 x y h1)). Qed.
Lemma lem1992288 (x : real) (y : real) (h1 : term297 x y) : term317 x y.
Proof. exact (conj (@lem1992287 x y h1) (@lem1992170 x y h1)). Qed.
Lemma lem1992290 (x : real) (y : real) : term137 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem1992291 (x : real) (y : real) : term318 x y.
Proof. exact (@lem1992290 (term205 x y) (term256 x y)). Qed.
Lemma lem1992292 (x : real) (y : real) (h1 : term297 x y) : term319 x y.
Proof. exact (@lem1992291 x y (@lem1992288 x y h1)). Qed.
Lemma lem1992293 (x : real) (y : real) : (term320 x y) = (term321 x y).
Proof. exact (@lem1982753 (term208 x) (term203 x) (term203 y) (term208 y)). Qed.
Lemma lem1992294 (x : real) : (term322 x) = (term323 x).
Proof. exact (@lem1982711 term178 term200 x). Qed.
Lemma lem1992300 : term324.
Proof. exact (@lem1981473 term58 term174 term107 term174 term24 term58). Qed.
Lemma lem1992302 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1992303 : term215 = term216.
Proof. exact (@lem1992302 (NUMERAL 0) term179). Qed.
Lemma lem1992304 : term217 = term194.
Proof. exact (@lem912803). Qed.
Lemma lem1992305 (h1 : term217 = term194) : term216 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term194 h1). Qed.
Lemma lem1992306 : (term217 = term194) = (term216 = True).
Proof. exact (prop_ext (fun h1 : term217 = term194 => @lem1992305 h1) (fun h1 : term216 = True => @lem1992304)). Qed.
Lemma lem1992307 : term216 = True.
Proof. exact (EQ_MP (@lem1992306) (@lem1992304)). Qed.
Lemma lem1992308 : term215 = True.
Proof. exact (TRANS (@lem1992303) (@lem1992307)). Qed.
Lemma lem1992309 : True = term215.
Proof. exact (SYM (@lem1992308)). Qed.
Lemma lem1992310 : term215.
Proof. exact (EQ_MP (@lem1992309) (@lem0)). Qed.
Lemma lem1992311 : term325.
Proof. exact (@lem1992300 (@lem1992310)). Qed.
Lemma lem1992313 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1992314 : term215 = term216.
Proof. exact (@lem1992313 (NUMERAL 0) term179). Qed.
Lemma lem1992315 : term217 = term194.
Proof. exact (@lem912803). Qed.
Lemma lem1992316 (h1 : term217 = term194) : term216 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term194 h1). Qed.
Lemma lem1992317 : (term217 = term194) = (term216 = True).
Proof. exact (prop_ext (fun h1 : term217 = term194 => @lem1992316 h1) (fun h1 : term216 = True => @lem1992315)). Qed.
Lemma lem1992318 : term216 = True.
Proof. exact (EQ_MP (@lem1992317) (@lem1992315)). Qed.
Lemma lem1992319 : term215 = True.
Proof. exact (TRANS (@lem1992314) (@lem1992318)). Qed.
Lemma lem1992320 : True = term215.
Proof. exact (SYM (@lem1992319)). Qed.
Lemma lem1992321 : term215.
Proof. exact (EQ_MP (@lem1992320) (@lem0)). Qed.
Lemma lem1992322 : term326.
Proof. exact (@lem1992311 (@lem1992321)). Qed.
Lemma lem1992324 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1992325 : term57 = term68.
Proof. exact (@lem1992324 (NUMERAL 0) term61). Qed.
Lemma lem1992326 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1992327 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1992328 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1992327 h1) (fun h1 : term68 = True => @lem1992326)). Qed.
Lemma lem1992329 : term68 = True.
Proof. exact (EQ_MP (@lem1992328) (@lem1992326)). Qed.
Lemma lem1992330 : term57 = True.
Proof. exact (TRANS (@lem1992325) (@lem1992329)). Qed.
Lemma lem1992331 : True = term57.
Proof. exact (SYM (@lem1992330)). Qed.
Lemma lem1992332 : term57.
Proof. exact (EQ_MP (@lem1992331) (@lem0)). Qed.
Lemma lem1992333 : term327.
Proof. exact (@lem1992322 (@lem1992332)). Qed.
Lemma lem1992335 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1992336 : term276 = term277.
Proof. exact (@lem1992335 term61 term179). Qed.
Lemma lem1992337 : term223 = term194.
Proof. exact (@lem996238 term194). Qed.
Lemma lem1992338 : (term223 = term194) = (term224 = term179).
Proof. exact (@lem1007663 (BIT1 0) term194 term194). Qed.
Lemma lem1992339 : term224 = term179.
Proof. exact (EQ_MP (@lem1992338) (@lem1992337)). Qed.
Lemma lem1992340 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1992341 : term222 = term174.
Proof. exact (MK_COMB (@lem1992340) (@lem1992339)). Qed.
Lemma lem1992342 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1992343 : term277 = term278.
Proof. exact (MK_COMB (@lem1992342) (@lem1992341)). Qed.
Lemma lem1992344 : term276 = term278.
Proof. exact (TRANS (@lem1992336) (@lem1992343)). Qed.
Lemma lem1992346 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1992347 : term221 = term222.
Proof. exact (@lem1992346 term61 term179). Qed.
Lemma lem1992348 : term223 = term194.
Proof. exact (@lem996238 term194). Qed.
Lemma lem1992349 : (term223 = term194) = (term224 = term179).
Proof. exact (@lem1007663 (BIT1 0) term194 term194). Qed.
Lemma lem1992350 : term224 = term179.
Proof. exact (EQ_MP (@lem1992349) (@lem1992348)). Qed.
Lemma lem1992351 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1992352 : term222 = term174.
Proof. exact (MK_COMB (@lem1992351) (@lem1992350)). Qed.
Lemma lem1992353 : term221 = term174.
Proof. exact (TRANS (@lem1992347) (@lem1992352)). Qed.
Lemma lem1992354 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1992355 : term328 = term329.
Proof. exact (MK_COMB (@lem1992354) (@lem1992353)). Qed.
Lemma lem1992356 : term330 = term331.
Proof. exact (MK_COMB (@lem1992355) (@lem1992344)). Qed.
Lemma lem1992358 (m : nat) : (term332 m) = term24.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1992359 : term331 = term24.
Proof. exact (@lem1992358 term179). Qed.
Lemma lem1992360 : term330 = term24.
Proof. exact (TRANS (@lem1992356) (@lem1992359)). Qed.
Lemma lem1992361 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1992362 : term333 = term127.
Proof. exact (MK_COMB (@lem1992361) (@lem1992360)). Qed.
Lemma lem1992363 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1992364 : term334 = term79.
Proof. exact (MK_COMB (@lem1992362) (@lem1992363)). Qed.
Lemma lem1992366 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1992367 : term79 = term24.
Proof. exact (@lem1992366 term61). Qed.
Lemma lem1992368 : term334 = term24.
Proof. exact (TRANS (@lem1992364) (@lem1992367)). Qed.
Lemma lem1992370 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1992371 : term335 = term336.
Proof. exact (@lem1992370 term179 term179). Qed.
Lemma lem1992372 : (term76 = (BIT1 0)) = (term337 = term338).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1992373 : term337 = term338.
Proof. exact (EQ_MP (@lem1992372) (@lem940073)). Qed.
Lemma lem1992374 : (term337 = term338) = (term339 = term340).
Proof. exact (@lem1008952 term194 term338). Qed.
Lemma lem1992375 : term339 = term340.
Proof. exact (EQ_MP (@lem1992374) (@lem1992373)). Qed.
Lemma lem1992376 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1992377 : term336 = term341.
Proof. exact (MK_COMB (@lem1992376) (@lem1992375)). Qed.
Lemma lem1992378 : term335 = term341.
Proof. exact (TRANS (@lem1992371) (@lem1992377)). Qed.
Lemma lem1992379 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem1992380 : term342 = term343.
Proof. exact (MK_COMB (@lem1992379) (@lem1992378)). Qed.
Lemma lem1992382 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1992383 : term343 = term24.
Proof. exact (@lem1992382 term340). Qed.
Lemma lem1992384 : term342 = term24.
Proof. exact (TRANS (@lem1992380) (@lem1992383)). Qed.
Lemma lem1992385 : term24 = term342.
Proof. exact (SYM (@lem1992384)). Qed.
Lemma lem1992386 : term334 = term342.
Proof. exact (TRANS (@lem1992368) (@lem1992385)). Qed.
Lemma lem1992388 : term344 = term62.
Proof. exact (@lem1992333 (@lem1992386)). Qed.
Lemma lem1992390 (x : real) : (term130 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem1992391 : term62 = term24.
Proof. exact (@lem1992390 term24). Qed.
Lemma lem1992392 : term344 = term24.
Proof. exact (TRANS (@lem1992388) (@lem1992391)). Qed.
Lemma lem1992393 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1992394 : term345 = term127.
Proof. exact (MK_COMB (@lem1992393) (@lem1992392)). Qed.
Lemma lem1992395 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1992396 (x : real) : (term323 x) = (term132 x).
Proof. exact (MK_COMB (@lem1992394) (@lem1992395 x)). Qed.
Lemma lem1992397 (x : real) : (term322 x) = (term132 x).
Proof. exact (TRANS (@lem1992294 x) (@lem1992396 x)). Qed.
Lemma lem1992398 (x : real) : (term132 x) = term24.
Proof. exact (@lem1982719 x). Qed.
Lemma lem1992399 (x : real) : (term322 x) = term24.
Proof. exact (TRANS (@lem1992397 x) (@lem1992398 x)). Qed.
Lemma lem1992400 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1992401 (x : real) : (term346 x) = term144.
Proof. exact (MK_COMB (@lem1992400) (@lem1992399 x)). Qed.
Lemma lem1992402 (y : real) : (term347 y) = (term348 y).
Proof. exact (@lem1982711 term200 term178 y). Qed.
Lemma lem1992408 : term349.
Proof. exact (@lem1981473 term107 term174 term58 term174 term24 term58). Qed.
Lemma lem1992410 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1992411 : term215 = term216.
Proof. exact (@lem1992410 (NUMERAL 0) term179). Qed.
Lemma lem1992412 : term217 = term194.
Proof. exact (@lem912803). Qed.
Lemma lem1992413 (h1 : term217 = term194) : term216 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term194 h1). Qed.
Lemma lem1992414 : (term217 = term194) = (term216 = True).
Proof. exact (prop_ext (fun h1 : term217 = term194 => @lem1992413 h1) (fun h1 : term216 = True => @lem1992412)). Qed.
Lemma lem1992415 : term216 = True.
Proof. exact (EQ_MP (@lem1992414) (@lem1992412)). Qed.
Lemma lem1992416 : term215 = True.
Proof. exact (TRANS (@lem1992411) (@lem1992415)). Qed.
Lemma lem1992417 : True = term215.
Proof. exact (SYM (@lem1992416)). Qed.
Lemma lem1992418 : term215.
Proof. exact (EQ_MP (@lem1992417) (@lem0)). Qed.
Lemma lem1992419 : term350.
Proof. exact (@lem1992408 (@lem1992418)). Qed.
Lemma lem1992421 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1992422 : term215 = term216.
Proof. exact (@lem1992421 (NUMERAL 0) term179). Qed.
Lemma lem1992423 : term217 = term194.
Proof. exact (@lem912803). Qed.
Lemma lem1992424 (h1 : term217 = term194) : term216 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term194 h1). Qed.
Lemma lem1992425 : (term217 = term194) = (term216 = True).
Proof. exact (prop_ext (fun h1 : term217 = term194 => @lem1992424 h1) (fun h1 : term216 = True => @lem1992423)). Qed.
Lemma lem1992426 : term216 = True.
Proof. exact (EQ_MP (@lem1992425) (@lem1992423)). Qed.
Lemma lem1992427 : term215 = True.
Proof. exact (TRANS (@lem1992422) (@lem1992426)). Qed.
Lemma lem1992428 : True = term215.
Proof. exact (SYM (@lem1992427)). Qed.
Lemma lem1992429 : term215.
Proof. exact (EQ_MP (@lem1992428) (@lem0)). Qed.
Lemma lem1992430 : term351.
Proof. exact (@lem1992419 (@lem1992429)). Qed.
Lemma lem1992432 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1992433 : term57 = term68.
Proof. exact (@lem1992432 (NUMERAL 0) term61). Qed.
Lemma lem1992434 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1992435 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1992436 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1992435 h1) (fun h1 : term68 = True => @lem1992434)). Qed.
Lemma lem1992437 : term68 = True.
Proof. exact (EQ_MP (@lem1992436) (@lem1992434)). Qed.
Lemma lem1992438 : term57 = True.
Proof. exact (TRANS (@lem1992433) (@lem1992437)). Qed.
Lemma lem1992439 : True = term57.
Proof. exact (SYM (@lem1992438)). Qed.
Lemma lem1992440 : term57.
Proof. exact (EQ_MP (@lem1992439) (@lem0)). Qed.
Lemma lem1992441 : term352.
Proof. exact (@lem1992430 (@lem1992440)). Qed.
Lemma lem1992443 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1992444 : term221 = term222.
Proof. exact (@lem1992443 term61 term179). Qed.
Lemma lem1992445 : term223 = term194.
Proof. exact (@lem996238 term194). Qed.
Lemma lem1992446 : (term223 = term194) = (term224 = term179).
Proof. exact (@lem1007663 (BIT1 0) term194 term194). Qed.
Lemma lem1992447 : term224 = term179.
Proof. exact (EQ_MP (@lem1992446) (@lem1992445)). Qed.
Lemma lem1992448 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1992449 : term222 = term174.
Proof. exact (MK_COMB (@lem1992448) (@lem1992447)). Qed.
Lemma lem1992450 : term221 = term174.
Proof. exact (TRANS (@lem1992444) (@lem1992449)). Qed.
Lemma lem1992452 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1992453 : term276 = term277.
Proof. exact (@lem1992452 term61 term179). Qed.
Lemma lem1992454 : term223 = term194.
Proof. exact (@lem996238 term194). Qed.
Lemma lem1992455 : (term223 = term194) = (term224 = term179).
Proof. exact (@lem1007663 (BIT1 0) term194 term194). Qed.
Lemma lem1992456 : term224 = term179.
Proof. exact (EQ_MP (@lem1992455) (@lem1992454)). Qed.
Lemma lem1992457 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1992458 : term222 = term174.
Proof. exact (MK_COMB (@lem1992457) (@lem1992456)). Qed.
Lemma lem1992459 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1992460 : term277 = term278.
Proof. exact (MK_COMB (@lem1992459) (@lem1992458)). Qed.
Lemma lem1992461 : term276 = term278.
Proof. exact (TRANS (@lem1992453) (@lem1992460)). Qed.
Lemma lem1992462 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1992463 : term353 = term354.
Proof. exact (MK_COMB (@lem1992462) (@lem1992461)). Qed.
Lemma lem1992464 : term355 = term356.
Proof. exact (MK_COMB (@lem1992463) (@lem1992450)). Qed.
Lemma lem1992466 (m : nat) : (term125 m) = term24.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1992467 : term356 = term24.
Proof. exact (@lem1992466 term179). Qed.
Lemma lem1992468 : term355 = term24.
Proof. exact (TRANS (@lem1992464) (@lem1992467)). Qed.
Lemma lem1992469 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1992470 : term357 = term127.
Proof. exact (MK_COMB (@lem1992469) (@lem1992468)). Qed.
Lemma lem1992471 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1992472 : term358 = term79.
Proof. exact (MK_COMB (@lem1992470) (@lem1992471)). Qed.
Lemma lem1992474 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1992475 : term79 = term24.
Proof. exact (@lem1992474 term61). Qed.
Lemma lem1992476 : term358 = term24.
Proof. exact (TRANS (@lem1992472) (@lem1992475)). Qed.
Lemma lem1992478 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1992479 : term335 = term336.
Proof. exact (@lem1992478 term179 term179). Qed.
Lemma lem1992480 : (term76 = (BIT1 0)) = (term337 = term338).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1992481 : term337 = term338.
Proof. exact (EQ_MP (@lem1992480) (@lem940073)). Qed.
Lemma lem1992482 : (term337 = term338) = (term339 = term340).
Proof. exact (@lem1008952 term194 term338). Qed.
Lemma lem1992483 : term339 = term340.
Proof. exact (EQ_MP (@lem1992482) (@lem1992481)). Qed.
Lemma lem1992484 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1992485 : term336 = term341.
Proof. exact (MK_COMB (@lem1992484) (@lem1992483)). Qed.
Lemma lem1992486 : term335 = term341.
Proof. exact (TRANS (@lem1992479) (@lem1992485)). Qed.
Lemma lem1992487 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem1992488 : term342 = term343.
Proof. exact (MK_COMB (@lem1992487) (@lem1992486)). Qed.
Lemma lem1992490 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1992491 : term343 = term24.
Proof. exact (@lem1992490 term340). Qed.
Lemma lem1992492 : term342 = term24.
Proof. exact (TRANS (@lem1992488) (@lem1992491)). Qed.
Lemma lem1992493 : term24 = term342.
Proof. exact (SYM (@lem1992492)). Qed.
Lemma lem1992494 : term358 = term342.
Proof. exact (TRANS (@lem1992476) (@lem1992493)). Qed.
Lemma lem1992496 : term359 = term62.
Proof. exact (@lem1992441 (@lem1992494)). Qed.
Lemma lem1992498 (x : real) : (term130 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem1992499 : term62 = term24.
Proof. exact (@lem1992498 term24). Qed.
Lemma lem1992500 : term359 = term24.
Proof. exact (TRANS (@lem1992496) (@lem1992499)). Qed.
Lemma lem1992501 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1992502 : term360 = term127.
Proof. exact (MK_COMB (@lem1992501) (@lem1992500)). Qed.
Lemma lem1992503 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1992504 (y : real) : (term348 y) = (term132 y).
Proof. exact (MK_COMB (@lem1992502) (@lem1992503 y)). Qed.
Lemma lem1992505 (y : real) : (term347 y) = (term132 y).
Proof. exact (TRANS (@lem1992402 y) (@lem1992504 y)). Qed.
Lemma lem1992506 (y : real) : (term132 y) = term24.
Proof. exact (@lem1982719 y). Qed.
Lemma lem1992507 (y : real) : (term347 y) = term24.
Proof. exact (TRANS (@lem1992505 y) (@lem1992506 y)). Qed.
Lemma lem1992508 (x : real) (y : real) : (term321 x y) = term145.
Proof. exact (MK_COMB (@lem1992401 x) (@lem1992507 y)). Qed.
Lemma lem1992509 (x : real) (y : real) : (term320 x y) = term145.
Proof. exact (TRANS (@lem1992293 x y) (@lem1992508 x y)). Qed.
Lemma lem1992510 : term145 = term24.
Proof. exact (@lem1982721 term24). Qed.
Lemma lem1992511 (x : real) (y : real) : (term320 x y) = term24.
Proof. exact (TRANS (@lem1992509 x y) (@lem1992510)). Qed.
Lemma lem1992512 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1992513 (x : real) (y : real) : (term361 x y) = term147.
Proof. exact (MK_COMB (@lem1992512) (@lem1992511 x y)). Qed.
Lemma lem1992514 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1992515 (x : real) (y : real) : (term319 x y) = term148.
Proof. exact (MK_COMB (@lem1992513 x y) (@lem1992514)). Qed.
Lemma lem1992516 (x : real) (y : real) (h1 : term297 x y) : term148.
Proof. exact (EQ_MP (@lem1992515 x y) (@lem1992292 x y h1)). Qed.
Lemma lem1992518 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1992519 : term148 = term149.
Proof. exact (@lem1992518 term24 term24). Qed.
Lemma lem1992521 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1992522 : term24 = term62.
Proof. exact (@lem1992521 (NUMERAL 0)). Qed.
Lemma lem1992524 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1992525 : term24 = term62.
Proof. exact (@lem1992524 (NUMERAL 0)). Qed.
Lemma lem1992526 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1992527 : term63 = term64.
Proof. exact (MK_COMB (@lem1992526) (@lem1992525)). Qed.
Lemma lem1992528 : term149 = term150.
Proof. exact (MK_COMB (@lem1992527) (@lem1992522)). Qed.
Lemma lem1992529 : term151.
Proof. exact (@lem1980255 term24 term58 term24 term58). Qed.
Lemma lem1992531 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1992532 : term57 = term68.
Proof. exact (@lem1992531 (NUMERAL 0) term61). Qed.
Lemma lem1992533 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1992534 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1992535 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1992534 h1) (fun h1 : term68 = True => @lem1992533)). Qed.
Lemma lem1992536 : term68 = True.
Proof. exact (EQ_MP (@lem1992535) (@lem1992533)). Qed.
Lemma lem1992537 : term57 = True.
Proof. exact (TRANS (@lem1992532) (@lem1992536)). Qed.
Lemma lem1992538 : True = term57.
Proof. exact (SYM (@lem1992537)). Qed.
Lemma lem1992539 : term57.
Proof. exact (EQ_MP (@lem1992538) (@lem0)). Qed.
Lemma lem1992540 : term152.
Proof. exact (@lem1992529 (@lem1992539)). Qed.
Lemma lem1992542 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1992543 : term57 = term68.
Proof. exact (@lem1992542 (NUMERAL 0) term61). Qed.
Lemma lem1992544 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1992545 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1992546 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1992545 h1) (fun h1 : term68 = True => @lem1992544)). Qed.
Lemma lem1992547 : term68 = True.
Proof. exact (EQ_MP (@lem1992546) (@lem1992544)). Qed.
Lemma lem1992548 : term57 = True.
Proof. exact (TRANS (@lem1992543) (@lem1992547)). Qed.
Lemma lem1992549 : True = term57.
Proof. exact (SYM (@lem1992548)). Qed.
Lemma lem1992550 : term57.
Proof. exact (EQ_MP (@lem1992549) (@lem0)). Qed.
Lemma lem1992551 : term150 = term153.
Proof. exact (@lem1992540 (@lem1992550)). Qed.
Lemma lem1992553 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1992554 : term79 = term24.
Proof. exact (@lem1992553 term61). Qed.
Lemma lem1992556 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1992557 : term79 = term24.
Proof. exact (@lem1992556 term61). Qed.
Lemma lem1992558 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1992559 : term80 = term63.
Proof. exact (MK_COMB (@lem1992558) (@lem1992557)). Qed.
Lemma lem1992560 : term153 = term149.
Proof. exact (MK_COMB (@lem1992559) (@lem1992554)). Qed.
Lemma lem1992562 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1992563 : term149 = term154.
Proof. exact (@lem1992562 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1992564 : term154 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1992565 : term149 = False.
Proof. exact (TRANS (@lem1992563) (@lem1992564)). Qed.
Lemma lem1992566 : term153 = False.
Proof. exact (TRANS (@lem1992560) (@lem1992565)). Qed.
Lemma lem1992567 : term150 = False.
Proof. exact (TRANS (@lem1992551) (@lem1992566)). Qed.
Lemma lem1992568 : term149 = False.
Proof. exact (TRANS (@lem1992528) (@lem1992567)). Qed.
Lemma lem1992569 : term148 = False.
Proof. exact (TRANS (@lem1992519) (@lem1992568)). Qed.
Lemma lem1992570 (x : real) (y : real) (h1 : term297 x y) : False.
Proof. exact (EQ_MP (@lem1992569) (@lem1992516 x y h1)). Qed.
Lemma lem1992571 (x : real) (y : real) (h1 : term296 x y) : False.
Proof. exact (or_elim (@lem1991616 x y h1) (fun h0 : term297 x y => @lem1992093 x y h0) (fun h0 : term297 x y => @lem1992570 x y h0)). Qed.
Lemma lem1992573 (x : real) (y : real) (h1 : term296 x y) : term296 x y.
Proof. exact (h1). Qed.
Lemma lem1992574 (x : real) (y : real) (h1 : term296 x y) : (term296 x y) = False.
Proof. exact (prop_ext (fun h2 : term296 x y => @lem1992571 x y h1) (fun h2 : False => @lem1992573 x y h1)). Qed.
Lemma lem1992575 (x : real) (y : real) (h1 : term296 x y) : False.
Proof. exact (EQ_MP (@lem1992574 x y h1) (@lem1992573 x y h1)). Qed.
Lemma lem1992576 (x : real) (y : real) (h1 : term168 x y) : term168 x y.
Proof. exact (h1). Qed.
Lemma lem1992577 (x : real) (y : real) (h1 : term168 x y) : term296 x y.
Proof. exact (EQ_MP (@lem1991606 x y) (@lem1992576 x y h1)). Qed.
Lemma lem1992578 (x : real) (y : real) (h1 : term168 x y) : (term296 x y) = False.
Proof. exact (prop_ext (fun h2 : term296 x y => @lem1992575 x y h2) (fun h2 : False => @lem1992577 x y h1)). Qed.
Lemma lem1992579 (x : real) (y : real) (h1 : term168 x y) : False.
Proof. exact (EQ_MP (@lem1992578 x y h1) (@lem1992577 x y h1)). Qed.
Lemma lem1992580 (x : real) (y : real) : term362 x y.
Proof. exact (fun h0 : term168 x y => @lem1992579 x y h0). Qed.
Lemma lem1992581 (x : real) (y : real) : term363 x y.
Proof. exact (@lem1386578 (term364 x y)). Qed.
Lemma lem1992584 (x : real) (y : real) : term364 x y.
Proof. exact (@lem1992581 x y (@lem1992580 x y)). Qed.
Lemma lem1992585 (y : real) (x : real) (h1 : term17 y x) : real_le x y.
Proof. exact (@lem1992584 x y (@lem1990724 y x h1)). Qed.
Lemma lem1992586 (x : real) (y : real) : term365 x y.
Proof. exact (fun h0 : term17 y x => @lem1992585 y x h0). Qed.
Lemma lem1992587 (x : real) (y : real) : term366 x y.
Proof. exact (conj (@lem1990720 y x) (@lem1992586 x y)). Qed.
Lemma lem1992588 (y : real) (x : real) : (term366 x y) = ((real_le x y) = (term17 y x)).
Proof. exact (@lem32 (real_le x y) (term17 y x)). Qed.
Lemma lem1992589 (y : real) (x : real) : (real_le x y) = (term17 y x).
Proof. exact (EQ_MP (@lem1992588 y x) (@lem1992587 x y)). Qed.
Lemma lem1992594 (x : real) : term367 x.
Proof. exact (fun y : real => @lem1992589 y x). Qed.
Lemma lem1992599 : term368.
Proof. exact (fun x : real => @lem1992594 x). Qed.
