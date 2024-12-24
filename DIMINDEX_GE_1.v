Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIMINDEX_GE_1_term_abbrevs.
Require Import DIMINDEX_NONZERO_spec.
Require Import INT_POS_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm17500_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
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
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988293_spec.
Require Import thm1988332_spec.
Require Import thm1988336_spec.
Require Import thm1988342_spec.
Require Import thm2318495_spec.
Require Import thm2318497_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318574_spec.
Require Import thm2318575_spec.
Require Import thm2318604_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm2841413_spec.
Require Import thm2841414_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem7591738 (x : nat) : (term0 x) = (x = (NUMERAL 0)).
Proof. exact (@lem16933 (x = (NUMERAL 0))). Qed.
Lemma lem7591740 (x : nat) : (term1 x) = (term1 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem7591741 (x : nat) : (term2 x) = (term3 x).
Proof. exact (MK_COMB (@lem7591740 x) (@lem7591738 x)). Qed.
Lemma lem7591746 (x : nat) : (term4 x) = (term4 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem7591747 (x : nat) : (term5 x) = (term6 x).
Proof. exact (MK_COMB (@lem7591746 x) (@lem7591741 x)). Qed.
Lemma lem7591748 (x : nat) : ((term7 x) = (term8 x)) = (term5 x).
Proof. exact (@lem17500 (term7 x) (term8 x)). Qed.
Lemma lem7591804 (x : nat) : ((term7 x) = (term8 x)) = (term6 x).
Proof. exact (TRANS (@lem7591748 x) (@lem7591747 x)). Qed.
Lemma lem7591806 (m : nat) (n : nat) : (Peano.le m n) = (term9 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7591807 (x : nat) : (term7 x) = (term10 x).
Proof. exact (@lem7591806 term11 x). Qed.
Lemma lem7591808 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7591809 (x : nat) : (term12 x) = (term13 x).
Proof. exact (MK_COMB (@lem7591808) (@lem7591807 x)). Qed.
Lemma lem7591811 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem7591812 (x : nat) : (x = (NUMERAL 0)) = ((int_of_num x) = term14).
Proof. exact (@lem7591811 x (NUMERAL 0)). Qed.
Lemma lem7591815 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7591816 (x : nat) : (term8 x) = (term15 x).
Proof. exact (MK_COMB (@lem7591815) (@lem7591812 x)). Qed.
Lemma lem7591817 (x : nat) : (term16 x) = (term17 x).
Proof. exact (MK_COMB (@lem7591809 x) (@lem7591816 x)). Qed.
Lemma lem7591818 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7591819 (x : nat) : (term4 x) = (term18 x).
Proof. exact (MK_COMB (@lem7591818) (@lem7591817 x)). Qed.
Lemma lem7591821 (m : nat) (n : nat) : (Peano.le m n) = (term9 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7591822 (x : nat) : (term7 x) = (term10 x).
Proof. exact (@lem7591821 term11 x). Qed.
Lemma lem7591823 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7591824 (x : nat) : (term19 x) = (term20 x).
Proof. exact (MK_COMB (@lem7591823) (@lem7591822 x)). Qed.
Lemma lem7591825 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7591826 (x : nat) : (term1 x) = (term21 x).
Proof. exact (MK_COMB (@lem7591825) (@lem7591824 x)). Qed.
Lemma lem7591828 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem7591829 (x : nat) : (x = (NUMERAL 0)) = ((int_of_num x) = term14).
Proof. exact (@lem7591828 x (NUMERAL 0)). Qed.
Lemma lem7591832 (x : nat) : (term3 x) = (term22 x).
Proof. exact (MK_COMB (@lem7591826 x) (@lem7591829 x)). Qed.
Lemma lem7591833 (x : nat) : (term6 x) = (term23 x).
Proof. exact (MK_COMB (@lem7591819 x) (@lem7591832 x)). Qed.
Lemma lem7591834 (x : nat) : ((term7 x) = (term8 x)) = (term23 x).
Proof. exact (TRANS (@lem7591804 x) (@lem7591833 x)). Qed.
Lemma lem7591835 (x : nat) : term24 x.
Proof. exact (@lem2307535 x). Qed.
Lemma lem7591836 (x : nat) : (term24 x) = (term25 x).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem7591837 (x : nat) : term25 x.
Proof. exact (EQ_MP (@lem7591836 x) (@lem7591835 x)). Qed.
Lemma lem7591838 (_97606 : int) : (term26 _97606) = (term27 _97606).
Proof. exact (@lem2318604 (term27 _97606)). Qed.
Lemma lem7591856 (_97606 : int) : (term28 _97606) = (_97606 = term14).
Proof. exact (@lem16933 (_97606 = term14)). Qed.
Lemma lem7591858 (_97606 : int) : (term29 _97606) = (term29 _97606).
Proof. exact (eq_refl (term29 _97606)). Qed.
Lemma lem7591859 (_97606 : int) : (term30 _97606) = (term31 _97606).
Proof. exact (MK_COMB (@lem7591858 _97606) (@lem7591856 _97606)). Qed.
Lemma lem7591860 (_97606 : int) : (term32 _97606) = (term30 _97606).
Proof. exact (@lem17045 (term33 _97606) (term34 _97606)). Qed.
Lemma lem7591861 (_97606 : int) : (term32 _97606) = (term31 _97606).
Proof. exact (TRANS (@lem7591860 _97606) (@lem7591859 _97606)). Qed.
Lemma lem7591864 (_97606 : int) : (term35 _97606) = (term33 _97606).
Proof. exact (@lem16933 (term33 _97606)). Qed.
Lemma lem7591865 (_97606 : int) : (term34 _97606) = (term34 _97606).
Proof. exact (eq_refl (term34 _97606)). Qed.
Lemma lem7591866 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7591867 (_97606 : int) : (term36 _97606) = (term37 _97606).
Proof. exact (MK_COMB (@lem7591866) (@lem7591864 _97606)). Qed.
Lemma lem7591868 (_97606 : int) : (term38 _97606) = (term39 _97606).
Proof. exact (MK_COMB (@lem7591867 _97606) (@lem7591865 _97606)). Qed.
Lemma lem7591869 (_97606 : int) : (term40 _97606) = (term38 _97606).
Proof. exact (@lem17045 (term41 _97606) (_97606 = term14)). Qed.
Lemma lem7591870 (_97606 : int) : (term40 _97606) = (term39 _97606).
Proof. exact (TRANS (@lem7591869 _97606) (@lem7591868 _97606)). Qed.
Lemma lem7591871 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7591872 (_97606 : int) : (term42 _97606) = (term43 _97606).
Proof. exact (MK_COMB (@lem7591871) (@lem7591861 _97606)). Qed.
Lemma lem7591873 (_97606 : int) : (term44 _97606) = (term45 _97606).
Proof. exact (MK_COMB (@lem7591872 _97606) (@lem7591870 _97606)). Qed.
Lemma lem7591874 (_97606 : int) : (term46 _97606) = (term44 _97606).
Proof. exact (@lem17160 (term47 _97606) (term48 _97606)). Qed.
Lemma lem7591875 (_97606 : int) : (term46 _97606) = (term45 _97606).
Proof. exact (TRANS (@lem7591874 _97606) (@lem7591873 _97606)). Qed.
Lemma lem7591877 (_97606 : int) : (term49 _97606) = (term49 _97606).
Proof. exact (eq_refl (term49 _97606)). Qed.
Lemma lem7591878 (_97606 : int) : (term50 _97606) = (term51 _97606).
Proof. exact (MK_COMB (@lem7591877 _97606) (@lem7591875 _97606)). Qed.
Lemma lem7591879 (_97606 : int) : (term52 _97606) = (term50 _97606).
Proof. exact (@lem17362 (term53 _97606) (term54 _97606)). Qed.
Lemma lem7591903 (_97606 : int) : (term52 _97606) = (term51 _97606).
Proof. exact (TRANS (@lem7591879 _97606) (@lem7591878 _97606)). Qed.
Lemma lem7591906 (x : int) (y : int) : (int_le x y) = (term55 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7591907 (_97606 : int) : (term53 _97606) = (term56 _97606).
Proof. exact (@lem7591906 term14 _97606). Qed.
Lemma lem7591909 (n : nat) : (term57 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7591910 : term58 = term59.
Proof. exact (@lem7591909 (NUMERAL 0)). Qed.
Lemma lem7591911 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7591912 : term60 = term61.
Proof. exact (MK_COMB (@lem7591911) (@lem7591910)). Qed.
Lemma lem7591913 (_97606 : int) : (real_of_int _97606) = (real_of_int _97606).
Proof. exact (eq_refl (real_of_int _97606)). Qed.
Lemma lem7591914 (_97606 : int) : (term56 _97606) = (term62 _97606).
Proof. exact (MK_COMB (@lem7591912) (@lem7591913 _97606)). Qed.
Lemma lem7591916 (_97606 : int) : (term53 _97606) = (term62 _97606).
Proof. exact (TRANS (@lem7591907 _97606) (@lem7591914 _97606)). Qed.
Lemma lem7591918 (y : int) (x : int) : (term63 x y) = (term64 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7591919 (_97606 : int) : (term41 _97606) = (term65 _97606).
Proof. exact (@lem7591918 _97606 term66). Qed.
Lemma lem7591921 (x : int) (y : int) : (int_le x y) = (term55 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7591922 (_97606 : int) : (term65 _97606) = (term67 _97606).
Proof. exact (@lem7591921 (term68 _97606) term66). Qed.
Lemma lem7591924 (x : int) (y : int) : (term69 x y) = (term70 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7591925 (_97606 : int) : (term71 _97606) = (term72 _97606).
Proof. exact (@lem7591924 _97606 term66). Qed.
Lemma lem7591927 (n : nat) : (term57 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7591928 : term73 = term74.
Proof. exact (@lem7591927 term11). Qed.
Lemma lem7591929 (_97606 : int) : (term75 _97606) = (term75 _97606).
Proof. exact (eq_refl (term75 _97606)). Qed.
Lemma lem7591930 (_97606 : int) : (term72 _97606) = (term76 _97606).
Proof. exact (MK_COMB (@lem7591929 _97606) (@lem7591928)). Qed.
Lemma lem7591931 (_97606 : int) : (term71 _97606) = (term76 _97606).
Proof. exact (TRANS (@lem7591925 _97606) (@lem7591930 _97606)). Qed.
Lemma lem7591932 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7591933 (_97606 : int) : (term77 _97606) = (term78 _97606).
Proof. exact (MK_COMB (@lem7591932) (@lem7591931 _97606)). Qed.
Lemma lem7591935 (n : nat) : (term57 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7591936 : term73 = term74.
Proof. exact (@lem7591935 term11). Qed.
Lemma lem7591937 (_97606 : int) : (term67 _97606) = (term79 _97606).
Proof. exact (MK_COMB (@lem7591933 _97606) (@lem7591936)). Qed.
Lemma lem7591938 (_97606 : int) : (term65 _97606) = (term79 _97606).
Proof. exact (TRANS (@lem7591922 _97606) (@lem7591937 _97606)). Qed.
Lemma lem7591939 (_97606 : int) : (term41 _97606) = (term79 _97606).
Proof. exact (TRANS (@lem7591919 _97606) (@lem7591938 _97606)). Qed.
Lemma lem7591942 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem7591943 (_97606 : int) : (_97606 = term14) = ((real_of_int _97606) = term58).
Proof. exact (@lem7591942 _97606 term14). Qed.
Lemma lem7591947 (n : nat) : (term57 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7591948 : term58 = term59.
Proof. exact (@lem7591947 (NUMERAL 0)). Qed.
Lemma lem7591949 (_97606 : int) : (term80 _97606) = (term80 _97606).
Proof. exact (eq_refl (term80 _97606)). Qed.
Lemma lem7591950 (_97606 : int) : ((real_of_int _97606) = term58) = ((real_of_int _97606) = term59).
Proof. exact (MK_COMB (@lem7591949 _97606) (@lem7591948)). Qed.
Lemma lem7591952 (_97606 : int) : (_97606 = term14) = ((real_of_int _97606) = term59).
Proof. exact (TRANS (@lem7591943 _97606) (@lem7591950 _97606)). Qed.
Lemma lem7591953 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7591954 (_97606 : int) : (term29 _97606) = (term81 _97606).
Proof. exact (MK_COMB (@lem7591953) (@lem7591939 _97606)). Qed.
Lemma lem7591955 (_97606 : int) : (term31 _97606) = (term82 _97606).
Proof. exact (MK_COMB (@lem7591954 _97606) (@lem7591952 _97606)). Qed.
Lemma lem7591958 (x : int) (y : int) : (int_le x y) = (term55 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7591959 (_97606 : int) : (term33 _97606) = (term83 _97606).
Proof. exact (@lem7591958 term66 _97606). Qed.
Lemma lem7591961 (n : nat) : (term57 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7591962 : term73 = term74.
Proof. exact (@lem7591961 term11). Qed.
Lemma lem7591963 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7591964 : term84 = term85.
Proof. exact (MK_COMB (@lem7591963) (@lem7591962)). Qed.
Lemma lem7591965 (_97606 : int) : (real_of_int _97606) = (real_of_int _97606).
Proof. exact (eq_refl (real_of_int _97606)). Qed.
Lemma lem7591966 (_97606 : int) : (term83 _97606) = (term86 _97606).
Proof. exact (MK_COMB (@lem7591964) (@lem7591965 _97606)). Qed.
Lemma lem7591968 (_97606 : int) : (term33 _97606) = (term86 _97606).
Proof. exact (TRANS (@lem7591959 _97606) (@lem7591966 _97606)). Qed.
Lemma lem7591970 (y : int) (x : int) : (term87 x y) = (term88 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem7591971 (_97606 : int) : (term34 _97606) = (term89 _97606).
Proof. exact (@lem7591970 term14 _97606). Qed.
Lemma lem7591973 (x : int) (y : int) : (int_le x y) = (term55 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7591974 (_97606 : int) : (term90 _97606) = (term91 _97606).
Proof. exact (@lem7591973 (term68 _97606) term14). Qed.
Lemma lem7591976 (x : int) (y : int) : (term69 x y) = (term70 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7591977 (_97606 : int) : (term71 _97606) = (term72 _97606).
Proof. exact (@lem7591976 _97606 term66). Qed.
Lemma lem7591979 (n : nat) : (term57 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7591980 : term73 = term74.
Proof. exact (@lem7591979 term11). Qed.
Lemma lem7591981 (_97606 : int) : (term75 _97606) = (term75 _97606).
Proof. exact (eq_refl (term75 _97606)). Qed.
Lemma lem7591982 (_97606 : int) : (term72 _97606) = (term76 _97606).
Proof. exact (MK_COMB (@lem7591981 _97606) (@lem7591980)). Qed.
Lemma lem7591983 (_97606 : int) : (term71 _97606) = (term76 _97606).
Proof. exact (TRANS (@lem7591977 _97606) (@lem7591982 _97606)). Qed.
Lemma lem7591984 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7591985 (_97606 : int) : (term77 _97606) = (term78 _97606).
Proof. exact (MK_COMB (@lem7591984) (@lem7591983 _97606)). Qed.
Lemma lem7591987 (n : nat) : (term57 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7591988 : term58 = term59.
Proof. exact (@lem7591987 (NUMERAL 0)). Qed.
Lemma lem7591989 (_97606 : int) : (term91 _97606) = (term92 _97606).
Proof. exact (MK_COMB (@lem7591985 _97606) (@lem7591988)). Qed.
Lemma lem7591990 (_97606 : int) : (term90 _97606) = (term92 _97606).
Proof. exact (TRANS (@lem7591974 _97606) (@lem7591989 _97606)). Qed.
Lemma lem7591991 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7591992 (_97606 : int) : (term93 _97606) = (term94 _97606).
Proof. exact (MK_COMB (@lem7591991) (@lem7591990 _97606)). Qed.
Lemma lem7591994 (x : int) (y : int) : (int_le x y) = (term55 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7591995 (_97606 : int) : (term95 _97606) = (term96 _97606).
Proof. exact (@lem7591994 term97 _97606). Qed.
Lemma lem7591997 (x : int) (y : int) : (term69 x y) = (term70 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7591998 : term98 = term99.
Proof. exact (@lem7591997 term14 term66). Qed.
Lemma lem7592000 (n : nat) : (term57 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7592001 : term58 = term59.
Proof. exact (@lem7592000 (NUMERAL 0)). Qed.
Lemma lem7592002 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7592003 : term100 = term101.
Proof. exact (MK_COMB (@lem7592002) (@lem7592001)). Qed.
Lemma lem7592005 (n : nat) : (term57 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7592006 : term73 = term74.
Proof. exact (@lem7592005 term11). Qed.
Lemma lem7592007 : term99 = term102.
Proof. exact (MK_COMB (@lem7592003) (@lem7592006)). Qed.
Lemma lem7592008 : term98 = term102.
Proof. exact (TRANS (@lem7591998) (@lem7592007)). Qed.
Lemma lem7592009 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7592010 : term103 = term104.
Proof. exact (MK_COMB (@lem7592009) (@lem7592008)). Qed.
Lemma lem7592011 (_97606 : int) : (real_of_int _97606) = (real_of_int _97606).
Proof. exact (eq_refl (real_of_int _97606)). Qed.
Lemma lem7592012 (_97606 : int) : (term96 _97606) = (term105 _97606).
Proof. exact (MK_COMB (@lem7592010) (@lem7592011 _97606)). Qed.
Lemma lem7592013 (_97606 : int) : (term95 _97606) = (term105 _97606).
Proof. exact (TRANS (@lem7591995 _97606) (@lem7592012 _97606)). Qed.
Lemma lem7592014 (_97606 : int) : (term89 _97606) = (term106 _97606).
Proof. exact (MK_COMB (@lem7591992 _97606) (@lem7592013 _97606)). Qed.
Lemma lem7592015 (_97606 : int) : (term34 _97606) = (term106 _97606).
Proof. exact (TRANS (@lem7591971 _97606) (@lem7592014 _97606)). Qed.
Lemma lem7592016 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7592017 (_97606 : int) : (term37 _97606) = (term107 _97606).
Proof. exact (MK_COMB (@lem7592016) (@lem7591968 _97606)). Qed.
Lemma lem7592018 (_97606 : int) : (term39 _97606) = (term108 _97606).
Proof. exact (MK_COMB (@lem7592017 _97606) (@lem7592015 _97606)). Qed.
Lemma lem7592019 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7592020 (_97606 : int) : (term43 _97606) = (term109 _97606).
Proof. exact (MK_COMB (@lem7592019) (@lem7591955 _97606)). Qed.
Lemma lem7592021 (_97606 : int) : (term45 _97606) = (term110 _97606).
Proof. exact (MK_COMB (@lem7592020 _97606) (@lem7592018 _97606)). Qed.
Lemma lem7592022 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7592023 (_97606 : int) : (term49 _97606) = (term111 _97606).
Proof. exact (MK_COMB (@lem7592022) (@lem7591916 _97606)). Qed.
Lemma lem7592024 (_97606 : int) : (term51 _97606) = (term112 _97606).
Proof. exact (MK_COMB (@lem7592023 _97606) (@lem7592021 _97606)). Qed.
Lemma lem7592025 (_97606 : int) : (term52 _97606) = (term112 _97606).
Proof. exact (TRANS (@lem7591903 _97606) (@lem7592024 _97606)). Qed.
Lemma lem7592029 (t : Prop) : (term113 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7592085 (_97606 : int) : (term114 _97606) = (term112 _97606).
Proof. exact (@lem7592029 (term112 _97606)). Qed.
Lemma lem7592086 (_97606 : int) : (term62 _97606) = (term115 _97606).
Proof. exact (@lem1988287 (real_of_int _97606) term59). Qed.
Lemma lem7592092 (_97606 : int) : (term116 _97606) = (term117 _97606).
Proof. exact (@lem1982792 (real_of_int _97606) term59). Qed.
Lemma lem7592094 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7592095 : term59 = term119.
Proof. exact (@lem7592094 (NUMERAL 0)). Qed.
Lemma lem7592097 (x : nat) : (term120 x) = (term121 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7592098 : term122 = term123.
Proof. exact (@lem7592097 term11). Qed.
Lemma lem7592099 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7592100 : term124 = term125.
Proof. exact (MK_COMB (@lem7592099) (@lem7592098)). Qed.
Lemma lem7592101 : term126 = term127.
Proof. exact (MK_COMB (@lem7592100) (@lem7592095)). Qed.
Lemma lem7592102 : term127 = term128.
Proof. exact (@lem1981613 term122 term59 term74 term74). Qed.
Lemma lem7592104 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7592105 : term131 = term132.
Proof. exact (@lem7592104 term11 term11). Qed.
Lemma lem7592106 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7592107 : term134 = term11.
Proof. exact (EQ_MP (@lem7592106) (@lem940073)). Qed.
Lemma lem7592108 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7592109 : term132 = term74.
Proof. exact (MK_COMB (@lem7592108) (@lem7592107)). Qed.
Lemma lem7592110 : term131 = term74.
Proof. exact (TRANS (@lem7592105) (@lem7592109)). Qed.
Lemma lem7592112 (x : nat) : (term135 x) = term59.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7592113 : term126 = term59.
Proof. exact (@lem7592112 term11). Qed.
Lemma lem7592114 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7592115 : term136 = term137.
Proof. exact (MK_COMB (@lem7592114) (@lem7592113)). Qed.
Lemma lem7592116 : term128 = term119.
Proof. exact (MK_COMB (@lem7592115) (@lem7592110)). Qed.
Lemma lem7592117 : term127 = term119.
Proof. exact (TRANS (@lem7592102) (@lem7592116)). Qed.
Lemma lem7592118 : term126 = term119.
Proof. exact (TRANS (@lem7592101) (@lem7592117)). Qed.
Lemma lem7592120 (x : real) : (term138 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7592121 : term119 = term59.
Proof. exact (@lem7592120 term59). Qed.
Lemma lem7592122 : term126 = term59.
Proof. exact (TRANS (@lem7592118) (@lem7592121)). Qed.
Lemma lem7592123 (_97606 : int) : (term75 _97606) = (term75 _97606).
Proof. exact (eq_refl (term75 _97606)). Qed.
Lemma lem7592124 (_97606 : int) : (term117 _97606) = (term139 _97606).
Proof. exact (MK_COMB (@lem7592123 _97606) (@lem7592122)). Qed.
Lemma lem7592125 (_97606 : int) : (term139 _97606) = (real_of_int _97606).
Proof. exact (@lem1982723 (real_of_int _97606)). Qed.
Lemma lem7592126 (_97606 : int) : (term117 _97606) = (real_of_int _97606).
Proof. exact (TRANS (@lem7592124 _97606) (@lem7592125 _97606)). Qed.
Lemma lem7592128 (_97606 : int) : (term116 _97606) = (real_of_int _97606).
Proof. exact (TRANS (@lem7592092 _97606) (@lem7592126 _97606)). Qed.
Lemma lem7592129 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7592130 (_97606 : int) : (term140 _97606) = (term141 _97606).
Proof. exact (MK_COMB (@lem7592129) (@lem7592128 _97606)). Qed.
Lemma lem7592131 : term59 = term59.
Proof. exact (eq_refl term59). Qed.
Lemma lem7592132 (_97606 : int) : (term115 _97606) = (term142 _97606).
Proof. exact (MK_COMB (@lem7592130 _97606) (@lem7592131)). Qed.
Lemma lem7592133 (_97606 : int) : (term62 _97606) = (term142 _97606).
Proof. exact (TRANS (@lem7592086 _97606) (@lem7592132 _97606)). Qed.
Lemma lem7592134 (_97606 : int) : (term79 _97606) = (term143 _97606).
Proof. exact (@lem1988287 term74 (term76 _97606)). Qed.
Lemma lem7592146 (_97606 : int) : (term144 _97606) = (term145 _97606).
Proof. exact (@lem1982792 term74 (term76 _97606)). Qed.
Lemma lem7592147 (_97606 : int) : (term146 _97606) = (term147 _97606).
Proof. exact (@lem1982781 (real_of_int _97606) term122 term74). Qed.
Lemma lem7592149 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7592150 : term74 = term148.
Proof. exact (@lem7592149 term11). Qed.
Lemma lem7592152 (x : nat) : (term120 x) = (term121 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7592153 : term122 = term123.
Proof. exact (@lem7592152 term11). Qed.
Lemma lem7592154 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7592155 : term124 = term125.
Proof. exact (MK_COMB (@lem7592154) (@lem7592153)). Qed.
Lemma lem7592156 : term149 = term150.
Proof. exact (MK_COMB (@lem7592155) (@lem7592150)). Qed.
Lemma lem7592157 : term150 = term151.
Proof. exact (@lem1981613 term122 term74 term74 term74). Qed.
Lemma lem7592159 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7592160 : term131 = term132.
Proof. exact (@lem7592159 term11 term11). Qed.
Lemma lem7592161 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7592162 : term134 = term11.
Proof. exact (EQ_MP (@lem7592161) (@lem940073)). Qed.
Lemma lem7592163 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7592164 : term132 = term74.
Proof. exact (MK_COMB (@lem7592163) (@lem7592162)). Qed.
Lemma lem7592165 : term131 = term74.
Proof. exact (TRANS (@lem7592160) (@lem7592164)). Qed.
Lemma lem7592167 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7592168 : term149 = term154.
Proof. exact (@lem7592167 term11 term11). Qed.
Lemma lem7592169 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7592170 : term134 = term11.
Proof. exact (EQ_MP (@lem7592169) (@lem940073)). Qed.
Lemma lem7592171 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7592172 : term132 = term74.
Proof. exact (MK_COMB (@lem7592171) (@lem7592170)). Qed.
Lemma lem7592173 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7592174 : term154 = term122.
Proof. exact (MK_COMB (@lem7592173) (@lem7592172)). Qed.
Lemma lem7592175 : term149 = term122.
Proof. exact (TRANS (@lem7592168) (@lem7592174)). Qed.
Lemma lem7592176 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7592177 : term155 = term156.
Proof. exact (MK_COMB (@lem7592176) (@lem7592175)). Qed.
Lemma lem7592178 : term151 = term123.
Proof. exact (MK_COMB (@lem7592177) (@lem7592165)). Qed.
Lemma lem7592179 : term150 = term123.
Proof. exact (TRANS (@lem7592157) (@lem7592178)). Qed.
Lemma lem7592180 : term149 = term123.
Proof. exact (TRANS (@lem7592156) (@lem7592179)). Qed.
Lemma lem7592182 (x : real) : (term138 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7592183 : term123 = term122.
Proof. exact (@lem7592182 term122). Qed.
Lemma lem7592184 : term149 = term122.
Proof. exact (TRANS (@lem7592180) (@lem7592183)). Qed.
Lemma lem7592187 (_97606 : int) : (term157 _97606) = (term157 _97606).
Proof. exact (eq_refl (term157 _97606)). Qed.
Lemma lem7592188 (_97606 : int) : (term147 _97606) = (term158 _97606).
Proof. exact (MK_COMB (@lem7592187 _97606) (@lem7592184)). Qed.
Lemma lem7592189 (_97606 : int) : (term146 _97606) = (term158 _97606).
Proof. exact (TRANS (@lem7592147 _97606) (@lem7592188 _97606)). Qed.
Lemma lem7592190 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem7592191 (_97606 : int) : (term145 _97606) = (term160 _97606).
Proof. exact (MK_COMB (@lem7592190) (@lem7592189 _97606)). Qed.
Lemma lem7592192 (_97606 : int) : (term160 _97606) = (term161 _97606).
Proof. exact (@lem1982757 (term162 _97606) term74 term122). Qed.
Lemma lem7592194 (x : nat) : (term120 x) = (term121 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7592195 : term122 = term123.
Proof. exact (@lem7592194 term11). Qed.
Lemma lem7592197 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7592198 : term74 = term148.
Proof. exact (@lem7592197 term11). Qed.
Lemma lem7592199 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7592200 : term159 = term163.
Proof. exact (MK_COMB (@lem7592199) (@lem7592198)). Qed.
Lemma lem7592201 : term164 = term165.
Proof. exact (MK_COMB (@lem7592200) (@lem7592195)). Qed.
Lemma lem7592202 : term166.
Proof. exact (@lem1981473 term74 term74 term122 term74 term59 term74). Qed.
Lemma lem7592204 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7592205 : term168 = term169.
Proof. exact (@lem7592204 (NUMERAL 0) term11). Qed.
Lemma lem7592206 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7592207 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7592208 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7592207 h1) (fun h1 : term169 = True => @lem7592206)). Qed.
Lemma lem7592209 : term169 = True.
Proof. exact (EQ_MP (@lem7592208) (@lem7592206)). Qed.
Lemma lem7592210 : term168 = True.
Proof. exact (TRANS (@lem7592205) (@lem7592209)). Qed.
Lemma lem7592211 : True = term168.
Proof. exact (SYM (@lem7592210)). Qed.
Lemma lem7592212 : term168.
Proof. exact (EQ_MP (@lem7592211) (@lem0)). Qed.
Lemma lem7592213 : term171.
Proof. exact (@lem7592202 (@lem7592212)). Qed.
Lemma lem7592215 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7592216 : term168 = term169.
Proof. exact (@lem7592215 (NUMERAL 0) term11). Qed.
Lemma lem7592217 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7592218 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7592219 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7592218 h1) (fun h1 : term169 = True => @lem7592217)). Qed.
Lemma lem7592220 : term169 = True.
Proof. exact (EQ_MP (@lem7592219) (@lem7592217)). Qed.
Lemma lem7592221 : term168 = True.
Proof. exact (TRANS (@lem7592216) (@lem7592220)). Qed.
Lemma lem7592222 : True = term168.
Proof. exact (SYM (@lem7592221)). Qed.
Lemma lem7592223 : term168.
Proof. exact (EQ_MP (@lem7592222) (@lem0)). Qed.
Lemma lem7592224 : term172.
Proof. exact (@lem7592213 (@lem7592223)). Qed.
Lemma lem7592226 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7592227 : term168 = term169.
Proof. exact (@lem7592226 (NUMERAL 0) term11). Qed.
Lemma lem7592228 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7592229 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7592230 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7592229 h1) (fun h1 : term169 = True => @lem7592228)). Qed.
Lemma lem7592231 : term169 = True.
Proof. exact (EQ_MP (@lem7592230) (@lem7592228)). Qed.
Lemma lem7592232 : term168 = True.
Proof. exact (TRANS (@lem7592227) (@lem7592231)). Qed.
Lemma lem7592233 : True = term168.
Proof. exact (SYM (@lem7592232)). Qed.
Lemma lem7592234 : term168.
Proof. exact (EQ_MP (@lem7592233) (@lem0)). Qed.
Lemma lem7592235 : term173.
Proof. exact (@lem7592224 (@lem7592234)). Qed.
Lemma lem7592237 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7592238 : term149 = term154.
Proof. exact (@lem7592237 term11 term11). Qed.
Lemma lem7592239 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7592240 : term134 = term11.
Proof. exact (EQ_MP (@lem7592239) (@lem940073)). Qed.
Lemma lem7592241 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7592242 : term132 = term74.
Proof. exact (MK_COMB (@lem7592241) (@lem7592240)). Qed.
Lemma lem7592243 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7592244 : term154 = term122.
Proof. exact (MK_COMB (@lem7592243) (@lem7592242)). Qed.
Lemma lem7592245 : term149 = term122.
Proof. exact (TRANS (@lem7592238) (@lem7592244)). Qed.
Lemma lem7592247 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7592248 : term131 = term132.
Proof. exact (@lem7592247 term11 term11). Qed.
Lemma lem7592249 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7592250 : term134 = term11.
Proof. exact (EQ_MP (@lem7592249) (@lem940073)). Qed.
Lemma lem7592251 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7592252 : term132 = term74.
Proof. exact (MK_COMB (@lem7592251) (@lem7592250)). Qed.
Lemma lem7592253 : term131 = term74.
Proof. exact (TRANS (@lem7592248) (@lem7592252)). Qed.
Lemma lem7592254 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7592255 : term174 = term159.
Proof. exact (MK_COMB (@lem7592254) (@lem7592253)). Qed.
Lemma lem7592256 : term175 = term164.
Proof. exact (MK_COMB (@lem7592255) (@lem7592245)). Qed.
Lemma lem7592258 (m : nat) : (term176 m) = term59.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem7592259 : term164 = term59.
Proof. exact (@lem7592258 term11). Qed.
Lemma lem7592260 : term175 = term59.
Proof. exact (TRANS (@lem7592256) (@lem7592259)). Qed.
Lemma lem7592261 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7592262 : term177 = term178.
Proof. exact (MK_COMB (@lem7592261) (@lem7592260)). Qed.
Lemma lem7592263 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem7592264 : term179 = term180.
Proof. exact (MK_COMB (@lem7592262) (@lem7592263)). Qed.
Lemma lem7592266 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7592267 : term180 = term59.
Proof. exact (@lem7592266 term11). Qed.
Lemma lem7592268 : term179 = term59.
Proof. exact (TRANS (@lem7592264) (@lem7592267)). Qed.
Lemma lem7592270 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7592271 : term131 = term132.
Proof. exact (@lem7592270 term11 term11). Qed.
Lemma lem7592272 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7592273 : term134 = term11.
Proof. exact (EQ_MP (@lem7592272) (@lem940073)). Qed.
Lemma lem7592274 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7592275 : term132 = term74.
Proof. exact (MK_COMB (@lem7592274) (@lem7592273)). Qed.
Lemma lem7592276 : term131 = term74.
Proof. exact (TRANS (@lem7592271) (@lem7592275)). Qed.
Lemma lem7592277 : term178 = term178.
Proof. exact (eq_refl term178). Qed.
Lemma lem7592278 : term182 = term180.
Proof. exact (MK_COMB (@lem7592277) (@lem7592276)). Qed.
Lemma lem7592280 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7592281 : term180 = term59.
Proof. exact (@lem7592280 term11). Qed.
Lemma lem7592282 : term182 = term59.
Proof. exact (TRANS (@lem7592278) (@lem7592281)). Qed.
Lemma lem7592283 : term59 = term182.
Proof. exact (SYM (@lem7592282)). Qed.
Lemma lem7592284 : term179 = term182.
Proof. exact (TRANS (@lem7592268) (@lem7592283)). Qed.
Lemma lem7592285 : term165 = term119.
Proof. exact (@lem7592235 (@lem7592284)). Qed.
Lemma lem7592286 : term164 = term119.
Proof. exact (TRANS (@lem7592201) (@lem7592285)). Qed.
Lemma lem7592288 (x : real) : (term138 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7592289 : term119 = term59.
Proof. exact (@lem7592288 term59). Qed.
Lemma lem7592290 : term164 = term59.
Proof. exact (TRANS (@lem7592286) (@lem7592289)). Qed.
Lemma lem7592291 (_97606 : int) : (term157 _97606) = (term157 _97606).
Proof. exact (eq_refl (term157 _97606)). Qed.
Lemma lem7592292 (_97606 : int) : (term161 _97606) = (term183 _97606).
Proof. exact (MK_COMB (@lem7592291 _97606) (@lem7592290)). Qed.
Lemma lem7592293 (_97606 : int) : (term160 _97606) = (term183 _97606).
Proof. exact (TRANS (@lem7592192 _97606) (@lem7592292 _97606)). Qed.
Lemma lem7592294 (_97606 : int) : (term183 _97606) = (term162 _97606).
Proof. exact (@lem1982723 (term162 _97606)). Qed.
Lemma lem7592295 (_97606 : int) : (term160 _97606) = (term162 _97606).
Proof. exact (TRANS (@lem7592293 _97606) (@lem7592294 _97606)). Qed.
Lemma lem7592296 (_97606 : int) : (term145 _97606) = (term162 _97606).
Proof. exact (TRANS (@lem7592191 _97606) (@lem7592295 _97606)). Qed.
Lemma lem7592298 (_97606 : int) : (term144 _97606) = (term162 _97606).
Proof. exact (TRANS (@lem7592146 _97606) (@lem7592296 _97606)). Qed.
Lemma lem7592299 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7592300 (_97606 : int) : (term184 _97606) = (term185 _97606).
Proof. exact (MK_COMB (@lem7592299) (@lem7592298 _97606)). Qed.
Lemma lem7592301 : term59 = term59.
Proof. exact (eq_refl term59). Qed.
Lemma lem7592302 (_97606 : int) : (term143 _97606) = (term186 _97606).
Proof. exact (MK_COMB (@lem7592300 _97606) (@lem7592301)). Qed.
Lemma lem7592303 (_97606 : int) : (term79 _97606) = (term186 _97606).
Proof. exact (TRANS (@lem7592134 _97606) (@lem7592302 _97606)). Qed.
Lemma lem7592304 (_97606 : int) : ((real_of_int _97606) = term59) = ((term116 _97606) = term59).
Proof. exact (@lem1988293 (real_of_int _97606) term59). Qed.
Lemma lem7592310 (_97606 : int) : (term116 _97606) = (term117 _97606).
Proof. exact (@lem1982792 (real_of_int _97606) term59). Qed.
Lemma lem7592312 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7592313 : term59 = term119.
Proof. exact (@lem7592312 (NUMERAL 0)). Qed.
Lemma lem7592315 (x : nat) : (term120 x) = (term121 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7592316 : term122 = term123.
Proof. exact (@lem7592315 term11). Qed.
Lemma lem7592317 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7592318 : term124 = term125.
Proof. exact (MK_COMB (@lem7592317) (@lem7592316)). Qed.
Lemma lem7592319 : term126 = term127.
Proof. exact (MK_COMB (@lem7592318) (@lem7592313)). Qed.
Lemma lem7592320 : term127 = term128.
Proof. exact (@lem1981613 term122 term59 term74 term74). Qed.
Lemma lem7592322 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7592323 : term131 = term132.
Proof. exact (@lem7592322 term11 term11). Qed.
Lemma lem7592324 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7592325 : term134 = term11.
Proof. exact (EQ_MP (@lem7592324) (@lem940073)). Qed.
Lemma lem7592326 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7592327 : term132 = term74.
Proof. exact (MK_COMB (@lem7592326) (@lem7592325)). Qed.
Lemma lem7592328 : term131 = term74.
Proof. exact (TRANS (@lem7592323) (@lem7592327)). Qed.
Lemma lem7592330 (x : nat) : (term135 x) = term59.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7592331 : term126 = term59.
Proof. exact (@lem7592330 term11). Qed.
Lemma lem7592332 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7592333 : term136 = term137.
Proof. exact (MK_COMB (@lem7592332) (@lem7592331)). Qed.
Lemma lem7592334 : term128 = term119.
Proof. exact (MK_COMB (@lem7592333) (@lem7592328)). Qed.
Lemma lem7592335 : term127 = term119.
Proof. exact (TRANS (@lem7592320) (@lem7592334)). Qed.
Lemma lem7592336 : term126 = term119.
Proof. exact (TRANS (@lem7592319) (@lem7592335)). Qed.
Lemma lem7592338 (x : real) : (term138 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7592339 : term119 = term59.
Proof. exact (@lem7592338 term59). Qed.
Lemma lem7592340 : term126 = term59.
Proof. exact (TRANS (@lem7592336) (@lem7592339)). Qed.
Lemma lem7592341 (_97606 : int) : (term75 _97606) = (term75 _97606).
Proof. exact (eq_refl (term75 _97606)). Qed.
Lemma lem7592342 (_97606 : int) : (term117 _97606) = (term139 _97606).
Proof. exact (MK_COMB (@lem7592341 _97606) (@lem7592340)). Qed.
Lemma lem7592343 (_97606 : int) : (term139 _97606) = (real_of_int _97606).
Proof. exact (@lem1982723 (real_of_int _97606)). Qed.
Lemma lem7592344 (_97606 : int) : (term117 _97606) = (real_of_int _97606).
Proof. exact (TRANS (@lem7592342 _97606) (@lem7592343 _97606)). Qed.
Lemma lem7592346 (_97606 : int) : (term116 _97606) = (real_of_int _97606).
Proof. exact (TRANS (@lem7592310 _97606) (@lem7592344 _97606)). Qed.
Lemma lem7592347 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7592348 (_97606 : int) : (term187 _97606) = (term80 _97606).
Proof. exact (MK_COMB (@lem7592347) (@lem7592346 _97606)). Qed.
Lemma lem7592349 : term59 = term59.
Proof. exact (eq_refl term59). Qed.
Lemma lem7592350 (_97606 : int) : ((term116 _97606) = term59) = ((real_of_int _97606) = term59).
Proof. exact (MK_COMB (@lem7592348 _97606) (@lem7592349)). Qed.
Lemma lem7592351 (_97606 : int) : ((real_of_int _97606) = term59) = ((real_of_int _97606) = term59).
Proof. exact (TRANS (@lem7592304 _97606) (@lem7592350 _97606)). Qed.
Lemma lem7592352 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7592353 (_97606 : int) : (term81 _97606) = (term188 _97606).
Proof. exact (MK_COMB (@lem7592352) (@lem7592303 _97606)). Qed.
Lemma lem7592354 (_97606 : int) : (term82 _97606) = (term189 _97606).
Proof. exact (MK_COMB (@lem7592353 _97606) (@lem7592351 _97606)). Qed.
Lemma lem7592355 (_97606 : int) : (term86 _97606) = (term190 _97606).
Proof. exact (@lem1988287 (real_of_int _97606) term74). Qed.
Lemma lem7592361 (_97606 : int) : (term191 _97606) = (term192 _97606).
Proof. exact (@lem1982792 (real_of_int _97606) term74). Qed.
Lemma lem7592363 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7592364 : term74 = term148.
Proof. exact (@lem7592363 term11). Qed.
Lemma lem7592366 (x : nat) : (term120 x) = (term121 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7592367 : term122 = term123.
Proof. exact (@lem7592366 term11). Qed.
Lemma lem7592368 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7592369 : term124 = term125.
Proof. exact (MK_COMB (@lem7592368) (@lem7592367)). Qed.
Lemma lem7592370 : term149 = term150.
Proof. exact (MK_COMB (@lem7592369) (@lem7592364)). Qed.
Lemma lem7592371 : term150 = term151.
Proof. exact (@lem1981613 term122 term74 term74 term74). Qed.
Lemma lem7592373 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7592374 : term131 = term132.
Proof. exact (@lem7592373 term11 term11). Qed.
Lemma lem7592375 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7592376 : term134 = term11.
Proof. exact (EQ_MP (@lem7592375) (@lem940073)). Qed.
Lemma lem7592377 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7592378 : term132 = term74.
Proof. exact (MK_COMB (@lem7592377) (@lem7592376)). Qed.
Lemma lem7592379 : term131 = term74.
Proof. exact (TRANS (@lem7592374) (@lem7592378)). Qed.
Lemma lem7592381 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7592382 : term149 = term154.
Proof. exact (@lem7592381 term11 term11). Qed.
Lemma lem7592383 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7592384 : term134 = term11.
Proof. exact (EQ_MP (@lem7592383) (@lem940073)). Qed.
Lemma lem7592385 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7592386 : term132 = term74.
Proof. exact (MK_COMB (@lem7592385) (@lem7592384)). Qed.
Lemma lem7592387 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7592388 : term154 = term122.
Proof. exact (MK_COMB (@lem7592387) (@lem7592386)). Qed.
Lemma lem7592389 : term149 = term122.
Proof. exact (TRANS (@lem7592382) (@lem7592388)). Qed.
Lemma lem7592390 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7592391 : term155 = term156.
Proof. exact (MK_COMB (@lem7592390) (@lem7592389)). Qed.
Lemma lem7592392 : term151 = term123.
Proof. exact (MK_COMB (@lem7592391) (@lem7592379)). Qed.
Lemma lem7592393 : term150 = term123.
Proof. exact (TRANS (@lem7592371) (@lem7592392)). Qed.
Lemma lem7592394 : term149 = term123.
Proof. exact (TRANS (@lem7592370) (@lem7592393)). Qed.
Lemma lem7592396 (x : real) : (term138 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7592397 : term123 = term122.
Proof. exact (@lem7592396 term122). Qed.
Lemma lem7592398 : term149 = term122.
Proof. exact (TRANS (@lem7592394) (@lem7592397)). Qed.
Lemma lem7592399 (_97606 : int) : (term75 _97606) = (term75 _97606).
Proof. exact (eq_refl (term75 _97606)). Qed.
Lemma lem7592402 (_97606 : int) : (term192 _97606) = (term193 _97606).
Proof. exact (MK_COMB (@lem7592399 _97606) (@lem7592398)). Qed.
Lemma lem7592404 (_97606 : int) : (term191 _97606) = (term193 _97606).
Proof. exact (TRANS (@lem7592361 _97606) (@lem7592402 _97606)). Qed.
Lemma lem7592405 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7592406 (_97606 : int) : (term194 _97606) = (term195 _97606).
Proof. exact (MK_COMB (@lem7592405) (@lem7592404 _97606)). Qed.
Lemma lem7592407 : term59 = term59.
Proof. exact (eq_refl term59). Qed.
Lemma lem7592408 (_97606 : int) : (term190 _97606) = (term196 _97606).
Proof. exact (MK_COMB (@lem7592406 _97606) (@lem7592407)). Qed.
Lemma lem7592409 (_97606 : int) : (term86 _97606) = (term196 _97606).
Proof. exact (TRANS (@lem7592355 _97606) (@lem7592408 _97606)). Qed.
Lemma lem7592410 (_97606 : int) : (term92 _97606) = (term197 _97606).
Proof. exact (@lem1988287 term59 (term76 _97606)). Qed.
Lemma lem7592422 (_97606 : int) : (term198 _97606) = (term199 _97606).
Proof. exact (@lem1982792 term59 (term76 _97606)). Qed.
Lemma lem7592423 (_97606 : int) : (term146 _97606) = (term147 _97606).
Proof. exact (@lem1982781 (real_of_int _97606) term122 term74). Qed.
Lemma lem7592425 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7592426 : term74 = term148.
Proof. exact (@lem7592425 term11). Qed.
Lemma lem7592428 (x : nat) : (term120 x) = (term121 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7592429 : term122 = term123.
Proof. exact (@lem7592428 term11). Qed.
Lemma lem7592430 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7592431 : term124 = term125.
Proof. exact (MK_COMB (@lem7592430) (@lem7592429)). Qed.
Lemma lem7592432 : term149 = term150.
Proof. exact (MK_COMB (@lem7592431) (@lem7592426)). Qed.
Lemma lem7592433 : term150 = term151.
Proof. exact (@lem1981613 term122 term74 term74 term74). Qed.
Lemma lem7592435 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7592436 : term131 = term132.
Proof. exact (@lem7592435 term11 term11). Qed.
Lemma lem7592437 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7592438 : term134 = term11.
Proof. exact (EQ_MP (@lem7592437) (@lem940073)). Qed.
Lemma lem7592439 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7592440 : term132 = term74.
Proof. exact (MK_COMB (@lem7592439) (@lem7592438)). Qed.
Lemma lem7592441 : term131 = term74.
Proof. exact (TRANS (@lem7592436) (@lem7592440)). Qed.
Lemma lem7592443 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7592444 : term149 = term154.
Proof. exact (@lem7592443 term11 term11). Qed.
Lemma lem7592445 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7592446 : term134 = term11.
Proof. exact (EQ_MP (@lem7592445) (@lem940073)). Qed.
Lemma lem7592447 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7592448 : term132 = term74.
Proof. exact (MK_COMB (@lem7592447) (@lem7592446)). Qed.
Lemma lem7592449 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7592450 : term154 = term122.
Proof. exact (MK_COMB (@lem7592449) (@lem7592448)). Qed.
Lemma lem7592451 : term149 = term122.
Proof. exact (TRANS (@lem7592444) (@lem7592450)). Qed.
Lemma lem7592452 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7592453 : term155 = term156.
Proof. exact (MK_COMB (@lem7592452) (@lem7592451)). Qed.
Lemma lem7592454 : term151 = term123.
Proof. exact (MK_COMB (@lem7592453) (@lem7592441)). Qed.
Lemma lem7592455 : term150 = term123.
Proof. exact (TRANS (@lem7592433) (@lem7592454)). Qed.
Lemma lem7592456 : term149 = term123.
Proof. exact (TRANS (@lem7592432) (@lem7592455)). Qed.
Lemma lem7592458 (x : real) : (term138 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7592459 : term123 = term122.
Proof. exact (@lem7592458 term122). Qed.
Lemma lem7592460 : term149 = term122.
Proof. exact (TRANS (@lem7592456) (@lem7592459)). Qed.
Lemma lem7592463 (_97606 : int) : (term157 _97606) = (term157 _97606).
Proof. exact (eq_refl (term157 _97606)). Qed.
Lemma lem7592464 (_97606 : int) : (term147 _97606) = (term158 _97606).
Proof. exact (MK_COMB (@lem7592463 _97606) (@lem7592460)). Qed.
Lemma lem7592465 (_97606 : int) : (term146 _97606) = (term158 _97606).
Proof. exact (TRANS (@lem7592423 _97606) (@lem7592464 _97606)). Qed.
Lemma lem7592466 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem7592467 (_97606 : int) : (term199 _97606) = (term200 _97606).
Proof. exact (MK_COMB (@lem7592466) (@lem7592465 _97606)). Qed.
Lemma lem7592468 (_97606 : int) : (term200 _97606) = (term158 _97606).
Proof. exact (@lem1982721 (term158 _97606)). Qed.
Lemma lem7592469 (_97606 : int) : (term199 _97606) = (term158 _97606).
Proof. exact (TRANS (@lem7592467 _97606) (@lem7592468 _97606)). Qed.
Lemma lem7592471 (_97606 : int) : (term198 _97606) = (term158 _97606).
Proof. exact (TRANS (@lem7592422 _97606) (@lem7592469 _97606)). Qed.
Lemma lem7592472 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7592473 (_97606 : int) : (term201 _97606) = (term202 _97606).
Proof. exact (MK_COMB (@lem7592472) (@lem7592471 _97606)). Qed.
Lemma lem7592474 : term59 = term59.
Proof. exact (eq_refl term59). Qed.
Lemma lem7592475 (_97606 : int) : (term197 _97606) = (term203 _97606).
Proof. exact (MK_COMB (@lem7592473 _97606) (@lem7592474)). Qed.
Lemma lem7592476 (_97606 : int) : (term92 _97606) = (term203 _97606).
Proof. exact (TRANS (@lem7592410 _97606) (@lem7592475 _97606)). Qed.
Lemma lem7592477 (_97606 : int) : (term105 _97606) = (term204 _97606).
Proof. exact (@lem1988287 (real_of_int _97606) term102). Qed.
Lemma lem7592484 : term102 = term74.
Proof. exact (@lem1982721 term74). Qed.
Lemma lem7592487 (_97606 : int) : (term205 _97606) = (term205 _97606).
Proof. exact (eq_refl (term205 _97606)). Qed.
Lemma lem7592488 (_97606 : int) : (term206 _97606) = (term191 _97606).
Proof. exact (MK_COMB (@lem7592487 _97606) (@lem7592484)). Qed.
Lemma lem7592489 (_97606 : int) : (term191 _97606) = (term192 _97606).
Proof. exact (@lem1982792 (real_of_int _97606) term74). Qed.
Lemma lem7592491 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7592492 : term74 = term148.
Proof. exact (@lem7592491 term11). Qed.
Lemma lem7592494 (x : nat) : (term120 x) = (term121 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7592495 : term122 = term123.
Proof. exact (@lem7592494 term11). Qed.
Lemma lem7592496 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7592497 : term124 = term125.
Proof. exact (MK_COMB (@lem7592496) (@lem7592495)). Qed.
Lemma lem7592498 : term149 = term150.
Proof. exact (MK_COMB (@lem7592497) (@lem7592492)). Qed.
Lemma lem7592499 : term150 = term151.
Proof. exact (@lem1981613 term122 term74 term74 term74). Qed.
Lemma lem7592501 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7592502 : term131 = term132.
Proof. exact (@lem7592501 term11 term11). Qed.
Lemma lem7592503 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7592504 : term134 = term11.
Proof. exact (EQ_MP (@lem7592503) (@lem940073)). Qed.
Lemma lem7592505 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7592506 : term132 = term74.
Proof. exact (MK_COMB (@lem7592505) (@lem7592504)). Qed.
Lemma lem7592507 : term131 = term74.
Proof. exact (TRANS (@lem7592502) (@lem7592506)). Qed.
Lemma lem7592509 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7592510 : term149 = term154.
Proof. exact (@lem7592509 term11 term11). Qed.
Lemma lem7592511 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7592512 : term134 = term11.
Proof. exact (EQ_MP (@lem7592511) (@lem940073)). Qed.
Lemma lem7592513 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7592514 : term132 = term74.
Proof. exact (MK_COMB (@lem7592513) (@lem7592512)). Qed.
Lemma lem7592515 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7592516 : term154 = term122.
Proof. exact (MK_COMB (@lem7592515) (@lem7592514)). Qed.
Lemma lem7592517 : term149 = term122.
Proof. exact (TRANS (@lem7592510) (@lem7592516)). Qed.
Lemma lem7592518 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7592519 : term155 = term156.
Proof. exact (MK_COMB (@lem7592518) (@lem7592517)). Qed.
Lemma lem7592520 : term151 = term123.
Proof. exact (MK_COMB (@lem7592519) (@lem7592507)). Qed.
Lemma lem7592521 : term150 = term123.
Proof. exact (TRANS (@lem7592499) (@lem7592520)). Qed.
Lemma lem7592522 : term149 = term123.
Proof. exact (TRANS (@lem7592498) (@lem7592521)). Qed.
Lemma lem7592524 (x : real) : (term138 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7592525 : term123 = term122.
Proof. exact (@lem7592524 term122). Qed.
Lemma lem7592526 : term149 = term122.
Proof. exact (TRANS (@lem7592522) (@lem7592525)). Qed.
Lemma lem7592527 (_97606 : int) : (term75 _97606) = (term75 _97606).
Proof. exact (eq_refl (term75 _97606)). Qed.
Lemma lem7592530 (_97606 : int) : (term192 _97606) = (term193 _97606).
Proof. exact (MK_COMB (@lem7592527 _97606) (@lem7592526)). Qed.
Lemma lem7592531 (_97606 : int) : (term191 _97606) = (term193 _97606).
Proof. exact (TRANS (@lem7592489 _97606) (@lem7592530 _97606)). Qed.
Lemma lem7592532 (_97606 : int) : (term206 _97606) = (term193 _97606).
Proof. exact (TRANS (@lem7592488 _97606) (@lem7592531 _97606)). Qed.
Lemma lem7592533 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7592534 (_97606 : int) : (term207 _97606) = (term195 _97606).
Proof. exact (MK_COMB (@lem7592533) (@lem7592532 _97606)). Qed.
Lemma lem7592535 : term59 = term59.
Proof. exact (eq_refl term59). Qed.
Lemma lem7592536 (_97606 : int) : (term204 _97606) = (term196 _97606).
Proof. exact (MK_COMB (@lem7592534 _97606) (@lem7592535)). Qed.
Lemma lem7592537 (_97606 : int) : (term105 _97606) = (term196 _97606).
Proof. exact (TRANS (@lem7592477 _97606) (@lem7592536 _97606)). Qed.
Lemma lem7592538 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7592539 (_97606 : int) : (term94 _97606) = (term208 _97606).
Proof. exact (MK_COMB (@lem7592538) (@lem7592476 _97606)). Qed.
Lemma lem7592540 (_97606 : int) : (term106 _97606) = (term209 _97606).
Proof. exact (MK_COMB (@lem7592539 _97606) (@lem7592537 _97606)). Qed.
Lemma lem7592541 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7592542 (_97606 : int) : (term107 _97606) = (term210 _97606).
Proof. exact (MK_COMB (@lem7592541) (@lem7592409 _97606)). Qed.
Lemma lem7592543 (_97606 : int) : (term108 _97606) = (term211 _97606).
Proof. exact (MK_COMB (@lem7592542 _97606) (@lem7592540 _97606)). Qed.
Lemma lem7592544 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7592545 (_97606 : int) : (term109 _97606) = (term212 _97606).
Proof. exact (MK_COMB (@lem7592544) (@lem7592354 _97606)). Qed.
Lemma lem7592546 (_97606 : int) : (term110 _97606) = (term213 _97606).
Proof. exact (MK_COMB (@lem7592545 _97606) (@lem7592543 _97606)). Qed.
Lemma lem7592547 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7592548 (_97606 : int) : (term111 _97606) = (term214 _97606).
Proof. exact (MK_COMB (@lem7592547) (@lem7592133 _97606)). Qed.
Lemma lem7592549 (_97606 : int) : (term112 _97606) = (term215 _97606).
Proof. exact (MK_COMB (@lem7592548 _97606) (@lem7592546 _97606)). Qed.
Lemma lem7592556 (_97606 : int) : (term114 _97606) = (term215 _97606).
Proof. exact (TRANS (@lem7592085 _97606) (@lem7592549 _97606)). Qed.
Lemma lem7592574 (_97606 : int) : (term213 _97606) = (term216 _97606).
Proof. exact (@lem19158 (term196 _97606) (term189 _97606) (term209 _97606)). Qed.
Lemma lem7592575 (_97606 : int) : (term217 _97606) = (term218 _97606).
Proof. exact (@lem19158 (term203 _97606) (term189 _97606) (term196 _97606)). Qed.
Lemma lem7592582 (_97606 : int) : (term219 _97606) = (term220 _97606).
Proof. exact (@lem19367 (term186 _97606) ((real_of_int _97606) = term59) (term196 _97606)). Qed.
Lemma lem7592589 (_97606 : int) : (term221 _97606) = (term222 _97606).
Proof. exact (@lem19367 (term186 _97606) ((real_of_int _97606) = term59) (term203 _97606)). Qed.
Lemma lem7592590 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7592591 (_97606 : int) : (term223 _97606) = (term224 _97606).
Proof. exact (MK_COMB (@lem7592590) (@lem7592589 _97606)). Qed.
Lemma lem7592592 (_97606 : int) : (term218 _97606) = (term225 _97606).
Proof. exact (MK_COMB (@lem7592591 _97606) (@lem7592582 _97606)). Qed.
Lemma lem7592593 (_97606 : int) : (term217 _97606) = (term225 _97606).
Proof. exact (TRANS (@lem7592575 _97606) (@lem7592592 _97606)). Qed.
Lemma lem7592600 (_97606 : int) : (term219 _97606) = (term220 _97606).
Proof. exact (@lem19367 (term186 _97606) ((real_of_int _97606) = term59) (term196 _97606)). Qed.
Lemma lem7592601 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7592602 (_97606 : int) : (term226 _97606) = (term227 _97606).
Proof. exact (MK_COMB (@lem7592601) (@lem7592600 _97606)). Qed.
Lemma lem7592603 (_97606 : int) : (term216 _97606) = (term228 _97606).
Proof. exact (MK_COMB (@lem7592602 _97606) (@lem7592593 _97606)). Qed.
Lemma lem7592605 (_97606 : int) : (term213 _97606) = (term228 _97606).
Proof. exact (TRANS (@lem7592574 _97606) (@lem7592603 _97606)). Qed.
Lemma lem7592608 (_97606 : int) : (term214 _97606) = (term214 _97606).
Proof. exact (eq_refl (term214 _97606)). Qed.
Lemma lem7592609 (_97606 : int) : (term215 _97606) = (term229 _97606).
Proof. exact (MK_COMB (@lem7592608 _97606) (@lem7592605 _97606)). Qed.
Lemma lem7592610 (_97606 : int) : (term229 _97606) = (term230 _97606).
Proof. exact (@lem19158 (term220 _97606) (term142 _97606) (term225 _97606)). Qed.
Lemma lem7592611 (_97606 : int) : (term231 _97606) = (term232 _97606).
Proof. exact (@lem19158 (term222 _97606) (term142 _97606) (term220 _97606)). Qed.
Lemma lem7592618 (_97606 : int) : (term233 _97606) = (term234 _97606).
Proof. exact (@lem19158 (term235 _97606) (term142 _97606) (term236 _97606)). Qed.
Lemma lem7592625 (_97606 : int) : (term237 _97606) = (term238 _97606).
Proof. exact (@lem19158 (term239 _97606) (term142 _97606) (term240 _97606)). Qed.
Lemma lem7592626 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7592627 (_97606 : int) : (term241 _97606) = (term242 _97606).
Proof. exact (MK_COMB (@lem7592626) (@lem7592625 _97606)). Qed.
Lemma lem7592628 (_97606 : int) : (term232 _97606) = (term243 _97606).
Proof. exact (MK_COMB (@lem7592627 _97606) (@lem7592618 _97606)). Qed.
Lemma lem7592629 (_97606 : int) : (term231 _97606) = (term243 _97606).
Proof. exact (TRANS (@lem7592611 _97606) (@lem7592628 _97606)). Qed.
Lemma lem7592636 (_97606 : int) : (term233 _97606) = (term234 _97606).
Proof. exact (@lem19158 (term235 _97606) (term142 _97606) (term236 _97606)). Qed.
Lemma lem7592637 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7592638 (_97606 : int) : (term244 _97606) = (term245 _97606).
Proof. exact (MK_COMB (@lem7592637) (@lem7592636 _97606)). Qed.
Lemma lem7592639 (_97606 : int) : (term230 _97606) = (term246 _97606).
Proof. exact (MK_COMB (@lem7592638 _97606) (@lem7592629 _97606)). Qed.
Lemma lem7592640 (_97606 : int) : (term229 _97606) = (term246 _97606).
Proof. exact (TRANS (@lem7592610 _97606) (@lem7592639 _97606)). Qed.
Lemma lem7592641 (_97606 : int) : (term215 _97606) = (term246 _97606).
Proof. exact (TRANS (@lem7592609 _97606) (@lem7592640 _97606)). Qed.
Lemma lem7592642 (_97606 : int) : (term114 _97606) = (term246 _97606).
Proof. exact (TRANS (@lem7592556 _97606) (@lem7592641 _97606)). Qed.
Lemma lem7592676 (_97606 : int) (h1 : term246 _97606) : term246 _97606.
Proof. exact (h1). Qed.
Lemma lem7592677 (_97606 : int) (h1 : term234 _97606) : term234 _97606.
Proof. exact (h1). Qed.
Lemma lem7592678 (_97606 : int) (h1 : term247 _97606) : term247 _97606.
Proof. exact (h1). Qed.
Lemma lem7592679 (_97606 : int) (h1 : term247 _97606) : term235 _97606.
Proof. exact (proj2 (@lem7592678 _97606 h1)). Qed.
Lemma lem7592681 (_97606 : int) (h1 : term247 _97606) : term196 _97606.
Proof. exact (proj2 (@lem7592679 _97606 h1)). Qed.
Lemma lem7592682 (_97606 : int) (h1 : term247 _97606) : term186 _97606.
Proof. exact (proj1 (@lem7592679 _97606 h1)). Qed.
Lemma lem7592684 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7592685 : term248 = term168.
Proof. exact (@lem7592684 term59 term74). Qed.
Lemma lem7592687 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7592688 : term74 = term148.
Proof. exact (@lem7592687 term11). Qed.
Lemma lem7592690 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7592691 : term59 = term119.
Proof. exact (@lem7592690 (NUMERAL 0)). Qed.
Lemma lem7592692 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7592693 : term249 = term250.
Proof. exact (MK_COMB (@lem7592692) (@lem7592691)). Qed.
Lemma lem7592694 : term168 = term251.
Proof. exact (MK_COMB (@lem7592693) (@lem7592688)). Qed.
Lemma lem7592695 : term252.
Proof. exact (@lem1980255 term59 term74 term74 term74). Qed.
Lemma lem7592697 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7592698 : term168 = term169.
Proof. exact (@lem7592697 (NUMERAL 0) term11). Qed.
Lemma lem7592699 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7592700 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7592701 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7592700 h1) (fun h1 : term169 = True => @lem7592699)). Qed.
Lemma lem7592702 : term169 = True.
Proof. exact (EQ_MP (@lem7592701) (@lem7592699)). Qed.
Lemma lem7592703 : term168 = True.
Proof. exact (TRANS (@lem7592698) (@lem7592702)). Qed.
Lemma lem7592704 : True = term168.
Proof. exact (SYM (@lem7592703)). Qed.
Lemma lem7592705 : term168.
Proof. exact (EQ_MP (@lem7592704) (@lem0)). Qed.
Lemma lem7592706 : term253.
Proof. exact (@lem7592695 (@lem7592705)). Qed.
Lemma lem7592708 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7592709 : term168 = term169.
Proof. exact (@lem7592708 (NUMERAL 0) term11). Qed.
Lemma lem7592710 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7592711 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7592712 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7592711 h1) (fun h1 : term169 = True => @lem7592710)). Qed.
Lemma lem7592713 : term169 = True.
Proof. exact (EQ_MP (@lem7592712) (@lem7592710)). Qed.
Lemma lem7592714 : term168 = True.
Proof. exact (TRANS (@lem7592709) (@lem7592713)). Qed.
Lemma lem7592715 : True = term168.
Proof. exact (SYM (@lem7592714)). Qed.
Lemma lem7592716 : term168.
Proof. exact (EQ_MP (@lem7592715) (@lem0)). Qed.
Lemma lem7592717 : term251 = term254.
Proof. exact (@lem7592706 (@lem7592716)). Qed.
Lemma lem7592719 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7592720 : term131 = term132.
Proof. exact (@lem7592719 term11 term11). Qed.
Lemma lem7592721 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7592722 : term134 = term11.
Proof. exact (EQ_MP (@lem7592721) (@lem940073)). Qed.
Lemma lem7592723 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7592724 : term132 = term74.
Proof. exact (MK_COMB (@lem7592723) (@lem7592722)). Qed.
Lemma lem7592725 : term131 = term74.
Proof. exact (TRANS (@lem7592720) (@lem7592724)). Qed.
Lemma lem7592727 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7592728 : term180 = term59.
Proof. exact (@lem7592727 term11). Qed.
Lemma lem7592729 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7592730 : term255 = term249.
Proof. exact (MK_COMB (@lem7592729) (@lem7592728)). Qed.
Lemma lem7592731 : term254 = term168.
Proof. exact (MK_COMB (@lem7592730) (@lem7592725)). Qed.
Lemma lem7592733 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7592734 : term168 = term169.
Proof. exact (@lem7592733 (NUMERAL 0) term11). Qed.
Lemma lem7592735 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7592736 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7592737 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7592736 h1) (fun h1 : term169 = True => @lem7592735)). Qed.
Lemma lem7592738 : term169 = True.
Proof. exact (EQ_MP (@lem7592737) (@lem7592735)). Qed.
Lemma lem7592739 : term168 = True.
Proof. exact (TRANS (@lem7592734) (@lem7592738)). Qed.
Lemma lem7592740 : term254 = True.
Proof. exact (TRANS (@lem7592731) (@lem7592739)). Qed.
Lemma lem7592741 : term251 = True.
Proof. exact (TRANS (@lem7592717) (@lem7592740)). Qed.
Lemma lem7592742 : term168 = True.
Proof. exact (TRANS (@lem7592694) (@lem7592741)). Qed.
Lemma lem7592743 : term248 = True.
Proof. exact (TRANS (@lem7592685) (@lem7592742)). Qed.
Lemma lem7592744 : True = term248.
Proof. exact (SYM (@lem7592743)). Qed.
Lemma lem7592745 : term248.
Proof. exact (EQ_MP (@lem7592744) (@lem0)). Qed.
Lemma lem7592746 (_97606 : int) (h1 : term247 _97606) : term256 _97606.
Proof. exact (conj (@lem7592745) (@lem7592681 _97606 h1)). Qed.
Lemma lem7592748 (x : real) (y : real) : term257 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7592749 (_97606 : int) : term258 _97606.
Proof. exact (@lem7592748 term74 (term193 _97606)). Qed.
Lemma lem7592750 (_97606 : int) (h1 : term247 _97606) : term259 _97606.
Proof. exact (@lem7592749 _97606 (@lem7592746 _97606 h1)). Qed.
Lemma lem7592751 (_97606 : int) : (term260 _97606) = (term193 _97606).
Proof. exact (@lem1982733 (term193 _97606)). Qed.
Lemma lem7592752 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7592753 (_97606 : int) : (term261 _97606) = (term195 _97606).
Proof. exact (MK_COMB (@lem7592752) (@lem7592751 _97606)). Qed.
Lemma lem7592754 : term59 = term59.
Proof. exact (eq_refl term59). Qed.
Lemma lem7592755 (_97606 : int) : (term259 _97606) = (term196 _97606).
Proof. exact (MK_COMB (@lem7592753 _97606) (@lem7592754)). Qed.
Lemma lem7592756 (_97606 : int) (h1 : term247 _97606) : term196 _97606.
Proof. exact (EQ_MP (@lem7592755 _97606) (@lem7592750 _97606 h1)). Qed.
Lemma lem7592758 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7592759 : term248 = term168.
Proof. exact (@lem7592758 term59 term74). Qed.
Lemma lem7592761 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7592762 : term74 = term148.
Proof. exact (@lem7592761 term11). Qed.
Lemma lem7592764 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7592765 : term59 = term119.
Proof. exact (@lem7592764 (NUMERAL 0)). Qed.
Lemma lem7592766 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7592767 : term249 = term250.
Proof. exact (MK_COMB (@lem7592766) (@lem7592765)). Qed.
Lemma lem7592768 : term168 = term251.
Proof. exact (MK_COMB (@lem7592767) (@lem7592762)). Qed.
Lemma lem7592769 : term252.
Proof. exact (@lem1980255 term59 term74 term74 term74). Qed.
Lemma lem7592771 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7592772 : term168 = term169.
Proof. exact (@lem7592771 (NUMERAL 0) term11). Qed.
Lemma lem7592773 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7592774 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7592775 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7592774 h1) (fun h1 : term169 = True => @lem7592773)). Qed.
Lemma lem7592776 : term169 = True.
Proof. exact (EQ_MP (@lem7592775) (@lem7592773)). Qed.
Lemma lem7592777 : term168 = True.
Proof. exact (TRANS (@lem7592772) (@lem7592776)). Qed.
Lemma lem7592778 : True = term168.
Proof. exact (SYM (@lem7592777)). Qed.
Lemma lem7592779 : term168.
Proof. exact (EQ_MP (@lem7592778) (@lem0)). Qed.
Lemma lem7592780 : term253.
Proof. exact (@lem7592769 (@lem7592779)). Qed.
Lemma lem7592782 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7592783 : term168 = term169.
Proof. exact (@lem7592782 (NUMERAL 0) term11). Qed.
Lemma lem7592784 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7592785 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7592786 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7592785 h1) (fun h1 : term169 = True => @lem7592784)). Qed.
Lemma lem7592787 : term169 = True.
Proof. exact (EQ_MP (@lem7592786) (@lem7592784)). Qed.
Lemma lem7592788 : term168 = True.
Proof. exact (TRANS (@lem7592783) (@lem7592787)). Qed.
Lemma lem7592789 : True = term168.
Proof. exact (SYM (@lem7592788)). Qed.
Lemma lem7592790 : term168.
Proof. exact (EQ_MP (@lem7592789) (@lem0)). Qed.
Lemma lem7592791 : term251 = term254.
Proof. exact (@lem7592780 (@lem7592790)). Qed.
Lemma lem7592793 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7592794 : term131 = term132.
Proof. exact (@lem7592793 term11 term11). Qed.
Lemma lem7592795 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7592796 : term134 = term11.
Proof. exact (EQ_MP (@lem7592795) (@lem940073)). Qed.
Lemma lem7592797 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7592798 : term132 = term74.
Proof. exact (MK_COMB (@lem7592797) (@lem7592796)). Qed.
Lemma lem7592799 : term131 = term74.
Proof. exact (TRANS (@lem7592794) (@lem7592798)). Qed.
Lemma lem7592801 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7592802 : term180 = term59.
Proof. exact (@lem7592801 term11). Qed.
Lemma lem7592803 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7592804 : term255 = term249.
Proof. exact (MK_COMB (@lem7592803) (@lem7592802)). Qed.
Lemma lem7592805 : term254 = term168.
Proof. exact (MK_COMB (@lem7592804) (@lem7592799)). Qed.
Lemma lem7592807 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7592808 : term168 = term169.
Proof. exact (@lem7592807 (NUMERAL 0) term11). Qed.
Lemma lem7592809 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7592810 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7592811 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7592810 h1) (fun h1 : term169 = True => @lem7592809)). Qed.
Lemma lem7592812 : term169 = True.
Proof. exact (EQ_MP (@lem7592811) (@lem7592809)). Qed.
Lemma lem7592813 : term168 = True.
Proof. exact (TRANS (@lem7592808) (@lem7592812)). Qed.
Lemma lem7592814 : term254 = True.
Proof. exact (TRANS (@lem7592805) (@lem7592813)). Qed.
Lemma lem7592815 : term251 = True.
Proof. exact (TRANS (@lem7592791) (@lem7592814)). Qed.
Lemma lem7592816 : term168 = True.
Proof. exact (TRANS (@lem7592768) (@lem7592815)). Qed.
Lemma lem7592817 : term248 = True.
Proof. exact (TRANS (@lem7592759) (@lem7592816)). Qed.
Lemma lem7592818 : True = term248.
Proof. exact (SYM (@lem7592817)). Qed.
Lemma lem7592819 : term248.
Proof. exact (EQ_MP (@lem7592818) (@lem0)). Qed.
Lemma lem7592820 (_97606 : int) (h1 : term247 _97606) : term262 _97606.
Proof. exact (conj (@lem7592819) (@lem7592682 _97606 h1)). Qed.
Lemma lem7592822 (x : real) (y : real) : term257 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7592823 (_97606 : int) : term263 _97606.
Proof. exact (@lem7592822 term74 (term162 _97606)). Qed.
Lemma lem7592824 (_97606 : int) (h1 : term247 _97606) : term264 _97606.
Proof. exact (@lem7592823 _97606 (@lem7592820 _97606 h1)). Qed.
Lemma lem7592825 (_97606 : int) : (term265 _97606) = (term162 _97606).
Proof. exact (@lem1982733 (term162 _97606)). Qed.
Lemma lem7592826 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7592827 (_97606 : int) : (term266 _97606) = (term185 _97606).
Proof. exact (MK_COMB (@lem7592826) (@lem7592825 _97606)). Qed.
Lemma lem7592828 : term59 = term59.
Proof. exact (eq_refl term59). Qed.
Lemma lem7592829 (_97606 : int) : (term264 _97606) = (term186 _97606).
Proof. exact (MK_COMB (@lem7592827 _97606) (@lem7592828)). Qed.
Lemma lem7592830 (_97606 : int) (h1 : term247 _97606) : term186 _97606.
Proof. exact (EQ_MP (@lem7592829 _97606) (@lem7592824 _97606 h1)). Qed.
Lemma lem7592831 (_97606 : int) (h1 : term247 _97606) : term235 _97606.
Proof. exact (conj (@lem7592830 _97606 h1) (@lem7592756 _97606 h1)). Qed.
Lemma lem7592833 (x : real) (y : real) : term267 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7592834 (_97606 : int) : term268 _97606.
Proof. exact (@lem7592833 (term162 _97606) (term193 _97606)). Qed.
Lemma lem7592835 (_97606 : int) (h1 : term247 _97606) : term269 _97606.
Proof. exact (@lem7592834 _97606 (@lem7592831 _97606 h1)). Qed.
Lemma lem7592836 (_97606 : int) : (term270 _97606) = (term271 _97606).
Proof. exact (@lem1982763 (term162 _97606) (real_of_int _97606) term122). Qed.
Lemma lem7592837 (_97606 : int) : (term272 _97606) = (term273 _97606).
Proof. exact (@lem1982713 term122 (real_of_int _97606)). Qed.
Lemma lem7592839 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7592840 : term74 = term148.
Proof. exact (@lem7592839 term11). Qed.
Lemma lem7592842 (x : nat) : (term120 x) = (term121 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7592843 : term122 = term123.
Proof. exact (@lem7592842 term11). Qed.
Lemma lem7592844 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7592845 : term274 = term275.
Proof. exact (MK_COMB (@lem7592844) (@lem7592843)). Qed.
Lemma lem7592846 : term276 = term277.
Proof. exact (MK_COMB (@lem7592845) (@lem7592840)). Qed.
Lemma lem7592847 : term278.
Proof. exact (@lem1981473 term122 term74 term74 term74 term59 term74). Qed.
Lemma lem7592849 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7592850 : term168 = term169.
Proof. exact (@lem7592849 (NUMERAL 0) term11). Qed.
Lemma lem7592851 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7592852 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7592853 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7592852 h1) (fun h1 : term169 = True => @lem7592851)). Qed.
Lemma lem7592854 : term169 = True.
Proof. exact (EQ_MP (@lem7592853) (@lem7592851)). Qed.
Lemma lem7592855 : term168 = True.
Proof. exact (TRANS (@lem7592850) (@lem7592854)). Qed.
Lemma lem7592856 : True = term168.
Proof. exact (SYM (@lem7592855)). Qed.
Lemma lem7592857 : term168.
Proof. exact (EQ_MP (@lem7592856) (@lem0)). Qed.
Lemma lem7592858 : term279.
Proof. exact (@lem7592847 (@lem7592857)). Qed.
Lemma lem7592860 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7592861 : term168 = term169.
Proof. exact (@lem7592860 (NUMERAL 0) term11). Qed.
Lemma lem7592862 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7592863 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7592864 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7592863 h1) (fun h1 : term169 = True => @lem7592862)). Qed.
Lemma lem7592865 : term169 = True.
Proof. exact (EQ_MP (@lem7592864) (@lem7592862)). Qed.
Lemma lem7592866 : term168 = True.
Proof. exact (TRANS (@lem7592861) (@lem7592865)). Qed.
Lemma lem7592867 : True = term168.
Proof. exact (SYM (@lem7592866)). Qed.
Lemma lem7592868 : term168.
Proof. exact (EQ_MP (@lem7592867) (@lem0)). Qed.
Lemma lem7592869 : term280.
Proof. exact (@lem7592858 (@lem7592868)). Qed.
Lemma lem7592871 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7592872 : term168 = term169.
Proof. exact (@lem7592871 (NUMERAL 0) term11). Qed.
Lemma lem7592873 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7592874 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7592875 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7592874 h1) (fun h1 : term169 = True => @lem7592873)). Qed.
Lemma lem7592876 : term169 = True.
Proof. exact (EQ_MP (@lem7592875) (@lem7592873)). Qed.
Lemma lem7592877 : term168 = True.
Proof. exact (TRANS (@lem7592872) (@lem7592876)). Qed.
Lemma lem7592878 : True = term168.
Proof. exact (SYM (@lem7592877)). Qed.
Lemma lem7592879 : term168.
Proof. exact (EQ_MP (@lem7592878) (@lem0)). Qed.
Lemma lem7592880 : term281.
Proof. exact (@lem7592869 (@lem7592879)). Qed.
Lemma lem7592882 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7592883 : term131 = term132.
Proof. exact (@lem7592882 term11 term11). Qed.
Lemma lem7592884 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7592885 : term134 = term11.
Proof. exact (EQ_MP (@lem7592884) (@lem940073)). Qed.
Lemma lem7592886 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7592887 : term132 = term74.
Proof. exact (MK_COMB (@lem7592886) (@lem7592885)). Qed.
Lemma lem7592888 : term131 = term74.
Proof. exact (TRANS (@lem7592883) (@lem7592887)). Qed.
Lemma lem7592890 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7592891 : term149 = term154.
Proof. exact (@lem7592890 term11 term11). Qed.
Lemma lem7592892 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7592893 : term134 = term11.
Proof. exact (EQ_MP (@lem7592892) (@lem940073)). Qed.
Lemma lem7592894 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7592895 : term132 = term74.
Proof. exact (MK_COMB (@lem7592894) (@lem7592893)). Qed.
Lemma lem7592896 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7592897 : term154 = term122.
Proof. exact (MK_COMB (@lem7592896) (@lem7592895)). Qed.
Lemma lem7592898 : term149 = term122.
Proof. exact (TRANS (@lem7592891) (@lem7592897)). Qed.
Lemma lem7592899 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7592900 : term282 = term274.
Proof. exact (MK_COMB (@lem7592899) (@lem7592898)). Qed.
Lemma lem7592901 : term283 = term276.
Proof. exact (MK_COMB (@lem7592900) (@lem7592888)). Qed.
Lemma lem7592903 (m : nat) : (term284 m) = term59.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7592904 : term276 = term59.
Proof. exact (@lem7592903 term11). Qed.
Lemma lem7592905 : term283 = term59.
Proof. exact (TRANS (@lem7592901) (@lem7592904)). Qed.
Lemma lem7592906 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7592907 : term285 = term178.
Proof. exact (MK_COMB (@lem7592906) (@lem7592905)). Qed.
Lemma lem7592908 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem7592909 : term286 = term180.
Proof. exact (MK_COMB (@lem7592907) (@lem7592908)). Qed.
Lemma lem7592911 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7592912 : term180 = term59.
Proof. exact (@lem7592911 term11). Qed.
Lemma lem7592913 : term286 = term59.
Proof. exact (TRANS (@lem7592909) (@lem7592912)). Qed.
Lemma lem7592915 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7592916 : term131 = term132.
Proof. exact (@lem7592915 term11 term11). Qed.
Lemma lem7592917 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7592918 : term134 = term11.
Proof. exact (EQ_MP (@lem7592917) (@lem940073)). Qed.
Lemma lem7592919 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7592920 : term132 = term74.
Proof. exact (MK_COMB (@lem7592919) (@lem7592918)). Qed.
Lemma lem7592921 : term131 = term74.
Proof. exact (TRANS (@lem7592916) (@lem7592920)). Qed.
Lemma lem7592922 : term178 = term178.
Proof. exact (eq_refl term178). Qed.
Lemma lem7592923 : term182 = term180.
Proof. exact (MK_COMB (@lem7592922) (@lem7592921)). Qed.
Lemma lem7592925 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7592926 : term180 = term59.
Proof. exact (@lem7592925 term11). Qed.
Lemma lem7592927 : term182 = term59.
Proof. exact (TRANS (@lem7592923) (@lem7592926)). Qed.
Lemma lem7592928 : term59 = term182.
Proof. exact (SYM (@lem7592927)). Qed.
Lemma lem7592929 : term286 = term182.
Proof. exact (TRANS (@lem7592913) (@lem7592928)). Qed.
Lemma lem7592930 : term277 = term119.
Proof. exact (@lem7592880 (@lem7592929)). Qed.
Lemma lem7592931 : term276 = term119.
Proof. exact (TRANS (@lem7592846) (@lem7592930)). Qed.
Lemma lem7592933 (x : real) : (term138 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7592934 : term119 = term59.
Proof. exact (@lem7592933 term59). Qed.
Lemma lem7592935 : term276 = term59.
Proof. exact (TRANS (@lem7592931) (@lem7592934)). Qed.
Lemma lem7592936 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7592937 : term287 = term178.
Proof. exact (MK_COMB (@lem7592936) (@lem7592935)). Qed.
Lemma lem7592938 (_97606 : int) : (real_of_int _97606) = (real_of_int _97606).
Proof. exact (eq_refl (real_of_int _97606)). Qed.
Lemma lem7592939 (_97606 : int) : (term273 _97606) = (term288 _97606).
Proof. exact (MK_COMB (@lem7592937) (@lem7592938 _97606)). Qed.
Lemma lem7592940 (_97606 : int) : (term272 _97606) = (term288 _97606).
Proof. exact (TRANS (@lem7592837 _97606) (@lem7592939 _97606)). Qed.
Lemma lem7592941 (_97606 : int) : (term288 _97606) = term59.
Proof. exact (@lem1982719 (real_of_int _97606)). Qed.
Lemma lem7592942 (_97606 : int) : (term272 _97606) = term59.
Proof. exact (TRANS (@lem7592940 _97606) (@lem7592941 _97606)). Qed.
Lemma lem7592943 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7592944 (_97606 : int) : (term289 _97606) = term101.
Proof. exact (MK_COMB (@lem7592943) (@lem7592942 _97606)). Qed.
Lemma lem7592945 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem7592946 (_97606 : int) : (term271 _97606) = term290.
Proof. exact (MK_COMB (@lem7592944 _97606) (@lem7592945)). Qed.
Lemma lem7592947 (_97606 : int) : (term270 _97606) = term290.
Proof. exact (TRANS (@lem7592836 _97606) (@lem7592946 _97606)). Qed.
Lemma lem7592948 : term290 = term122.
Proof. exact (@lem1982721 term122). Qed.
Lemma lem7592949 (_97606 : int) : (term270 _97606) = term122.
Proof. exact (TRANS (@lem7592947 _97606) (@lem7592948)). Qed.
Lemma lem7592950 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7592951 (_97606 : int) : (term291 _97606) = term292.
Proof. exact (MK_COMB (@lem7592950) (@lem7592949 _97606)). Qed.
Lemma lem7592952 : term59 = term59.
Proof. exact (eq_refl term59). Qed.
Lemma lem7592953 (_97606 : int) : (term269 _97606) = term293.
Proof. exact (MK_COMB (@lem7592951 _97606) (@lem7592952)). Qed.
Lemma lem7592954 (_97606 : int) (h1 : term247 _97606) : term293.
Proof. exact (EQ_MP (@lem7592953 _97606) (@lem7592835 _97606 h1)). Qed.
Lemma lem7592956 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7592957 : term293 = term294.
Proof. exact (@lem7592956 term59 term122). Qed.
Lemma lem7592959 (x : nat) : (term120 x) = (term121 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7592960 : term122 = term123.
Proof. exact (@lem7592959 term11). Qed.
Lemma lem7592962 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7592963 : term59 = term119.
Proof. exact (@lem7592962 (NUMERAL 0)). Qed.
Lemma lem7592964 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7592965 : term61 = term295.
Proof. exact (MK_COMB (@lem7592964) (@lem7592963)). Qed.
Lemma lem7592966 : term294 = term296.
Proof. exact (MK_COMB (@lem7592965) (@lem7592960)). Qed.
Lemma lem7592967 : term297.
Proof. exact (@lem1980026 term59 term74 term122 term74). Qed.
Lemma lem7592969 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7592970 : term168 = term169.
Proof. exact (@lem7592969 (NUMERAL 0) term11). Qed.
Lemma lem7592971 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7592972 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7592973 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7592972 h1) (fun h1 : term169 = True => @lem7592971)). Qed.
Lemma lem7592974 : term169 = True.
Proof. exact (EQ_MP (@lem7592973) (@lem7592971)). Qed.
Lemma lem7592975 : term168 = True.
Proof. exact (TRANS (@lem7592970) (@lem7592974)). Qed.
Lemma lem7592976 : True = term168.
Proof. exact (SYM (@lem7592975)). Qed.
Lemma lem7592977 : term168.
Proof. exact (EQ_MP (@lem7592976) (@lem0)). Qed.
Lemma lem7592978 : term298.
Proof. exact (@lem7592967 (@lem7592977)). Qed.
Lemma lem7592980 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7592981 : term168 = term169.
Proof. exact (@lem7592980 (NUMERAL 0) term11). Qed.
Lemma lem7592982 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7592983 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7592984 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7592983 h1) (fun h1 : term169 = True => @lem7592982)). Qed.
Lemma lem7592985 : term169 = True.
Proof. exact (EQ_MP (@lem7592984) (@lem7592982)). Qed.
Lemma lem7592986 : term168 = True.
Proof. exact (TRANS (@lem7592981) (@lem7592985)). Qed.
Lemma lem7592987 : True = term168.
Proof. exact (SYM (@lem7592986)). Qed.
Lemma lem7592988 : term168.
Proof. exact (EQ_MP (@lem7592987) (@lem0)). Qed.
Lemma lem7592989 : term296 = term299.
Proof. exact (@lem7592978 (@lem7592988)). Qed.
Lemma lem7592991 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7592992 : term149 = term154.
Proof. exact (@lem7592991 term11 term11). Qed.
Lemma lem7592993 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7592994 : term134 = term11.
Proof. exact (EQ_MP (@lem7592993) (@lem940073)). Qed.
Lemma lem7592995 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7592996 : term132 = term74.
Proof. exact (MK_COMB (@lem7592995) (@lem7592994)). Qed.
Lemma lem7592997 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7592998 : term154 = term122.
Proof. exact (MK_COMB (@lem7592997) (@lem7592996)). Qed.
Lemma lem7592999 : term149 = term122.
Proof. exact (TRANS (@lem7592992) (@lem7592998)). Qed.
Lemma lem7593001 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7593002 : term180 = term59.
Proof. exact (@lem7593001 term11). Qed.
Lemma lem7593003 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7593004 : term300 = term61.
Proof. exact (MK_COMB (@lem7593003) (@lem7593002)). Qed.
Lemma lem7593005 : term299 = term294.
Proof. exact (MK_COMB (@lem7593004) (@lem7592999)). Qed.
Lemma lem7593007 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7593008 : term294 = term303.
Proof. exact (@lem7593007 (NUMERAL 0) term11). Qed.
Lemma lem7593009 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593010 (h1 : term170 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7593011 : (term170 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593010 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem7593009)). Qed.
Lemma lem7593012 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7593011) (@lem7593009)). Qed.
Lemma lem7593013 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7593014 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7593015 : term304 = (and True).
Proof. exact (MK_COMB (@lem7593014) (@lem7593013)). Qed.
Lemma lem7593016 : term303 = (True /\ False).
Proof. exact (MK_COMB (@lem7593015) (@lem7593012)). Qed.
Lemma lem7593018 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7593019 : term303 = False.
Proof. exact (TRANS (@lem7593016) (@lem7593018)). Qed.
Lemma lem7593020 : term294 = False.
Proof. exact (TRANS (@lem7593008) (@lem7593019)). Qed.
Lemma lem7593021 : term299 = False.
Proof. exact (TRANS (@lem7593005) (@lem7593020)). Qed.
Lemma lem7593022 : term296 = False.
Proof. exact (TRANS (@lem7592989) (@lem7593021)). Qed.
Lemma lem7593023 : term294 = False.
Proof. exact (TRANS (@lem7592966) (@lem7593022)). Qed.
Lemma lem7593024 : term293 = False.
Proof. exact (TRANS (@lem7592957) (@lem7593023)). Qed.
Lemma lem7593025 (_97606 : int) (h1 : term247 _97606) : False.
Proof. exact (EQ_MP (@lem7593024) (@lem7592954 _97606 h1)). Qed.
Lemma lem7593026 (_97606 : int) (h1 : term305 _97606) : term305 _97606.
Proof. exact (h1). Qed.
Lemma lem7593027 (_97606 : int) (h1 : term305 _97606) : term236 _97606.
Proof. exact (proj2 (@lem7593026 _97606 h1)). Qed.
Lemma lem7593029 (_97606 : int) (h1 : term305 _97606) : term196 _97606.
Proof. exact (proj2 (@lem7593027 _97606 h1)). Qed.
Lemma lem7593030 (_97606 : int) (h1 : term305 _97606) : (real_of_int _97606) = term59.
Proof. exact (proj1 (@lem7593027 _97606 h1)). Qed.
Lemma lem7593032 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7593033 : term248 = term168.
Proof. exact (@lem7593032 term59 term74). Qed.
Lemma lem7593035 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7593036 : term74 = term148.
Proof. exact (@lem7593035 term11). Qed.
Lemma lem7593038 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7593039 : term59 = term119.
Proof. exact (@lem7593038 (NUMERAL 0)). Qed.
Lemma lem7593040 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7593041 : term249 = term250.
Proof. exact (MK_COMB (@lem7593040) (@lem7593039)). Qed.
Lemma lem7593042 : term168 = term251.
Proof. exact (MK_COMB (@lem7593041) (@lem7593036)). Qed.
Lemma lem7593043 : term252.
Proof. exact (@lem1980255 term59 term74 term74 term74). Qed.
Lemma lem7593045 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593046 : term168 = term169.
Proof. exact (@lem7593045 (NUMERAL 0) term11). Qed.
Lemma lem7593047 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593048 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593049 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593048 h1) (fun h1 : term169 = True => @lem7593047)). Qed.
Lemma lem7593050 : term169 = True.
Proof. exact (EQ_MP (@lem7593049) (@lem7593047)). Qed.
Lemma lem7593051 : term168 = True.
Proof. exact (TRANS (@lem7593046) (@lem7593050)). Qed.
Lemma lem7593052 : True = term168.
Proof. exact (SYM (@lem7593051)). Qed.
Lemma lem7593053 : term168.
Proof. exact (EQ_MP (@lem7593052) (@lem0)). Qed.
Lemma lem7593054 : term253.
Proof. exact (@lem7593043 (@lem7593053)). Qed.
Lemma lem7593056 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593057 : term168 = term169.
Proof. exact (@lem7593056 (NUMERAL 0) term11). Qed.
Lemma lem7593058 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593059 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593060 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593059 h1) (fun h1 : term169 = True => @lem7593058)). Qed.
Lemma lem7593061 : term169 = True.
Proof. exact (EQ_MP (@lem7593060) (@lem7593058)). Qed.
Lemma lem7593062 : term168 = True.
Proof. exact (TRANS (@lem7593057) (@lem7593061)). Qed.
Lemma lem7593063 : True = term168.
Proof. exact (SYM (@lem7593062)). Qed.
Lemma lem7593064 : term168.
Proof. exact (EQ_MP (@lem7593063) (@lem0)). Qed.
Lemma lem7593065 : term251 = term254.
Proof. exact (@lem7593054 (@lem7593064)). Qed.
Lemma lem7593067 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7593068 : term131 = term132.
Proof. exact (@lem7593067 term11 term11). Qed.
Lemma lem7593069 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7593070 : term134 = term11.
Proof. exact (EQ_MP (@lem7593069) (@lem940073)). Qed.
Lemma lem7593071 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7593072 : term132 = term74.
Proof. exact (MK_COMB (@lem7593071) (@lem7593070)). Qed.
Lemma lem7593073 : term131 = term74.
Proof. exact (TRANS (@lem7593068) (@lem7593072)). Qed.
Lemma lem7593075 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7593076 : term180 = term59.
Proof. exact (@lem7593075 term11). Qed.
Lemma lem7593077 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7593078 : term255 = term249.
Proof. exact (MK_COMB (@lem7593077) (@lem7593076)). Qed.
Lemma lem7593079 : term254 = term168.
Proof. exact (MK_COMB (@lem7593078) (@lem7593073)). Qed.
Lemma lem7593081 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593082 : term168 = term169.
Proof. exact (@lem7593081 (NUMERAL 0) term11). Qed.
Lemma lem7593083 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593084 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593085 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593084 h1) (fun h1 : term169 = True => @lem7593083)). Qed.
Lemma lem7593086 : term169 = True.
Proof. exact (EQ_MP (@lem7593085) (@lem7593083)). Qed.
Lemma lem7593087 : term168 = True.
Proof. exact (TRANS (@lem7593082) (@lem7593086)). Qed.
Lemma lem7593088 : term254 = True.
Proof. exact (TRANS (@lem7593079) (@lem7593087)). Qed.
Lemma lem7593089 : term251 = True.
Proof. exact (TRANS (@lem7593065) (@lem7593088)). Qed.
Lemma lem7593090 : term168 = True.
Proof. exact (TRANS (@lem7593042) (@lem7593089)). Qed.
Lemma lem7593091 : term248 = True.
Proof. exact (TRANS (@lem7593033) (@lem7593090)). Qed.
Lemma lem7593092 : True = term248.
Proof. exact (SYM (@lem7593091)). Qed.
Lemma lem7593093 : term248.
Proof. exact (EQ_MP (@lem7593092) (@lem0)). Qed.
Lemma lem7593094 (_97606 : int) (h1 : term305 _97606) : term256 _97606.
Proof. exact (conj (@lem7593093) (@lem7593029 _97606 h1)). Qed.
Lemma lem7593096 (x : real) (y : real) : term257 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7593097 (_97606 : int) : term258 _97606.
Proof. exact (@lem7593096 term74 (term193 _97606)). Qed.
Lemma lem7593098 (_97606 : int) (h1 : term305 _97606) : term259 _97606.
Proof. exact (@lem7593097 _97606 (@lem7593094 _97606 h1)). Qed.
Lemma lem7593099 (_97606 : int) : (term260 _97606) = (term193 _97606).
Proof. exact (@lem1982733 (term193 _97606)). Qed.
Lemma lem7593100 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7593101 (_97606 : int) : (term261 _97606) = (term195 _97606).
Proof. exact (MK_COMB (@lem7593100) (@lem7593099 _97606)). Qed.
Lemma lem7593102 : term59 = term59.
Proof. exact (eq_refl term59). Qed.
Lemma lem7593103 (_97606 : int) : (term259 _97606) = (term196 _97606).
Proof. exact (MK_COMB (@lem7593101 _97606) (@lem7593102)). Qed.
Lemma lem7593104 (_97606 : int) (h1 : term305 _97606) : term196 _97606.
Proof. exact (EQ_MP (@lem7593103 _97606) (@lem7593098 _97606 h1)). Qed.
Lemma lem7593106 (y : real) : term306 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem7593107 (_97606 : int) : term307 _97606.
Proof. exact (@lem7593106 (real_of_int _97606)). Qed.
Lemma lem7593108 (_97606 : int) (h1 : term305 _97606) : term308 _97606.
Proof. exact (@lem7593107 _97606 (@lem7593030 _97606 h1)). Qed.
Lemma lem7593109 (_97606 : int) (h1 : term305 _97606) : term309 _97606.
Proof. exact (@lem7593108 _97606 h1 term122). Qed.
Lemma lem7593110 (_97606 : int) : (term309 _97606) = ((term162 _97606) = term59).
Proof. exact (eq_refl (term309 _97606)). Qed.
Lemma lem7593117 (_97606 : int) (h1 : term305 _97606) : (term162 _97606) = term59.
Proof. exact (EQ_MP (@lem7593110 _97606) (@lem7593109 _97606 h1)). Qed.
Lemma lem7593118 (_97606 : int) (h1 : term305 _97606) : term310 _97606.
Proof. exact (conj (@lem7593117 _97606 h1) (@lem7593104 _97606 h1)). Qed.
Lemma lem7593120 (x : real) (y : real) : term311 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem7593121 (_97606 : int) : term312 _97606.
Proof. exact (@lem7593120 (term162 _97606) (term193 _97606)). Qed.
Lemma lem7593122 (_97606 : int) (h1 : term305 _97606) : term269 _97606.
Proof. exact (@lem7593121 _97606 (@lem7593118 _97606 h1)). Qed.
Lemma lem7593123 (_97606 : int) : (term270 _97606) = (term271 _97606).
Proof. exact (@lem1982763 (term162 _97606) (real_of_int _97606) term122). Qed.
Lemma lem7593124 (_97606 : int) : (term272 _97606) = (term273 _97606).
Proof. exact (@lem1982713 term122 (real_of_int _97606)). Qed.
Lemma lem7593126 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7593127 : term74 = term148.
Proof. exact (@lem7593126 term11). Qed.
Lemma lem7593129 (x : nat) : (term120 x) = (term121 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7593130 : term122 = term123.
Proof. exact (@lem7593129 term11). Qed.
Lemma lem7593131 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7593132 : term274 = term275.
Proof. exact (MK_COMB (@lem7593131) (@lem7593130)). Qed.
Lemma lem7593133 : term276 = term277.
Proof. exact (MK_COMB (@lem7593132) (@lem7593127)). Qed.
Lemma lem7593134 : term278.
Proof. exact (@lem1981473 term122 term74 term74 term74 term59 term74). Qed.
Lemma lem7593136 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593137 : term168 = term169.
Proof. exact (@lem7593136 (NUMERAL 0) term11). Qed.
Lemma lem7593138 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593139 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593140 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593139 h1) (fun h1 : term169 = True => @lem7593138)). Qed.
Lemma lem7593141 : term169 = True.
Proof. exact (EQ_MP (@lem7593140) (@lem7593138)). Qed.
Lemma lem7593142 : term168 = True.
Proof. exact (TRANS (@lem7593137) (@lem7593141)). Qed.
Lemma lem7593143 : True = term168.
Proof. exact (SYM (@lem7593142)). Qed.
Lemma lem7593144 : term168.
Proof. exact (EQ_MP (@lem7593143) (@lem0)). Qed.
Lemma lem7593145 : term279.
Proof. exact (@lem7593134 (@lem7593144)). Qed.
Lemma lem7593147 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593148 : term168 = term169.
Proof. exact (@lem7593147 (NUMERAL 0) term11). Qed.
Lemma lem7593149 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593150 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593151 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593150 h1) (fun h1 : term169 = True => @lem7593149)). Qed.
Lemma lem7593152 : term169 = True.
Proof. exact (EQ_MP (@lem7593151) (@lem7593149)). Qed.
Lemma lem7593153 : term168 = True.
Proof. exact (TRANS (@lem7593148) (@lem7593152)). Qed.
Lemma lem7593154 : True = term168.
Proof. exact (SYM (@lem7593153)). Qed.
Lemma lem7593155 : term168.
Proof. exact (EQ_MP (@lem7593154) (@lem0)). Qed.
Lemma lem7593156 : term280.
Proof. exact (@lem7593145 (@lem7593155)). Qed.
Lemma lem7593158 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593159 : term168 = term169.
Proof. exact (@lem7593158 (NUMERAL 0) term11). Qed.
Lemma lem7593160 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593161 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593162 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593161 h1) (fun h1 : term169 = True => @lem7593160)). Qed.
Lemma lem7593163 : term169 = True.
Proof. exact (EQ_MP (@lem7593162) (@lem7593160)). Qed.
Lemma lem7593164 : term168 = True.
Proof. exact (TRANS (@lem7593159) (@lem7593163)). Qed.
Lemma lem7593165 : True = term168.
Proof. exact (SYM (@lem7593164)). Qed.
Lemma lem7593166 : term168.
Proof. exact (EQ_MP (@lem7593165) (@lem0)). Qed.
Lemma lem7593167 : term281.
Proof. exact (@lem7593156 (@lem7593166)). Qed.
Lemma lem7593169 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7593170 : term131 = term132.
Proof. exact (@lem7593169 term11 term11). Qed.
Lemma lem7593171 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7593172 : term134 = term11.
Proof. exact (EQ_MP (@lem7593171) (@lem940073)). Qed.
Lemma lem7593173 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7593174 : term132 = term74.
Proof. exact (MK_COMB (@lem7593173) (@lem7593172)). Qed.
Lemma lem7593175 : term131 = term74.
Proof. exact (TRANS (@lem7593170) (@lem7593174)). Qed.
Lemma lem7593177 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7593178 : term149 = term154.
Proof. exact (@lem7593177 term11 term11). Qed.
Lemma lem7593179 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7593180 : term134 = term11.
Proof. exact (EQ_MP (@lem7593179) (@lem940073)). Qed.
Lemma lem7593181 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7593182 : term132 = term74.
Proof. exact (MK_COMB (@lem7593181) (@lem7593180)). Qed.
Lemma lem7593183 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7593184 : term154 = term122.
Proof. exact (MK_COMB (@lem7593183) (@lem7593182)). Qed.
Lemma lem7593185 : term149 = term122.
Proof. exact (TRANS (@lem7593178) (@lem7593184)). Qed.
Lemma lem7593186 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7593187 : term282 = term274.
Proof. exact (MK_COMB (@lem7593186) (@lem7593185)). Qed.
Lemma lem7593188 : term283 = term276.
Proof. exact (MK_COMB (@lem7593187) (@lem7593175)). Qed.
Lemma lem7593190 (m : nat) : (term284 m) = term59.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7593191 : term276 = term59.
Proof. exact (@lem7593190 term11). Qed.
Lemma lem7593192 : term283 = term59.
Proof. exact (TRANS (@lem7593188) (@lem7593191)). Qed.
Lemma lem7593193 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7593194 : term285 = term178.
Proof. exact (MK_COMB (@lem7593193) (@lem7593192)). Qed.
Lemma lem7593195 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem7593196 : term286 = term180.
Proof. exact (MK_COMB (@lem7593194) (@lem7593195)). Qed.
Lemma lem7593198 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7593199 : term180 = term59.
Proof. exact (@lem7593198 term11). Qed.
Lemma lem7593200 : term286 = term59.
Proof. exact (TRANS (@lem7593196) (@lem7593199)). Qed.
Lemma lem7593202 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7593203 : term131 = term132.
Proof. exact (@lem7593202 term11 term11). Qed.
Lemma lem7593204 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7593205 : term134 = term11.
Proof. exact (EQ_MP (@lem7593204) (@lem940073)). Qed.
Lemma lem7593206 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7593207 : term132 = term74.
Proof. exact (MK_COMB (@lem7593206) (@lem7593205)). Qed.
Lemma lem7593208 : term131 = term74.
Proof. exact (TRANS (@lem7593203) (@lem7593207)). Qed.
Lemma lem7593209 : term178 = term178.
Proof. exact (eq_refl term178). Qed.
Lemma lem7593210 : term182 = term180.
Proof. exact (MK_COMB (@lem7593209) (@lem7593208)). Qed.
Lemma lem7593212 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7593213 : term180 = term59.
Proof. exact (@lem7593212 term11). Qed.
Lemma lem7593214 : term182 = term59.
Proof. exact (TRANS (@lem7593210) (@lem7593213)). Qed.
Lemma lem7593215 : term59 = term182.
Proof. exact (SYM (@lem7593214)). Qed.
Lemma lem7593216 : term286 = term182.
Proof. exact (TRANS (@lem7593200) (@lem7593215)). Qed.
Lemma lem7593217 : term277 = term119.
Proof. exact (@lem7593167 (@lem7593216)). Qed.
Lemma lem7593218 : term276 = term119.
Proof. exact (TRANS (@lem7593133) (@lem7593217)). Qed.
Lemma lem7593220 (x : real) : (term138 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7593221 : term119 = term59.
Proof. exact (@lem7593220 term59). Qed.
Lemma lem7593222 : term276 = term59.
Proof. exact (TRANS (@lem7593218) (@lem7593221)). Qed.
Lemma lem7593223 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7593224 : term287 = term178.
Proof. exact (MK_COMB (@lem7593223) (@lem7593222)). Qed.
Lemma lem7593225 (_97606 : int) : (real_of_int _97606) = (real_of_int _97606).
Proof. exact (eq_refl (real_of_int _97606)). Qed.
Lemma lem7593226 (_97606 : int) : (term273 _97606) = (term288 _97606).
Proof. exact (MK_COMB (@lem7593224) (@lem7593225 _97606)). Qed.
Lemma lem7593227 (_97606 : int) : (term272 _97606) = (term288 _97606).
Proof. exact (TRANS (@lem7593124 _97606) (@lem7593226 _97606)). Qed.
Lemma lem7593228 (_97606 : int) : (term288 _97606) = term59.
Proof. exact (@lem1982719 (real_of_int _97606)). Qed.
Lemma lem7593229 (_97606 : int) : (term272 _97606) = term59.
Proof. exact (TRANS (@lem7593227 _97606) (@lem7593228 _97606)). Qed.
Lemma lem7593230 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7593231 (_97606 : int) : (term289 _97606) = term101.
Proof. exact (MK_COMB (@lem7593230) (@lem7593229 _97606)). Qed.
Lemma lem7593232 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem7593233 (_97606 : int) : (term271 _97606) = term290.
Proof. exact (MK_COMB (@lem7593231 _97606) (@lem7593232)). Qed.
Lemma lem7593234 (_97606 : int) : (term270 _97606) = term290.
Proof. exact (TRANS (@lem7593123 _97606) (@lem7593233 _97606)). Qed.
Lemma lem7593235 : term290 = term122.
Proof. exact (@lem1982721 term122). Qed.
Lemma lem7593236 (_97606 : int) : (term270 _97606) = term122.
Proof. exact (TRANS (@lem7593234 _97606) (@lem7593235)). Qed.
Lemma lem7593237 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7593238 (_97606 : int) : (term291 _97606) = term292.
Proof. exact (MK_COMB (@lem7593237) (@lem7593236 _97606)). Qed.
Lemma lem7593239 : term59 = term59.
Proof. exact (eq_refl term59). Qed.
Lemma lem7593240 (_97606 : int) : (term269 _97606) = term293.
Proof. exact (MK_COMB (@lem7593238 _97606) (@lem7593239)). Qed.
Lemma lem7593241 (_97606 : int) (h1 : term305 _97606) : term293.
Proof. exact (EQ_MP (@lem7593240 _97606) (@lem7593122 _97606 h1)). Qed.
Lemma lem7593243 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7593244 : term293 = term294.
Proof. exact (@lem7593243 term59 term122). Qed.
Lemma lem7593246 (x : nat) : (term120 x) = (term121 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7593247 : term122 = term123.
Proof. exact (@lem7593246 term11). Qed.
Lemma lem7593249 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7593250 : term59 = term119.
Proof. exact (@lem7593249 (NUMERAL 0)). Qed.
Lemma lem7593251 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7593252 : term61 = term295.
Proof. exact (MK_COMB (@lem7593251) (@lem7593250)). Qed.
Lemma lem7593253 : term294 = term296.
Proof. exact (MK_COMB (@lem7593252) (@lem7593247)). Qed.
Lemma lem7593254 : term297.
Proof. exact (@lem1980026 term59 term74 term122 term74). Qed.
Lemma lem7593256 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593257 : term168 = term169.
Proof. exact (@lem7593256 (NUMERAL 0) term11). Qed.
Lemma lem7593258 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593259 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593260 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593259 h1) (fun h1 : term169 = True => @lem7593258)). Qed.
Lemma lem7593261 : term169 = True.
Proof. exact (EQ_MP (@lem7593260) (@lem7593258)). Qed.
Lemma lem7593262 : term168 = True.
Proof. exact (TRANS (@lem7593257) (@lem7593261)). Qed.
Lemma lem7593263 : True = term168.
Proof. exact (SYM (@lem7593262)). Qed.
Lemma lem7593264 : term168.
Proof. exact (EQ_MP (@lem7593263) (@lem0)). Qed.
Lemma lem7593265 : term298.
Proof. exact (@lem7593254 (@lem7593264)). Qed.
Lemma lem7593267 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593268 : term168 = term169.
Proof. exact (@lem7593267 (NUMERAL 0) term11). Qed.
Lemma lem7593269 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593270 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593271 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593270 h1) (fun h1 : term169 = True => @lem7593269)). Qed.
Lemma lem7593272 : term169 = True.
Proof. exact (EQ_MP (@lem7593271) (@lem7593269)). Qed.
Lemma lem7593273 : term168 = True.
Proof. exact (TRANS (@lem7593268) (@lem7593272)). Qed.
Lemma lem7593274 : True = term168.
Proof. exact (SYM (@lem7593273)). Qed.
Lemma lem7593275 : term168.
Proof. exact (EQ_MP (@lem7593274) (@lem0)). Qed.
Lemma lem7593276 : term296 = term299.
Proof. exact (@lem7593265 (@lem7593275)). Qed.
Lemma lem7593278 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7593279 : term149 = term154.
Proof. exact (@lem7593278 term11 term11). Qed.
Lemma lem7593280 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7593281 : term134 = term11.
Proof. exact (EQ_MP (@lem7593280) (@lem940073)). Qed.
Lemma lem7593282 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7593283 : term132 = term74.
Proof. exact (MK_COMB (@lem7593282) (@lem7593281)). Qed.
Lemma lem7593284 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7593285 : term154 = term122.
Proof. exact (MK_COMB (@lem7593284) (@lem7593283)). Qed.
Lemma lem7593286 : term149 = term122.
Proof. exact (TRANS (@lem7593279) (@lem7593285)). Qed.
Lemma lem7593288 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7593289 : term180 = term59.
Proof. exact (@lem7593288 term11). Qed.
Lemma lem7593290 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7593291 : term300 = term61.
Proof. exact (MK_COMB (@lem7593290) (@lem7593289)). Qed.
Lemma lem7593292 : term299 = term294.
Proof. exact (MK_COMB (@lem7593291) (@lem7593286)). Qed.
Lemma lem7593294 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7593295 : term294 = term303.
Proof. exact (@lem7593294 (NUMERAL 0) term11). Qed.
Lemma lem7593296 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593297 (h1 : term170 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7593298 : (term170 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593297 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem7593296)). Qed.
Lemma lem7593299 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7593298) (@lem7593296)). Qed.
Lemma lem7593300 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7593301 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7593302 : term304 = (and True).
Proof. exact (MK_COMB (@lem7593301) (@lem7593300)). Qed.
Lemma lem7593303 : term303 = (True /\ False).
Proof. exact (MK_COMB (@lem7593302) (@lem7593299)). Qed.
Lemma lem7593305 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7593306 : term303 = False.
Proof. exact (TRANS (@lem7593303) (@lem7593305)). Qed.
Lemma lem7593307 : term294 = False.
Proof. exact (TRANS (@lem7593295) (@lem7593306)). Qed.
Lemma lem7593308 : term299 = False.
Proof. exact (TRANS (@lem7593292) (@lem7593307)). Qed.
Lemma lem7593309 : term296 = False.
Proof. exact (TRANS (@lem7593276) (@lem7593308)). Qed.
Lemma lem7593310 : term294 = False.
Proof. exact (TRANS (@lem7593253) (@lem7593309)). Qed.
Lemma lem7593311 : term293 = False.
Proof. exact (TRANS (@lem7593244) (@lem7593310)). Qed.
Lemma lem7593312 (_97606 : int) (h1 : term305 _97606) : False.
Proof. exact (EQ_MP (@lem7593311) (@lem7593241 _97606 h1)). Qed.
Lemma lem7593313 (_97606 : int) (h1 : term234 _97606) : False.
Proof. exact (or_elim (@lem7592677 _97606 h1) (fun h0 : term247 _97606 => @lem7593025 _97606 h0) (fun h0 : term305 _97606 => @lem7593312 _97606 h0)). Qed.
Lemma lem7593314 (_97606 : int) (h1 : term243 _97606) : term243 _97606.
Proof. exact (h1). Qed.
Lemma lem7593315 (_97606 : int) (h1 : term238 _97606) : term238 _97606.
Proof. exact (h1). Qed.
Lemma lem7593316 (_97606 : int) (h1 : term313 _97606) : term313 _97606.
Proof. exact (h1). Qed.
Lemma lem7593317 (_97606 : int) (h1 : term313 _97606) : term239 _97606.
Proof. exact (proj2 (@lem7593316 _97606 h1)). Qed.
Lemma lem7593318 (_97606 : int) (h1 : term313 _97606) : term142 _97606.
Proof. exact (proj1 (@lem7593316 _97606 h1)). Qed.
Lemma lem7593319 (_97606 : int) (h1 : term313 _97606) : term203 _97606.
Proof. exact (proj2 (@lem7593317 _97606 h1)). Qed.
Lemma lem7593322 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7593323 : term248 = term168.
Proof. exact (@lem7593322 term59 term74). Qed.
Lemma lem7593325 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7593326 : term74 = term148.
Proof. exact (@lem7593325 term11). Qed.
Lemma lem7593328 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7593329 : term59 = term119.
Proof. exact (@lem7593328 (NUMERAL 0)). Qed.
Lemma lem7593330 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7593331 : term249 = term250.
Proof. exact (MK_COMB (@lem7593330) (@lem7593329)). Qed.
Lemma lem7593332 : term168 = term251.
Proof. exact (MK_COMB (@lem7593331) (@lem7593326)). Qed.
Lemma lem7593333 : term252.
Proof. exact (@lem1980255 term59 term74 term74 term74). Qed.
Lemma lem7593335 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593336 : term168 = term169.
Proof. exact (@lem7593335 (NUMERAL 0) term11). Qed.
Lemma lem7593337 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593338 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593339 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593338 h1) (fun h1 : term169 = True => @lem7593337)). Qed.
Lemma lem7593340 : term169 = True.
Proof. exact (EQ_MP (@lem7593339) (@lem7593337)). Qed.
Lemma lem7593341 : term168 = True.
Proof. exact (TRANS (@lem7593336) (@lem7593340)). Qed.
Lemma lem7593342 : True = term168.
Proof. exact (SYM (@lem7593341)). Qed.
Lemma lem7593343 : term168.
Proof. exact (EQ_MP (@lem7593342) (@lem0)). Qed.
Lemma lem7593344 : term253.
Proof. exact (@lem7593333 (@lem7593343)). Qed.
Lemma lem7593346 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593347 : term168 = term169.
Proof. exact (@lem7593346 (NUMERAL 0) term11). Qed.
Lemma lem7593348 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593349 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593350 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593349 h1) (fun h1 : term169 = True => @lem7593348)). Qed.
Lemma lem7593351 : term169 = True.
Proof. exact (EQ_MP (@lem7593350) (@lem7593348)). Qed.
Lemma lem7593352 : term168 = True.
Proof. exact (TRANS (@lem7593347) (@lem7593351)). Qed.
Lemma lem7593353 : True = term168.
Proof. exact (SYM (@lem7593352)). Qed.
Lemma lem7593354 : term168.
Proof. exact (EQ_MP (@lem7593353) (@lem0)). Qed.
Lemma lem7593355 : term251 = term254.
Proof. exact (@lem7593344 (@lem7593354)). Qed.
Lemma lem7593357 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7593358 : term131 = term132.
Proof. exact (@lem7593357 term11 term11). Qed.
Lemma lem7593359 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7593360 : term134 = term11.
Proof. exact (EQ_MP (@lem7593359) (@lem940073)). Qed.
Lemma lem7593361 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7593362 : term132 = term74.
Proof. exact (MK_COMB (@lem7593361) (@lem7593360)). Qed.
Lemma lem7593363 : term131 = term74.
Proof. exact (TRANS (@lem7593358) (@lem7593362)). Qed.
Lemma lem7593365 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7593366 : term180 = term59.
Proof. exact (@lem7593365 term11). Qed.
Lemma lem7593367 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7593368 : term255 = term249.
Proof. exact (MK_COMB (@lem7593367) (@lem7593366)). Qed.
Lemma lem7593369 : term254 = term168.
Proof. exact (MK_COMB (@lem7593368) (@lem7593363)). Qed.
Lemma lem7593371 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593372 : term168 = term169.
Proof. exact (@lem7593371 (NUMERAL 0) term11). Qed.
Lemma lem7593373 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593374 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593375 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593374 h1) (fun h1 : term169 = True => @lem7593373)). Qed.
Lemma lem7593376 : term169 = True.
Proof. exact (EQ_MP (@lem7593375) (@lem7593373)). Qed.
Lemma lem7593377 : term168 = True.
Proof. exact (TRANS (@lem7593372) (@lem7593376)). Qed.
Lemma lem7593378 : term254 = True.
Proof. exact (TRANS (@lem7593369) (@lem7593377)). Qed.
Lemma lem7593379 : term251 = True.
Proof. exact (TRANS (@lem7593355) (@lem7593378)). Qed.
Lemma lem7593380 : term168 = True.
Proof. exact (TRANS (@lem7593332) (@lem7593379)). Qed.
Lemma lem7593381 : term248 = True.
Proof. exact (TRANS (@lem7593323) (@lem7593380)). Qed.
Lemma lem7593382 : True = term248.
Proof. exact (SYM (@lem7593381)). Qed.
Lemma lem7593383 : term248.
Proof. exact (EQ_MP (@lem7593382) (@lem0)). Qed.
Lemma lem7593384 (_97606 : int) (h1 : term313 _97606) : term314 _97606.
Proof. exact (conj (@lem7593383) (@lem7593318 _97606 h1)). Qed.
Lemma lem7593386 (x : real) (y : real) : term257 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7593387 (_97606 : int) : term315 _97606.
Proof. exact (@lem7593386 term74 (real_of_int _97606)). Qed.
Lemma lem7593388 (_97606 : int) (h1 : term313 _97606) : term316 _97606.
Proof. exact (@lem7593387 _97606 (@lem7593384 _97606 h1)). Qed.
Lemma lem7593389 (_97606 : int) : (term317 _97606) = (real_of_int _97606).
Proof. exact (@lem1982733 (real_of_int _97606)). Qed.
Lemma lem7593390 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7593391 (_97606 : int) : (term318 _97606) = (term141 _97606).
Proof. exact (MK_COMB (@lem7593390) (@lem7593389 _97606)). Qed.
Lemma lem7593392 : term59 = term59.
Proof. exact (eq_refl term59). Qed.
Lemma lem7593393 (_97606 : int) : (term316 _97606) = (term142 _97606).
Proof. exact (MK_COMB (@lem7593391 _97606) (@lem7593392)). Qed.
Lemma lem7593394 (_97606 : int) (h1 : term313 _97606) : term142 _97606.
Proof. exact (EQ_MP (@lem7593393 _97606) (@lem7593388 _97606 h1)). Qed.
Lemma lem7593396 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7593397 : term248 = term168.
Proof. exact (@lem7593396 term59 term74). Qed.
Lemma lem7593399 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7593400 : term74 = term148.
Proof. exact (@lem7593399 term11). Qed.
Lemma lem7593402 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7593403 : term59 = term119.
Proof. exact (@lem7593402 (NUMERAL 0)). Qed.
Lemma lem7593404 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7593405 : term249 = term250.
Proof. exact (MK_COMB (@lem7593404) (@lem7593403)). Qed.
Lemma lem7593406 : term168 = term251.
Proof. exact (MK_COMB (@lem7593405) (@lem7593400)). Qed.
Lemma lem7593407 : term252.
Proof. exact (@lem1980255 term59 term74 term74 term74). Qed.
Lemma lem7593409 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593410 : term168 = term169.
Proof. exact (@lem7593409 (NUMERAL 0) term11). Qed.
Lemma lem7593411 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593412 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593413 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593412 h1) (fun h1 : term169 = True => @lem7593411)). Qed.
Lemma lem7593414 : term169 = True.
Proof. exact (EQ_MP (@lem7593413) (@lem7593411)). Qed.
Lemma lem7593415 : term168 = True.
Proof. exact (TRANS (@lem7593410) (@lem7593414)). Qed.
Lemma lem7593416 : True = term168.
Proof. exact (SYM (@lem7593415)). Qed.
Lemma lem7593417 : term168.
Proof. exact (EQ_MP (@lem7593416) (@lem0)). Qed.
Lemma lem7593418 : term253.
Proof. exact (@lem7593407 (@lem7593417)). Qed.
Lemma lem7593420 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593421 : term168 = term169.
Proof. exact (@lem7593420 (NUMERAL 0) term11). Qed.
Lemma lem7593422 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593423 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593424 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593423 h1) (fun h1 : term169 = True => @lem7593422)). Qed.
Lemma lem7593425 : term169 = True.
Proof. exact (EQ_MP (@lem7593424) (@lem7593422)). Qed.
Lemma lem7593426 : term168 = True.
Proof. exact (TRANS (@lem7593421) (@lem7593425)). Qed.
Lemma lem7593427 : True = term168.
Proof. exact (SYM (@lem7593426)). Qed.
Lemma lem7593428 : term168.
Proof. exact (EQ_MP (@lem7593427) (@lem0)). Qed.
Lemma lem7593429 : term251 = term254.
Proof. exact (@lem7593418 (@lem7593428)). Qed.
Lemma lem7593431 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7593432 : term131 = term132.
Proof. exact (@lem7593431 term11 term11). Qed.
Lemma lem7593433 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7593434 : term134 = term11.
Proof. exact (EQ_MP (@lem7593433) (@lem940073)). Qed.
Lemma lem7593435 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7593436 : term132 = term74.
Proof. exact (MK_COMB (@lem7593435) (@lem7593434)). Qed.
Lemma lem7593437 : term131 = term74.
Proof. exact (TRANS (@lem7593432) (@lem7593436)). Qed.
Lemma lem7593439 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7593440 : term180 = term59.
Proof. exact (@lem7593439 term11). Qed.
Lemma lem7593441 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7593442 : term255 = term249.
Proof. exact (MK_COMB (@lem7593441) (@lem7593440)). Qed.
Lemma lem7593443 : term254 = term168.
Proof. exact (MK_COMB (@lem7593442) (@lem7593437)). Qed.
Lemma lem7593445 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593446 : term168 = term169.
Proof. exact (@lem7593445 (NUMERAL 0) term11). Qed.
Lemma lem7593447 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593448 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593449 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593448 h1) (fun h1 : term169 = True => @lem7593447)). Qed.
Lemma lem7593450 : term169 = True.
Proof. exact (EQ_MP (@lem7593449) (@lem7593447)). Qed.
Lemma lem7593451 : term168 = True.
Proof. exact (TRANS (@lem7593446) (@lem7593450)). Qed.
Lemma lem7593452 : term254 = True.
Proof. exact (TRANS (@lem7593443) (@lem7593451)). Qed.
Lemma lem7593453 : term251 = True.
Proof. exact (TRANS (@lem7593429) (@lem7593452)). Qed.
Lemma lem7593454 : term168 = True.
Proof. exact (TRANS (@lem7593406) (@lem7593453)). Qed.
Lemma lem7593455 : term248 = True.
Proof. exact (TRANS (@lem7593397) (@lem7593454)). Qed.
Lemma lem7593456 : True = term248.
Proof. exact (SYM (@lem7593455)). Qed.
Lemma lem7593457 : term248.
Proof. exact (EQ_MP (@lem7593456) (@lem0)). Qed.
Lemma lem7593458 (_97606 : int) (h1 : term313 _97606) : term319 _97606.
Proof. exact (conj (@lem7593457) (@lem7593319 _97606 h1)). Qed.
Lemma lem7593460 (x : real) (y : real) : term257 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7593461 (_97606 : int) : term320 _97606.
Proof. exact (@lem7593460 term74 (term158 _97606)). Qed.
Lemma lem7593462 (_97606 : int) (h1 : term313 _97606) : term321 _97606.
Proof. exact (@lem7593461 _97606 (@lem7593458 _97606 h1)). Qed.
Lemma lem7593463 (_97606 : int) : (term322 _97606) = (term158 _97606).
Proof. exact (@lem1982733 (term158 _97606)). Qed.
Lemma lem7593464 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7593465 (_97606 : int) : (term323 _97606) = (term202 _97606).
Proof. exact (MK_COMB (@lem7593464) (@lem7593463 _97606)). Qed.
Lemma lem7593466 : term59 = term59.
Proof. exact (eq_refl term59). Qed.
Lemma lem7593467 (_97606 : int) : (term321 _97606) = (term203 _97606).
Proof. exact (MK_COMB (@lem7593465 _97606) (@lem7593466)). Qed.
Lemma lem7593468 (_97606 : int) (h1 : term313 _97606) : term203 _97606.
Proof. exact (EQ_MP (@lem7593467 _97606) (@lem7593462 _97606 h1)). Qed.
Lemma lem7593469 (_97606 : int) (h1 : term313 _97606) : term324 _97606.
Proof. exact (conj (@lem7593468 _97606 h1) (@lem7593394 _97606 h1)). Qed.
Lemma lem7593471 (x : real) (y : real) : term267 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7593472 (_97606 : int) : term325 _97606.
Proof. exact (@lem7593471 (term158 _97606) (real_of_int _97606)). Qed.
Lemma lem7593473 (_97606 : int) (h1 : term313 _97606) : term326 _97606.
Proof. exact (@lem7593472 _97606 (@lem7593469 _97606 h1)). Qed.
Lemma lem7593474 (_97606 : int) : (term327 _97606) = (term271 _97606).
Proof. exact (@lem1982759 (term162 _97606) (real_of_int _97606) term122). Qed.
Lemma lem7593475 (_97606 : int) : (term272 _97606) = (term273 _97606).
Proof. exact (@lem1982713 term122 (real_of_int _97606)). Qed.
Lemma lem7593477 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7593478 : term74 = term148.
Proof. exact (@lem7593477 term11). Qed.
Lemma lem7593480 (x : nat) : (term120 x) = (term121 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7593481 : term122 = term123.
Proof. exact (@lem7593480 term11). Qed.
Lemma lem7593482 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7593483 : term274 = term275.
Proof. exact (MK_COMB (@lem7593482) (@lem7593481)). Qed.
Lemma lem7593484 : term276 = term277.
Proof. exact (MK_COMB (@lem7593483) (@lem7593478)). Qed.
Lemma lem7593485 : term278.
Proof. exact (@lem1981473 term122 term74 term74 term74 term59 term74). Qed.
Lemma lem7593487 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593488 : term168 = term169.
Proof. exact (@lem7593487 (NUMERAL 0) term11). Qed.
Lemma lem7593489 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593490 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593491 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593490 h1) (fun h1 : term169 = True => @lem7593489)). Qed.
Lemma lem7593492 : term169 = True.
Proof. exact (EQ_MP (@lem7593491) (@lem7593489)). Qed.
Lemma lem7593493 : term168 = True.
Proof. exact (TRANS (@lem7593488) (@lem7593492)). Qed.
Lemma lem7593494 : True = term168.
Proof. exact (SYM (@lem7593493)). Qed.
Lemma lem7593495 : term168.
Proof. exact (EQ_MP (@lem7593494) (@lem0)). Qed.
Lemma lem7593496 : term279.
Proof. exact (@lem7593485 (@lem7593495)). Qed.
Lemma lem7593498 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593499 : term168 = term169.
Proof. exact (@lem7593498 (NUMERAL 0) term11). Qed.
Lemma lem7593500 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593501 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593502 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593501 h1) (fun h1 : term169 = True => @lem7593500)). Qed.
Lemma lem7593503 : term169 = True.
Proof. exact (EQ_MP (@lem7593502) (@lem7593500)). Qed.
Lemma lem7593504 : term168 = True.
Proof. exact (TRANS (@lem7593499) (@lem7593503)). Qed.
Lemma lem7593505 : True = term168.
Proof. exact (SYM (@lem7593504)). Qed.
Lemma lem7593506 : term168.
Proof. exact (EQ_MP (@lem7593505) (@lem0)). Qed.
Lemma lem7593507 : term280.
Proof. exact (@lem7593496 (@lem7593506)). Qed.
Lemma lem7593509 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593510 : term168 = term169.
Proof. exact (@lem7593509 (NUMERAL 0) term11). Qed.
Lemma lem7593511 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593512 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593513 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593512 h1) (fun h1 : term169 = True => @lem7593511)). Qed.
Lemma lem7593514 : term169 = True.
Proof. exact (EQ_MP (@lem7593513) (@lem7593511)). Qed.
Lemma lem7593515 : term168 = True.
Proof. exact (TRANS (@lem7593510) (@lem7593514)). Qed.
Lemma lem7593516 : True = term168.
Proof. exact (SYM (@lem7593515)). Qed.
Lemma lem7593517 : term168.
Proof. exact (EQ_MP (@lem7593516) (@lem0)). Qed.
Lemma lem7593518 : term281.
Proof. exact (@lem7593507 (@lem7593517)). Qed.
Lemma lem7593520 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7593521 : term131 = term132.
Proof. exact (@lem7593520 term11 term11). Qed.
Lemma lem7593522 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7593523 : term134 = term11.
Proof. exact (EQ_MP (@lem7593522) (@lem940073)). Qed.
Lemma lem7593524 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7593525 : term132 = term74.
Proof. exact (MK_COMB (@lem7593524) (@lem7593523)). Qed.
Lemma lem7593526 : term131 = term74.
Proof. exact (TRANS (@lem7593521) (@lem7593525)). Qed.
Lemma lem7593528 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7593529 : term149 = term154.
Proof. exact (@lem7593528 term11 term11). Qed.
Lemma lem7593530 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7593531 : term134 = term11.
Proof. exact (EQ_MP (@lem7593530) (@lem940073)). Qed.
Lemma lem7593532 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7593533 : term132 = term74.
Proof. exact (MK_COMB (@lem7593532) (@lem7593531)). Qed.
Lemma lem7593534 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7593535 : term154 = term122.
Proof. exact (MK_COMB (@lem7593534) (@lem7593533)). Qed.
Lemma lem7593536 : term149 = term122.
Proof. exact (TRANS (@lem7593529) (@lem7593535)). Qed.
Lemma lem7593537 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7593538 : term282 = term274.
Proof. exact (MK_COMB (@lem7593537) (@lem7593536)). Qed.
Lemma lem7593539 : term283 = term276.
Proof. exact (MK_COMB (@lem7593538) (@lem7593526)). Qed.
Lemma lem7593541 (m : nat) : (term284 m) = term59.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7593542 : term276 = term59.
Proof. exact (@lem7593541 term11). Qed.
Lemma lem7593543 : term283 = term59.
Proof. exact (TRANS (@lem7593539) (@lem7593542)). Qed.
Lemma lem7593544 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7593545 : term285 = term178.
Proof. exact (MK_COMB (@lem7593544) (@lem7593543)). Qed.
Lemma lem7593546 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem7593547 : term286 = term180.
Proof. exact (MK_COMB (@lem7593545) (@lem7593546)). Qed.
Lemma lem7593549 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7593550 : term180 = term59.
Proof. exact (@lem7593549 term11). Qed.
Lemma lem7593551 : term286 = term59.
Proof. exact (TRANS (@lem7593547) (@lem7593550)). Qed.
Lemma lem7593553 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7593554 : term131 = term132.
Proof. exact (@lem7593553 term11 term11). Qed.
Lemma lem7593555 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7593556 : term134 = term11.
Proof. exact (EQ_MP (@lem7593555) (@lem940073)). Qed.
Lemma lem7593557 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7593558 : term132 = term74.
Proof. exact (MK_COMB (@lem7593557) (@lem7593556)). Qed.
Lemma lem7593559 : term131 = term74.
Proof. exact (TRANS (@lem7593554) (@lem7593558)). Qed.
Lemma lem7593560 : term178 = term178.
Proof. exact (eq_refl term178). Qed.
Lemma lem7593561 : term182 = term180.
Proof. exact (MK_COMB (@lem7593560) (@lem7593559)). Qed.
Lemma lem7593563 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7593564 : term180 = term59.
Proof. exact (@lem7593563 term11). Qed.
Lemma lem7593565 : term182 = term59.
Proof. exact (TRANS (@lem7593561) (@lem7593564)). Qed.
Lemma lem7593566 : term59 = term182.
Proof. exact (SYM (@lem7593565)). Qed.
Lemma lem7593567 : term286 = term182.
Proof. exact (TRANS (@lem7593551) (@lem7593566)). Qed.
Lemma lem7593568 : term277 = term119.
Proof. exact (@lem7593518 (@lem7593567)). Qed.
Lemma lem7593569 : term276 = term119.
Proof. exact (TRANS (@lem7593484) (@lem7593568)). Qed.
Lemma lem7593571 (x : real) : (term138 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7593572 : term119 = term59.
Proof. exact (@lem7593571 term59). Qed.
Lemma lem7593573 : term276 = term59.
Proof. exact (TRANS (@lem7593569) (@lem7593572)). Qed.
Lemma lem7593574 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7593575 : term287 = term178.
Proof. exact (MK_COMB (@lem7593574) (@lem7593573)). Qed.
Lemma lem7593576 (_97606 : int) : (real_of_int _97606) = (real_of_int _97606).
Proof. exact (eq_refl (real_of_int _97606)). Qed.
Lemma lem7593577 (_97606 : int) : (term273 _97606) = (term288 _97606).
Proof. exact (MK_COMB (@lem7593575) (@lem7593576 _97606)). Qed.
Lemma lem7593578 (_97606 : int) : (term272 _97606) = (term288 _97606).
Proof. exact (TRANS (@lem7593475 _97606) (@lem7593577 _97606)). Qed.
Lemma lem7593579 (_97606 : int) : (term288 _97606) = term59.
Proof. exact (@lem1982719 (real_of_int _97606)). Qed.
Lemma lem7593580 (_97606 : int) : (term272 _97606) = term59.
Proof. exact (TRANS (@lem7593578 _97606) (@lem7593579 _97606)). Qed.
Lemma lem7593581 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7593582 (_97606 : int) : (term289 _97606) = term101.
Proof. exact (MK_COMB (@lem7593581) (@lem7593580 _97606)). Qed.
Lemma lem7593583 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem7593584 (_97606 : int) : (term271 _97606) = term290.
Proof. exact (MK_COMB (@lem7593582 _97606) (@lem7593583)). Qed.
Lemma lem7593585 (_97606 : int) : (term327 _97606) = term290.
Proof. exact (TRANS (@lem7593474 _97606) (@lem7593584 _97606)). Qed.
Lemma lem7593586 : term290 = term122.
Proof. exact (@lem1982721 term122). Qed.
Lemma lem7593587 (_97606 : int) : (term327 _97606) = term122.
Proof. exact (TRANS (@lem7593585 _97606) (@lem7593586)). Qed.
Lemma lem7593588 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7593589 (_97606 : int) : (term328 _97606) = term292.
Proof. exact (MK_COMB (@lem7593588) (@lem7593587 _97606)). Qed.
Lemma lem7593590 : term59 = term59.
Proof. exact (eq_refl term59). Qed.
Lemma lem7593591 (_97606 : int) : (term326 _97606) = term293.
Proof. exact (MK_COMB (@lem7593589 _97606) (@lem7593590)). Qed.
Lemma lem7593592 (_97606 : int) (h1 : term313 _97606) : term293.
Proof. exact (EQ_MP (@lem7593591 _97606) (@lem7593473 _97606 h1)). Qed.
Lemma lem7593594 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7593595 : term293 = term294.
Proof. exact (@lem7593594 term59 term122). Qed.
Lemma lem7593597 (x : nat) : (term120 x) = (term121 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7593598 : term122 = term123.
Proof. exact (@lem7593597 term11). Qed.
Lemma lem7593600 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7593601 : term59 = term119.
Proof. exact (@lem7593600 (NUMERAL 0)). Qed.
Lemma lem7593602 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7593603 : term61 = term295.
Proof. exact (MK_COMB (@lem7593602) (@lem7593601)). Qed.
Lemma lem7593604 : term294 = term296.
Proof. exact (MK_COMB (@lem7593603) (@lem7593598)). Qed.
Lemma lem7593605 : term297.
Proof. exact (@lem1980026 term59 term74 term122 term74). Qed.
Lemma lem7593607 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593608 : term168 = term169.
Proof. exact (@lem7593607 (NUMERAL 0) term11). Qed.
Lemma lem7593609 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593610 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593611 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593610 h1) (fun h1 : term169 = True => @lem7593609)). Qed.
Lemma lem7593612 : term169 = True.
Proof. exact (EQ_MP (@lem7593611) (@lem7593609)). Qed.
Lemma lem7593613 : term168 = True.
Proof. exact (TRANS (@lem7593608) (@lem7593612)). Qed.
Lemma lem7593614 : True = term168.
Proof. exact (SYM (@lem7593613)). Qed.
Lemma lem7593615 : term168.
Proof. exact (EQ_MP (@lem7593614) (@lem0)). Qed.
Lemma lem7593616 : term298.
Proof. exact (@lem7593605 (@lem7593615)). Qed.
Lemma lem7593618 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593619 : term168 = term169.
Proof. exact (@lem7593618 (NUMERAL 0) term11). Qed.
Lemma lem7593620 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593621 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593622 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593621 h1) (fun h1 : term169 = True => @lem7593620)). Qed.
Lemma lem7593623 : term169 = True.
Proof. exact (EQ_MP (@lem7593622) (@lem7593620)). Qed.
Lemma lem7593624 : term168 = True.
Proof. exact (TRANS (@lem7593619) (@lem7593623)). Qed.
Lemma lem7593625 : True = term168.
Proof. exact (SYM (@lem7593624)). Qed.
Lemma lem7593626 : term168.
Proof. exact (EQ_MP (@lem7593625) (@lem0)). Qed.
Lemma lem7593627 : term296 = term299.
Proof. exact (@lem7593616 (@lem7593626)). Qed.
Lemma lem7593629 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7593630 : term149 = term154.
Proof. exact (@lem7593629 term11 term11). Qed.
Lemma lem7593631 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7593632 : term134 = term11.
Proof. exact (EQ_MP (@lem7593631) (@lem940073)). Qed.
Lemma lem7593633 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7593634 : term132 = term74.
Proof. exact (MK_COMB (@lem7593633) (@lem7593632)). Qed.
Lemma lem7593635 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7593636 : term154 = term122.
Proof. exact (MK_COMB (@lem7593635) (@lem7593634)). Qed.
Lemma lem7593637 : term149 = term122.
Proof. exact (TRANS (@lem7593630) (@lem7593636)). Qed.
Lemma lem7593639 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7593640 : term180 = term59.
Proof. exact (@lem7593639 term11). Qed.
Lemma lem7593641 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7593642 : term300 = term61.
Proof. exact (MK_COMB (@lem7593641) (@lem7593640)). Qed.
Lemma lem7593643 : term299 = term294.
Proof. exact (MK_COMB (@lem7593642) (@lem7593637)). Qed.
Lemma lem7593645 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7593646 : term294 = term303.
Proof. exact (@lem7593645 (NUMERAL 0) term11). Qed.
Lemma lem7593647 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593648 (h1 : term170 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7593649 : (term170 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593648 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem7593647)). Qed.
Lemma lem7593650 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7593649) (@lem7593647)). Qed.
Lemma lem7593651 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7593652 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7593653 : term304 = (and True).
Proof. exact (MK_COMB (@lem7593652) (@lem7593651)). Qed.
Lemma lem7593654 : term303 = (True /\ False).
Proof. exact (MK_COMB (@lem7593653) (@lem7593650)). Qed.
Lemma lem7593656 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7593657 : term303 = False.
Proof. exact (TRANS (@lem7593654) (@lem7593656)). Qed.
Lemma lem7593658 : term294 = False.
Proof. exact (TRANS (@lem7593646) (@lem7593657)). Qed.
Lemma lem7593659 : term299 = False.
Proof. exact (TRANS (@lem7593643) (@lem7593658)). Qed.
Lemma lem7593660 : term296 = False.
Proof. exact (TRANS (@lem7593627) (@lem7593659)). Qed.
Lemma lem7593661 : term294 = False.
Proof. exact (TRANS (@lem7593604) (@lem7593660)). Qed.
Lemma lem7593662 : term293 = False.
Proof. exact (TRANS (@lem7593595) (@lem7593661)). Qed.
Lemma lem7593663 (_97606 : int) (h1 : term313 _97606) : False.
Proof. exact (EQ_MP (@lem7593662) (@lem7593592 _97606 h1)). Qed.
Lemma lem7593664 (_97606 : int) (h1 : term329 _97606) : term329 _97606.
Proof. exact (h1). Qed.
Lemma lem7593665 (_97606 : int) (h1 : term329 _97606) : term240 _97606.
Proof. exact (proj2 (@lem7593664 _97606 h1)). Qed.
Lemma lem7593667 (_97606 : int) (h1 : term329 _97606) : term203 _97606.
Proof. exact (proj2 (@lem7593665 _97606 h1)). Qed.
Lemma lem7593668 (_97606 : int) (h1 : term329 _97606) : (real_of_int _97606) = term59.
Proof. exact (proj1 (@lem7593665 _97606 h1)). Qed.
Lemma lem7593670 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7593671 : term248 = term168.
Proof. exact (@lem7593670 term59 term74). Qed.
Lemma lem7593673 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7593674 : term74 = term148.
Proof. exact (@lem7593673 term11). Qed.
Lemma lem7593676 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7593677 : term59 = term119.
Proof. exact (@lem7593676 (NUMERAL 0)). Qed.
Lemma lem7593678 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7593679 : term249 = term250.
Proof. exact (MK_COMB (@lem7593678) (@lem7593677)). Qed.
Lemma lem7593680 : term168 = term251.
Proof. exact (MK_COMB (@lem7593679) (@lem7593674)). Qed.
Lemma lem7593681 : term252.
Proof. exact (@lem1980255 term59 term74 term74 term74). Qed.
Lemma lem7593683 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593684 : term168 = term169.
Proof. exact (@lem7593683 (NUMERAL 0) term11). Qed.
Lemma lem7593685 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593686 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593687 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593686 h1) (fun h1 : term169 = True => @lem7593685)). Qed.
Lemma lem7593688 : term169 = True.
Proof. exact (EQ_MP (@lem7593687) (@lem7593685)). Qed.
Lemma lem7593689 : term168 = True.
Proof. exact (TRANS (@lem7593684) (@lem7593688)). Qed.
Lemma lem7593690 : True = term168.
Proof. exact (SYM (@lem7593689)). Qed.
Lemma lem7593691 : term168.
Proof. exact (EQ_MP (@lem7593690) (@lem0)). Qed.
Lemma lem7593692 : term253.
Proof. exact (@lem7593681 (@lem7593691)). Qed.
Lemma lem7593694 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593695 : term168 = term169.
Proof. exact (@lem7593694 (NUMERAL 0) term11). Qed.
Lemma lem7593696 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593697 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593698 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593697 h1) (fun h1 : term169 = True => @lem7593696)). Qed.
Lemma lem7593699 : term169 = True.
Proof. exact (EQ_MP (@lem7593698) (@lem7593696)). Qed.
Lemma lem7593700 : term168 = True.
Proof. exact (TRANS (@lem7593695) (@lem7593699)). Qed.
Lemma lem7593701 : True = term168.
Proof. exact (SYM (@lem7593700)). Qed.
Lemma lem7593702 : term168.
Proof. exact (EQ_MP (@lem7593701) (@lem0)). Qed.
Lemma lem7593703 : term251 = term254.
Proof. exact (@lem7593692 (@lem7593702)). Qed.
Lemma lem7593705 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7593706 : term131 = term132.
Proof. exact (@lem7593705 term11 term11). Qed.
Lemma lem7593707 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7593708 : term134 = term11.
Proof. exact (EQ_MP (@lem7593707) (@lem940073)). Qed.
Lemma lem7593709 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7593710 : term132 = term74.
Proof. exact (MK_COMB (@lem7593709) (@lem7593708)). Qed.
Lemma lem7593711 : term131 = term74.
Proof. exact (TRANS (@lem7593706) (@lem7593710)). Qed.
Lemma lem7593713 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7593714 : term180 = term59.
Proof. exact (@lem7593713 term11). Qed.
Lemma lem7593715 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7593716 : term255 = term249.
Proof. exact (MK_COMB (@lem7593715) (@lem7593714)). Qed.
Lemma lem7593717 : term254 = term168.
Proof. exact (MK_COMB (@lem7593716) (@lem7593711)). Qed.
Lemma lem7593719 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593720 : term168 = term169.
Proof. exact (@lem7593719 (NUMERAL 0) term11). Qed.
Lemma lem7593721 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593722 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593723 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593722 h1) (fun h1 : term169 = True => @lem7593721)). Qed.
Lemma lem7593724 : term169 = True.
Proof. exact (EQ_MP (@lem7593723) (@lem7593721)). Qed.
Lemma lem7593725 : term168 = True.
Proof. exact (TRANS (@lem7593720) (@lem7593724)). Qed.
Lemma lem7593726 : term254 = True.
Proof. exact (TRANS (@lem7593717) (@lem7593725)). Qed.
Lemma lem7593727 : term251 = True.
Proof. exact (TRANS (@lem7593703) (@lem7593726)). Qed.
Lemma lem7593728 : term168 = True.
Proof. exact (TRANS (@lem7593680) (@lem7593727)). Qed.
Lemma lem7593729 : term248 = True.
Proof. exact (TRANS (@lem7593671) (@lem7593728)). Qed.
Lemma lem7593730 : True = term248.
Proof. exact (SYM (@lem7593729)). Qed.
Lemma lem7593731 : term248.
Proof. exact (EQ_MP (@lem7593730) (@lem0)). Qed.
Lemma lem7593732 (_97606 : int) (h1 : term329 _97606) : term319 _97606.
Proof. exact (conj (@lem7593731) (@lem7593667 _97606 h1)). Qed.
Lemma lem7593734 (x : real) (y : real) : term257 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7593735 (_97606 : int) : term320 _97606.
Proof. exact (@lem7593734 term74 (term158 _97606)). Qed.
Lemma lem7593736 (_97606 : int) (h1 : term329 _97606) : term321 _97606.
Proof. exact (@lem7593735 _97606 (@lem7593732 _97606 h1)). Qed.
Lemma lem7593737 (_97606 : int) : (term322 _97606) = (term158 _97606).
Proof. exact (@lem1982733 (term158 _97606)). Qed.
Lemma lem7593738 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7593739 (_97606 : int) : (term323 _97606) = (term202 _97606).
Proof. exact (MK_COMB (@lem7593738) (@lem7593737 _97606)). Qed.
Lemma lem7593740 : term59 = term59.
Proof. exact (eq_refl term59). Qed.
Lemma lem7593741 (_97606 : int) : (term321 _97606) = (term203 _97606).
Proof. exact (MK_COMB (@lem7593739 _97606) (@lem7593740)). Qed.
Lemma lem7593742 (_97606 : int) (h1 : term329 _97606) : term203 _97606.
Proof. exact (EQ_MP (@lem7593741 _97606) (@lem7593736 _97606 h1)). Qed.
Lemma lem7593744 (y : real) : term306 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem7593745 (_97606 : int) : term307 _97606.
Proof. exact (@lem7593744 (real_of_int _97606)). Qed.
Lemma lem7593746 (_97606 : int) (h1 : term329 _97606) : term308 _97606.
Proof. exact (@lem7593745 _97606 (@lem7593668 _97606 h1)). Qed.
Lemma lem7593747 (_97606 : int) (h1 : term329 _97606) : term330 _97606.
Proof. exact (@lem7593746 _97606 h1 term74). Qed.
Lemma lem7593748 (_97606 : int) : (term330 _97606) = ((term317 _97606) = term59).
Proof. exact (eq_refl (term330 _97606)). Qed.
Lemma lem7593749 (_97606 : int) (h1 : term329 _97606) : (term317 _97606) = term59.
Proof. exact (EQ_MP (@lem7593748 _97606) (@lem7593747 _97606 h1)). Qed.
Lemma lem7593750 (_97606 : int) : (term317 _97606) = (real_of_int _97606).
Proof. exact (@lem1982733 (real_of_int _97606)). Qed.
Lemma lem7593751 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7593752 (_97606 : int) : (term331 _97606) = (term80 _97606).
Proof. exact (MK_COMB (@lem7593751) (@lem7593750 _97606)). Qed.
Lemma lem7593753 : term59 = term59.
Proof. exact (eq_refl term59). Qed.
Lemma lem7593754 (_97606 : int) : ((term317 _97606) = term59) = ((real_of_int _97606) = term59).
Proof. exact (MK_COMB (@lem7593752 _97606) (@lem7593753)). Qed.
Lemma lem7593755 (_97606 : int) (h1 : term329 _97606) : (real_of_int _97606) = term59.
Proof. exact (EQ_MP (@lem7593754 _97606) (@lem7593749 _97606 h1)). Qed.
Lemma lem7593756 (_97606 : int) (h1 : term329 _97606) : term240 _97606.
Proof. exact (conj (@lem7593755 _97606 h1) (@lem7593742 _97606 h1)). Qed.
Lemma lem7593758 (x : real) (y : real) : term311 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem7593759 (_97606 : int) : term332 _97606.
Proof. exact (@lem7593758 (real_of_int _97606) (term158 _97606)). Qed.
Lemma lem7593760 (_97606 : int) (h1 : term329 _97606) : term333 _97606.
Proof. exact (@lem7593759 _97606 (@lem7593756 _97606 h1)). Qed.
Lemma lem7593761 (_97606 : int) : (term334 _97606) = (term335 _97606).
Proof. exact (@lem1982763 (real_of_int _97606) (term162 _97606) term122). Qed.
Lemma lem7593762 (_97606 : int) : (term336 _97606) = (term273 _97606).
Proof. exact (@lem1982715 term122 (real_of_int _97606)). Qed.
Lemma lem7593764 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7593765 : term74 = term148.
Proof. exact (@lem7593764 term11). Qed.
Lemma lem7593767 (x : nat) : (term120 x) = (term121 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7593768 : term122 = term123.
Proof. exact (@lem7593767 term11). Qed.
Lemma lem7593769 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7593770 : term274 = term275.
Proof. exact (MK_COMB (@lem7593769) (@lem7593768)). Qed.
Lemma lem7593771 : term276 = term277.
Proof. exact (MK_COMB (@lem7593770) (@lem7593765)). Qed.
Lemma lem7593772 : term278.
Proof. exact (@lem1981473 term122 term74 term74 term74 term59 term74). Qed.
Lemma lem7593774 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593775 : term168 = term169.
Proof. exact (@lem7593774 (NUMERAL 0) term11). Qed.
Lemma lem7593776 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593777 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593778 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593777 h1) (fun h1 : term169 = True => @lem7593776)). Qed.
Lemma lem7593779 : term169 = True.
Proof. exact (EQ_MP (@lem7593778) (@lem7593776)). Qed.
Lemma lem7593780 : term168 = True.
Proof. exact (TRANS (@lem7593775) (@lem7593779)). Qed.
Lemma lem7593781 : True = term168.
Proof. exact (SYM (@lem7593780)). Qed.
Lemma lem7593782 : term168.
Proof. exact (EQ_MP (@lem7593781) (@lem0)). Qed.
Lemma lem7593783 : term279.
Proof. exact (@lem7593772 (@lem7593782)). Qed.
Lemma lem7593785 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593786 : term168 = term169.
Proof. exact (@lem7593785 (NUMERAL 0) term11). Qed.
Lemma lem7593787 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593788 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593789 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593788 h1) (fun h1 : term169 = True => @lem7593787)). Qed.
Lemma lem7593790 : term169 = True.
Proof. exact (EQ_MP (@lem7593789) (@lem7593787)). Qed.
Lemma lem7593791 : term168 = True.
Proof. exact (TRANS (@lem7593786) (@lem7593790)). Qed.
Lemma lem7593792 : True = term168.
Proof. exact (SYM (@lem7593791)). Qed.
Lemma lem7593793 : term168.
Proof. exact (EQ_MP (@lem7593792) (@lem0)). Qed.
Lemma lem7593794 : term280.
Proof. exact (@lem7593783 (@lem7593793)). Qed.
Lemma lem7593796 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593797 : term168 = term169.
Proof. exact (@lem7593796 (NUMERAL 0) term11). Qed.
Lemma lem7593798 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593799 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593800 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593799 h1) (fun h1 : term169 = True => @lem7593798)). Qed.
Lemma lem7593801 : term169 = True.
Proof. exact (EQ_MP (@lem7593800) (@lem7593798)). Qed.
Lemma lem7593802 : term168 = True.
Proof. exact (TRANS (@lem7593797) (@lem7593801)). Qed.
Lemma lem7593803 : True = term168.
Proof. exact (SYM (@lem7593802)). Qed.
Lemma lem7593804 : term168.
Proof. exact (EQ_MP (@lem7593803) (@lem0)). Qed.
Lemma lem7593805 : term281.
Proof. exact (@lem7593794 (@lem7593804)). Qed.
Lemma lem7593807 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7593808 : term131 = term132.
Proof. exact (@lem7593807 term11 term11). Qed.
Lemma lem7593809 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7593810 : term134 = term11.
Proof. exact (EQ_MP (@lem7593809) (@lem940073)). Qed.
Lemma lem7593811 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7593812 : term132 = term74.
Proof. exact (MK_COMB (@lem7593811) (@lem7593810)). Qed.
Lemma lem7593813 : term131 = term74.
Proof. exact (TRANS (@lem7593808) (@lem7593812)). Qed.
Lemma lem7593815 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7593816 : term149 = term154.
Proof. exact (@lem7593815 term11 term11). Qed.
Lemma lem7593817 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7593818 : term134 = term11.
Proof. exact (EQ_MP (@lem7593817) (@lem940073)). Qed.
Lemma lem7593819 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7593820 : term132 = term74.
Proof. exact (MK_COMB (@lem7593819) (@lem7593818)). Qed.
Lemma lem7593821 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7593822 : term154 = term122.
Proof. exact (MK_COMB (@lem7593821) (@lem7593820)). Qed.
Lemma lem7593823 : term149 = term122.
Proof. exact (TRANS (@lem7593816) (@lem7593822)). Qed.
Lemma lem7593824 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7593825 : term282 = term274.
Proof. exact (MK_COMB (@lem7593824) (@lem7593823)). Qed.
Lemma lem7593826 : term283 = term276.
Proof. exact (MK_COMB (@lem7593825) (@lem7593813)). Qed.
Lemma lem7593828 (m : nat) : (term284 m) = term59.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7593829 : term276 = term59.
Proof. exact (@lem7593828 term11). Qed.
Lemma lem7593830 : term283 = term59.
Proof. exact (TRANS (@lem7593826) (@lem7593829)). Qed.
Lemma lem7593831 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7593832 : term285 = term178.
Proof. exact (MK_COMB (@lem7593831) (@lem7593830)). Qed.
Lemma lem7593833 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem7593834 : term286 = term180.
Proof. exact (MK_COMB (@lem7593832) (@lem7593833)). Qed.
Lemma lem7593836 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7593837 : term180 = term59.
Proof. exact (@lem7593836 term11). Qed.
Lemma lem7593838 : term286 = term59.
Proof. exact (TRANS (@lem7593834) (@lem7593837)). Qed.
Lemma lem7593840 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7593841 : term131 = term132.
Proof. exact (@lem7593840 term11 term11). Qed.
Lemma lem7593842 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7593843 : term134 = term11.
Proof. exact (EQ_MP (@lem7593842) (@lem940073)). Qed.
Lemma lem7593844 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7593845 : term132 = term74.
Proof. exact (MK_COMB (@lem7593844) (@lem7593843)). Qed.
Lemma lem7593846 : term131 = term74.
Proof. exact (TRANS (@lem7593841) (@lem7593845)). Qed.
Lemma lem7593847 : term178 = term178.
Proof. exact (eq_refl term178). Qed.
Lemma lem7593848 : term182 = term180.
Proof. exact (MK_COMB (@lem7593847) (@lem7593846)). Qed.
Lemma lem7593850 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7593851 : term180 = term59.
Proof. exact (@lem7593850 term11). Qed.
Lemma lem7593852 : term182 = term59.
Proof. exact (TRANS (@lem7593848) (@lem7593851)). Qed.
Lemma lem7593853 : term59 = term182.
Proof. exact (SYM (@lem7593852)). Qed.
Lemma lem7593854 : term286 = term182.
Proof. exact (TRANS (@lem7593838) (@lem7593853)). Qed.
Lemma lem7593855 : term277 = term119.
Proof. exact (@lem7593805 (@lem7593854)). Qed.
Lemma lem7593856 : term276 = term119.
Proof. exact (TRANS (@lem7593771) (@lem7593855)). Qed.
Lemma lem7593858 (x : real) : (term138 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7593859 : term119 = term59.
Proof. exact (@lem7593858 term59). Qed.
Lemma lem7593860 : term276 = term59.
Proof. exact (TRANS (@lem7593856) (@lem7593859)). Qed.
Lemma lem7593861 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7593862 : term287 = term178.
Proof. exact (MK_COMB (@lem7593861) (@lem7593860)). Qed.
Lemma lem7593863 (_97606 : int) : (real_of_int _97606) = (real_of_int _97606).
Proof. exact (eq_refl (real_of_int _97606)). Qed.
Lemma lem7593864 (_97606 : int) : (term273 _97606) = (term288 _97606).
Proof. exact (MK_COMB (@lem7593862) (@lem7593863 _97606)). Qed.
Lemma lem7593865 (_97606 : int) : (term336 _97606) = (term288 _97606).
Proof. exact (TRANS (@lem7593762 _97606) (@lem7593864 _97606)). Qed.
Lemma lem7593866 (_97606 : int) : (term288 _97606) = term59.
Proof. exact (@lem1982719 (real_of_int _97606)). Qed.
Lemma lem7593867 (_97606 : int) : (term336 _97606) = term59.
Proof. exact (TRANS (@lem7593865 _97606) (@lem7593866 _97606)). Qed.
Lemma lem7593868 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7593869 (_97606 : int) : (term337 _97606) = term101.
Proof. exact (MK_COMB (@lem7593868) (@lem7593867 _97606)). Qed.
Lemma lem7593870 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem7593871 (_97606 : int) : (term335 _97606) = term290.
Proof. exact (MK_COMB (@lem7593869 _97606) (@lem7593870)). Qed.
Lemma lem7593872 (_97606 : int) : (term334 _97606) = term290.
Proof. exact (TRANS (@lem7593761 _97606) (@lem7593871 _97606)). Qed.
Lemma lem7593873 : term290 = term122.
Proof. exact (@lem1982721 term122). Qed.
Lemma lem7593874 (_97606 : int) : (term334 _97606) = term122.
Proof. exact (TRANS (@lem7593872 _97606) (@lem7593873)). Qed.
Lemma lem7593875 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7593876 (_97606 : int) : (term338 _97606) = term292.
Proof. exact (MK_COMB (@lem7593875) (@lem7593874 _97606)). Qed.
Lemma lem7593877 : term59 = term59.
Proof. exact (eq_refl term59). Qed.
Lemma lem7593878 (_97606 : int) : (term333 _97606) = term293.
Proof. exact (MK_COMB (@lem7593876 _97606) (@lem7593877)). Qed.
Lemma lem7593879 (_97606 : int) (h1 : term329 _97606) : term293.
Proof. exact (EQ_MP (@lem7593878 _97606) (@lem7593760 _97606 h1)). Qed.
Lemma lem7593881 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7593882 : term293 = term294.
Proof. exact (@lem7593881 term59 term122). Qed.
Lemma lem7593884 (x : nat) : (term120 x) = (term121 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7593885 : term122 = term123.
Proof. exact (@lem7593884 term11). Qed.
Lemma lem7593887 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7593888 : term59 = term119.
Proof. exact (@lem7593887 (NUMERAL 0)). Qed.
Lemma lem7593889 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7593890 : term61 = term295.
Proof. exact (MK_COMB (@lem7593889) (@lem7593888)). Qed.
Lemma lem7593891 : term294 = term296.
Proof. exact (MK_COMB (@lem7593890) (@lem7593885)). Qed.
Lemma lem7593892 : term297.
Proof. exact (@lem1980026 term59 term74 term122 term74). Qed.
Lemma lem7593894 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593895 : term168 = term169.
Proof. exact (@lem7593894 (NUMERAL 0) term11). Qed.
Lemma lem7593896 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593897 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593898 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593897 h1) (fun h1 : term169 = True => @lem7593896)). Qed.
Lemma lem7593899 : term169 = True.
Proof. exact (EQ_MP (@lem7593898) (@lem7593896)). Qed.
Lemma lem7593900 : term168 = True.
Proof. exact (TRANS (@lem7593895) (@lem7593899)). Qed.
Lemma lem7593901 : True = term168.
Proof. exact (SYM (@lem7593900)). Qed.
Lemma lem7593902 : term168.
Proof. exact (EQ_MP (@lem7593901) (@lem0)). Qed.
Lemma lem7593903 : term298.
Proof. exact (@lem7593892 (@lem7593902)). Qed.
Lemma lem7593905 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593906 : term168 = term169.
Proof. exact (@lem7593905 (NUMERAL 0) term11). Qed.
Lemma lem7593907 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593908 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593909 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593908 h1) (fun h1 : term169 = True => @lem7593907)). Qed.
Lemma lem7593910 : term169 = True.
Proof. exact (EQ_MP (@lem7593909) (@lem7593907)). Qed.
Lemma lem7593911 : term168 = True.
Proof. exact (TRANS (@lem7593906) (@lem7593910)). Qed.
Lemma lem7593912 : True = term168.
Proof. exact (SYM (@lem7593911)). Qed.
Lemma lem7593913 : term168.
Proof. exact (EQ_MP (@lem7593912) (@lem0)). Qed.
Lemma lem7593914 : term296 = term299.
Proof. exact (@lem7593903 (@lem7593913)). Qed.
Lemma lem7593916 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7593917 : term149 = term154.
Proof. exact (@lem7593916 term11 term11). Qed.
Lemma lem7593918 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7593919 : term134 = term11.
Proof. exact (EQ_MP (@lem7593918) (@lem940073)). Qed.
Lemma lem7593920 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7593921 : term132 = term74.
Proof. exact (MK_COMB (@lem7593920) (@lem7593919)). Qed.
Lemma lem7593922 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7593923 : term154 = term122.
Proof. exact (MK_COMB (@lem7593922) (@lem7593921)). Qed.
Lemma lem7593924 : term149 = term122.
Proof. exact (TRANS (@lem7593917) (@lem7593923)). Qed.
Lemma lem7593926 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7593927 : term180 = term59.
Proof. exact (@lem7593926 term11). Qed.
Lemma lem7593928 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7593929 : term300 = term61.
Proof. exact (MK_COMB (@lem7593928) (@lem7593927)). Qed.
Lemma lem7593930 : term299 = term294.
Proof. exact (MK_COMB (@lem7593929) (@lem7593924)). Qed.
Lemma lem7593932 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7593933 : term294 = term303.
Proof. exact (@lem7593932 (NUMERAL 0) term11). Qed.
Lemma lem7593934 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593935 (h1 : term170 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7593936 : (term170 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593935 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem7593934)). Qed.
Lemma lem7593937 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7593936) (@lem7593934)). Qed.
Lemma lem7593938 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7593939 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7593940 : term304 = (and True).
Proof. exact (MK_COMB (@lem7593939) (@lem7593938)). Qed.
Lemma lem7593941 : term303 = (True /\ False).
Proof. exact (MK_COMB (@lem7593940) (@lem7593937)). Qed.
Lemma lem7593943 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7593944 : term303 = False.
Proof. exact (TRANS (@lem7593941) (@lem7593943)). Qed.
Lemma lem7593945 : term294 = False.
Proof. exact (TRANS (@lem7593933) (@lem7593944)). Qed.
Lemma lem7593946 : term299 = False.
Proof. exact (TRANS (@lem7593930) (@lem7593945)). Qed.
Lemma lem7593947 : term296 = False.
Proof. exact (TRANS (@lem7593914) (@lem7593946)). Qed.
Lemma lem7593948 : term294 = False.
Proof. exact (TRANS (@lem7593891) (@lem7593947)). Qed.
Lemma lem7593949 : term293 = False.
Proof. exact (TRANS (@lem7593882) (@lem7593948)). Qed.
Lemma lem7593950 (_97606 : int) (h1 : term329 _97606) : False.
Proof. exact (EQ_MP (@lem7593949) (@lem7593879 _97606 h1)). Qed.
Lemma lem7593951 (_97606 : int) (h1 : term238 _97606) : False.
Proof. exact (or_elim (@lem7593315 _97606 h1) (fun h0 : term313 _97606 => @lem7593663 _97606 h0) (fun h0 : term329 _97606 => @lem7593950 _97606 h0)). Qed.
Lemma lem7593952 (_97606 : int) (h1 : term234 _97606) : term234 _97606.
Proof. exact (h1). Qed.
Lemma lem7593953 (_97606 : int) (h1 : term247 _97606) : term247 _97606.
Proof. exact (h1). Qed.
Lemma lem7593954 (_97606 : int) (h1 : term247 _97606) : term235 _97606.
Proof. exact (proj2 (@lem7593953 _97606 h1)). Qed.
Lemma lem7593956 (_97606 : int) (h1 : term247 _97606) : term196 _97606.
Proof. exact (proj2 (@lem7593954 _97606 h1)). Qed.
Lemma lem7593957 (_97606 : int) (h1 : term247 _97606) : term186 _97606.
Proof. exact (proj1 (@lem7593954 _97606 h1)). Qed.
Lemma lem7593959 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7593960 : term248 = term168.
Proof. exact (@lem7593959 term59 term74). Qed.
Lemma lem7593962 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7593963 : term74 = term148.
Proof. exact (@lem7593962 term11). Qed.
Lemma lem7593965 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7593966 : term59 = term119.
Proof. exact (@lem7593965 (NUMERAL 0)). Qed.
Lemma lem7593967 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7593968 : term249 = term250.
Proof. exact (MK_COMB (@lem7593967) (@lem7593966)). Qed.
Lemma lem7593969 : term168 = term251.
Proof. exact (MK_COMB (@lem7593968) (@lem7593963)). Qed.
Lemma lem7593970 : term252.
Proof. exact (@lem1980255 term59 term74 term74 term74). Qed.
Lemma lem7593972 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593973 : term168 = term169.
Proof. exact (@lem7593972 (NUMERAL 0) term11). Qed.
Lemma lem7593974 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593975 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593976 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593975 h1) (fun h1 : term169 = True => @lem7593974)). Qed.
Lemma lem7593977 : term169 = True.
Proof. exact (EQ_MP (@lem7593976) (@lem7593974)). Qed.
Lemma lem7593978 : term168 = True.
Proof. exact (TRANS (@lem7593973) (@lem7593977)). Qed.
Lemma lem7593979 : True = term168.
Proof. exact (SYM (@lem7593978)). Qed.
Lemma lem7593980 : term168.
Proof. exact (EQ_MP (@lem7593979) (@lem0)). Qed.
Lemma lem7593981 : term253.
Proof. exact (@lem7593970 (@lem7593980)). Qed.
Lemma lem7593983 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7593984 : term168 = term169.
Proof. exact (@lem7593983 (NUMERAL 0) term11). Qed.
Lemma lem7593985 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7593986 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7593987 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7593986 h1) (fun h1 : term169 = True => @lem7593985)). Qed.
Lemma lem7593988 : term169 = True.
Proof. exact (EQ_MP (@lem7593987) (@lem7593985)). Qed.
Lemma lem7593989 : term168 = True.
Proof. exact (TRANS (@lem7593984) (@lem7593988)). Qed.
Lemma lem7593990 : True = term168.
Proof. exact (SYM (@lem7593989)). Qed.
Lemma lem7593991 : term168.
Proof. exact (EQ_MP (@lem7593990) (@lem0)). Qed.
Lemma lem7593992 : term251 = term254.
Proof. exact (@lem7593981 (@lem7593991)). Qed.
Lemma lem7593994 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7593995 : term131 = term132.
Proof. exact (@lem7593994 term11 term11). Qed.
Lemma lem7593996 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7593997 : term134 = term11.
Proof. exact (EQ_MP (@lem7593996) (@lem940073)). Qed.
Lemma lem7593998 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7593999 : term132 = term74.
Proof. exact (MK_COMB (@lem7593998) (@lem7593997)). Qed.
Lemma lem7594000 : term131 = term74.
Proof. exact (TRANS (@lem7593995) (@lem7593999)). Qed.
Lemma lem7594002 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7594003 : term180 = term59.
Proof. exact (@lem7594002 term11). Qed.
Lemma lem7594004 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7594005 : term255 = term249.
Proof. exact (MK_COMB (@lem7594004) (@lem7594003)). Qed.
Lemma lem7594006 : term254 = term168.
Proof. exact (MK_COMB (@lem7594005) (@lem7594000)). Qed.
Lemma lem7594008 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7594009 : term168 = term169.
Proof. exact (@lem7594008 (NUMERAL 0) term11). Qed.
Lemma lem7594010 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7594011 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7594012 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7594011 h1) (fun h1 : term169 = True => @lem7594010)). Qed.
Lemma lem7594013 : term169 = True.
Proof. exact (EQ_MP (@lem7594012) (@lem7594010)). Qed.
Lemma lem7594014 : term168 = True.
Proof. exact (TRANS (@lem7594009) (@lem7594013)). Qed.
Lemma lem7594015 : term254 = True.
Proof. exact (TRANS (@lem7594006) (@lem7594014)). Qed.
Lemma lem7594016 : term251 = True.
Proof. exact (TRANS (@lem7593992) (@lem7594015)). Qed.
Lemma lem7594017 : term168 = True.
Proof. exact (TRANS (@lem7593969) (@lem7594016)). Qed.
Lemma lem7594018 : term248 = True.
Proof. exact (TRANS (@lem7593960) (@lem7594017)). Qed.
Lemma lem7594019 : True = term248.
Proof. exact (SYM (@lem7594018)). Qed.
Lemma lem7594020 : term248.
Proof. exact (EQ_MP (@lem7594019) (@lem0)). Qed.
Lemma lem7594021 (_97606 : int) (h1 : term247 _97606) : term256 _97606.
Proof. exact (conj (@lem7594020) (@lem7593956 _97606 h1)). Qed.
Lemma lem7594023 (x : real) (y : real) : term257 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7594024 (_97606 : int) : term258 _97606.
Proof. exact (@lem7594023 term74 (term193 _97606)). Qed.
Lemma lem7594025 (_97606 : int) (h1 : term247 _97606) : term259 _97606.
Proof. exact (@lem7594024 _97606 (@lem7594021 _97606 h1)). Qed.
Lemma lem7594026 (_97606 : int) : (term260 _97606) = (term193 _97606).
Proof. exact (@lem1982733 (term193 _97606)). Qed.
Lemma lem7594027 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7594028 (_97606 : int) : (term261 _97606) = (term195 _97606).
Proof. exact (MK_COMB (@lem7594027) (@lem7594026 _97606)). Qed.
Lemma lem7594029 : term59 = term59.
Proof. exact (eq_refl term59). Qed.
Lemma lem7594030 (_97606 : int) : (term259 _97606) = (term196 _97606).
Proof. exact (MK_COMB (@lem7594028 _97606) (@lem7594029)). Qed.
Lemma lem7594031 (_97606 : int) (h1 : term247 _97606) : term196 _97606.
Proof. exact (EQ_MP (@lem7594030 _97606) (@lem7594025 _97606 h1)). Qed.
Lemma lem7594033 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7594034 : term248 = term168.
Proof. exact (@lem7594033 term59 term74). Qed.
Lemma lem7594036 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7594037 : term74 = term148.
Proof. exact (@lem7594036 term11). Qed.
Lemma lem7594039 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7594040 : term59 = term119.
Proof. exact (@lem7594039 (NUMERAL 0)). Qed.
Lemma lem7594041 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7594042 : term249 = term250.
Proof. exact (MK_COMB (@lem7594041) (@lem7594040)). Qed.
Lemma lem7594043 : term168 = term251.
Proof. exact (MK_COMB (@lem7594042) (@lem7594037)). Qed.
Lemma lem7594044 : term252.
Proof. exact (@lem1980255 term59 term74 term74 term74). Qed.
Lemma lem7594046 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7594047 : term168 = term169.
Proof. exact (@lem7594046 (NUMERAL 0) term11). Qed.
Lemma lem7594048 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7594049 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7594050 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7594049 h1) (fun h1 : term169 = True => @lem7594048)). Qed.
Lemma lem7594051 : term169 = True.
Proof. exact (EQ_MP (@lem7594050) (@lem7594048)). Qed.
Lemma lem7594052 : term168 = True.
Proof. exact (TRANS (@lem7594047) (@lem7594051)). Qed.
Lemma lem7594053 : True = term168.
Proof. exact (SYM (@lem7594052)). Qed.
Lemma lem7594054 : term168.
Proof. exact (EQ_MP (@lem7594053) (@lem0)). Qed.
Lemma lem7594055 : term253.
Proof. exact (@lem7594044 (@lem7594054)). Qed.
Lemma lem7594057 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7594058 : term168 = term169.
Proof. exact (@lem7594057 (NUMERAL 0) term11). Qed.
Lemma lem7594059 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7594060 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7594061 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7594060 h1) (fun h1 : term169 = True => @lem7594059)). Qed.
Lemma lem7594062 : term169 = True.
Proof. exact (EQ_MP (@lem7594061) (@lem7594059)). Qed.
Lemma lem7594063 : term168 = True.
Proof. exact (TRANS (@lem7594058) (@lem7594062)). Qed.
Lemma lem7594064 : True = term168.
Proof. exact (SYM (@lem7594063)). Qed.
Lemma lem7594065 : term168.
Proof. exact (EQ_MP (@lem7594064) (@lem0)). Qed.
Lemma lem7594066 : term251 = term254.
Proof. exact (@lem7594055 (@lem7594065)). Qed.
Lemma lem7594068 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7594069 : term131 = term132.
Proof. exact (@lem7594068 term11 term11). Qed.
Lemma lem7594070 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7594071 : term134 = term11.
Proof. exact (EQ_MP (@lem7594070) (@lem940073)). Qed.
Lemma lem7594072 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7594073 : term132 = term74.
Proof. exact (MK_COMB (@lem7594072) (@lem7594071)). Qed.
Lemma lem7594074 : term131 = term74.
Proof. exact (TRANS (@lem7594069) (@lem7594073)). Qed.
Lemma lem7594076 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7594077 : term180 = term59.
Proof. exact (@lem7594076 term11). Qed.
Lemma lem7594078 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7594079 : term255 = term249.
Proof. exact (MK_COMB (@lem7594078) (@lem7594077)). Qed.
Lemma lem7594080 : term254 = term168.
Proof. exact (MK_COMB (@lem7594079) (@lem7594074)). Qed.
Lemma lem7594082 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7594083 : term168 = term169.
Proof. exact (@lem7594082 (NUMERAL 0) term11). Qed.
Lemma lem7594084 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7594085 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7594086 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7594085 h1) (fun h1 : term169 = True => @lem7594084)). Qed.
Lemma lem7594087 : term169 = True.
Proof. exact (EQ_MP (@lem7594086) (@lem7594084)). Qed.
Lemma lem7594088 : term168 = True.
Proof. exact (TRANS (@lem7594083) (@lem7594087)). Qed.
Lemma lem7594089 : term254 = True.
Proof. exact (TRANS (@lem7594080) (@lem7594088)). Qed.
Lemma lem7594090 : term251 = True.
Proof. exact (TRANS (@lem7594066) (@lem7594089)). Qed.
Lemma lem7594091 : term168 = True.
Proof. exact (TRANS (@lem7594043) (@lem7594090)). Qed.
Lemma lem7594092 : term248 = True.
Proof. exact (TRANS (@lem7594034) (@lem7594091)). Qed.
Lemma lem7594093 : True = term248.
Proof. exact (SYM (@lem7594092)). Qed.
Lemma lem7594094 : term248.
Proof. exact (EQ_MP (@lem7594093) (@lem0)). Qed.
Lemma lem7594095 (_97606 : int) (h1 : term247 _97606) : term262 _97606.
Proof. exact (conj (@lem7594094) (@lem7593957 _97606 h1)). Qed.
Lemma lem7594097 (x : real) (y : real) : term257 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7594098 (_97606 : int) : term263 _97606.
Proof. exact (@lem7594097 term74 (term162 _97606)). Qed.
Lemma lem7594099 (_97606 : int) (h1 : term247 _97606) : term264 _97606.
Proof. exact (@lem7594098 _97606 (@lem7594095 _97606 h1)). Qed.
Lemma lem7594100 (_97606 : int) : (term265 _97606) = (term162 _97606).
Proof. exact (@lem1982733 (term162 _97606)). Qed.
Lemma lem7594101 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7594102 (_97606 : int) : (term266 _97606) = (term185 _97606).
Proof. exact (MK_COMB (@lem7594101) (@lem7594100 _97606)). Qed.
Lemma lem7594103 : term59 = term59.
Proof. exact (eq_refl term59). Qed.
Lemma lem7594104 (_97606 : int) : (term264 _97606) = (term186 _97606).
Proof. exact (MK_COMB (@lem7594102 _97606) (@lem7594103)). Qed.
Lemma lem7594105 (_97606 : int) (h1 : term247 _97606) : term186 _97606.
Proof. exact (EQ_MP (@lem7594104 _97606) (@lem7594099 _97606 h1)). Qed.
Lemma lem7594106 (_97606 : int) (h1 : term247 _97606) : term235 _97606.
Proof. exact (conj (@lem7594105 _97606 h1) (@lem7594031 _97606 h1)). Qed.
Lemma lem7594108 (x : real) (y : real) : term267 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7594109 (_97606 : int) : term268 _97606.
Proof. exact (@lem7594108 (term162 _97606) (term193 _97606)). Qed.
Lemma lem7594110 (_97606 : int) (h1 : term247 _97606) : term269 _97606.
Proof. exact (@lem7594109 _97606 (@lem7594106 _97606 h1)). Qed.
Lemma lem7594111 (_97606 : int) : (term270 _97606) = (term271 _97606).
Proof. exact (@lem1982763 (term162 _97606) (real_of_int _97606) term122). Qed.
Lemma lem7594112 (_97606 : int) : (term272 _97606) = (term273 _97606).
Proof. exact (@lem1982713 term122 (real_of_int _97606)). Qed.
Lemma lem7594114 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7594115 : term74 = term148.
Proof. exact (@lem7594114 term11). Qed.
Lemma lem7594117 (x : nat) : (term120 x) = (term121 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7594118 : term122 = term123.
Proof. exact (@lem7594117 term11). Qed.
Lemma lem7594119 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7594120 : term274 = term275.
Proof. exact (MK_COMB (@lem7594119) (@lem7594118)). Qed.
Lemma lem7594121 : term276 = term277.
Proof. exact (MK_COMB (@lem7594120) (@lem7594115)). Qed.
Lemma lem7594122 : term278.
Proof. exact (@lem1981473 term122 term74 term74 term74 term59 term74). Qed.
Lemma lem7594124 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7594125 : term168 = term169.
Proof. exact (@lem7594124 (NUMERAL 0) term11). Qed.
Lemma lem7594126 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7594127 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7594128 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7594127 h1) (fun h1 : term169 = True => @lem7594126)). Qed.
Lemma lem7594129 : term169 = True.
Proof. exact (EQ_MP (@lem7594128) (@lem7594126)). Qed.
Lemma lem7594130 : term168 = True.
Proof. exact (TRANS (@lem7594125) (@lem7594129)). Qed.
Lemma lem7594131 : True = term168.
Proof. exact (SYM (@lem7594130)). Qed.
Lemma lem7594132 : term168.
Proof. exact (EQ_MP (@lem7594131) (@lem0)). Qed.
Lemma lem7594133 : term279.
Proof. exact (@lem7594122 (@lem7594132)). Qed.
Lemma lem7594135 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7594136 : term168 = term169.
Proof. exact (@lem7594135 (NUMERAL 0) term11). Qed.
Lemma lem7594137 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7594138 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7594139 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7594138 h1) (fun h1 : term169 = True => @lem7594137)). Qed.
Lemma lem7594140 : term169 = True.
Proof. exact (EQ_MP (@lem7594139) (@lem7594137)). Qed.
Lemma lem7594141 : term168 = True.
Proof. exact (TRANS (@lem7594136) (@lem7594140)). Qed.
Lemma lem7594142 : True = term168.
Proof. exact (SYM (@lem7594141)). Qed.
Lemma lem7594143 : term168.
Proof. exact (EQ_MP (@lem7594142) (@lem0)). Qed.
Lemma lem7594144 : term280.
Proof. exact (@lem7594133 (@lem7594143)). Qed.
Lemma lem7594146 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7594147 : term168 = term169.
Proof. exact (@lem7594146 (NUMERAL 0) term11). Qed.
Lemma lem7594148 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7594149 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7594150 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7594149 h1) (fun h1 : term169 = True => @lem7594148)). Qed.
Lemma lem7594151 : term169 = True.
Proof. exact (EQ_MP (@lem7594150) (@lem7594148)). Qed.
Lemma lem7594152 : term168 = True.
Proof. exact (TRANS (@lem7594147) (@lem7594151)). Qed.
Lemma lem7594153 : True = term168.
Proof. exact (SYM (@lem7594152)). Qed.
Lemma lem7594154 : term168.
Proof. exact (EQ_MP (@lem7594153) (@lem0)). Qed.
Lemma lem7594155 : term281.
Proof. exact (@lem7594144 (@lem7594154)). Qed.
Lemma lem7594157 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7594158 : term131 = term132.
Proof. exact (@lem7594157 term11 term11). Qed.
Lemma lem7594159 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7594160 : term134 = term11.
Proof. exact (EQ_MP (@lem7594159) (@lem940073)). Qed.
Lemma lem7594161 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7594162 : term132 = term74.
Proof. exact (MK_COMB (@lem7594161) (@lem7594160)). Qed.
Lemma lem7594163 : term131 = term74.
Proof. exact (TRANS (@lem7594158) (@lem7594162)). Qed.
Lemma lem7594165 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7594166 : term149 = term154.
Proof. exact (@lem7594165 term11 term11). Qed.
Lemma lem7594167 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7594168 : term134 = term11.
Proof. exact (EQ_MP (@lem7594167) (@lem940073)). Qed.
Lemma lem7594169 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7594170 : term132 = term74.
Proof. exact (MK_COMB (@lem7594169) (@lem7594168)). Qed.
Lemma lem7594171 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7594172 : term154 = term122.
Proof. exact (MK_COMB (@lem7594171) (@lem7594170)). Qed.
Lemma lem7594173 : term149 = term122.
Proof. exact (TRANS (@lem7594166) (@lem7594172)). Qed.
Lemma lem7594174 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7594175 : term282 = term274.
Proof. exact (MK_COMB (@lem7594174) (@lem7594173)). Qed.
Lemma lem7594176 : term283 = term276.
Proof. exact (MK_COMB (@lem7594175) (@lem7594163)). Qed.
Lemma lem7594178 (m : nat) : (term284 m) = term59.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7594179 : term276 = term59.
Proof. exact (@lem7594178 term11). Qed.
Lemma lem7594180 : term283 = term59.
Proof. exact (TRANS (@lem7594176) (@lem7594179)). Qed.
Lemma lem7594181 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7594182 : term285 = term178.
Proof. exact (MK_COMB (@lem7594181) (@lem7594180)). Qed.
Lemma lem7594183 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem7594184 : term286 = term180.
Proof. exact (MK_COMB (@lem7594182) (@lem7594183)). Qed.
Lemma lem7594186 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7594187 : term180 = term59.
Proof. exact (@lem7594186 term11). Qed.
Lemma lem7594188 : term286 = term59.
Proof. exact (TRANS (@lem7594184) (@lem7594187)). Qed.
Lemma lem7594190 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7594191 : term131 = term132.
Proof. exact (@lem7594190 term11 term11). Qed.
Lemma lem7594192 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7594193 : term134 = term11.
Proof. exact (EQ_MP (@lem7594192) (@lem940073)). Qed.
Lemma lem7594194 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7594195 : term132 = term74.
Proof. exact (MK_COMB (@lem7594194) (@lem7594193)). Qed.
Lemma lem7594196 : term131 = term74.
Proof. exact (TRANS (@lem7594191) (@lem7594195)). Qed.
Lemma lem7594197 : term178 = term178.
Proof. exact (eq_refl term178). Qed.
Lemma lem7594198 : term182 = term180.
Proof. exact (MK_COMB (@lem7594197) (@lem7594196)). Qed.
Lemma lem7594200 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7594201 : term180 = term59.
Proof. exact (@lem7594200 term11). Qed.
Lemma lem7594202 : term182 = term59.
Proof. exact (TRANS (@lem7594198) (@lem7594201)). Qed.
Lemma lem7594203 : term59 = term182.
Proof. exact (SYM (@lem7594202)). Qed.
Lemma lem7594204 : term286 = term182.
Proof. exact (TRANS (@lem7594188) (@lem7594203)). Qed.
Lemma lem7594205 : term277 = term119.
Proof. exact (@lem7594155 (@lem7594204)). Qed.
Lemma lem7594206 : term276 = term119.
Proof. exact (TRANS (@lem7594121) (@lem7594205)). Qed.
Lemma lem7594208 (x : real) : (term138 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7594209 : term119 = term59.
Proof. exact (@lem7594208 term59). Qed.
Lemma lem7594210 : term276 = term59.
Proof. exact (TRANS (@lem7594206) (@lem7594209)). Qed.
Lemma lem7594211 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7594212 : term287 = term178.
Proof. exact (MK_COMB (@lem7594211) (@lem7594210)). Qed.
Lemma lem7594213 (_97606 : int) : (real_of_int _97606) = (real_of_int _97606).
Proof. exact (eq_refl (real_of_int _97606)). Qed.
Lemma lem7594214 (_97606 : int) : (term273 _97606) = (term288 _97606).
Proof. exact (MK_COMB (@lem7594212) (@lem7594213 _97606)). Qed.
Lemma lem7594215 (_97606 : int) : (term272 _97606) = (term288 _97606).
Proof. exact (TRANS (@lem7594112 _97606) (@lem7594214 _97606)). Qed.
Lemma lem7594216 (_97606 : int) : (term288 _97606) = term59.
Proof. exact (@lem1982719 (real_of_int _97606)). Qed.
Lemma lem7594217 (_97606 : int) : (term272 _97606) = term59.
Proof. exact (TRANS (@lem7594215 _97606) (@lem7594216 _97606)). Qed.
Lemma lem7594218 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7594219 (_97606 : int) : (term289 _97606) = term101.
Proof. exact (MK_COMB (@lem7594218) (@lem7594217 _97606)). Qed.
Lemma lem7594220 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem7594221 (_97606 : int) : (term271 _97606) = term290.
Proof. exact (MK_COMB (@lem7594219 _97606) (@lem7594220)). Qed.
Lemma lem7594222 (_97606 : int) : (term270 _97606) = term290.
Proof. exact (TRANS (@lem7594111 _97606) (@lem7594221 _97606)). Qed.
Lemma lem7594223 : term290 = term122.
Proof. exact (@lem1982721 term122). Qed.
Lemma lem7594224 (_97606 : int) : (term270 _97606) = term122.
Proof. exact (TRANS (@lem7594222 _97606) (@lem7594223)). Qed.
Lemma lem7594225 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7594226 (_97606 : int) : (term291 _97606) = term292.
Proof. exact (MK_COMB (@lem7594225) (@lem7594224 _97606)). Qed.
Lemma lem7594227 : term59 = term59.
Proof. exact (eq_refl term59). Qed.
Lemma lem7594228 (_97606 : int) : (term269 _97606) = term293.
Proof. exact (MK_COMB (@lem7594226 _97606) (@lem7594227)). Qed.
Lemma lem7594229 (_97606 : int) (h1 : term247 _97606) : term293.
Proof. exact (EQ_MP (@lem7594228 _97606) (@lem7594110 _97606 h1)). Qed.
Lemma lem7594231 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7594232 : term293 = term294.
Proof. exact (@lem7594231 term59 term122). Qed.
Lemma lem7594234 (x : nat) : (term120 x) = (term121 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7594235 : term122 = term123.
Proof. exact (@lem7594234 term11). Qed.
Lemma lem7594237 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7594238 : term59 = term119.
Proof. exact (@lem7594237 (NUMERAL 0)). Qed.
Lemma lem7594239 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7594240 : term61 = term295.
Proof. exact (MK_COMB (@lem7594239) (@lem7594238)). Qed.
Lemma lem7594241 : term294 = term296.
Proof. exact (MK_COMB (@lem7594240) (@lem7594235)). Qed.
Lemma lem7594242 : term297.
Proof. exact (@lem1980026 term59 term74 term122 term74). Qed.
Lemma lem7594244 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7594245 : term168 = term169.
Proof. exact (@lem7594244 (NUMERAL 0) term11). Qed.
Lemma lem7594246 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7594247 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7594248 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7594247 h1) (fun h1 : term169 = True => @lem7594246)). Qed.
Lemma lem7594249 : term169 = True.
Proof. exact (EQ_MP (@lem7594248) (@lem7594246)). Qed.
Lemma lem7594250 : term168 = True.
Proof. exact (TRANS (@lem7594245) (@lem7594249)). Qed.
Lemma lem7594251 : True = term168.
Proof. exact (SYM (@lem7594250)). Qed.
Lemma lem7594252 : term168.
Proof. exact (EQ_MP (@lem7594251) (@lem0)). Qed.
Lemma lem7594253 : term298.
Proof. exact (@lem7594242 (@lem7594252)). Qed.
Lemma lem7594255 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7594256 : term168 = term169.
Proof. exact (@lem7594255 (NUMERAL 0) term11). Qed.
Lemma lem7594257 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7594258 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7594259 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7594258 h1) (fun h1 : term169 = True => @lem7594257)). Qed.
Lemma lem7594260 : term169 = True.
Proof. exact (EQ_MP (@lem7594259) (@lem7594257)). Qed.
Lemma lem7594261 : term168 = True.
Proof. exact (TRANS (@lem7594256) (@lem7594260)). Qed.
Lemma lem7594262 : True = term168.
Proof. exact (SYM (@lem7594261)). Qed.
Lemma lem7594263 : term168.
Proof. exact (EQ_MP (@lem7594262) (@lem0)). Qed.
Lemma lem7594264 : term296 = term299.
Proof. exact (@lem7594253 (@lem7594263)). Qed.
Lemma lem7594266 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7594267 : term149 = term154.
Proof. exact (@lem7594266 term11 term11). Qed.
Lemma lem7594268 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7594269 : term134 = term11.
Proof. exact (EQ_MP (@lem7594268) (@lem940073)). Qed.
Lemma lem7594270 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7594271 : term132 = term74.
Proof. exact (MK_COMB (@lem7594270) (@lem7594269)). Qed.
Lemma lem7594272 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7594273 : term154 = term122.
Proof. exact (MK_COMB (@lem7594272) (@lem7594271)). Qed.
Lemma lem7594274 : term149 = term122.
Proof. exact (TRANS (@lem7594267) (@lem7594273)). Qed.
Lemma lem7594276 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7594277 : term180 = term59.
Proof. exact (@lem7594276 term11). Qed.
Lemma lem7594278 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7594279 : term300 = term61.
Proof. exact (MK_COMB (@lem7594278) (@lem7594277)). Qed.
Lemma lem7594280 : term299 = term294.
Proof. exact (MK_COMB (@lem7594279) (@lem7594274)). Qed.
Lemma lem7594282 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7594283 : term294 = term303.
Proof. exact (@lem7594282 (NUMERAL 0) term11). Qed.
Lemma lem7594284 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7594285 (h1 : term170 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7594286 : (term170 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7594285 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem7594284)). Qed.
Lemma lem7594287 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7594286) (@lem7594284)). Qed.
Lemma lem7594288 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7594289 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7594290 : term304 = (and True).
Proof. exact (MK_COMB (@lem7594289) (@lem7594288)). Qed.
Lemma lem7594291 : term303 = (True /\ False).
Proof. exact (MK_COMB (@lem7594290) (@lem7594287)). Qed.
Lemma lem7594293 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7594294 : term303 = False.
Proof. exact (TRANS (@lem7594291) (@lem7594293)). Qed.
Lemma lem7594295 : term294 = False.
Proof. exact (TRANS (@lem7594283) (@lem7594294)). Qed.
Lemma lem7594296 : term299 = False.
Proof. exact (TRANS (@lem7594280) (@lem7594295)). Qed.
Lemma lem7594297 : term296 = False.
Proof. exact (TRANS (@lem7594264) (@lem7594296)). Qed.
Lemma lem7594298 : term294 = False.
Proof. exact (TRANS (@lem7594241) (@lem7594297)). Qed.
Lemma lem7594299 : term293 = False.
Proof. exact (TRANS (@lem7594232) (@lem7594298)). Qed.
Lemma lem7594300 (_97606 : int) (h1 : term247 _97606) : False.
Proof. exact (EQ_MP (@lem7594299) (@lem7594229 _97606 h1)). Qed.
Lemma lem7594301 (_97606 : int) (h1 : term305 _97606) : term305 _97606.
Proof. exact (h1). Qed.
Lemma lem7594302 (_97606 : int) (h1 : term305 _97606) : term236 _97606.
Proof. exact (proj2 (@lem7594301 _97606 h1)). Qed.
Lemma lem7594304 (_97606 : int) (h1 : term305 _97606) : term196 _97606.
Proof. exact (proj2 (@lem7594302 _97606 h1)). Qed.
Lemma lem7594305 (_97606 : int) (h1 : term305 _97606) : (real_of_int _97606) = term59.
Proof. exact (proj1 (@lem7594302 _97606 h1)). Qed.
Lemma lem7594307 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7594308 : term248 = term168.
Proof. exact (@lem7594307 term59 term74). Qed.
Lemma lem7594310 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7594311 : term74 = term148.
Proof. exact (@lem7594310 term11). Qed.
Lemma lem7594313 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7594314 : term59 = term119.
Proof. exact (@lem7594313 (NUMERAL 0)). Qed.
Lemma lem7594315 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7594316 : term249 = term250.
Proof. exact (MK_COMB (@lem7594315) (@lem7594314)). Qed.
Lemma lem7594317 : term168 = term251.
Proof. exact (MK_COMB (@lem7594316) (@lem7594311)). Qed.
Lemma lem7594318 : term252.
Proof. exact (@lem1980255 term59 term74 term74 term74). Qed.
Lemma lem7594320 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7594321 : term168 = term169.
Proof. exact (@lem7594320 (NUMERAL 0) term11). Qed.
Lemma lem7594322 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7594323 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7594324 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7594323 h1) (fun h1 : term169 = True => @lem7594322)). Qed.
Lemma lem7594325 : term169 = True.
Proof. exact (EQ_MP (@lem7594324) (@lem7594322)). Qed.
Lemma lem7594326 : term168 = True.
Proof. exact (TRANS (@lem7594321) (@lem7594325)). Qed.
Lemma lem7594327 : True = term168.
Proof. exact (SYM (@lem7594326)). Qed.
Lemma lem7594328 : term168.
Proof. exact (EQ_MP (@lem7594327) (@lem0)). Qed.
Lemma lem7594329 : term253.
Proof. exact (@lem7594318 (@lem7594328)). Qed.
Lemma lem7594331 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7594332 : term168 = term169.
Proof. exact (@lem7594331 (NUMERAL 0) term11). Qed.
Lemma lem7594333 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7594334 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7594335 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7594334 h1) (fun h1 : term169 = True => @lem7594333)). Qed.
Lemma lem7594336 : term169 = True.
Proof. exact (EQ_MP (@lem7594335) (@lem7594333)). Qed.
Lemma lem7594337 : term168 = True.
Proof. exact (TRANS (@lem7594332) (@lem7594336)). Qed.
Lemma lem7594338 : True = term168.
Proof. exact (SYM (@lem7594337)). Qed.
Lemma lem7594339 : term168.
Proof. exact (EQ_MP (@lem7594338) (@lem0)). Qed.
Lemma lem7594340 : term251 = term254.
Proof. exact (@lem7594329 (@lem7594339)). Qed.
Lemma lem7594342 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7594343 : term131 = term132.
Proof. exact (@lem7594342 term11 term11). Qed.
Lemma lem7594344 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7594345 : term134 = term11.
Proof. exact (EQ_MP (@lem7594344) (@lem940073)). Qed.
Lemma lem7594346 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7594347 : term132 = term74.
Proof. exact (MK_COMB (@lem7594346) (@lem7594345)). Qed.
Lemma lem7594348 : term131 = term74.
Proof. exact (TRANS (@lem7594343) (@lem7594347)). Qed.
Lemma lem7594350 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7594351 : term180 = term59.
Proof. exact (@lem7594350 term11). Qed.
Lemma lem7594352 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7594353 : term255 = term249.
Proof. exact (MK_COMB (@lem7594352) (@lem7594351)). Qed.
Lemma lem7594354 : term254 = term168.
Proof. exact (MK_COMB (@lem7594353) (@lem7594348)). Qed.
Lemma lem7594356 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7594357 : term168 = term169.
Proof. exact (@lem7594356 (NUMERAL 0) term11). Qed.
Lemma lem7594358 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7594359 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7594360 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7594359 h1) (fun h1 : term169 = True => @lem7594358)). Qed.
Lemma lem7594361 : term169 = True.
Proof. exact (EQ_MP (@lem7594360) (@lem7594358)). Qed.
Lemma lem7594362 : term168 = True.
Proof. exact (TRANS (@lem7594357) (@lem7594361)). Qed.
Lemma lem7594363 : term254 = True.
Proof. exact (TRANS (@lem7594354) (@lem7594362)). Qed.
Lemma lem7594364 : term251 = True.
Proof. exact (TRANS (@lem7594340) (@lem7594363)). Qed.
Lemma lem7594365 : term168 = True.
Proof. exact (TRANS (@lem7594317) (@lem7594364)). Qed.
Lemma lem7594366 : term248 = True.
Proof. exact (TRANS (@lem7594308) (@lem7594365)). Qed.
Lemma lem7594367 : True = term248.
Proof. exact (SYM (@lem7594366)). Qed.
Lemma lem7594368 : term248.
Proof. exact (EQ_MP (@lem7594367) (@lem0)). Qed.
Lemma lem7594369 (_97606 : int) (h1 : term305 _97606) : term256 _97606.
Proof. exact (conj (@lem7594368) (@lem7594304 _97606 h1)). Qed.
Lemma lem7594371 (x : real) (y : real) : term257 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7594372 (_97606 : int) : term258 _97606.
Proof. exact (@lem7594371 term74 (term193 _97606)). Qed.
Lemma lem7594373 (_97606 : int) (h1 : term305 _97606) : term259 _97606.
Proof. exact (@lem7594372 _97606 (@lem7594369 _97606 h1)). Qed.
Lemma lem7594374 (_97606 : int) : (term260 _97606) = (term193 _97606).
Proof. exact (@lem1982733 (term193 _97606)). Qed.
Lemma lem7594375 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7594376 (_97606 : int) : (term261 _97606) = (term195 _97606).
Proof. exact (MK_COMB (@lem7594375) (@lem7594374 _97606)). Qed.
Lemma lem7594377 : term59 = term59.
Proof. exact (eq_refl term59). Qed.
Lemma lem7594378 (_97606 : int) : (term259 _97606) = (term196 _97606).
Proof. exact (MK_COMB (@lem7594376 _97606) (@lem7594377)). Qed.
Lemma lem7594379 (_97606 : int) (h1 : term305 _97606) : term196 _97606.
Proof. exact (EQ_MP (@lem7594378 _97606) (@lem7594373 _97606 h1)). Qed.
Lemma lem7594381 (y : real) : term306 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem7594382 (_97606 : int) : term307 _97606.
Proof. exact (@lem7594381 (real_of_int _97606)). Qed.
Lemma lem7594383 (_97606 : int) (h1 : term305 _97606) : term308 _97606.
Proof. exact (@lem7594382 _97606 (@lem7594305 _97606 h1)). Qed.
Lemma lem7594384 (_97606 : int) (h1 : term305 _97606) : term309 _97606.
Proof. exact (@lem7594383 _97606 h1 term122). Qed.
Lemma lem7594385 (_97606 : int) : (term309 _97606) = ((term162 _97606) = term59).
Proof. exact (eq_refl (term309 _97606)). Qed.
Lemma lem7594392 (_97606 : int) (h1 : term305 _97606) : (term162 _97606) = term59.
Proof. exact (EQ_MP (@lem7594385 _97606) (@lem7594384 _97606 h1)). Qed.
Lemma lem7594393 (_97606 : int) (h1 : term305 _97606) : term310 _97606.
Proof. exact (conj (@lem7594392 _97606 h1) (@lem7594379 _97606 h1)). Qed.
Lemma lem7594395 (x : real) (y : real) : term311 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem7594396 (_97606 : int) : term312 _97606.
Proof. exact (@lem7594395 (term162 _97606) (term193 _97606)). Qed.
Lemma lem7594397 (_97606 : int) (h1 : term305 _97606) : term269 _97606.
Proof. exact (@lem7594396 _97606 (@lem7594393 _97606 h1)). Qed.
Lemma lem7594398 (_97606 : int) : (term270 _97606) = (term271 _97606).
Proof. exact (@lem1982763 (term162 _97606) (real_of_int _97606) term122). Qed.
Lemma lem7594399 (_97606 : int) : (term272 _97606) = (term273 _97606).
Proof. exact (@lem1982713 term122 (real_of_int _97606)). Qed.
Lemma lem7594401 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7594402 : term74 = term148.
Proof. exact (@lem7594401 term11). Qed.
Lemma lem7594404 (x : nat) : (term120 x) = (term121 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7594405 : term122 = term123.
Proof. exact (@lem7594404 term11). Qed.
Lemma lem7594406 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7594407 : term274 = term275.
Proof. exact (MK_COMB (@lem7594406) (@lem7594405)). Qed.
Lemma lem7594408 : term276 = term277.
Proof. exact (MK_COMB (@lem7594407) (@lem7594402)). Qed.
Lemma lem7594409 : term278.
Proof. exact (@lem1981473 term122 term74 term74 term74 term59 term74). Qed.
Lemma lem7594411 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7594412 : term168 = term169.
Proof. exact (@lem7594411 (NUMERAL 0) term11). Qed.
Lemma lem7594413 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7594414 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7594415 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7594414 h1) (fun h1 : term169 = True => @lem7594413)). Qed.
Lemma lem7594416 : term169 = True.
Proof. exact (EQ_MP (@lem7594415) (@lem7594413)). Qed.
Lemma lem7594417 : term168 = True.
Proof. exact (TRANS (@lem7594412) (@lem7594416)). Qed.
Lemma lem7594418 : True = term168.
Proof. exact (SYM (@lem7594417)). Qed.
Lemma lem7594419 : term168.
Proof. exact (EQ_MP (@lem7594418) (@lem0)). Qed.
Lemma lem7594420 : term279.
Proof. exact (@lem7594409 (@lem7594419)). Qed.
Lemma lem7594422 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7594423 : term168 = term169.
Proof. exact (@lem7594422 (NUMERAL 0) term11). Qed.
Lemma lem7594424 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7594425 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7594426 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7594425 h1) (fun h1 : term169 = True => @lem7594424)). Qed.
Lemma lem7594427 : term169 = True.
Proof. exact (EQ_MP (@lem7594426) (@lem7594424)). Qed.
Lemma lem7594428 : term168 = True.
Proof. exact (TRANS (@lem7594423) (@lem7594427)). Qed.
Lemma lem7594429 : True = term168.
Proof. exact (SYM (@lem7594428)). Qed.
Lemma lem7594430 : term168.
Proof. exact (EQ_MP (@lem7594429) (@lem0)). Qed.
Lemma lem7594431 : term280.
Proof. exact (@lem7594420 (@lem7594430)). Qed.
Lemma lem7594433 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7594434 : term168 = term169.
Proof. exact (@lem7594433 (NUMERAL 0) term11). Qed.
Lemma lem7594435 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7594436 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7594437 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7594436 h1) (fun h1 : term169 = True => @lem7594435)). Qed.
Lemma lem7594438 : term169 = True.
Proof. exact (EQ_MP (@lem7594437) (@lem7594435)). Qed.
Lemma lem7594439 : term168 = True.
Proof. exact (TRANS (@lem7594434) (@lem7594438)). Qed.
Lemma lem7594440 : True = term168.
Proof. exact (SYM (@lem7594439)). Qed.
Lemma lem7594441 : term168.
Proof. exact (EQ_MP (@lem7594440) (@lem0)). Qed.
Lemma lem7594442 : term281.
Proof. exact (@lem7594431 (@lem7594441)). Qed.
Lemma lem7594444 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7594445 : term131 = term132.
Proof. exact (@lem7594444 term11 term11). Qed.
Lemma lem7594446 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7594447 : term134 = term11.
Proof. exact (EQ_MP (@lem7594446) (@lem940073)). Qed.
Lemma lem7594448 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7594449 : term132 = term74.
Proof. exact (MK_COMB (@lem7594448) (@lem7594447)). Qed.
Lemma lem7594450 : term131 = term74.
Proof. exact (TRANS (@lem7594445) (@lem7594449)). Qed.
Lemma lem7594452 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7594453 : term149 = term154.
Proof. exact (@lem7594452 term11 term11). Qed.
Lemma lem7594454 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7594455 : term134 = term11.
Proof. exact (EQ_MP (@lem7594454) (@lem940073)). Qed.
Lemma lem7594456 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7594457 : term132 = term74.
Proof. exact (MK_COMB (@lem7594456) (@lem7594455)). Qed.
Lemma lem7594458 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7594459 : term154 = term122.
Proof. exact (MK_COMB (@lem7594458) (@lem7594457)). Qed.
Lemma lem7594460 : term149 = term122.
Proof. exact (TRANS (@lem7594453) (@lem7594459)). Qed.
Lemma lem7594461 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7594462 : term282 = term274.
Proof. exact (MK_COMB (@lem7594461) (@lem7594460)). Qed.
Lemma lem7594463 : term283 = term276.
Proof. exact (MK_COMB (@lem7594462) (@lem7594450)). Qed.
Lemma lem7594465 (m : nat) : (term284 m) = term59.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7594466 : term276 = term59.
Proof. exact (@lem7594465 term11). Qed.
Lemma lem7594467 : term283 = term59.
Proof. exact (TRANS (@lem7594463) (@lem7594466)). Qed.
Lemma lem7594468 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7594469 : term285 = term178.
Proof. exact (MK_COMB (@lem7594468) (@lem7594467)). Qed.
Lemma lem7594470 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem7594471 : term286 = term180.
Proof. exact (MK_COMB (@lem7594469) (@lem7594470)). Qed.
Lemma lem7594473 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7594474 : term180 = term59.
Proof. exact (@lem7594473 term11). Qed.
Lemma lem7594475 : term286 = term59.
Proof. exact (TRANS (@lem7594471) (@lem7594474)). Qed.
Lemma lem7594477 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7594478 : term131 = term132.
Proof. exact (@lem7594477 term11 term11). Qed.
Lemma lem7594479 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7594480 : term134 = term11.
Proof. exact (EQ_MP (@lem7594479) (@lem940073)). Qed.
Lemma lem7594481 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7594482 : term132 = term74.
Proof. exact (MK_COMB (@lem7594481) (@lem7594480)). Qed.
Lemma lem7594483 : term131 = term74.
Proof. exact (TRANS (@lem7594478) (@lem7594482)). Qed.
Lemma lem7594484 : term178 = term178.
Proof. exact (eq_refl term178). Qed.
Lemma lem7594485 : term182 = term180.
Proof. exact (MK_COMB (@lem7594484) (@lem7594483)). Qed.
Lemma lem7594487 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7594488 : term180 = term59.
Proof. exact (@lem7594487 term11). Qed.
Lemma lem7594489 : term182 = term59.
Proof. exact (TRANS (@lem7594485) (@lem7594488)). Qed.
Lemma lem7594490 : term59 = term182.
Proof. exact (SYM (@lem7594489)). Qed.
Lemma lem7594491 : term286 = term182.
Proof. exact (TRANS (@lem7594475) (@lem7594490)). Qed.
Lemma lem7594492 : term277 = term119.
Proof. exact (@lem7594442 (@lem7594491)). Qed.
Lemma lem7594493 : term276 = term119.
Proof. exact (TRANS (@lem7594408) (@lem7594492)). Qed.
Lemma lem7594495 (x : real) : (term138 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7594496 : term119 = term59.
Proof. exact (@lem7594495 term59). Qed.
Lemma lem7594497 : term276 = term59.
Proof. exact (TRANS (@lem7594493) (@lem7594496)). Qed.
Lemma lem7594498 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7594499 : term287 = term178.
Proof. exact (MK_COMB (@lem7594498) (@lem7594497)). Qed.
Lemma lem7594500 (_97606 : int) : (real_of_int _97606) = (real_of_int _97606).
Proof. exact (eq_refl (real_of_int _97606)). Qed.
Lemma lem7594501 (_97606 : int) : (term273 _97606) = (term288 _97606).
Proof. exact (MK_COMB (@lem7594499) (@lem7594500 _97606)). Qed.
Lemma lem7594502 (_97606 : int) : (term272 _97606) = (term288 _97606).
Proof. exact (TRANS (@lem7594399 _97606) (@lem7594501 _97606)). Qed.
Lemma lem7594503 (_97606 : int) : (term288 _97606) = term59.
Proof. exact (@lem1982719 (real_of_int _97606)). Qed.
Lemma lem7594504 (_97606 : int) : (term272 _97606) = term59.
Proof. exact (TRANS (@lem7594502 _97606) (@lem7594503 _97606)). Qed.
Lemma lem7594505 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7594506 (_97606 : int) : (term289 _97606) = term101.
Proof. exact (MK_COMB (@lem7594505) (@lem7594504 _97606)). Qed.
Lemma lem7594507 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem7594508 (_97606 : int) : (term271 _97606) = term290.
Proof. exact (MK_COMB (@lem7594506 _97606) (@lem7594507)). Qed.
Lemma lem7594509 (_97606 : int) : (term270 _97606) = term290.
Proof. exact (TRANS (@lem7594398 _97606) (@lem7594508 _97606)). Qed.
Lemma lem7594510 : term290 = term122.
Proof. exact (@lem1982721 term122). Qed.
Lemma lem7594511 (_97606 : int) : (term270 _97606) = term122.
Proof. exact (TRANS (@lem7594509 _97606) (@lem7594510)). Qed.
Lemma lem7594512 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7594513 (_97606 : int) : (term291 _97606) = term292.
Proof. exact (MK_COMB (@lem7594512) (@lem7594511 _97606)). Qed.
Lemma lem7594514 : term59 = term59.
Proof. exact (eq_refl term59). Qed.
Lemma lem7594515 (_97606 : int) : (term269 _97606) = term293.
Proof. exact (MK_COMB (@lem7594513 _97606) (@lem7594514)). Qed.
Lemma lem7594516 (_97606 : int) (h1 : term305 _97606) : term293.
Proof. exact (EQ_MP (@lem7594515 _97606) (@lem7594397 _97606 h1)). Qed.
Lemma lem7594518 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7594519 : term293 = term294.
Proof. exact (@lem7594518 term59 term122). Qed.
Lemma lem7594521 (x : nat) : (term120 x) = (term121 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7594522 : term122 = term123.
Proof. exact (@lem7594521 term11). Qed.
Lemma lem7594524 (x : nat) : (real_of_num x) = (term118 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7594525 : term59 = term119.
Proof. exact (@lem7594524 (NUMERAL 0)). Qed.
Lemma lem7594526 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7594527 : term61 = term295.
Proof. exact (MK_COMB (@lem7594526) (@lem7594525)). Qed.
Lemma lem7594528 : term294 = term296.
Proof. exact (MK_COMB (@lem7594527) (@lem7594522)). Qed.
Lemma lem7594529 : term297.
Proof. exact (@lem1980026 term59 term74 term122 term74). Qed.
Lemma lem7594531 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7594532 : term168 = term169.
Proof. exact (@lem7594531 (NUMERAL 0) term11). Qed.
Lemma lem7594533 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7594534 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7594535 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7594534 h1) (fun h1 : term169 = True => @lem7594533)). Qed.
Lemma lem7594536 : term169 = True.
Proof. exact (EQ_MP (@lem7594535) (@lem7594533)). Qed.
Lemma lem7594537 : term168 = True.
Proof. exact (TRANS (@lem7594532) (@lem7594536)). Qed.
Lemma lem7594538 : True = term168.
Proof. exact (SYM (@lem7594537)). Qed.
Lemma lem7594539 : term168.
Proof. exact (EQ_MP (@lem7594538) (@lem0)). Qed.
Lemma lem7594540 : term298.
Proof. exact (@lem7594529 (@lem7594539)). Qed.
Lemma lem7594542 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7594543 : term168 = term169.
Proof. exact (@lem7594542 (NUMERAL 0) term11). Qed.
Lemma lem7594544 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7594545 (h1 : term170 = (BIT1 0)) : term169 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7594546 : (term170 = (BIT1 0)) = (term169 = True).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7594545 h1) (fun h1 : term169 = True => @lem7594544)). Qed.
Lemma lem7594547 : term169 = True.
Proof. exact (EQ_MP (@lem7594546) (@lem7594544)). Qed.
Lemma lem7594548 : term168 = True.
Proof. exact (TRANS (@lem7594543) (@lem7594547)). Qed.
Lemma lem7594549 : True = term168.
Proof. exact (SYM (@lem7594548)). Qed.
Lemma lem7594550 : term168.
Proof. exact (EQ_MP (@lem7594549) (@lem0)). Qed.
Lemma lem7594551 : term296 = term299.
Proof. exact (@lem7594540 (@lem7594550)). Qed.
Lemma lem7594553 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7594554 : term149 = term154.
Proof. exact (@lem7594553 term11 term11). Qed.
Lemma lem7594555 : (term133 = (BIT1 0)) = (term134 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7594556 : term134 = term11.
Proof. exact (EQ_MP (@lem7594555) (@lem940073)). Qed.
Lemma lem7594557 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7594558 : term132 = term74.
Proof. exact (MK_COMB (@lem7594557) (@lem7594556)). Qed.
Lemma lem7594559 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7594560 : term154 = term122.
Proof. exact (MK_COMB (@lem7594559) (@lem7594558)). Qed.
Lemma lem7594561 : term149 = term122.
Proof. exact (TRANS (@lem7594554) (@lem7594560)). Qed.
Lemma lem7594563 (x : nat) : (term181 x) = term59.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7594564 : term180 = term59.
Proof. exact (@lem7594563 term11). Qed.
Lemma lem7594565 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7594566 : term300 = term61.
Proof. exact (MK_COMB (@lem7594565) (@lem7594564)). Qed.
Lemma lem7594567 : term299 = term294.
Proof. exact (MK_COMB (@lem7594566) (@lem7594561)). Qed.
Lemma lem7594569 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7594570 : term294 = term303.
Proof. exact (@lem7594569 (NUMERAL 0) term11). Qed.
Lemma lem7594571 : term170 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7594572 (h1 : term170 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7594573 : (term170 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term170 = (BIT1 0) => @lem7594572 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem7594571)). Qed.
Lemma lem7594574 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7594573) (@lem7594571)). Qed.
Lemma lem7594575 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7594576 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7594577 : term304 = (and True).
Proof. exact (MK_COMB (@lem7594576) (@lem7594575)). Qed.
Lemma lem7594578 : term303 = (True /\ False).
Proof. exact (MK_COMB (@lem7594577) (@lem7594574)). Qed.
Lemma lem7594580 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7594581 : term303 = False.
Proof. exact (TRANS (@lem7594578) (@lem7594580)). Qed.
Lemma lem7594582 : term294 = False.
Proof. exact (TRANS (@lem7594570) (@lem7594581)). Qed.
Lemma lem7594583 : term299 = False.
Proof. exact (TRANS (@lem7594567) (@lem7594582)). Qed.
Lemma lem7594584 : term296 = False.
Proof. exact (TRANS (@lem7594551) (@lem7594583)). Qed.
Lemma lem7594585 : term294 = False.
Proof. exact (TRANS (@lem7594528) (@lem7594584)). Qed.
Lemma lem7594586 : term293 = False.
Proof. exact (TRANS (@lem7594519) (@lem7594585)). Qed.
Lemma lem7594587 (_97606 : int) (h1 : term305 _97606) : False.
Proof. exact (EQ_MP (@lem7594586) (@lem7594516 _97606 h1)). Qed.
Lemma lem7594588 (_97606 : int) (h1 : term234 _97606) : False.
Proof. exact (or_elim (@lem7593952 _97606 h1) (fun h0 : term247 _97606 => @lem7594300 _97606 h0) (fun h0 : term305 _97606 => @lem7594587 _97606 h0)). Qed.
Lemma lem7594589 (_97606 : int) (h1 : term243 _97606) : False.
Proof. exact (or_elim (@lem7593314 _97606 h1) (fun h0 : term238 _97606 => @lem7593951 _97606 h0) (fun h0 : term234 _97606 => @lem7594588 _97606 h0)). Qed.
Lemma lem7594590 (_97606 : int) (h1 : term246 _97606) : False.
Proof. exact (or_elim (@lem7592676 _97606 h1) (fun h0 : term234 _97606 => @lem7593313 _97606 h0) (fun h0 : term243 _97606 => @lem7594589 _97606 h0)). Qed.
Lemma lem7594592 (_97606 : int) (h1 : term246 _97606) : term246 _97606.
Proof. exact (h1). Qed.
Lemma lem7594593 (_97606 : int) (h1 : term246 _97606) : (term246 _97606) = False.
Proof. exact (prop_ext (fun h2 : term246 _97606 => @lem7594590 _97606 h1) (fun h2 : False => @lem7594592 _97606 h1)). Qed.
Lemma lem7594594 (_97606 : int) (h1 : term246 _97606) : False.
Proof. exact (EQ_MP (@lem7594593 _97606 h1) (@lem7594592 _97606 h1)). Qed.
Lemma lem7594595 (_97606 : int) (h1 : term114 _97606) : term114 _97606.
Proof. exact (h1). Qed.
Lemma lem7594596 (_97606 : int) (h1 : term114 _97606) : term246 _97606.
Proof. exact (EQ_MP (@lem7592642 _97606) (@lem7594595 _97606 h1)). Qed.
Lemma lem7594597 (_97606 : int) (h1 : term114 _97606) : (term246 _97606) = False.
Proof. exact (prop_ext (fun h2 : term246 _97606 => @lem7594594 _97606 h2) (fun h2 : False => @lem7594596 _97606 h1)). Qed.
Lemma lem7594598 (_97606 : int) (h1 : term114 _97606) : False.
Proof. exact (EQ_MP (@lem7594597 _97606 h1) (@lem7594596 _97606 h1)). Qed.
Lemma lem7594599 (_97606 : int) : term339 _97606.
Proof. exact (fun h0 : term114 _97606 => @lem7594598 _97606 h0). Qed.
Lemma lem7594600 (_97606 : int) : term340 _97606.
Proof. exact (@lem1386578 (term341 _97606)). Qed.
Lemma lem7594603 (_97606 : int) : term341 _97606.
Proof. exact (@lem7594600 _97606 (@lem7594599 _97606)). Qed.
Lemma lem7594604 (_97606 : int) : (term112 _97606) = (term52 _97606).
Proof. exact (SYM (@lem7592025 _97606)). Qed.
Lemma lem7594605 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7594606 (_97606 : int) : (term341 _97606) = (term26 _97606).
Proof. exact (MK_COMB (@lem7594605) (@lem7594604 _97606)). Qed.
Lemma lem7594607 (_97606 : int) : term26 _97606.
Proof. exact (EQ_MP (@lem7594606 _97606) (@lem7594603 _97606)). Qed.
Lemma lem7594608 (_97606 : int) : term27 _97606.
Proof. exact (EQ_MP (@lem7591838 _97606) (@lem7594607 _97606)). Qed.
Lemma lem7594609 (x : nat) : term342 x.
Proof. exact (@lem7594608 (int_of_num x)). Qed.
Lemma lem7594610 (x : nat) : term23 x.
Proof. exact (@lem7594609 x (@lem7591837 x)). Qed.
Lemma lem7594611 (x : nat) : (term23 x) = ((term7 x) = (term8 x)).
Proof. exact (SYM (@lem7591834 x)). Qed.
Lemma lem7594613 {A : Type'} (s : A -> Prop) : term343 A s.
Proof. exact (@lem7591719 A s). Qed.
Lemma lem7594614 {A : Type'} (s : A -> Prop) : (term343 A s) = (term344 A s).
Proof. exact (eq_refl (term343 A s)). Qed.
Lemma lem7594615 {A : Type'} (s : A -> Prop) : term344 A s.
Proof. exact (EQ_MP (@lem7594614 A s) (@lem7594613 A s)). Qed.
Lemma lem7594616 {A : Type'} (s : A -> Prop) : term345 A s.
Proof. exact (@lem82 ((@dimindex A s) = (NUMERAL 0))). Qed.
Lemma lem7594634 (x : nat) : (term7 x) = (term8 x).
Proof. exact (EQ_MP (@lem7594611 x) (@lem7594610 x)). Qed.
Lemma lem7594635 {A : Type'} (s : A -> Prop) : (term346 A s) = (term344 A s).
Proof. exact (@lem7594634 (@dimindex A s)). Qed.
Lemma lem7594637 {A : Type'} (s : A -> Prop) : ((@dimindex A s) = (NUMERAL 0)) = False.
Proof. exact (@lem7594616 A s (@lem7594615 A s)). Qed.
Lemma lem7594638 {A : Type'} (s : A -> Prop) : ((@dimindex A s) = (NUMERAL 0)) = False.
Proof. exact (@lem7594637 A s). Qed.
Lemma lem7594639 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7594640 {A : Type'} (s : A -> Prop) : (term344 A s) = (~ False).
Proof. exact (MK_COMB (@lem7594639) (@lem7594638 A s)). Qed.
Lemma lem7594642 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem7594643 {A : Type'} (s : A -> Prop) : (term344 A s) = True.
Proof. exact (TRANS (@lem7594640 A s) (@lem7594642)). Qed.
Lemma lem7594644 {A : Type'} (s : A -> Prop) : (term346 A s) = True.
Proof. exact (TRANS (@lem7594635 A s) (@lem7594643 A s)). Qed.
Lemma lem7594645 {A : Type'} : (term347 A) = (term348 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7594644 A s)). Qed.
Lemma lem7594646 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7594647 {A : Type'} : (term349 A) = (term350 A).
Proof. exact (MK_COMB (@lem7594646 A) (@lem7594645 A)). Qed.
Lemma lem7594649 {A : Type'} (t : Prop) : (term351 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7594650 {A : Type'} (t : Prop) : (term352 A t) = t.
Proof. exact (@lem7594649 (A -> Prop) t). Qed.
Lemma lem7594651 {A : Type'} : (term350 A) = True.
Proof. exact (@lem7594650 A True). Qed.
Lemma lem7594652 {A : Type'} : (term349 A) = True.
Proof. exact (TRANS (@lem7594647 A) (@lem7594651 A)). Qed.
Lemma lem7594653 {A : Type'} : True = (term349 A).
Proof. exact (SYM (@lem7594652 A)). Qed.
Lemma lem7594654 {A : Type'} : term349 A.
Proof. exact (EQ_MP (@lem7594653 A) (@lem0)). Qed.
