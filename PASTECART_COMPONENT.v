Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PASTECART_COMPONENT_term_abbrevs.
Require Import INT_POS_spec.
Require Import LAMBDA_BETA_spec.
Require Import pastecart_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1032098_spec.
Require Import thm1032781_spec.
Require Import thm12653_spec.
Require Import thm13473_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
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
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988293_spec.
Require Import thm1988332_spec.
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
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841401_spec.
Require Import thm2841402_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm2841413_spec.
Require Import thm2841414_spec.
Require Import thm7_spec.
Require Import thm7640410_spec.
Require Import thm7640437_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem7664795 {M : Type'} (i : nat) : (term0 M i) = (term1 M i).
Proof. exact (@lem17265 (term2 M i) (term3 i)). Qed.
Lemma lem7664797 (m : nat) (n : nat) : (Peano.le m n) = (term4 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7664798 {M : Type'} (i : nat) : (term2 M i) = (term5 M i).
Proof. exact (@lem7664797 (term6 M) i). Qed.
Lemma lem7664800 (m : nat) (n : nat) : (term7 m n) = (term8 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7664801 {M : Type'} : (term9 M) = (term10 M).
Proof. exact (@lem7664800 (@dimindex M (@UNIV M)) term11). Qed.
Lemma lem7664802 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem7664803 {M : Type'} : (term12 M) = (term13 M).
Proof. exact (MK_COMB (@lem7664802) (@lem7664801 M)). Qed.
Lemma lem7664804 (i : nat) : (int_of_num i) = (int_of_num i).
Proof. exact (eq_refl (int_of_num i)). Qed.
Lemma lem7664805 {M : Type'} (i : nat) : (term5 M i) = (term14 M i).
Proof. exact (MK_COMB (@lem7664803 M) (@lem7664804 i)). Qed.
Lemma lem7664806 {M : Type'} (i : nat) : (term2 M i) = (term14 M i).
Proof. exact (TRANS (@lem7664798 M i) (@lem7664805 M i)). Qed.
Lemma lem7664807 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7664808 {M : Type'} (i : nat) : (term15 M i) = (term16 M i).
Proof. exact (MK_COMB (@lem7664807) (@lem7664806 M i)). Qed.
Lemma lem7664809 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7664810 {M : Type'} (i : nat) : (term17 M i) = (term18 M i).
Proof. exact (MK_COMB (@lem7664809) (@lem7664808 M i)). Qed.
Lemma lem7664812 (m : nat) (n : nat) : (Peano.le m n) = (term4 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7664813 (i : nat) : (term3 i) = (term19 i).
Proof. exact (@lem7664812 term11 i). Qed.
Lemma lem7664814 {M : Type'} (i : nat) : (term1 M i) = (term20 M i).
Proof. exact (MK_COMB (@lem7664810 M i) (@lem7664813 i)). Qed.
Lemma lem7664815 {M : Type'} (i : nat) : (term0 M i) = (term20 M i).
Proof. exact (TRANS (@lem7664795 M i) (@lem7664814 M i)). Qed.
Lemma lem7664816 (i : nat) : term21 i.
Proof. exact (@lem2307535 i). Qed.
Lemma lem7664817 (i : nat) : (term21 i) = (term22 i).
Proof. exact (eq_refl (term21 i)). Qed.
Lemma lem7664818 (i : nat) : term22 i.
Proof. exact (EQ_MP (@lem7664817 i) (@lem7664816 i)). Qed.
Lemma lem7664819 {M : Type'} : term23 M.
Proof. exact (@lem2307535 (@dimindex M (@UNIV M))). Qed.
Lemma lem7664820 {M : Type'} : (term23 M) = (term24 M).
Proof. exact (eq_refl (term23 M)). Qed.
Lemma lem7664821 {M : Type'} : term24 M.
Proof. exact (EQ_MP (@lem7664820 M) (@lem7664819 M)). Qed.
Lemma lem7664822 (_98770 : int) (_98769 : int) : (term25 _98770 _98769) = (term26 _98770 _98769).
Proof. exact (@lem2318604 (term26 _98770 _98769)). Qed.
Lemma lem7664838 (_98770 : int) (_98769 : int) : (term27 _98770 _98769) = (term28 _98770 _98769).
Proof. exact (@lem16933 (term28 _98770 _98769)). Qed.
Lemma lem7664839 (_98769 : int) : (term29 _98769) = (term29 _98769).
Proof. exact (eq_refl (term29 _98769)). Qed.
Lemma lem7664840 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7664841 (_98770 : int) (_98769 : int) : (term30 _98770 _98769) = (term31 _98770 _98769).
Proof. exact (MK_COMB (@lem7664840) (@lem7664838 _98770 _98769)). Qed.
Lemma lem7664842 (_98770 : int) (_98769 : int) : (term32 _98770 _98769) = (term33 _98770 _98769).
Proof. exact (MK_COMB (@lem7664841 _98770 _98769) (@lem7664839 _98769)). Qed.
Lemma lem7664843 (_98770 : int) (_98769 : int) : (term34 _98770 _98769) = (term32 _98770 _98769).
Proof. exact (@lem17160 (term35 _98770 _98769) (term36 _98769)). Qed.
Lemma lem7664844 (_98770 : int) (_98769 : int) : (term34 _98770 _98769) = (term33 _98770 _98769).
Proof. exact (TRANS (@lem7664843 _98770 _98769) (@lem7664842 _98770 _98769)). Qed.
Lemma lem7664846 (_98770 : int) : (term37 _98770) = (term37 _98770).
Proof. exact (eq_refl (term37 _98770)). Qed.
Lemma lem7664847 (_98770 : int) (_98769 : int) : (term38 _98770 _98769) = (term39 _98770 _98769).
Proof. exact (MK_COMB (@lem7664846 _98770) (@lem7664844 _98770 _98769)). Qed.
Lemma lem7664848 (_98770 : int) (_98769 : int) : (term40 _98770 _98769) = (term38 _98770 _98769).
Proof. exact (@lem17362 (term41 _98770) (term42 _98770 _98769)). Qed.
Lemma lem7664849 (_98770 : int) (_98769 : int) : (term40 _98770 _98769) = (term39 _98770 _98769).
Proof. exact (TRANS (@lem7664848 _98770 _98769) (@lem7664847 _98770 _98769)). Qed.
Lemma lem7664851 (_98769 : int) : (term37 _98769) = (term37 _98769).
Proof. exact (eq_refl (term37 _98769)). Qed.
Lemma lem7664852 (_98770 : int) (_98769 : int) : (term43 _98770 _98769) = (term44 _98770 _98769).
Proof. exact (MK_COMB (@lem7664851 _98769) (@lem7664849 _98770 _98769)). Qed.
Lemma lem7664853 (_98770 : int) (_98769 : int) : (term45 _98770 _98769) = (term43 _98770 _98769).
Proof. exact (@lem17362 (term41 _98769) (term46 _98770 _98769)). Qed.
Lemma lem7664871 (_98770 : int) (_98769 : int) : (term45 _98770 _98769) = (term44 _98770 _98769).
Proof. exact (TRANS (@lem7664853 _98770 _98769) (@lem7664852 _98770 _98769)). Qed.
Lemma lem7664874 (x : int) (y : int) : (int_le x y) = (term47 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7664875 (_98769 : int) : (term41 _98769) = (term48 _98769).
Proof. exact (@lem7664874 term49 _98769). Qed.
Lemma lem7664877 (n : nat) : (term50 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7664878 : term51 = term52.
Proof. exact (@lem7664877 (NUMERAL 0)). Qed.
Lemma lem7664879 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7664880 : term53 = term54.
Proof. exact (MK_COMB (@lem7664879) (@lem7664878)). Qed.
Lemma lem7664881 (_98769 : int) : (real_of_int _98769) = (real_of_int _98769).
Proof. exact (eq_refl (real_of_int _98769)). Qed.
Lemma lem7664882 (_98769 : int) : (term48 _98769) = (term55 _98769).
Proof. exact (MK_COMB (@lem7664880) (@lem7664881 _98769)). Qed.
Lemma lem7664884 (_98769 : int) : (term41 _98769) = (term55 _98769).
Proof. exact (TRANS (@lem7664875 _98769) (@lem7664882 _98769)). Qed.
Lemma lem7664887 (x : int) (y : int) : (int_le x y) = (term47 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7664888 (_98770 : int) : (term41 _98770) = (term48 _98770).
Proof. exact (@lem7664887 term49 _98770). Qed.
Lemma lem7664890 (n : nat) : (term50 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7664891 : term51 = term52.
Proof. exact (@lem7664890 (NUMERAL 0)). Qed.
Lemma lem7664892 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7664893 : term53 = term54.
Proof. exact (MK_COMB (@lem7664892) (@lem7664891)). Qed.
Lemma lem7664894 (_98770 : int) : (real_of_int _98770) = (real_of_int _98770).
Proof. exact (eq_refl (real_of_int _98770)). Qed.
Lemma lem7664895 (_98770 : int) : (term48 _98770) = (term55 _98770).
Proof. exact (MK_COMB (@lem7664893) (@lem7664894 _98770)). Qed.
Lemma lem7664897 (_98770 : int) : (term41 _98770) = (term55 _98770).
Proof. exact (TRANS (@lem7664888 _98770) (@lem7664895 _98770)). Qed.
Lemma lem7664900 (x : int) (y : int) : (int_le x y) = (term47 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7664901 (_98770 : int) (_98769 : int) : (term28 _98770 _98769) = (term56 _98770 _98769).
Proof. exact (@lem7664900 (term57 _98770) _98769). Qed.
Lemma lem7664903 (x : int) (y : int) : (term58 x y) = (term59 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7664904 (_98770 : int) : (term60 _98770) = (term61 _98770).
Proof. exact (@lem7664903 _98770 term62). Qed.
Lemma lem7664906 (n : nat) : (term50 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7664907 : term63 = term64.
Proof. exact (@lem7664906 term11). Qed.
Lemma lem7664908 (_98770 : int) : (term65 _98770) = (term65 _98770).
Proof. exact (eq_refl (term65 _98770)). Qed.
Lemma lem7664909 (_98770 : int) : (term61 _98770) = (term66 _98770).
Proof. exact (MK_COMB (@lem7664908 _98770) (@lem7664907)). Qed.
Lemma lem7664910 (_98770 : int) : (term60 _98770) = (term66 _98770).
Proof. exact (TRANS (@lem7664904 _98770) (@lem7664909 _98770)). Qed.
Lemma lem7664911 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7664912 (_98770 : int) : (term67 _98770) = (term68 _98770).
Proof. exact (MK_COMB (@lem7664911) (@lem7664910 _98770)). Qed.
Lemma lem7664913 (_98769 : int) : (real_of_int _98769) = (real_of_int _98769).
Proof. exact (eq_refl (real_of_int _98769)). Qed.
Lemma lem7664914 (_98770 : int) (_98769 : int) : (term56 _98770 _98769) = (term69 _98770 _98769).
Proof. exact (MK_COMB (@lem7664912 _98770) (@lem7664913 _98769)). Qed.
Lemma lem7664916 (_98770 : int) (_98769 : int) : (term28 _98770 _98769) = (term69 _98770 _98769).
Proof. exact (TRANS (@lem7664901 _98770 _98769) (@lem7664914 _98770 _98769)). Qed.
Lemma lem7664918 (y : int) (x : int) : (term70 x y) = (term28 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7664919 (_98769 : int) : (term29 _98769) = (term71 _98769).
Proof. exact (@lem7664918 _98769 term62). Qed.
Lemma lem7664921 (x : int) (y : int) : (int_le x y) = (term47 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7664922 (_98769 : int) : (term71 _98769) = (term72 _98769).
Proof. exact (@lem7664921 (term57 _98769) term62). Qed.
Lemma lem7664924 (x : int) (y : int) : (term58 x y) = (term59 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7664925 (_98769 : int) : (term60 _98769) = (term61 _98769).
Proof. exact (@lem7664924 _98769 term62). Qed.
Lemma lem7664927 (n : nat) : (term50 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7664928 : term63 = term64.
Proof. exact (@lem7664927 term11). Qed.
Lemma lem7664929 (_98769 : int) : (term65 _98769) = (term65 _98769).
Proof. exact (eq_refl (term65 _98769)). Qed.
Lemma lem7664930 (_98769 : int) : (term61 _98769) = (term66 _98769).
Proof. exact (MK_COMB (@lem7664929 _98769) (@lem7664928)). Qed.
Lemma lem7664931 (_98769 : int) : (term60 _98769) = (term66 _98769).
Proof. exact (TRANS (@lem7664925 _98769) (@lem7664930 _98769)). Qed.
Lemma lem7664932 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7664933 (_98769 : int) : (term67 _98769) = (term68 _98769).
Proof. exact (MK_COMB (@lem7664932) (@lem7664931 _98769)). Qed.
Lemma lem7664935 (n : nat) : (term50 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7664936 : term63 = term64.
Proof. exact (@lem7664935 term11). Qed.
Lemma lem7664937 (_98769 : int) : (term72 _98769) = (term73 _98769).
Proof. exact (MK_COMB (@lem7664933 _98769) (@lem7664936)). Qed.
Lemma lem7664938 (_98769 : int) : (term71 _98769) = (term73 _98769).
Proof. exact (TRANS (@lem7664922 _98769) (@lem7664937 _98769)). Qed.
Lemma lem7664939 (_98769 : int) : (term29 _98769) = (term73 _98769).
Proof. exact (TRANS (@lem7664919 _98769) (@lem7664938 _98769)). Qed.
Lemma lem7664940 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7664941 (_98770 : int) (_98769 : int) : (term31 _98770 _98769) = (term74 _98770 _98769).
Proof. exact (MK_COMB (@lem7664940) (@lem7664916 _98770 _98769)). Qed.
Lemma lem7664942 (_98770 : int) (_98769 : int) : (term33 _98770 _98769) = (term75 _98770 _98769).
Proof. exact (MK_COMB (@lem7664941 _98770 _98769) (@lem7664939 _98769)). Qed.
Lemma lem7664943 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7664944 (_98770 : int) : (term37 _98770) = (term76 _98770).
Proof. exact (MK_COMB (@lem7664943) (@lem7664897 _98770)). Qed.
Lemma lem7664945 (_98770 : int) (_98769 : int) : (term39 _98770 _98769) = (term77 _98770 _98769).
Proof. exact (MK_COMB (@lem7664944 _98770) (@lem7664942 _98770 _98769)). Qed.
Lemma lem7664946 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7664947 (_98769 : int) : (term37 _98769) = (term76 _98769).
Proof. exact (MK_COMB (@lem7664946) (@lem7664884 _98769)). Qed.
Lemma lem7664948 (_98770 : int) (_98769 : int) : (term44 _98770 _98769) = (term78 _98770 _98769).
Proof. exact (MK_COMB (@lem7664947 _98769) (@lem7664945 _98770 _98769)). Qed.
Lemma lem7664949 (_98770 : int) (_98769 : int) : (term45 _98770 _98769) = (term78 _98770 _98769).
Proof. exact (TRANS (@lem7664871 _98770 _98769) (@lem7664948 _98770 _98769)). Qed.
Lemma lem7664953 (t : Prop) : (term79 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7664989 (_98770 : int) (_98769 : int) : (term80 _98770 _98769) = (term78 _98770 _98769).
Proof. exact (@lem7664953 (term78 _98770 _98769)). Qed.
Lemma lem7664990 (_98769 : int) : (term55 _98769) = (term81 _98769).
Proof. exact (@lem1988287 (real_of_int _98769) term52). Qed.
Lemma lem7664996 (_98769 : int) : (term82 _98769) = (term83 _98769).
Proof. exact (@lem1982792 (real_of_int _98769) term52). Qed.
Lemma lem7664998 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7664999 : term52 = term85.
Proof. exact (@lem7664998 (NUMERAL 0)). Qed.
Lemma lem7665001 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7665002 : term88 = term89.
Proof. exact (@lem7665001 term11). Qed.
Lemma lem7665003 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7665004 : term90 = term91.
Proof. exact (MK_COMB (@lem7665003) (@lem7665002)). Qed.
Lemma lem7665005 : term92 = term93.
Proof. exact (MK_COMB (@lem7665004) (@lem7664999)). Qed.
Lemma lem7665006 : term93 = term94.
Proof. exact (@lem1981613 term88 term52 term64 term64). Qed.
Lemma lem7665008 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7665009 : term97 = term98.
Proof. exact (@lem7665008 term11 term11). Qed.
Lemma lem7665010 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7665011 : term100 = term11.
Proof. exact (EQ_MP (@lem7665010) (@lem940073)). Qed.
Lemma lem7665012 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7665013 : term98 = term64.
Proof. exact (MK_COMB (@lem7665012) (@lem7665011)). Qed.
Lemma lem7665014 : term97 = term64.
Proof. exact (TRANS (@lem7665009) (@lem7665013)). Qed.
Lemma lem7665016 (x : nat) : (term101 x) = term52.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7665017 : term92 = term52.
Proof. exact (@lem7665016 term11). Qed.
Lemma lem7665018 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7665019 : term102 = term103.
Proof. exact (MK_COMB (@lem7665018) (@lem7665017)). Qed.
Lemma lem7665020 : term94 = term85.
Proof. exact (MK_COMB (@lem7665019) (@lem7665014)). Qed.
Lemma lem7665021 : term93 = term85.
Proof. exact (TRANS (@lem7665006) (@lem7665020)). Qed.
Lemma lem7665022 : term92 = term85.
Proof. exact (TRANS (@lem7665005) (@lem7665021)). Qed.
Lemma lem7665024 (x : real) : (term104 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7665025 : term85 = term52.
Proof. exact (@lem7665024 term52). Qed.
Lemma lem7665026 : term92 = term52.
Proof. exact (TRANS (@lem7665022) (@lem7665025)). Qed.
Lemma lem7665027 (_98769 : int) : (term65 _98769) = (term65 _98769).
Proof. exact (eq_refl (term65 _98769)). Qed.
Lemma lem7665028 (_98769 : int) : (term83 _98769) = (term105 _98769).
Proof. exact (MK_COMB (@lem7665027 _98769) (@lem7665026)). Qed.
Lemma lem7665029 (_98769 : int) : (term105 _98769) = (real_of_int _98769).
Proof. exact (@lem1982723 (real_of_int _98769)). Qed.
Lemma lem7665030 (_98769 : int) : (term83 _98769) = (real_of_int _98769).
Proof. exact (TRANS (@lem7665028 _98769) (@lem7665029 _98769)). Qed.
Lemma lem7665032 (_98769 : int) : (term82 _98769) = (real_of_int _98769).
Proof. exact (TRANS (@lem7664996 _98769) (@lem7665030 _98769)). Qed.
Lemma lem7665033 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7665034 (_98769 : int) : (term106 _98769) = (term107 _98769).
Proof. exact (MK_COMB (@lem7665033) (@lem7665032 _98769)). Qed.
Lemma lem7665035 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7665036 (_98769 : int) : (term81 _98769) = (term108 _98769).
Proof. exact (MK_COMB (@lem7665034 _98769) (@lem7665035)). Qed.
Lemma lem7665037 (_98769 : int) : (term55 _98769) = (term108 _98769).
Proof. exact (TRANS (@lem7664990 _98769) (@lem7665036 _98769)). Qed.
Lemma lem7665038 (_98770 : int) : (term55 _98770) = (term81 _98770).
Proof. exact (@lem1988287 (real_of_int _98770) term52). Qed.
Lemma lem7665044 (_98770 : int) : (term82 _98770) = (term83 _98770).
Proof. exact (@lem1982792 (real_of_int _98770) term52). Qed.
Lemma lem7665046 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7665047 : term52 = term85.
Proof. exact (@lem7665046 (NUMERAL 0)). Qed.
Lemma lem7665049 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7665050 : term88 = term89.
Proof. exact (@lem7665049 term11). Qed.
Lemma lem7665051 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7665052 : term90 = term91.
Proof. exact (MK_COMB (@lem7665051) (@lem7665050)). Qed.
Lemma lem7665053 : term92 = term93.
Proof. exact (MK_COMB (@lem7665052) (@lem7665047)). Qed.
Lemma lem7665054 : term93 = term94.
Proof. exact (@lem1981613 term88 term52 term64 term64). Qed.
Lemma lem7665056 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7665057 : term97 = term98.
Proof. exact (@lem7665056 term11 term11). Qed.
Lemma lem7665058 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7665059 : term100 = term11.
Proof. exact (EQ_MP (@lem7665058) (@lem940073)). Qed.
Lemma lem7665060 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7665061 : term98 = term64.
Proof. exact (MK_COMB (@lem7665060) (@lem7665059)). Qed.
Lemma lem7665062 : term97 = term64.
Proof. exact (TRANS (@lem7665057) (@lem7665061)). Qed.
Lemma lem7665064 (x : nat) : (term101 x) = term52.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7665065 : term92 = term52.
Proof. exact (@lem7665064 term11). Qed.
Lemma lem7665066 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7665067 : term102 = term103.
Proof. exact (MK_COMB (@lem7665066) (@lem7665065)). Qed.
Lemma lem7665068 : term94 = term85.
Proof. exact (MK_COMB (@lem7665067) (@lem7665062)). Qed.
Lemma lem7665069 : term93 = term85.
Proof. exact (TRANS (@lem7665054) (@lem7665068)). Qed.
Lemma lem7665070 : term92 = term85.
Proof. exact (TRANS (@lem7665053) (@lem7665069)). Qed.
Lemma lem7665072 (x : real) : (term104 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7665073 : term85 = term52.
Proof. exact (@lem7665072 term52). Qed.
Lemma lem7665074 : term92 = term52.
Proof. exact (TRANS (@lem7665070) (@lem7665073)). Qed.
Lemma lem7665075 (_98770 : int) : (term65 _98770) = (term65 _98770).
Proof. exact (eq_refl (term65 _98770)). Qed.
Lemma lem7665076 (_98770 : int) : (term83 _98770) = (term105 _98770).
Proof. exact (MK_COMB (@lem7665075 _98770) (@lem7665074)). Qed.
Lemma lem7665077 (_98770 : int) : (term105 _98770) = (real_of_int _98770).
Proof. exact (@lem1982723 (real_of_int _98770)). Qed.
Lemma lem7665078 (_98770 : int) : (term83 _98770) = (real_of_int _98770).
Proof. exact (TRANS (@lem7665076 _98770) (@lem7665077 _98770)). Qed.
Lemma lem7665080 (_98770 : int) : (term82 _98770) = (real_of_int _98770).
Proof. exact (TRANS (@lem7665044 _98770) (@lem7665078 _98770)). Qed.
Lemma lem7665081 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7665082 (_98770 : int) : (term106 _98770) = (term107 _98770).
Proof. exact (MK_COMB (@lem7665081) (@lem7665080 _98770)). Qed.
Lemma lem7665083 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7665084 (_98770 : int) : (term81 _98770) = (term108 _98770).
Proof. exact (MK_COMB (@lem7665082 _98770) (@lem7665083)). Qed.
Lemma lem7665085 (_98770 : int) : (term55 _98770) = (term108 _98770).
Proof. exact (TRANS (@lem7665038 _98770) (@lem7665084 _98770)). Qed.
Lemma lem7665086 (_98769 : int) (_98770 : int) : (term69 _98770 _98769) = (term109 _98769 _98770).
Proof. exact (@lem1988287 (real_of_int _98769) (term66 _98770)). Qed.
Lemma lem7665098 (_98769 : int) (_98770 : int) : (term110 _98769 _98770) = (term111 _98769 _98770).
Proof. exact (@lem1982792 (real_of_int _98769) (term66 _98770)). Qed.
Lemma lem7665099 (_98770 : int) : (term112 _98770) = (term113 _98770).
Proof. exact (@lem1982781 (real_of_int _98770) term88 term64). Qed.
Lemma lem7665101 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7665102 : term64 = term114.
Proof. exact (@lem7665101 term11). Qed.
Lemma lem7665104 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7665105 : term88 = term89.
Proof. exact (@lem7665104 term11). Qed.
Lemma lem7665106 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7665107 : term90 = term91.
Proof. exact (MK_COMB (@lem7665106) (@lem7665105)). Qed.
Lemma lem7665108 : term115 = term116.
Proof. exact (MK_COMB (@lem7665107) (@lem7665102)). Qed.
Lemma lem7665109 : term116 = term117.
Proof. exact (@lem1981613 term88 term64 term64 term64). Qed.
Lemma lem7665111 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7665112 : term97 = term98.
Proof. exact (@lem7665111 term11 term11). Qed.
Lemma lem7665113 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7665114 : term100 = term11.
Proof. exact (EQ_MP (@lem7665113) (@lem940073)). Qed.
Lemma lem7665115 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7665116 : term98 = term64.
Proof. exact (MK_COMB (@lem7665115) (@lem7665114)). Qed.
Lemma lem7665117 : term97 = term64.
Proof. exact (TRANS (@lem7665112) (@lem7665116)). Qed.
Lemma lem7665119 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7665120 : term115 = term120.
Proof. exact (@lem7665119 term11 term11). Qed.
Lemma lem7665121 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7665122 : term100 = term11.
Proof. exact (EQ_MP (@lem7665121) (@lem940073)). Qed.
Lemma lem7665123 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7665124 : term98 = term64.
Proof. exact (MK_COMB (@lem7665123) (@lem7665122)). Qed.
Lemma lem7665125 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7665126 : term120 = term88.
Proof. exact (MK_COMB (@lem7665125) (@lem7665124)). Qed.
Lemma lem7665127 : term115 = term88.
Proof. exact (TRANS (@lem7665120) (@lem7665126)). Qed.
Lemma lem7665128 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7665129 : term121 = term122.
Proof. exact (MK_COMB (@lem7665128) (@lem7665127)). Qed.
Lemma lem7665130 : term117 = term89.
Proof. exact (MK_COMB (@lem7665129) (@lem7665117)). Qed.
Lemma lem7665131 : term116 = term89.
Proof. exact (TRANS (@lem7665109) (@lem7665130)). Qed.
Lemma lem7665132 : term115 = term89.
Proof. exact (TRANS (@lem7665108) (@lem7665131)). Qed.
Lemma lem7665134 (x : real) : (term104 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7665135 : term89 = term88.
Proof. exact (@lem7665134 term88). Qed.
Lemma lem7665136 : term115 = term88.
Proof. exact (TRANS (@lem7665132) (@lem7665135)). Qed.
Lemma lem7665139 (_98770 : int) : (term123 _98770) = (term123 _98770).
Proof. exact (eq_refl (term123 _98770)). Qed.
Lemma lem7665140 (_98770 : int) : (term113 _98770) = (term124 _98770).
Proof. exact (MK_COMB (@lem7665139 _98770) (@lem7665136)). Qed.
Lemma lem7665141 (_98770 : int) : (term112 _98770) = (term124 _98770).
Proof. exact (TRANS (@lem7665099 _98770) (@lem7665140 _98770)). Qed.
Lemma lem7665142 (_98769 : int) : (term65 _98769) = (term65 _98769).
Proof. exact (eq_refl (term65 _98769)). Qed.
Lemma lem7665145 (_98769 : int) (_98770 : int) : (term111 _98769 _98770) = (term125 _98769 _98770).
Proof. exact (MK_COMB (@lem7665142 _98769) (@lem7665141 _98770)). Qed.
Lemma lem7665147 (_98769 : int) (_98770 : int) : (term110 _98769 _98770) = (term125 _98769 _98770).
Proof. exact (TRANS (@lem7665098 _98769 _98770) (@lem7665145 _98769 _98770)). Qed.
Lemma lem7665148 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7665149 (_98769 : int) (_98770 : int) : (term126 _98769 _98770) = (term127 _98769 _98770).
Proof. exact (MK_COMB (@lem7665148) (@lem7665147 _98769 _98770)). Qed.
Lemma lem7665150 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7665151 (_98769 : int) (_98770 : int) : (term109 _98769 _98770) = (term128 _98769 _98770).
Proof. exact (MK_COMB (@lem7665149 _98769 _98770) (@lem7665150)). Qed.
Lemma lem7665152 (_98769 : int) (_98770 : int) : (term69 _98770 _98769) = (term128 _98769 _98770).
Proof. exact (TRANS (@lem7665086 _98769 _98770) (@lem7665151 _98769 _98770)). Qed.
Lemma lem7665153 (_98769 : int) : (term73 _98769) = (term129 _98769).
Proof. exact (@lem1988287 term64 (term66 _98769)). Qed.
Lemma lem7665165 (_98769 : int) : (term130 _98769) = (term131 _98769).
Proof. exact (@lem1982792 term64 (term66 _98769)). Qed.
Lemma lem7665166 (_98769 : int) : (term112 _98769) = (term113 _98769).
Proof. exact (@lem1982781 (real_of_int _98769) term88 term64). Qed.
Lemma lem7665168 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7665169 : term64 = term114.
Proof. exact (@lem7665168 term11). Qed.
Lemma lem7665171 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7665172 : term88 = term89.
Proof. exact (@lem7665171 term11). Qed.
Lemma lem7665173 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7665174 : term90 = term91.
Proof. exact (MK_COMB (@lem7665173) (@lem7665172)). Qed.
Lemma lem7665175 : term115 = term116.
Proof. exact (MK_COMB (@lem7665174) (@lem7665169)). Qed.
Lemma lem7665176 : term116 = term117.
Proof. exact (@lem1981613 term88 term64 term64 term64). Qed.
Lemma lem7665178 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7665179 : term97 = term98.
Proof. exact (@lem7665178 term11 term11). Qed.
Lemma lem7665180 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7665181 : term100 = term11.
Proof. exact (EQ_MP (@lem7665180) (@lem940073)). Qed.
Lemma lem7665182 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7665183 : term98 = term64.
Proof. exact (MK_COMB (@lem7665182) (@lem7665181)). Qed.
Lemma lem7665184 : term97 = term64.
Proof. exact (TRANS (@lem7665179) (@lem7665183)). Qed.
Lemma lem7665186 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7665187 : term115 = term120.
Proof. exact (@lem7665186 term11 term11). Qed.
Lemma lem7665188 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7665189 : term100 = term11.
Proof. exact (EQ_MP (@lem7665188) (@lem940073)). Qed.
Lemma lem7665190 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7665191 : term98 = term64.
Proof. exact (MK_COMB (@lem7665190) (@lem7665189)). Qed.
Lemma lem7665192 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7665193 : term120 = term88.
Proof. exact (MK_COMB (@lem7665192) (@lem7665191)). Qed.
Lemma lem7665194 : term115 = term88.
Proof. exact (TRANS (@lem7665187) (@lem7665193)). Qed.
Lemma lem7665195 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7665196 : term121 = term122.
Proof. exact (MK_COMB (@lem7665195) (@lem7665194)). Qed.
Lemma lem7665197 : term117 = term89.
Proof. exact (MK_COMB (@lem7665196) (@lem7665184)). Qed.
Lemma lem7665198 : term116 = term89.
Proof. exact (TRANS (@lem7665176) (@lem7665197)). Qed.
Lemma lem7665199 : term115 = term89.
Proof. exact (TRANS (@lem7665175) (@lem7665198)). Qed.
Lemma lem7665201 (x : real) : (term104 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7665202 : term89 = term88.
Proof. exact (@lem7665201 term88). Qed.
Lemma lem7665203 : term115 = term88.
Proof. exact (TRANS (@lem7665199) (@lem7665202)). Qed.
Lemma lem7665206 (_98769 : int) : (term123 _98769) = (term123 _98769).
Proof. exact (eq_refl (term123 _98769)). Qed.
Lemma lem7665207 (_98769 : int) : (term113 _98769) = (term124 _98769).
Proof. exact (MK_COMB (@lem7665206 _98769) (@lem7665203)). Qed.
Lemma lem7665208 (_98769 : int) : (term112 _98769) = (term124 _98769).
Proof. exact (TRANS (@lem7665166 _98769) (@lem7665207 _98769)). Qed.
Lemma lem7665209 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem7665210 (_98769 : int) : (term131 _98769) = (term133 _98769).
Proof. exact (MK_COMB (@lem7665209) (@lem7665208 _98769)). Qed.
Lemma lem7665211 (_98769 : int) : (term133 _98769) = (term134 _98769).
Proof. exact (@lem1982757 (term135 _98769) term64 term88). Qed.
Lemma lem7665213 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7665214 : term88 = term89.
Proof. exact (@lem7665213 term11). Qed.
Lemma lem7665216 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7665217 : term64 = term114.
Proof. exact (@lem7665216 term11). Qed.
Lemma lem7665218 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7665219 : term132 = term136.
Proof. exact (MK_COMB (@lem7665218) (@lem7665217)). Qed.
Lemma lem7665220 : term137 = term138.
Proof. exact (MK_COMB (@lem7665219) (@lem7665214)). Qed.
Lemma lem7665221 : term139.
Proof. exact (@lem1981473 term64 term64 term88 term64 term52 term64). Qed.
Lemma lem7665223 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7665224 : term141 = term142.
Proof. exact (@lem7665223 (NUMERAL 0) term11). Qed.
Lemma lem7665225 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7665226 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7665227 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7665226 h1) (fun h1 : term142 = True => @lem7665225)). Qed.
Lemma lem7665228 : term142 = True.
Proof. exact (EQ_MP (@lem7665227) (@lem7665225)). Qed.
Lemma lem7665229 : term141 = True.
Proof. exact (TRANS (@lem7665224) (@lem7665228)). Qed.
Lemma lem7665230 : True = term141.
Proof. exact (SYM (@lem7665229)). Qed.
Lemma lem7665231 : term141.
Proof. exact (EQ_MP (@lem7665230) (@lem0)). Qed.
Lemma lem7665232 : term144.
Proof. exact (@lem7665221 (@lem7665231)). Qed.
Lemma lem7665234 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7665235 : term141 = term142.
Proof. exact (@lem7665234 (NUMERAL 0) term11). Qed.
Lemma lem7665236 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7665237 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7665238 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7665237 h1) (fun h1 : term142 = True => @lem7665236)). Qed.
Lemma lem7665239 : term142 = True.
Proof. exact (EQ_MP (@lem7665238) (@lem7665236)). Qed.
Lemma lem7665240 : term141 = True.
Proof. exact (TRANS (@lem7665235) (@lem7665239)). Qed.
Lemma lem7665241 : True = term141.
Proof. exact (SYM (@lem7665240)). Qed.
Lemma lem7665242 : term141.
Proof. exact (EQ_MP (@lem7665241) (@lem0)). Qed.
Lemma lem7665243 : term145.
Proof. exact (@lem7665232 (@lem7665242)). Qed.
Lemma lem7665245 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7665246 : term141 = term142.
Proof. exact (@lem7665245 (NUMERAL 0) term11). Qed.
Lemma lem7665247 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7665248 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7665249 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7665248 h1) (fun h1 : term142 = True => @lem7665247)). Qed.
Lemma lem7665250 : term142 = True.
Proof. exact (EQ_MP (@lem7665249) (@lem7665247)). Qed.
Lemma lem7665251 : term141 = True.
Proof. exact (TRANS (@lem7665246) (@lem7665250)). Qed.
Lemma lem7665252 : True = term141.
Proof. exact (SYM (@lem7665251)). Qed.
Lemma lem7665253 : term141.
Proof. exact (EQ_MP (@lem7665252) (@lem0)). Qed.
Lemma lem7665254 : term146.
Proof. exact (@lem7665243 (@lem7665253)). Qed.
Lemma lem7665256 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7665257 : term115 = term120.
Proof. exact (@lem7665256 term11 term11). Qed.
Lemma lem7665258 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7665259 : term100 = term11.
Proof. exact (EQ_MP (@lem7665258) (@lem940073)). Qed.
Lemma lem7665260 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7665261 : term98 = term64.
Proof. exact (MK_COMB (@lem7665260) (@lem7665259)). Qed.
Lemma lem7665262 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7665263 : term120 = term88.
Proof. exact (MK_COMB (@lem7665262) (@lem7665261)). Qed.
Lemma lem7665264 : term115 = term88.
Proof. exact (TRANS (@lem7665257) (@lem7665263)). Qed.
Lemma lem7665266 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7665267 : term97 = term98.
Proof. exact (@lem7665266 term11 term11). Qed.
Lemma lem7665268 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7665269 : term100 = term11.
Proof. exact (EQ_MP (@lem7665268) (@lem940073)). Qed.
Lemma lem7665270 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7665271 : term98 = term64.
Proof. exact (MK_COMB (@lem7665270) (@lem7665269)). Qed.
Lemma lem7665272 : term97 = term64.
Proof. exact (TRANS (@lem7665267) (@lem7665271)). Qed.
Lemma lem7665273 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7665274 : term147 = term132.
Proof. exact (MK_COMB (@lem7665273) (@lem7665272)). Qed.
Lemma lem7665275 : term148 = term137.
Proof. exact (MK_COMB (@lem7665274) (@lem7665264)). Qed.
Lemma lem7665277 (m : nat) : (term149 m) = term52.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem7665278 : term137 = term52.
Proof. exact (@lem7665277 term11). Qed.
Lemma lem7665279 : term148 = term52.
Proof. exact (TRANS (@lem7665275) (@lem7665278)). Qed.
Lemma lem7665280 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7665281 : term150 = term151.
Proof. exact (MK_COMB (@lem7665280) (@lem7665279)). Qed.
Lemma lem7665282 : term64 = term64.
Proof. exact (eq_refl term64). Qed.
Lemma lem7665283 : term152 = term153.
Proof. exact (MK_COMB (@lem7665281) (@lem7665282)). Qed.
Lemma lem7665285 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7665286 : term153 = term52.
Proof. exact (@lem7665285 term11). Qed.
Lemma lem7665287 : term152 = term52.
Proof. exact (TRANS (@lem7665283) (@lem7665286)). Qed.
Lemma lem7665289 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7665290 : term97 = term98.
Proof. exact (@lem7665289 term11 term11). Qed.
Lemma lem7665291 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7665292 : term100 = term11.
Proof. exact (EQ_MP (@lem7665291) (@lem940073)). Qed.
Lemma lem7665293 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7665294 : term98 = term64.
Proof. exact (MK_COMB (@lem7665293) (@lem7665292)). Qed.
Lemma lem7665295 : term97 = term64.
Proof. exact (TRANS (@lem7665290) (@lem7665294)). Qed.
Lemma lem7665296 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem7665297 : term155 = term153.
Proof. exact (MK_COMB (@lem7665296) (@lem7665295)). Qed.
Lemma lem7665299 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7665300 : term153 = term52.
Proof. exact (@lem7665299 term11). Qed.
Lemma lem7665301 : term155 = term52.
Proof. exact (TRANS (@lem7665297) (@lem7665300)). Qed.
Lemma lem7665302 : term52 = term155.
Proof. exact (SYM (@lem7665301)). Qed.
Lemma lem7665303 : term152 = term155.
Proof. exact (TRANS (@lem7665287) (@lem7665302)). Qed.
Lemma lem7665304 : term138 = term85.
Proof. exact (@lem7665254 (@lem7665303)). Qed.
Lemma lem7665305 : term137 = term85.
Proof. exact (TRANS (@lem7665220) (@lem7665304)). Qed.
Lemma lem7665307 (x : real) : (term104 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7665308 : term85 = term52.
Proof. exact (@lem7665307 term52). Qed.
Lemma lem7665309 : term137 = term52.
Proof. exact (TRANS (@lem7665305) (@lem7665308)). Qed.
Lemma lem7665310 (_98769 : int) : (term123 _98769) = (term123 _98769).
Proof. exact (eq_refl (term123 _98769)). Qed.
Lemma lem7665311 (_98769 : int) : (term134 _98769) = (term156 _98769).
Proof. exact (MK_COMB (@lem7665310 _98769) (@lem7665309)). Qed.
Lemma lem7665312 (_98769 : int) : (term133 _98769) = (term156 _98769).
Proof. exact (TRANS (@lem7665211 _98769) (@lem7665311 _98769)). Qed.
Lemma lem7665313 (_98769 : int) : (term156 _98769) = (term135 _98769).
Proof. exact (@lem1982723 (term135 _98769)). Qed.
Lemma lem7665314 (_98769 : int) : (term133 _98769) = (term135 _98769).
Proof. exact (TRANS (@lem7665312 _98769) (@lem7665313 _98769)). Qed.
Lemma lem7665315 (_98769 : int) : (term131 _98769) = (term135 _98769).
Proof. exact (TRANS (@lem7665210 _98769) (@lem7665314 _98769)). Qed.
Lemma lem7665317 (_98769 : int) : (term130 _98769) = (term135 _98769).
Proof. exact (TRANS (@lem7665165 _98769) (@lem7665315 _98769)). Qed.
Lemma lem7665318 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7665319 (_98769 : int) : (term157 _98769) = (term158 _98769).
Proof. exact (MK_COMB (@lem7665318) (@lem7665317 _98769)). Qed.
Lemma lem7665320 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7665321 (_98769 : int) : (term129 _98769) = (term159 _98769).
Proof. exact (MK_COMB (@lem7665319 _98769) (@lem7665320)). Qed.
Lemma lem7665322 (_98769 : int) : (term73 _98769) = (term159 _98769).
Proof. exact (TRANS (@lem7665153 _98769) (@lem7665321 _98769)). Qed.
Lemma lem7665323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7665324 (_98769 : int) (_98770 : int) : (term74 _98770 _98769) = (term160 _98769 _98770).
Proof. exact (MK_COMB (@lem7665323) (@lem7665152 _98769 _98770)). Qed.
Lemma lem7665325 (_98770 : int) (_98769 : int) : (term75 _98770 _98769) = (term161 _98770 _98769).
Proof. exact (MK_COMB (@lem7665324 _98769 _98770) (@lem7665322 _98769)). Qed.
Lemma lem7665326 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7665327 (_98770 : int) : (term76 _98770) = (term162 _98770).
Proof. exact (MK_COMB (@lem7665326) (@lem7665085 _98770)). Qed.
Lemma lem7665328 (_98770 : int) (_98769 : int) : (term77 _98770 _98769) = (term163 _98770 _98769).
Proof. exact (MK_COMB (@lem7665327 _98770) (@lem7665325 _98770 _98769)). Qed.
Lemma lem7665329 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7665330 (_98769 : int) : (term76 _98769) = (term162 _98769).
Proof. exact (MK_COMB (@lem7665329) (@lem7665037 _98769)). Qed.
Lemma lem7665331 (_98770 : int) (_98769 : int) : (term78 _98770 _98769) = (term164 _98770 _98769).
Proof. exact (MK_COMB (@lem7665330 _98769) (@lem7665328 _98770 _98769)). Qed.
Lemma lem7665358 (_98770 : int) (_98769 : int) : (term80 _98770 _98769) = (term164 _98770 _98769).
Proof. exact (TRANS (@lem7664989 _98770 _98769) (@lem7665331 _98770 _98769)). Qed.
Lemma lem7665362 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : term164 _98770 _98769.
Proof. exact (h1). Qed.
Lemma lem7665363 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : term163 _98770 _98769.
Proof. exact (proj2 (@lem7665362 _98770 _98769 h1)). Qed.
Lemma lem7665365 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : term161 _98770 _98769.
Proof. exact (proj2 (@lem7665363 _98770 _98769 h1)). Qed.
Lemma lem7665366 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : term108 _98770.
Proof. exact (proj1 (@lem7665363 _98770 _98769 h1)). Qed.
Lemma lem7665367 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : term159 _98769.
Proof. exact (proj2 (@lem7665365 _98770 _98769 h1)). Qed.
Lemma lem7665368 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : term128 _98769 _98770.
Proof. exact (proj1 (@lem7665365 _98770 _98769 h1)). Qed.
Lemma lem7665370 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7665371 : term165 = term141.
Proof. exact (@lem7665370 term52 term64). Qed.
Lemma lem7665373 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7665374 : term64 = term114.
Proof. exact (@lem7665373 term11). Qed.
Lemma lem7665376 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7665377 : term52 = term85.
Proof. exact (@lem7665376 (NUMERAL 0)). Qed.
Lemma lem7665378 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7665379 : term166 = term167.
Proof. exact (MK_COMB (@lem7665378) (@lem7665377)). Qed.
Lemma lem7665380 : term141 = term168.
Proof. exact (MK_COMB (@lem7665379) (@lem7665374)). Qed.
Lemma lem7665381 : term169.
Proof. exact (@lem1980255 term52 term64 term64 term64). Qed.
Lemma lem7665383 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7665384 : term141 = term142.
Proof. exact (@lem7665383 (NUMERAL 0) term11). Qed.
Lemma lem7665385 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7665386 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7665387 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7665386 h1) (fun h1 : term142 = True => @lem7665385)). Qed.
Lemma lem7665388 : term142 = True.
Proof. exact (EQ_MP (@lem7665387) (@lem7665385)). Qed.
Lemma lem7665389 : term141 = True.
Proof. exact (TRANS (@lem7665384) (@lem7665388)). Qed.
Lemma lem7665390 : True = term141.
Proof. exact (SYM (@lem7665389)). Qed.
Lemma lem7665391 : term141.
Proof. exact (EQ_MP (@lem7665390) (@lem0)). Qed.
Lemma lem7665392 : term170.
Proof. exact (@lem7665381 (@lem7665391)). Qed.
Lemma lem7665394 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7665395 : term141 = term142.
Proof. exact (@lem7665394 (NUMERAL 0) term11). Qed.
Lemma lem7665396 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7665397 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7665398 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7665397 h1) (fun h1 : term142 = True => @lem7665396)). Qed.
Lemma lem7665399 : term142 = True.
Proof. exact (EQ_MP (@lem7665398) (@lem7665396)). Qed.
Lemma lem7665400 : term141 = True.
Proof. exact (TRANS (@lem7665395) (@lem7665399)). Qed.
Lemma lem7665401 : True = term141.
Proof. exact (SYM (@lem7665400)). Qed.
Lemma lem7665402 : term141.
Proof. exact (EQ_MP (@lem7665401) (@lem0)). Qed.
Lemma lem7665403 : term168 = term171.
Proof. exact (@lem7665392 (@lem7665402)). Qed.
Lemma lem7665405 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7665406 : term97 = term98.
Proof. exact (@lem7665405 term11 term11). Qed.
Lemma lem7665407 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7665408 : term100 = term11.
Proof. exact (EQ_MP (@lem7665407) (@lem940073)). Qed.
Lemma lem7665409 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7665410 : term98 = term64.
Proof. exact (MK_COMB (@lem7665409) (@lem7665408)). Qed.
Lemma lem7665411 : term97 = term64.
Proof. exact (TRANS (@lem7665406) (@lem7665410)). Qed.
Lemma lem7665413 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7665414 : term153 = term52.
Proof. exact (@lem7665413 term11). Qed.
Lemma lem7665415 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7665416 : term172 = term166.
Proof. exact (MK_COMB (@lem7665415) (@lem7665414)). Qed.
Lemma lem7665417 : term171 = term141.
Proof. exact (MK_COMB (@lem7665416) (@lem7665411)). Qed.
Lemma lem7665419 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7665420 : term141 = term142.
Proof. exact (@lem7665419 (NUMERAL 0) term11). Qed.
Lemma lem7665421 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7665422 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7665423 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7665422 h1) (fun h1 : term142 = True => @lem7665421)). Qed.
Lemma lem7665424 : term142 = True.
Proof. exact (EQ_MP (@lem7665423) (@lem7665421)). Qed.
Lemma lem7665425 : term141 = True.
Proof. exact (TRANS (@lem7665420) (@lem7665424)). Qed.
Lemma lem7665426 : term171 = True.
Proof. exact (TRANS (@lem7665417) (@lem7665425)). Qed.
Lemma lem7665427 : term168 = True.
Proof. exact (TRANS (@lem7665403) (@lem7665426)). Qed.
Lemma lem7665428 : term141 = True.
Proof. exact (TRANS (@lem7665380) (@lem7665427)). Qed.
Lemma lem7665429 : term165 = True.
Proof. exact (TRANS (@lem7665371) (@lem7665428)). Qed.
Lemma lem7665430 : True = term165.
Proof. exact (SYM (@lem7665429)). Qed.
Lemma lem7665431 : term165.
Proof. exact (EQ_MP (@lem7665430) (@lem0)). Qed.
Lemma lem7665432 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : term173 _98770.
Proof. exact (conj (@lem7665431) (@lem7665366 _98770 _98769 h1)). Qed.
Lemma lem7665434 (x : real) (y : real) : term174 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7665435 (_98770 : int) : term175 _98770.
Proof. exact (@lem7665434 term64 (real_of_int _98770)). Qed.
Lemma lem7665436 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : term176 _98770.
Proof. exact (@lem7665435 _98770 (@lem7665432 _98770 _98769 h1)). Qed.
Lemma lem7665437 (_98770 : int) : (term177 _98770) = (real_of_int _98770).
Proof. exact (@lem1982733 (real_of_int _98770)). Qed.
Lemma lem7665438 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7665439 (_98770 : int) : (term178 _98770) = (term107 _98770).
Proof. exact (MK_COMB (@lem7665438) (@lem7665437 _98770)). Qed.
Lemma lem7665440 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7665441 (_98770 : int) : (term176 _98770) = (term108 _98770).
Proof. exact (MK_COMB (@lem7665439 _98770) (@lem7665440)). Qed.
Lemma lem7665442 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : term108 _98770.
Proof. exact (EQ_MP (@lem7665441 _98770) (@lem7665436 _98770 _98769 h1)). Qed.
Lemma lem7665444 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7665445 : term165 = term141.
Proof. exact (@lem7665444 term52 term64). Qed.
Lemma lem7665447 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7665448 : term64 = term114.
Proof. exact (@lem7665447 term11). Qed.
Lemma lem7665450 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7665451 : term52 = term85.
Proof. exact (@lem7665450 (NUMERAL 0)). Qed.
Lemma lem7665452 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7665453 : term166 = term167.
Proof. exact (MK_COMB (@lem7665452) (@lem7665451)). Qed.
Lemma lem7665454 : term141 = term168.
Proof. exact (MK_COMB (@lem7665453) (@lem7665448)). Qed.
Lemma lem7665455 : term169.
Proof. exact (@lem1980255 term52 term64 term64 term64). Qed.
Lemma lem7665457 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7665458 : term141 = term142.
Proof. exact (@lem7665457 (NUMERAL 0) term11). Qed.
Lemma lem7665459 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7665460 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7665461 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7665460 h1) (fun h1 : term142 = True => @lem7665459)). Qed.
Lemma lem7665462 : term142 = True.
Proof. exact (EQ_MP (@lem7665461) (@lem7665459)). Qed.
Lemma lem7665463 : term141 = True.
Proof. exact (TRANS (@lem7665458) (@lem7665462)). Qed.
Lemma lem7665464 : True = term141.
Proof. exact (SYM (@lem7665463)). Qed.
Lemma lem7665465 : term141.
Proof. exact (EQ_MP (@lem7665464) (@lem0)). Qed.
Lemma lem7665466 : term170.
Proof. exact (@lem7665455 (@lem7665465)). Qed.
Lemma lem7665468 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7665469 : term141 = term142.
Proof. exact (@lem7665468 (NUMERAL 0) term11). Qed.
Lemma lem7665470 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7665471 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7665472 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7665471 h1) (fun h1 : term142 = True => @lem7665470)). Qed.
Lemma lem7665473 : term142 = True.
Proof. exact (EQ_MP (@lem7665472) (@lem7665470)). Qed.
Lemma lem7665474 : term141 = True.
Proof. exact (TRANS (@lem7665469) (@lem7665473)). Qed.
Lemma lem7665475 : True = term141.
Proof. exact (SYM (@lem7665474)). Qed.
Lemma lem7665476 : term141.
Proof. exact (EQ_MP (@lem7665475) (@lem0)). Qed.
Lemma lem7665477 : term168 = term171.
Proof. exact (@lem7665466 (@lem7665476)). Qed.
Lemma lem7665479 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7665480 : term97 = term98.
Proof. exact (@lem7665479 term11 term11). Qed.
Lemma lem7665481 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7665482 : term100 = term11.
Proof. exact (EQ_MP (@lem7665481) (@lem940073)). Qed.
Lemma lem7665483 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7665484 : term98 = term64.
Proof. exact (MK_COMB (@lem7665483) (@lem7665482)). Qed.
Lemma lem7665485 : term97 = term64.
Proof. exact (TRANS (@lem7665480) (@lem7665484)). Qed.
Lemma lem7665487 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7665488 : term153 = term52.
Proof. exact (@lem7665487 term11). Qed.
Lemma lem7665489 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7665490 : term172 = term166.
Proof. exact (MK_COMB (@lem7665489) (@lem7665488)). Qed.
Lemma lem7665491 : term171 = term141.
Proof. exact (MK_COMB (@lem7665490) (@lem7665485)). Qed.
Lemma lem7665493 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7665494 : term141 = term142.
Proof. exact (@lem7665493 (NUMERAL 0) term11). Qed.
Lemma lem7665495 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7665496 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7665497 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7665496 h1) (fun h1 : term142 = True => @lem7665495)). Qed.
Lemma lem7665498 : term142 = True.
Proof. exact (EQ_MP (@lem7665497) (@lem7665495)). Qed.
Lemma lem7665499 : term141 = True.
Proof. exact (TRANS (@lem7665494) (@lem7665498)). Qed.
Lemma lem7665500 : term171 = True.
Proof. exact (TRANS (@lem7665491) (@lem7665499)). Qed.
Lemma lem7665501 : term168 = True.
Proof. exact (TRANS (@lem7665477) (@lem7665500)). Qed.
Lemma lem7665502 : term141 = True.
Proof. exact (TRANS (@lem7665454) (@lem7665501)). Qed.
Lemma lem7665503 : term165 = True.
Proof. exact (TRANS (@lem7665445) (@lem7665502)). Qed.
Lemma lem7665504 : True = term165.
Proof. exact (SYM (@lem7665503)). Qed.
Lemma lem7665505 : term165.
Proof. exact (EQ_MP (@lem7665504) (@lem0)). Qed.
Lemma lem7665506 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : term179 _98769 _98770.
Proof. exact (conj (@lem7665505) (@lem7665368 _98770 _98769 h1)). Qed.
Lemma lem7665508 (x : real) (y : real) : term174 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7665509 (_98769 : int) (_98770 : int) : term180 _98769 _98770.
Proof. exact (@lem7665508 term64 (term125 _98769 _98770)). Qed.
Lemma lem7665510 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : term181 _98769 _98770.
Proof. exact (@lem7665509 _98769 _98770 (@lem7665506 _98770 _98769 h1)). Qed.
Lemma lem7665511 (_98769 : int) (_98770 : int) : (term182 _98769 _98770) = (term125 _98769 _98770).
Proof. exact (@lem1982733 (term125 _98769 _98770)). Qed.
Lemma lem7665512 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7665513 (_98769 : int) (_98770 : int) : (term183 _98769 _98770) = (term127 _98769 _98770).
Proof. exact (MK_COMB (@lem7665512) (@lem7665511 _98769 _98770)). Qed.
Lemma lem7665514 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7665515 (_98769 : int) (_98770 : int) : (term181 _98769 _98770) = (term128 _98769 _98770).
Proof. exact (MK_COMB (@lem7665513 _98769 _98770) (@lem7665514)). Qed.
Lemma lem7665516 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : term128 _98769 _98770.
Proof. exact (EQ_MP (@lem7665515 _98769 _98770) (@lem7665510 _98770 _98769 h1)). Qed.
Lemma lem7665517 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : term184 _98769 _98770.
Proof. exact (conj (@lem7665516 _98770 _98769 h1) (@lem7665442 _98770 _98769 h1)). Qed.
Lemma lem7665519 (x : real) (y : real) : term185 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7665520 (_98769 : int) (_98770 : int) : term186 _98769 _98770.
Proof. exact (@lem7665519 (term125 _98769 _98770) (real_of_int _98770)). Qed.
Lemma lem7665521 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : term187 _98769 _98770.
Proof. exact (@lem7665520 _98769 _98770 (@lem7665517 _98770 _98769 h1)). Qed.
Lemma lem7665522 (_98769 : int) (_98770 : int) : (term188 _98769 _98770) = (term189 _98769 _98770).
Proof. exact (@lem1982755 (real_of_int _98769) (term124 _98770) (real_of_int _98770)). Qed.
Lemma lem7665523 (_98770 : int) : (term190 _98770) = (term191 _98770).
Proof. exact (@lem1982759 (term135 _98770) (real_of_int _98770) term88). Qed.
Lemma lem7665524 (_98770 : int) : (term192 _98770) = (term193 _98770).
Proof. exact (@lem1982713 term88 (real_of_int _98770)). Qed.
Lemma lem7665526 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7665527 : term64 = term114.
Proof. exact (@lem7665526 term11). Qed.
Lemma lem7665529 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7665530 : term88 = term89.
Proof. exact (@lem7665529 term11). Qed.
Lemma lem7665531 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7665532 : term194 = term195.
Proof. exact (MK_COMB (@lem7665531) (@lem7665530)). Qed.
Lemma lem7665533 : term196 = term197.
Proof. exact (MK_COMB (@lem7665532) (@lem7665527)). Qed.
Lemma lem7665534 : term198.
Proof. exact (@lem1981473 term88 term64 term64 term64 term52 term64). Qed.
Lemma lem7665536 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7665537 : term141 = term142.
Proof. exact (@lem7665536 (NUMERAL 0) term11). Qed.
Lemma lem7665538 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7665539 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7665540 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7665539 h1) (fun h1 : term142 = True => @lem7665538)). Qed.
Lemma lem7665541 : term142 = True.
Proof. exact (EQ_MP (@lem7665540) (@lem7665538)). Qed.
Lemma lem7665542 : term141 = True.
Proof. exact (TRANS (@lem7665537) (@lem7665541)). Qed.
Lemma lem7665543 : True = term141.
Proof. exact (SYM (@lem7665542)). Qed.
Lemma lem7665544 : term141.
Proof. exact (EQ_MP (@lem7665543) (@lem0)). Qed.
Lemma lem7665545 : term199.
Proof. exact (@lem7665534 (@lem7665544)). Qed.
Lemma lem7665547 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7665548 : term141 = term142.
Proof. exact (@lem7665547 (NUMERAL 0) term11). Qed.
Lemma lem7665549 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7665550 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7665551 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7665550 h1) (fun h1 : term142 = True => @lem7665549)). Qed.
Lemma lem7665552 : term142 = True.
Proof. exact (EQ_MP (@lem7665551) (@lem7665549)). Qed.
Lemma lem7665553 : term141 = True.
Proof. exact (TRANS (@lem7665548) (@lem7665552)). Qed.
Lemma lem7665554 : True = term141.
Proof. exact (SYM (@lem7665553)). Qed.
Lemma lem7665555 : term141.
Proof. exact (EQ_MP (@lem7665554) (@lem0)). Qed.
Lemma lem7665556 : term200.
Proof. exact (@lem7665545 (@lem7665555)). Qed.
Lemma lem7665558 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7665559 : term141 = term142.
Proof. exact (@lem7665558 (NUMERAL 0) term11). Qed.
Lemma lem7665560 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7665561 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7665562 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7665561 h1) (fun h1 : term142 = True => @lem7665560)). Qed.
Lemma lem7665563 : term142 = True.
Proof. exact (EQ_MP (@lem7665562) (@lem7665560)). Qed.
Lemma lem7665564 : term141 = True.
Proof. exact (TRANS (@lem7665559) (@lem7665563)). Qed.
Lemma lem7665565 : True = term141.
Proof. exact (SYM (@lem7665564)). Qed.
Lemma lem7665566 : term141.
Proof. exact (EQ_MP (@lem7665565) (@lem0)). Qed.
Lemma lem7665567 : term201.
Proof. exact (@lem7665556 (@lem7665566)). Qed.
Lemma lem7665569 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7665570 : term97 = term98.
Proof. exact (@lem7665569 term11 term11). Qed.
Lemma lem7665571 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7665572 : term100 = term11.
Proof. exact (EQ_MP (@lem7665571) (@lem940073)). Qed.
Lemma lem7665573 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7665574 : term98 = term64.
Proof. exact (MK_COMB (@lem7665573) (@lem7665572)). Qed.
Lemma lem7665575 : term97 = term64.
Proof. exact (TRANS (@lem7665570) (@lem7665574)). Qed.
Lemma lem7665577 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7665578 : term115 = term120.
Proof. exact (@lem7665577 term11 term11). Qed.
Lemma lem7665579 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7665580 : term100 = term11.
Proof. exact (EQ_MP (@lem7665579) (@lem940073)). Qed.
Lemma lem7665581 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7665582 : term98 = term64.
Proof. exact (MK_COMB (@lem7665581) (@lem7665580)). Qed.
Lemma lem7665583 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7665584 : term120 = term88.
Proof. exact (MK_COMB (@lem7665583) (@lem7665582)). Qed.
Lemma lem7665585 : term115 = term88.
Proof. exact (TRANS (@lem7665578) (@lem7665584)). Qed.
Lemma lem7665586 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7665587 : term202 = term194.
Proof. exact (MK_COMB (@lem7665586) (@lem7665585)). Qed.
Lemma lem7665588 : term203 = term196.
Proof. exact (MK_COMB (@lem7665587) (@lem7665575)). Qed.
Lemma lem7665590 (m : nat) : (term204 m) = term52.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7665591 : term196 = term52.
Proof. exact (@lem7665590 term11). Qed.
Lemma lem7665592 : term203 = term52.
Proof. exact (TRANS (@lem7665588) (@lem7665591)). Qed.
Lemma lem7665593 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7665594 : term205 = term151.
Proof. exact (MK_COMB (@lem7665593) (@lem7665592)). Qed.
Lemma lem7665595 : term64 = term64.
Proof. exact (eq_refl term64). Qed.
Lemma lem7665596 : term206 = term153.
Proof. exact (MK_COMB (@lem7665594) (@lem7665595)). Qed.
Lemma lem7665598 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7665599 : term153 = term52.
Proof. exact (@lem7665598 term11). Qed.
Lemma lem7665600 : term206 = term52.
Proof. exact (TRANS (@lem7665596) (@lem7665599)). Qed.
Lemma lem7665602 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7665603 : term97 = term98.
Proof. exact (@lem7665602 term11 term11). Qed.
Lemma lem7665604 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7665605 : term100 = term11.
Proof. exact (EQ_MP (@lem7665604) (@lem940073)). Qed.
Lemma lem7665606 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7665607 : term98 = term64.
Proof. exact (MK_COMB (@lem7665606) (@lem7665605)). Qed.
Lemma lem7665608 : term97 = term64.
Proof. exact (TRANS (@lem7665603) (@lem7665607)). Qed.
Lemma lem7665609 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem7665610 : term155 = term153.
Proof. exact (MK_COMB (@lem7665609) (@lem7665608)). Qed.
Lemma lem7665612 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7665613 : term153 = term52.
Proof. exact (@lem7665612 term11). Qed.
Lemma lem7665614 : term155 = term52.
Proof. exact (TRANS (@lem7665610) (@lem7665613)). Qed.
Lemma lem7665615 : term52 = term155.
Proof. exact (SYM (@lem7665614)). Qed.
Lemma lem7665616 : term206 = term155.
Proof. exact (TRANS (@lem7665600) (@lem7665615)). Qed.
Lemma lem7665617 : term197 = term85.
Proof. exact (@lem7665567 (@lem7665616)). Qed.
Lemma lem7665618 : term196 = term85.
Proof. exact (TRANS (@lem7665533) (@lem7665617)). Qed.
Lemma lem7665620 (x : real) : (term104 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7665621 : term85 = term52.
Proof. exact (@lem7665620 term52). Qed.
Lemma lem7665622 : term196 = term52.
Proof. exact (TRANS (@lem7665618) (@lem7665621)). Qed.
Lemma lem7665623 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7665624 : term207 = term151.
Proof. exact (MK_COMB (@lem7665623) (@lem7665622)). Qed.
Lemma lem7665625 (_98770 : int) : (real_of_int _98770) = (real_of_int _98770).
Proof. exact (eq_refl (real_of_int _98770)). Qed.
Lemma lem7665626 (_98770 : int) : (term193 _98770) = (term208 _98770).
Proof. exact (MK_COMB (@lem7665624) (@lem7665625 _98770)). Qed.
Lemma lem7665627 (_98770 : int) : (term192 _98770) = (term208 _98770).
Proof. exact (TRANS (@lem7665524 _98770) (@lem7665626 _98770)). Qed.
Lemma lem7665628 (_98770 : int) : (term208 _98770) = term52.
Proof. exact (@lem1982719 (real_of_int _98770)). Qed.
Lemma lem7665629 (_98770 : int) : (term192 _98770) = term52.
Proof. exact (TRANS (@lem7665627 _98770) (@lem7665628 _98770)). Qed.
Lemma lem7665630 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7665631 (_98770 : int) : (term209 _98770) = term210.
Proof. exact (MK_COMB (@lem7665630) (@lem7665629 _98770)). Qed.
Lemma lem7665632 : term88 = term88.
Proof. exact (eq_refl term88). Qed.
Lemma lem7665633 (_98770 : int) : (term191 _98770) = term211.
Proof. exact (MK_COMB (@lem7665631 _98770) (@lem7665632)). Qed.
Lemma lem7665634 (_98770 : int) : (term190 _98770) = term211.
Proof. exact (TRANS (@lem7665523 _98770) (@lem7665633 _98770)). Qed.
Lemma lem7665635 : term211 = term88.
Proof. exact (@lem1982721 term88). Qed.
Lemma lem7665636 (_98770 : int) : (term190 _98770) = term88.
Proof. exact (TRANS (@lem7665634 _98770) (@lem7665635)). Qed.
Lemma lem7665637 (_98769 : int) : (term65 _98769) = (term65 _98769).
Proof. exact (eq_refl (term65 _98769)). Qed.
Lemma lem7665638 (_98770 : int) (_98769 : int) : (term189 _98769 _98770) = (term212 _98769).
Proof. exact (MK_COMB (@lem7665637 _98769) (@lem7665636 _98770)). Qed.
Lemma lem7665639 (_98770 : int) (_98769 : int) : (term188 _98769 _98770) = (term212 _98769).
Proof. exact (TRANS (@lem7665522 _98769 _98770) (@lem7665638 _98770 _98769)). Qed.
Lemma lem7665640 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7665641 (_98770 : int) (_98769 : int) : (term213 _98769 _98770) = (term214 _98769).
Proof. exact (MK_COMB (@lem7665640) (@lem7665639 _98770 _98769)). Qed.
Lemma lem7665642 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7665643 (_98770 : int) (_98769 : int) : (term187 _98769 _98770) = (term215 _98769).
Proof. exact (MK_COMB (@lem7665641 _98770 _98769) (@lem7665642)). Qed.
Lemma lem7665644 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : term215 _98769.
Proof. exact (EQ_MP (@lem7665643 _98770 _98769) (@lem7665521 _98770 _98769 h1)). Qed.
Lemma lem7665646 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7665647 : term165 = term141.
Proof. exact (@lem7665646 term52 term64). Qed.
Lemma lem7665649 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7665650 : term64 = term114.
Proof. exact (@lem7665649 term11). Qed.
Lemma lem7665652 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7665653 : term52 = term85.
Proof. exact (@lem7665652 (NUMERAL 0)). Qed.
Lemma lem7665654 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7665655 : term166 = term167.
Proof. exact (MK_COMB (@lem7665654) (@lem7665653)). Qed.
Lemma lem7665656 : term141 = term168.
Proof. exact (MK_COMB (@lem7665655) (@lem7665650)). Qed.
Lemma lem7665657 : term169.
Proof. exact (@lem1980255 term52 term64 term64 term64). Qed.
Lemma lem7665659 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7665660 : term141 = term142.
Proof. exact (@lem7665659 (NUMERAL 0) term11). Qed.
Lemma lem7665661 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7665662 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7665663 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7665662 h1) (fun h1 : term142 = True => @lem7665661)). Qed.
Lemma lem7665664 : term142 = True.
Proof. exact (EQ_MP (@lem7665663) (@lem7665661)). Qed.
Lemma lem7665665 : term141 = True.
Proof. exact (TRANS (@lem7665660) (@lem7665664)). Qed.
Lemma lem7665666 : True = term141.
Proof. exact (SYM (@lem7665665)). Qed.
Lemma lem7665667 : term141.
Proof. exact (EQ_MP (@lem7665666) (@lem0)). Qed.
Lemma lem7665668 : term170.
Proof. exact (@lem7665657 (@lem7665667)). Qed.
Lemma lem7665670 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7665671 : term141 = term142.
Proof. exact (@lem7665670 (NUMERAL 0) term11). Qed.
Lemma lem7665672 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7665673 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7665674 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7665673 h1) (fun h1 : term142 = True => @lem7665672)). Qed.
Lemma lem7665675 : term142 = True.
Proof. exact (EQ_MP (@lem7665674) (@lem7665672)). Qed.
Lemma lem7665676 : term141 = True.
Proof. exact (TRANS (@lem7665671) (@lem7665675)). Qed.
Lemma lem7665677 : True = term141.
Proof. exact (SYM (@lem7665676)). Qed.
Lemma lem7665678 : term141.
Proof. exact (EQ_MP (@lem7665677) (@lem0)). Qed.
Lemma lem7665679 : term168 = term171.
Proof. exact (@lem7665668 (@lem7665678)). Qed.
Lemma lem7665681 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7665682 : term97 = term98.
Proof. exact (@lem7665681 term11 term11). Qed.
Lemma lem7665683 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7665684 : term100 = term11.
Proof. exact (EQ_MP (@lem7665683) (@lem940073)). Qed.
Lemma lem7665685 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7665686 : term98 = term64.
Proof. exact (MK_COMB (@lem7665685) (@lem7665684)). Qed.
Lemma lem7665687 : term97 = term64.
Proof. exact (TRANS (@lem7665682) (@lem7665686)). Qed.
Lemma lem7665689 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7665690 : term153 = term52.
Proof. exact (@lem7665689 term11). Qed.
Lemma lem7665691 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7665692 : term172 = term166.
Proof. exact (MK_COMB (@lem7665691) (@lem7665690)). Qed.
Lemma lem7665693 : term171 = term141.
Proof. exact (MK_COMB (@lem7665692) (@lem7665687)). Qed.
Lemma lem7665695 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7665696 : term141 = term142.
Proof. exact (@lem7665695 (NUMERAL 0) term11). Qed.
Lemma lem7665697 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7665698 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7665699 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7665698 h1) (fun h1 : term142 = True => @lem7665697)). Qed.
Lemma lem7665700 : term142 = True.
Proof. exact (EQ_MP (@lem7665699) (@lem7665697)). Qed.
Lemma lem7665701 : term141 = True.
Proof. exact (TRANS (@lem7665696) (@lem7665700)). Qed.
Lemma lem7665702 : term171 = True.
Proof. exact (TRANS (@lem7665693) (@lem7665701)). Qed.
Lemma lem7665703 : term168 = True.
Proof. exact (TRANS (@lem7665679) (@lem7665702)). Qed.
Lemma lem7665704 : term141 = True.
Proof. exact (TRANS (@lem7665656) (@lem7665703)). Qed.
Lemma lem7665705 : term165 = True.
Proof. exact (TRANS (@lem7665647) (@lem7665704)). Qed.
Lemma lem7665706 : True = term165.
Proof. exact (SYM (@lem7665705)). Qed.
Lemma lem7665707 : term165.
Proof. exact (EQ_MP (@lem7665706) (@lem0)). Qed.
Lemma lem7665708 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : term216 _98769.
Proof. exact (conj (@lem7665707) (@lem7665644 _98770 _98769 h1)). Qed.
Lemma lem7665710 (x : real) (y : real) : term174 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7665711 (_98769 : int) : term217 _98769.
Proof. exact (@lem7665710 term64 (term212 _98769)). Qed.
Lemma lem7665712 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : term218 _98769.
Proof. exact (@lem7665711 _98769 (@lem7665708 _98770 _98769 h1)). Qed.
Lemma lem7665713 (_98769 : int) : (term219 _98769) = (term212 _98769).
Proof. exact (@lem1982733 (term212 _98769)). Qed.
Lemma lem7665714 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7665715 (_98769 : int) : (term220 _98769) = (term214 _98769).
Proof. exact (MK_COMB (@lem7665714) (@lem7665713 _98769)). Qed.
Lemma lem7665716 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7665717 (_98769 : int) : (term218 _98769) = (term215 _98769).
Proof. exact (MK_COMB (@lem7665715 _98769) (@lem7665716)). Qed.
Lemma lem7665718 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : term215 _98769.
Proof. exact (EQ_MP (@lem7665717 _98769) (@lem7665712 _98770 _98769 h1)). Qed.
Lemma lem7665720 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7665721 : term165 = term141.
Proof. exact (@lem7665720 term52 term64). Qed.
Lemma lem7665723 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7665724 : term64 = term114.
Proof. exact (@lem7665723 term11). Qed.
Lemma lem7665726 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7665727 : term52 = term85.
Proof. exact (@lem7665726 (NUMERAL 0)). Qed.
Lemma lem7665728 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7665729 : term166 = term167.
Proof. exact (MK_COMB (@lem7665728) (@lem7665727)). Qed.
Lemma lem7665730 : term141 = term168.
Proof. exact (MK_COMB (@lem7665729) (@lem7665724)). Qed.
Lemma lem7665731 : term169.
Proof. exact (@lem1980255 term52 term64 term64 term64). Qed.
Lemma lem7665733 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7665734 : term141 = term142.
Proof. exact (@lem7665733 (NUMERAL 0) term11). Qed.
Lemma lem7665735 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7665736 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7665737 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7665736 h1) (fun h1 : term142 = True => @lem7665735)). Qed.
Lemma lem7665738 : term142 = True.
Proof. exact (EQ_MP (@lem7665737) (@lem7665735)). Qed.
Lemma lem7665739 : term141 = True.
Proof. exact (TRANS (@lem7665734) (@lem7665738)). Qed.
Lemma lem7665740 : True = term141.
Proof. exact (SYM (@lem7665739)). Qed.
Lemma lem7665741 : term141.
Proof. exact (EQ_MP (@lem7665740) (@lem0)). Qed.
Lemma lem7665742 : term170.
Proof. exact (@lem7665731 (@lem7665741)). Qed.
Lemma lem7665744 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7665745 : term141 = term142.
Proof. exact (@lem7665744 (NUMERAL 0) term11). Qed.
Lemma lem7665746 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7665747 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7665748 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7665747 h1) (fun h1 : term142 = True => @lem7665746)). Qed.
Lemma lem7665749 : term142 = True.
Proof. exact (EQ_MP (@lem7665748) (@lem7665746)). Qed.
Lemma lem7665750 : term141 = True.
Proof. exact (TRANS (@lem7665745) (@lem7665749)). Qed.
Lemma lem7665751 : True = term141.
Proof. exact (SYM (@lem7665750)). Qed.
Lemma lem7665752 : term141.
Proof. exact (EQ_MP (@lem7665751) (@lem0)). Qed.
Lemma lem7665753 : term168 = term171.
Proof. exact (@lem7665742 (@lem7665752)). Qed.
Lemma lem7665755 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7665756 : term97 = term98.
Proof. exact (@lem7665755 term11 term11). Qed.
Lemma lem7665757 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7665758 : term100 = term11.
Proof. exact (EQ_MP (@lem7665757) (@lem940073)). Qed.
Lemma lem7665759 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7665760 : term98 = term64.
Proof. exact (MK_COMB (@lem7665759) (@lem7665758)). Qed.
Lemma lem7665761 : term97 = term64.
Proof. exact (TRANS (@lem7665756) (@lem7665760)). Qed.
Lemma lem7665763 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7665764 : term153 = term52.
Proof. exact (@lem7665763 term11). Qed.
Lemma lem7665765 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7665766 : term172 = term166.
Proof. exact (MK_COMB (@lem7665765) (@lem7665764)). Qed.
Lemma lem7665767 : term171 = term141.
Proof. exact (MK_COMB (@lem7665766) (@lem7665761)). Qed.
Lemma lem7665769 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7665770 : term141 = term142.
Proof. exact (@lem7665769 (NUMERAL 0) term11). Qed.
Lemma lem7665771 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7665772 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7665773 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7665772 h1) (fun h1 : term142 = True => @lem7665771)). Qed.
Lemma lem7665774 : term142 = True.
Proof. exact (EQ_MP (@lem7665773) (@lem7665771)). Qed.
Lemma lem7665775 : term141 = True.
Proof. exact (TRANS (@lem7665770) (@lem7665774)). Qed.
Lemma lem7665776 : term171 = True.
Proof. exact (TRANS (@lem7665767) (@lem7665775)). Qed.
Lemma lem7665777 : term168 = True.
Proof. exact (TRANS (@lem7665753) (@lem7665776)). Qed.
Lemma lem7665778 : term141 = True.
Proof. exact (TRANS (@lem7665730) (@lem7665777)). Qed.
Lemma lem7665779 : term165 = True.
Proof. exact (TRANS (@lem7665721) (@lem7665778)). Qed.
Lemma lem7665780 : True = term165.
Proof. exact (SYM (@lem7665779)). Qed.
Lemma lem7665781 : term165.
Proof. exact (EQ_MP (@lem7665780) (@lem0)). Qed.
Lemma lem7665782 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : term221 _98769.
Proof. exact (conj (@lem7665781) (@lem7665367 _98770 _98769 h1)). Qed.
Lemma lem7665784 (x : real) (y : real) : term174 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7665785 (_98769 : int) : term222 _98769.
Proof. exact (@lem7665784 term64 (term135 _98769)). Qed.
Lemma lem7665786 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : term223 _98769.
Proof. exact (@lem7665785 _98769 (@lem7665782 _98770 _98769 h1)). Qed.
Lemma lem7665787 (_98769 : int) : (term224 _98769) = (term135 _98769).
Proof. exact (@lem1982733 (term135 _98769)). Qed.
Lemma lem7665788 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7665789 (_98769 : int) : (term225 _98769) = (term158 _98769).
Proof. exact (MK_COMB (@lem7665788) (@lem7665787 _98769)). Qed.
Lemma lem7665790 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7665791 (_98769 : int) : (term223 _98769) = (term159 _98769).
Proof. exact (MK_COMB (@lem7665789 _98769) (@lem7665790)). Qed.
Lemma lem7665792 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : term159 _98769.
Proof. exact (EQ_MP (@lem7665791 _98769) (@lem7665786 _98770 _98769 h1)). Qed.
Lemma lem7665793 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : term226 _98769.
Proof. exact (conj (@lem7665792 _98770 _98769 h1) (@lem7665718 _98770 _98769 h1)). Qed.
Lemma lem7665795 (x : real) (y : real) : term185 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7665796 (_98769 : int) : term227 _98769.
Proof. exact (@lem7665795 (term135 _98769) (term212 _98769)). Qed.
Lemma lem7665797 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : term228 _98769.
Proof. exact (@lem7665796 _98769 (@lem7665793 _98770 _98769 h1)). Qed.
Lemma lem7665798 (_98769 : int) : (term229 _98769) = (term191 _98769).
Proof. exact (@lem1982763 (term135 _98769) (real_of_int _98769) term88). Qed.
Lemma lem7665799 (_98769 : int) : (term192 _98769) = (term193 _98769).
Proof. exact (@lem1982713 term88 (real_of_int _98769)). Qed.
Lemma lem7665801 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7665802 : term64 = term114.
Proof. exact (@lem7665801 term11). Qed.
Lemma lem7665804 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7665805 : term88 = term89.
Proof. exact (@lem7665804 term11). Qed.
Lemma lem7665806 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7665807 : term194 = term195.
Proof. exact (MK_COMB (@lem7665806) (@lem7665805)). Qed.
Lemma lem7665808 : term196 = term197.
Proof. exact (MK_COMB (@lem7665807) (@lem7665802)). Qed.
Lemma lem7665809 : term198.
Proof. exact (@lem1981473 term88 term64 term64 term64 term52 term64). Qed.
Lemma lem7665811 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7665812 : term141 = term142.
Proof. exact (@lem7665811 (NUMERAL 0) term11). Qed.
Lemma lem7665813 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7665814 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7665815 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7665814 h1) (fun h1 : term142 = True => @lem7665813)). Qed.
Lemma lem7665816 : term142 = True.
Proof. exact (EQ_MP (@lem7665815) (@lem7665813)). Qed.
Lemma lem7665817 : term141 = True.
Proof. exact (TRANS (@lem7665812) (@lem7665816)). Qed.
Lemma lem7665818 : True = term141.
Proof. exact (SYM (@lem7665817)). Qed.
Lemma lem7665819 : term141.
Proof. exact (EQ_MP (@lem7665818) (@lem0)). Qed.
Lemma lem7665820 : term199.
Proof. exact (@lem7665809 (@lem7665819)). Qed.
Lemma lem7665822 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7665823 : term141 = term142.
Proof. exact (@lem7665822 (NUMERAL 0) term11). Qed.
Lemma lem7665824 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7665825 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7665826 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7665825 h1) (fun h1 : term142 = True => @lem7665824)). Qed.
Lemma lem7665827 : term142 = True.
Proof. exact (EQ_MP (@lem7665826) (@lem7665824)). Qed.
Lemma lem7665828 : term141 = True.
Proof. exact (TRANS (@lem7665823) (@lem7665827)). Qed.
Lemma lem7665829 : True = term141.
Proof. exact (SYM (@lem7665828)). Qed.
Lemma lem7665830 : term141.
Proof. exact (EQ_MP (@lem7665829) (@lem0)). Qed.
Lemma lem7665831 : term200.
Proof. exact (@lem7665820 (@lem7665830)). Qed.
Lemma lem7665833 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7665834 : term141 = term142.
Proof. exact (@lem7665833 (NUMERAL 0) term11). Qed.
Lemma lem7665835 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7665836 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7665837 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7665836 h1) (fun h1 : term142 = True => @lem7665835)). Qed.
Lemma lem7665838 : term142 = True.
Proof. exact (EQ_MP (@lem7665837) (@lem7665835)). Qed.
Lemma lem7665839 : term141 = True.
Proof. exact (TRANS (@lem7665834) (@lem7665838)). Qed.
Lemma lem7665840 : True = term141.
Proof. exact (SYM (@lem7665839)). Qed.
Lemma lem7665841 : term141.
Proof. exact (EQ_MP (@lem7665840) (@lem0)). Qed.
Lemma lem7665842 : term201.
Proof. exact (@lem7665831 (@lem7665841)). Qed.
Lemma lem7665844 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7665845 : term97 = term98.
Proof. exact (@lem7665844 term11 term11). Qed.
Lemma lem7665846 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7665847 : term100 = term11.
Proof. exact (EQ_MP (@lem7665846) (@lem940073)). Qed.
Lemma lem7665848 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7665849 : term98 = term64.
Proof. exact (MK_COMB (@lem7665848) (@lem7665847)). Qed.
Lemma lem7665850 : term97 = term64.
Proof. exact (TRANS (@lem7665845) (@lem7665849)). Qed.
Lemma lem7665852 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7665853 : term115 = term120.
Proof. exact (@lem7665852 term11 term11). Qed.
Lemma lem7665854 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7665855 : term100 = term11.
Proof. exact (EQ_MP (@lem7665854) (@lem940073)). Qed.
Lemma lem7665856 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7665857 : term98 = term64.
Proof. exact (MK_COMB (@lem7665856) (@lem7665855)). Qed.
Lemma lem7665858 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7665859 : term120 = term88.
Proof. exact (MK_COMB (@lem7665858) (@lem7665857)). Qed.
Lemma lem7665860 : term115 = term88.
Proof. exact (TRANS (@lem7665853) (@lem7665859)). Qed.
Lemma lem7665861 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7665862 : term202 = term194.
Proof. exact (MK_COMB (@lem7665861) (@lem7665860)). Qed.
Lemma lem7665863 : term203 = term196.
Proof. exact (MK_COMB (@lem7665862) (@lem7665850)). Qed.
Lemma lem7665865 (m : nat) : (term204 m) = term52.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7665866 : term196 = term52.
Proof. exact (@lem7665865 term11). Qed.
Lemma lem7665867 : term203 = term52.
Proof. exact (TRANS (@lem7665863) (@lem7665866)). Qed.
Lemma lem7665868 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7665869 : term205 = term151.
Proof. exact (MK_COMB (@lem7665868) (@lem7665867)). Qed.
Lemma lem7665870 : term64 = term64.
Proof. exact (eq_refl term64). Qed.
Lemma lem7665871 : term206 = term153.
Proof. exact (MK_COMB (@lem7665869) (@lem7665870)). Qed.
Lemma lem7665873 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7665874 : term153 = term52.
Proof. exact (@lem7665873 term11). Qed.
Lemma lem7665875 : term206 = term52.
Proof. exact (TRANS (@lem7665871) (@lem7665874)). Qed.
Lemma lem7665877 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7665878 : term97 = term98.
Proof. exact (@lem7665877 term11 term11). Qed.
Lemma lem7665879 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7665880 : term100 = term11.
Proof. exact (EQ_MP (@lem7665879) (@lem940073)). Qed.
Lemma lem7665881 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7665882 : term98 = term64.
Proof. exact (MK_COMB (@lem7665881) (@lem7665880)). Qed.
Lemma lem7665883 : term97 = term64.
Proof. exact (TRANS (@lem7665878) (@lem7665882)). Qed.
Lemma lem7665884 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem7665885 : term155 = term153.
Proof. exact (MK_COMB (@lem7665884) (@lem7665883)). Qed.
Lemma lem7665887 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7665888 : term153 = term52.
Proof. exact (@lem7665887 term11). Qed.
Lemma lem7665889 : term155 = term52.
Proof. exact (TRANS (@lem7665885) (@lem7665888)). Qed.
Lemma lem7665890 : term52 = term155.
Proof. exact (SYM (@lem7665889)). Qed.
Lemma lem7665891 : term206 = term155.
Proof. exact (TRANS (@lem7665875) (@lem7665890)). Qed.
Lemma lem7665892 : term197 = term85.
Proof. exact (@lem7665842 (@lem7665891)). Qed.
Lemma lem7665893 : term196 = term85.
Proof. exact (TRANS (@lem7665808) (@lem7665892)). Qed.
Lemma lem7665895 (x : real) : (term104 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7665896 : term85 = term52.
Proof. exact (@lem7665895 term52). Qed.
Lemma lem7665897 : term196 = term52.
Proof. exact (TRANS (@lem7665893) (@lem7665896)). Qed.
Lemma lem7665898 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7665899 : term207 = term151.
Proof. exact (MK_COMB (@lem7665898) (@lem7665897)). Qed.
Lemma lem7665900 (_98769 : int) : (real_of_int _98769) = (real_of_int _98769).
Proof. exact (eq_refl (real_of_int _98769)). Qed.
Lemma lem7665901 (_98769 : int) : (term193 _98769) = (term208 _98769).
Proof. exact (MK_COMB (@lem7665899) (@lem7665900 _98769)). Qed.
Lemma lem7665902 (_98769 : int) : (term192 _98769) = (term208 _98769).
Proof. exact (TRANS (@lem7665799 _98769) (@lem7665901 _98769)). Qed.
Lemma lem7665903 (_98769 : int) : (term208 _98769) = term52.
Proof. exact (@lem1982719 (real_of_int _98769)). Qed.
Lemma lem7665904 (_98769 : int) : (term192 _98769) = term52.
Proof. exact (TRANS (@lem7665902 _98769) (@lem7665903 _98769)). Qed.
Lemma lem7665905 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7665906 (_98769 : int) : (term209 _98769) = term210.
Proof. exact (MK_COMB (@lem7665905) (@lem7665904 _98769)). Qed.
Lemma lem7665907 : term88 = term88.
Proof. exact (eq_refl term88). Qed.
Lemma lem7665908 (_98769 : int) : (term191 _98769) = term211.
Proof. exact (MK_COMB (@lem7665906 _98769) (@lem7665907)). Qed.
Lemma lem7665909 (_98769 : int) : (term229 _98769) = term211.
Proof. exact (TRANS (@lem7665798 _98769) (@lem7665908 _98769)). Qed.
Lemma lem7665910 : term211 = term88.
Proof. exact (@lem1982721 term88). Qed.
Lemma lem7665911 (_98769 : int) : (term229 _98769) = term88.
Proof. exact (TRANS (@lem7665909 _98769) (@lem7665910)). Qed.
Lemma lem7665912 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7665913 (_98769 : int) : (term230 _98769) = term231.
Proof. exact (MK_COMB (@lem7665912) (@lem7665911 _98769)). Qed.
Lemma lem7665914 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7665915 (_98769 : int) : (term228 _98769) = term232.
Proof. exact (MK_COMB (@lem7665913 _98769) (@lem7665914)). Qed.
Lemma lem7665916 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : term232.
Proof. exact (EQ_MP (@lem7665915 _98769) (@lem7665797 _98770 _98769 h1)). Qed.
Lemma lem7665918 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7665919 : term232 = term233.
Proof. exact (@lem7665918 term52 term88). Qed.
Lemma lem7665921 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7665922 : term88 = term89.
Proof. exact (@lem7665921 term11). Qed.
Lemma lem7665924 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7665925 : term52 = term85.
Proof. exact (@lem7665924 (NUMERAL 0)). Qed.
Lemma lem7665926 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7665927 : term54 = term234.
Proof. exact (MK_COMB (@lem7665926) (@lem7665925)). Qed.
Lemma lem7665928 : term233 = term235.
Proof. exact (MK_COMB (@lem7665927) (@lem7665922)). Qed.
Lemma lem7665929 : term236.
Proof. exact (@lem1980026 term52 term64 term88 term64). Qed.
Lemma lem7665931 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7665932 : term141 = term142.
Proof. exact (@lem7665931 (NUMERAL 0) term11). Qed.
Lemma lem7665933 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7665934 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7665935 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7665934 h1) (fun h1 : term142 = True => @lem7665933)). Qed.
Lemma lem7665936 : term142 = True.
Proof. exact (EQ_MP (@lem7665935) (@lem7665933)). Qed.
Lemma lem7665937 : term141 = True.
Proof. exact (TRANS (@lem7665932) (@lem7665936)). Qed.
Lemma lem7665938 : True = term141.
Proof. exact (SYM (@lem7665937)). Qed.
Lemma lem7665939 : term141.
Proof. exact (EQ_MP (@lem7665938) (@lem0)). Qed.
Lemma lem7665940 : term237.
Proof. exact (@lem7665929 (@lem7665939)). Qed.
Lemma lem7665942 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7665943 : term141 = term142.
Proof. exact (@lem7665942 (NUMERAL 0) term11). Qed.
Lemma lem7665944 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7665945 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7665946 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7665945 h1) (fun h1 : term142 = True => @lem7665944)). Qed.
Lemma lem7665947 : term142 = True.
Proof. exact (EQ_MP (@lem7665946) (@lem7665944)). Qed.
Lemma lem7665948 : term141 = True.
Proof. exact (TRANS (@lem7665943) (@lem7665947)). Qed.
Lemma lem7665949 : True = term141.
Proof. exact (SYM (@lem7665948)). Qed.
Lemma lem7665950 : term141.
Proof. exact (EQ_MP (@lem7665949) (@lem0)). Qed.
Lemma lem7665951 : term235 = term238.
Proof. exact (@lem7665940 (@lem7665950)). Qed.
Lemma lem7665953 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7665954 : term115 = term120.
Proof. exact (@lem7665953 term11 term11). Qed.
Lemma lem7665955 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7665956 : term100 = term11.
Proof. exact (EQ_MP (@lem7665955) (@lem940073)). Qed.
Lemma lem7665957 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7665958 : term98 = term64.
Proof. exact (MK_COMB (@lem7665957) (@lem7665956)). Qed.
Lemma lem7665959 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7665960 : term120 = term88.
Proof. exact (MK_COMB (@lem7665959) (@lem7665958)). Qed.
Lemma lem7665961 : term115 = term88.
Proof. exact (TRANS (@lem7665954) (@lem7665960)). Qed.
Lemma lem7665963 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7665964 : term153 = term52.
Proof. exact (@lem7665963 term11). Qed.
Lemma lem7665965 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7665966 : term239 = term54.
Proof. exact (MK_COMB (@lem7665965) (@lem7665964)). Qed.
Lemma lem7665967 : term238 = term233.
Proof. exact (MK_COMB (@lem7665966) (@lem7665961)). Qed.
Lemma lem7665969 (m : nat) (n : nat) : (term240 m n) = (term241 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7665970 : term233 = term242.
Proof. exact (@lem7665969 (NUMERAL 0) term11). Qed.
Lemma lem7665971 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7665972 (h1 : term143 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7665973 : (term143 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7665972 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem7665971)). Qed.
Lemma lem7665974 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7665973) (@lem7665971)). Qed.
Lemma lem7665975 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7665976 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7665977 : term243 = (and True).
Proof. exact (MK_COMB (@lem7665976) (@lem7665975)). Qed.
Lemma lem7665978 : term242 = (True /\ False).
Proof. exact (MK_COMB (@lem7665977) (@lem7665974)). Qed.
Lemma lem7665980 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7665981 : term242 = False.
Proof. exact (TRANS (@lem7665978) (@lem7665980)). Qed.
Lemma lem7665982 : term233 = False.
Proof. exact (TRANS (@lem7665970) (@lem7665981)). Qed.
Lemma lem7665983 : term238 = False.
Proof. exact (TRANS (@lem7665967) (@lem7665982)). Qed.
Lemma lem7665984 : term235 = False.
Proof. exact (TRANS (@lem7665951) (@lem7665983)). Qed.
Lemma lem7665985 : term233 = False.
Proof. exact (TRANS (@lem7665928) (@lem7665984)). Qed.
Lemma lem7665986 : term232 = False.
Proof. exact (TRANS (@lem7665919) (@lem7665985)). Qed.
Lemma lem7665987 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : False.
Proof. exact (EQ_MP (@lem7665986) (@lem7665916 _98770 _98769 h1)). Qed.
Lemma lem7665989 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : term164 _98770 _98769.
Proof. exact (h1). Qed.
Lemma lem7665990 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : (term164 _98770 _98769) = False.
Proof. exact (prop_ext (fun h2 : term164 _98770 _98769 => @lem7665987 _98770 _98769 h1) (fun h2 : False => @lem7665989 _98770 _98769 h1)). Qed.
Lemma lem7665991 (_98770 : int) (_98769 : int) (h1 : term164 _98770 _98769) : False.
Proof. exact (EQ_MP (@lem7665990 _98770 _98769 h1) (@lem7665989 _98770 _98769 h1)). Qed.
Lemma lem7665992 (_98770 : int) (_98769 : int) (h1 : term80 _98770 _98769) : term80 _98770 _98769.
Proof. exact (h1). Qed.
Lemma lem7665993 (_98770 : int) (_98769 : int) (h1 : term80 _98770 _98769) : term164 _98770 _98769.
Proof. exact (EQ_MP (@lem7665358 _98770 _98769) (@lem7665992 _98770 _98769 h1)). Qed.
Lemma lem7665994 (_98770 : int) (_98769 : int) (h1 : term80 _98770 _98769) : (term164 _98770 _98769) = False.
Proof. exact (prop_ext (fun h2 : term164 _98770 _98769 => @lem7665991 _98770 _98769 h2) (fun h2 : False => @lem7665993 _98770 _98769 h1)). Qed.
Lemma lem7665995 (_98770 : int) (_98769 : int) (h1 : term80 _98770 _98769) : False.
Proof. exact (EQ_MP (@lem7665994 _98770 _98769 h1) (@lem7665993 _98770 _98769 h1)). Qed.
Lemma lem7665996 (_98770 : int) (_98769 : int) : term244 _98770 _98769.
Proof. exact (fun h0 : term80 _98770 _98769 => @lem7665995 _98770 _98769 h0). Qed.
Lemma lem7665997 (_98770 : int) (_98769 : int) : term245 _98770 _98769.
Proof. exact (@lem1386578 (term246 _98770 _98769)). Qed.
Lemma lem7666000 (_98770 : int) (_98769 : int) : term246 _98770 _98769.
Proof. exact (@lem7665997 _98770 _98769 (@lem7665996 _98770 _98769)). Qed.
Lemma lem7666001 (_98770 : int) (_98769 : int) : (term78 _98770 _98769) = (term45 _98770 _98769).
Proof. exact (SYM (@lem7664949 _98770 _98769)). Qed.
Lemma lem7666002 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7666003 (_98770 : int) (_98769 : int) : (term246 _98770 _98769) = (term25 _98770 _98769).
Proof. exact (MK_COMB (@lem7666002) (@lem7666001 _98770 _98769)). Qed.
Lemma lem7666004 (_98770 : int) (_98769 : int) : term25 _98770 _98769.
Proof. exact (EQ_MP (@lem7666003 _98770 _98769) (@lem7666000 _98770 _98769)). Qed.
Lemma lem7666005 (_98770 : int) (_98769 : int) : term26 _98770 _98769.
Proof. exact (EQ_MP (@lem7664822 _98770 _98769) (@lem7666004 _98770 _98769)). Qed.
Lemma lem7666006 {M : Type'} (i : nat) : term247 M i.
Proof. exact (@lem7666005 (term248 M) (int_of_num i)). Qed.
Lemma lem7666007 {M : Type'} (i : nat) : term249 M i.
Proof. exact (@lem7666006 M i (@lem7664818 i)). Qed.
Lemma lem7666008 {M : Type'} (i : nat) : term20 M i.
Proof. exact (@lem7666007 M i (@lem7664821 M)). Qed.
Lemma lem7666009 {M : Type'} (i : nat) : (term20 M i) = (term0 M i).
Proof. exact (SYM (@lem7664815 M i)). Qed.
Lemma lem7666010 {M : Type'} (i : nat) : term0 M i.
Proof. exact (EQ_MP (@lem7666009 M i) (@lem7666008 M i)). Qed.
Lemma lem7666011 {A M N : Type'} (f : cart A M) : term250 A M N f.
Proof. exact (@lem7632649 A M N f). Qed.
Lemma lem7666012 {A M N : Type'} (f : cart A M) : (term250 A M N f) = (term251 A M N f).
Proof. exact (eq_refl (term250 A M N f)). Qed.
Lemma lem7666013 {A M N : Type'} (f : cart A M) : term251 A M N f.
Proof. exact (EQ_MP (@lem7666012 A M N f) (@lem7666011 A M N f)). Qed.
Lemma lem7666014 {A M N : Type'} (f : cart A M) (g : cart A N) : term252 A M N f g.
Proof. exact (@lem7666013 A M N f g). Qed.
Lemma lem7666015 {A M N : Type'} (f : cart A M) (g : cart A N) : (term252 A M N f g) = ((@pastecart A M N f g) = (term253 A M N f g)).
Proof. exact (eq_refl (term252 A M N f g)). Qed.
Lemma lem7666038 {A M N : Type'} (f : cart A M) (g : cart A N) : (@pastecart A M N f g) = (term253 A M N f g).
Proof. exact (EQ_MP (@lem7666015 A M N f g) (@lem7666014 A M N f g)). Qed.
Lemma lem7666039 {A M N : Type'} (f : cart A M) (g : cart A N) : (@pastecart A M N f g) = (term253 A M N f g).
Proof. exact (@lem7666038 A M N f g). Qed.
Lemma lem7666040 {A M N : Type'} (u : cart A M) (v : cart A N) : (@pastecart A M N u v) = (term253 A M N u v).
Proof. exact (@lem7666039 A M N u v). Qed.
Lemma lem7666041 {A M N : Type'} : (@dollar A (finite_sum M N)) = (@dollar A (finite_sum M N)).
Proof. exact (eq_refl (@dollar A (finite_sum M N))). Qed.
Lemma lem7666042 {A M N : Type'} (u : cart A M) (v : cart A N) : (term254 A M N u v) = (term255 A M N u v).
Proof. exact (MK_COMB (@lem7666041 A M N) (@lem7666040 A M N u v)). Qed.
Lemma lem7666043 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7666044 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term256 A M N u v i) = (term257 A M N u v i).
Proof. exact (MK_COMB (@lem7666042 A M N u v) (@lem7666043 i)). Qed.
Lemma lem7666045 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem7666046 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term258 A M N u v i) = (term259 A M N u v i).
Proof. exact (MK_COMB (@lem7666045 A) (@lem7666044 A M N u v i)). Qed.
Lemma lem7666047 {A M : Type'} (u : cart A M) (i : nat) : (@dollar A M u i) = (@dollar A M u i).
Proof. exact (eq_refl (@dollar A M u i)). Qed.
Lemma lem7666048 {A M N : Type'} (v : cart A N) (u : cart A M) (i : nat) : ((term256 A M N u v i) = (@dollar A M u i)) = ((term257 A M N u v i) = (@dollar A M u i)).
Proof. exact (MK_COMB (@lem7666046 A M N u v i) (@lem7666047 A M u i)). Qed.
Lemma lem7666051 {M : Type'} (i : nat) : (term260 M i) = (term260 M i).
Proof. exact (eq_refl (term260 M i)). Qed.
Lemma lem7666052 {A M N : Type'} (v : cart A N) (u : cart A M) (i : nat) : (term261 A M N v u i) = (term262 A M N v u i).
Proof. exact (MK_COMB (@lem7666051 M i) (@lem7666048 A M N v u i)). Qed.
Lemma lem7666055 {A M N : Type'} (v : cart A N) (u : cart A M) : (term263 A M N v u) = (term264 A M N v u).
Proof. exact (fun_ext (fun i : nat => @lem7666052 A M N v u i)). Qed.
Lemma lem7666056 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7666057 {A M N : Type'} (v : cart A N) (u : cart A M) : (term265 A M N v u) = (term266 A M N v u).
Proof. exact (MK_COMB (@lem7666056) (@lem7666055 A M N v u)). Qed.
Lemma lem7666062 {A M N : Type'} (u : cart A M) : (term267 A M N u) = (term268 A M N u).
Proof. exact (fun_ext (fun v : cart A N => @lem7666057 A M N v u)). Qed.
Lemma lem7666063 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem7666064 {A M N : Type'} (u : cart A M) : (term269 A M N u) = (term270 A M N u).
Proof. exact (MK_COMB (@lem7666063 A N) (@lem7666062 A M N u)). Qed.
Lemma lem7666069 {A M N : Type'} : (term271 A M N) = (term272 A M N).
Proof. exact (fun_ext (fun u : cart A M => @lem7666064 A M N u)). Qed.
Lemma lem7666070 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem7666071 {A M N : Type'} : (term273 A M N) = (term274 A M N).
Proof. exact (MK_COMB (@lem7666070 A M) (@lem7666069 A M N)). Qed.
Lemma lem7666076 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7666077 {A M N : Type'} : (term275 A M N) = (term276 A M N).
Proof. exact (MK_COMB (@lem7666076) (@lem7666071 A M N)). Qed.
Lemma lem7666097 {A M N : Type'} (f : cart A M) (g : cart A N) : (@pastecart A M N f g) = (term253 A M N f g).
Proof. exact (EQ_MP (@lem7666015 A M N f g) (@lem7666014 A M N f g)). Qed.
Lemma lem7666098 {A M N : Type'} (f : cart A M) (g : cart A N) : (@pastecart A M N f g) = (term253 A M N f g).
Proof. exact (@lem7666097 A M N f g). Qed.
Lemma lem7666099 {A M N : Type'} (u : cart A M) (v : cart A N) : (@pastecart A M N u v) = (term253 A M N u v).
Proof. exact (@lem7666098 A M N u v). Qed.
Lemma lem7666100 {A M N : Type'} : (@dollar A (finite_sum M N)) = (@dollar A (finite_sum M N)).
Proof. exact (eq_refl (@dollar A (finite_sum M N))). Qed.
Lemma lem7666101 {A M N : Type'} (u : cart A M) (v : cart A N) : (term254 A M N u v) = (term255 A M N u v).
Proof. exact (MK_COMB (@lem7666100 A M N) (@lem7666099 A M N u v)). Qed.
Lemma lem7666102 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7666103 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term256 A M N u v i) = (term257 A M N u v i).
Proof. exact (MK_COMB (@lem7666101 A M N u v) (@lem7666102 i)). Qed.
Lemma lem7666104 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem7666105 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term258 A M N u v i) = (term259 A M N u v i).
Proof. exact (MK_COMB (@lem7666104 A) (@lem7666103 A M N u v i)). Qed.
Lemma lem7666106 {A M N : Type'} (v : cart A N) (i : nat) : (term277 A M N v i) = (term277 A M N v i).
Proof. exact (eq_refl (term277 A M N v i)). Qed.
Lemma lem7666107 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : ((term256 A M N u v i) = (term277 A M N v i)) = ((term257 A M N u v i) = (term277 A M N v i)).
Proof. exact (MK_COMB (@lem7666105 A M N u v i) (@lem7666106 A M N v i)). Qed.
Lemma lem7666110 {M N : Type'} (i : nat) : (term278 M N i) = (term278 M N i).
Proof. exact (eq_refl (term278 M N i)). Qed.
Lemma lem7666111 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term279 A M N u v i) = (term280 A M N u v i).
Proof. exact (MK_COMB (@lem7666110 M N i) (@lem7666107 A M N u v i)). Qed.
Lemma lem7666114 {A M N : Type'} (u : cart A M) (v : cart A N) : (term281 A M N u v) = (term282 A M N u v).
Proof. exact (fun_ext (fun i : nat => @lem7666111 A M N u v i)). Qed.
Lemma lem7666115 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7666116 {A M N : Type'} (u : cart A M) (v : cart A N) : (term283 A M N u v) = (term284 A M N u v).
Proof. exact (MK_COMB (@lem7666115) (@lem7666114 A M N u v)). Qed.
Lemma lem7666121 {A M N : Type'} (u : cart A M) : (term285 A M N u) = (term286 A M N u).
Proof. exact (fun_ext (fun v : cart A N => @lem7666116 A M N u v)). Qed.
Lemma lem7666122 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem7666123 {A M N : Type'} (u : cart A M) : (term287 A M N u) = (term288 A M N u).
Proof. exact (MK_COMB (@lem7666122 A N) (@lem7666121 A M N u)). Qed.
Lemma lem7666128 {A M N : Type'} : (term289 A M N) = (term290 A M N).
Proof. exact (fun_ext (fun u : cart A M => @lem7666123 A M N u)). Qed.
Lemma lem7666129 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem7666130 {A M N : Type'} : (term291 A M N) = (term292 A M N).
Proof. exact (MK_COMB (@lem7666129 A M) (@lem7666128 A M N)). Qed.
Lemma lem7666135 {A M N : Type'} : (term293 A M N) = (term294 A M N).
Proof. exact (MK_COMB (@lem7666077 A M N) (@lem7666130 A M N)). Qed.
Lemma lem7666138 {A M N : Type'} : (term294 A M N) = (term293 A M N).
Proof. exact (SYM (@lem7666135 A M N)). Qed.
Lemma lem7666139 {M : Type'} (i : nat) (h1 : term295 M i) : term295 M i.
Proof. exact (h1). Qed.
Lemma lem7666140 {M : Type'} (i : nat) (h1 : term296 M i) : term296 M i.
Proof. exact (h1). Qed.
Lemma lem7666141 (i : nat) (h1 : term3 i) : term3 i.
Proof. exact (h1). Qed.
Lemma lem7666142 {M N : Type'} (i : nat) (h1 : term297 M N i) : term297 M N i.
Proof. exact (h1). Qed.
Lemma lem7666143 {M N : Type'} (i : nat) (h1 : term298 M N i) : term298 M N i.
Proof. exact (h1). Qed.
Lemma lem7666144 {M : Type'} (i : nat) (h1 : term2 M i) : term2 M i.
Proof. exact (h1). Qed.
Lemma lem7666145 {M N : Type'} (i : nat) (h1 : term299 M N i) : term299 M N i.
Proof. exact (h1). Qed.
Lemma lem7666146 {M N : Type'} (i : nat) : (term299 M N i) = ((term299 M N i) = True).
Proof. exact (@lem7 (term299 M N i)). Qed.
Lemma lem7666148 {A B : Type'} (g : nat -> A) (i : nat) : term300 A B g i.
Proof. exact (@lem7622314 A B g i). Qed.
Lemma lem7666149 {A B : Type'} (g : nat -> A) (i : nat) : (term300 A B g i) = (term301 A B g i).
Proof. exact (eq_refl (term300 A B g i)). Qed.
Lemma lem7666150 {A B : Type'} (g : nat -> A) (i : nat) : term301 A B g i.
Proof. exact (EQ_MP (@lem7666149 A B g i) (@lem7666148 A B g i)). Qed.
Lemma lem7666151 {B : Type'} (i : nat) (h1 : term295 B i) : term295 B i.
Proof. exact (h1). Qed.
Lemma lem7666152 {A B : Type'} (g : nat -> A) (i : nat) (h1 : term295 B i) : (term302 A B g i) = (g i).
Proof. exact (@lem7666150 A B g i (@lem7666151 B i h1)). Qed.
Lemma lem7666158 (i : nat) : (term3 i) = ((term3 i) = True).
Proof. exact (@lem7 (term3 i)). Qed.
Lemma lem7666160 {M : Type'} (i : nat) : (term296 M i) = ((term296 M i) = True).
Proof. exact (@lem7 (term296 M i)). Qed.
Lemma lem7666165 {A B : Type'} (g : nat -> A) (i : nat) : term301 A B g i.
Proof. exact (fun h0 : term295 B i => @lem7666152 A B g i h0). Qed.
Lemma lem7666166 {A M N : Type'} (g : nat -> A) (i : nat) : term303 A M N g i.
Proof. exact (@lem7666165 A (finite_sum M N) g i). Qed.
Lemma lem7666167 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : term304 A M N u v i.
Proof. exact (@lem7666166 A M N (term305 A M N u v) i). Qed.
Lemma lem7666171 (i : nat) (h1 : term3 i) : (term3 i) = True.
Proof. exact (EQ_MP (@lem7666158 i) (@lem7666141 i h1)). Qed.
Lemma lem7666172 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7666173 (i : nat) (h1 : term3 i) : (term306 i) = (and True).
Proof. exact (MK_COMB (@lem7666172) (@lem7666171 i h1)). Qed.
Lemma lem7666175 {M N : Type'} (i : nat) (h1 : term299 M N i) : (term299 M N i) = True.
Proof. exact (EQ_MP (@lem7666146 M N i) (@lem7666145 M N i h1)). Qed.
Lemma lem7666176 {M N : Type'} (i : nat) (h1 : term299 M N i) (h2 : term3 i) : (term307 M N i) = (True /\ True).
Proof. exact (MK_COMB (@lem7666173 i h2) (@lem7666175 M N i h1)). Qed.
Lemma lem7666178 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7666179 : (True /\ True) = True.
Proof. exact (@lem7666178 True). Qed.
Lemma lem7666180 {M N : Type'} (i : nat) (h1 : term299 M N i) (h2 : term3 i) : (term307 M N i) = True.
Proof. exact (TRANS (@lem7666176 M N i h1 h2) (@lem7666179)). Qed.
Lemma lem7666181 {M N : Type'} (i : nat) (h1 : term299 M N i) (h2 : term3 i) : True = (term307 M N i).
Proof. exact (SYM (@lem7666180 M N i h1 h2)). Qed.
Lemma lem7666182 {M N : Type'} (i : nat) (h1 : term299 M N i) (h2 : term3 i) : term307 M N i.
Proof. exact (EQ_MP (@lem7666181 M N i h1 h2) (@lem0)). Qed.
Lemma lem7666183 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (h1 : term299 M N i) (h2 : term3 i) : (term257 A M N u v i) = (term308 A M N u v i).
Proof. exact (@lem7666167 A M N u v i (@lem7666182 M N i h1 h2)). Qed.
Lemma lem7666185 {A B : Type'} (f : A -> B) (y : A) : (term309 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7666186 {A : Type'} (f : nat -> A) (y : nat) : (term310 A f y) = (f y).
Proof. exact (@lem7666185 nat A f y). Qed.
Lemma lem7666187 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term311 A M N u v i) = (term308 A M N u v i).
Proof. exact (@lem7666186 A (term305 A M N u v) i). Qed.
Lemma lem7666188 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term308 A M N u v i) = (term312 A M N u v i).
Proof. exact (eq_refl (term308 A M N u v i)). Qed.
Lemma lem7666189 {A M N : Type'} (u : cart A M) (v : cart A N) : (term313 A M N u v) = (term305 A M N u v).
Proof. exact (fun_ext (fun i : nat => @lem7666188 A M N u v i)). Qed.
Lemma lem7666190 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7666191 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term311 A M N u v i) = (term308 A M N u v i).
Proof. exact (MK_COMB (@lem7666189 A M N u v) (@lem7666190 i)). Qed.
Lemma lem7666192 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem7666193 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term314 A M N u v i) = (term315 A M N u v i).
Proof. exact (MK_COMB (@lem7666192 A) (@lem7666191 A M N u v i)). Qed.
Lemma lem7666194 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term308 A M N u v i) = (term312 A M N u v i).
Proof. exact (eq_refl (term308 A M N u v i)). Qed.
Lemma lem7666195 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : ((term311 A M N u v i) = (term308 A M N u v i)) = ((term308 A M N u v i) = (term312 A M N u v i)).
Proof. exact (MK_COMB (@lem7666193 A M N u v i) (@lem7666194 A M N u v i)). Qed.
Lemma lem7666196 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term308 A M N u v i) = (term312 A M N u v i).
Proof. exact (EQ_MP (@lem7666195 A M N u v i) (@lem7666187 A M N u v i)). Qed.
Lemma lem7666198 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term316 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7666199 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term317 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7666198 _2963 g t e g' t' e'). Qed.
Lemma lem7666200 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term318 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7666199 _2963 g t e g' t'). Qed.
Lemma lem7666201 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term319 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7666200 _2963 g t e g'). Qed.
Lemma lem7666202 {A : Type'} (g : Prop) (t : A) (e : A) : term319 A g t e.
Proof. exact (@lem7666201 A g t e). Qed.
Lemma lem7666203 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : term320 A M N u v i.
Proof. exact (@lem7666202 A (term296 M i) (@dollar A M u i) (term277 A M N v i)). Qed.
Lemma lem7666204 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (g' : Prop) : term321 A M N u v i g'.
Proof. exact (@lem7666203 A M N u v i g'). Qed.
Lemma lem7666205 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (g' : Prop) : (term321 A M N u v i g') = (term322 A M N u v i g').
Proof. exact (eq_refl (term321 A M N u v i g')). Qed.
Lemma lem7666206 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (g' : Prop) : term322 A M N u v i g'.
Proof. exact (EQ_MP (@lem7666205 A M N u v i g') (@lem7666204 A M N u v i g')). Qed.
Lemma lem7666207 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (g' : Prop) (t' : A) : term323 A M N u v i g' t'.
Proof. exact (@lem7666206 A M N u v i g' t'). Qed.
Lemma lem7666208 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (g' : Prop) (t' : A) : (term323 A M N u v i g' t') = (term324 A M N u v i g' t').
Proof. exact (eq_refl (term323 A M N u v i g' t')). Qed.
Lemma lem7666209 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (g' : Prop) (t' : A) : term324 A M N u v i g' t'.
Proof. exact (EQ_MP (@lem7666208 A M N u v i g' t') (@lem7666207 A M N u v i g' t')). Qed.
Lemma lem7666210 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (g' : Prop) (t' : A) (e' : A) : term325 A M N u v i g' t' e'.
Proof. exact (@lem7666209 A M N u v i g' t' e'). Qed.
Lemma lem7666211 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (g' : Prop) (t' : A) (e' : A) : (term325 A M N u v i g' t' e') = (term326 A M N u v i g' t' e').
Proof. exact (eq_refl (term325 A M N u v i g' t' e')). Qed.
Lemma lem7666212 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (g' : Prop) (t' : A) (e' : A) : term326 A M N u v i g' t' e'.
Proof. exact (EQ_MP (@lem7666211 A M N u v i g' t' e') (@lem7666210 A M N u v i g' t' e')). Qed.
Lemma lem7666216 {M : Type'} (i : nat) (h1 : term296 M i) : (term296 M i) = True.
Proof. exact (EQ_MP (@lem7666160 M i) (@lem7666140 M i h1)). Qed.
Lemma lem7666217 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (t' : A) (e' : A) : term327 A M N u v i t' e'.
Proof. exact (@lem7666212 A M N u v i True t' e'). Qed.
Lemma lem7666218 {A M N : Type'} (u : cart A M) (v : cart A N) (t' : A) (e' : A) (i : nat) (h1 : term296 M i) : term328 A M N u v i t' e'.
Proof. exact (@lem7666217 A M N u v i t' e' (@lem7666216 M i h1)). Qed.
Lemma lem7666224 {A M : Type'} (u : cart A M) (i : nat) : (@dollar A M u i) = (@dollar A M u i).
Proof. exact (eq_refl (@dollar A M u i)). Qed.
Lemma lem7666225 {A M : Type'} (u : cart A M) (i : nat) : term329 A M u i.
Proof. exact (fun h0 : True => @lem7666224 A M u i). Qed.
Lemma lem7666226 {A M N : Type'} (v : cart A N) (u : cart A M) (e' : A) (i : nat) (h1 : term296 M i) : term330 A M N v u i e'.
Proof. exact (@lem7666218 A M N u v (@dollar A M u i) e' i h1). Qed.
Lemma lem7666227 {A M N : Type'} (v : cart A N) (u : cart A M) (e' : A) (i : nat) (h1 : term296 M i) : term331 A M N v u i e'.
Proof. exact (@lem7666226 A M N v u e' i h1 (@lem7666225 A M u i)). Qed.
Lemma lem7666231 {A M N : Type'} (v : cart A N) (i : nat) : (term277 A M N v i) = (term277 A M N v i).
Proof. exact (eq_refl (term277 A M N v i)). Qed.
Lemma lem7666232 {A M N : Type'} (v : cart A N) (i : nat) : term332 A M N v i.
Proof. exact (fun h0 : ~ True => @lem7666231 A M N v i). Qed.
Lemma lem7666233 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (h1 : term296 M i) : term333 A M N u v i.
Proof. exact (@lem7666227 A M N v u (term277 A M N v i) i h1). Qed.
Lemma lem7666234 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (h1 : term296 M i) : (term312 A M N u v i) = (term334 A M N u v i).
Proof. exact (@lem7666233 A M N u v i h1 (@lem7666232 A M N v i)). Qed.
Lemma lem7666236 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7666237 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem7666236 A t2 t1). Qed.
Lemma lem7666238 {A M N : Type'} (v : cart A N) (u : cart A M) (i : nat) : (term334 A M N u v i) = (@dollar A M u i).
Proof. exact (@lem7666237 A (term277 A M N v i) (@dollar A M u i)). Qed.
Lemma lem7666239 {A M N : Type'} (v : cart A N) (u : cart A M) (i : nat) (h1 : term296 M i) : (term312 A M N u v i) = (@dollar A M u i).
Proof. exact (TRANS (@lem7666234 A M N u v i h1) (@lem7666238 A M N v u i)). Qed.
Lemma lem7666240 {A M N : Type'} (v : cart A N) (u : cart A M) (i : nat) (h1 : term296 M i) : (term308 A M N u v i) = (@dollar A M u i).
Proof. exact (TRANS (@lem7666196 A M N u v i) (@lem7666239 A M N v u i h1)). Qed.
Lemma lem7666241 {A M N : Type'} (v : cart A N) (u : cart A M) (i : nat) (h1 : term296 M i) (h2 : term299 M N i) (h3 : term3 i) : (term257 A M N u v i) = (@dollar A M u i).
Proof. exact (TRANS (@lem7666183 A M N u v i h2 h3) (@lem7666240 A M N v u i h1)). Qed.
Lemma lem7666242 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem7666243 {A M N : Type'} (v : cart A N) (u : cart A M) (i : nat) (h1 : term296 M i) (h2 : term299 M N i) (h3 : term3 i) : (term259 A M N u v i) = (term335 A M u i).
Proof. exact (MK_COMB (@lem7666242 A) (@lem7666241 A M N v u i h1 h2 h3)). Qed.
Lemma lem7666244 {A M : Type'} (u : cart A M) (i : nat) : (@dollar A M u i) = (@dollar A M u i).
Proof. exact (eq_refl (@dollar A M u i)). Qed.
Lemma lem7666245 {A M N : Type'} (v : cart A N) (u : cart A M) (i : nat) (h1 : term296 M i) (h2 : term299 M N i) (h3 : term3 i) : ((term257 A M N u v i) = (@dollar A M u i)) = ((@dollar A M u i) = (@dollar A M u i)).
Proof. exact (MK_COMB (@lem7666243 A M N v u i h1 h2 h3) (@lem7666244 A M u i)). Qed.
Lemma lem7666247 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7666248 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem7666247 A x). Qed.
Lemma lem7666249 {A M : Type'} (u : cart A M) (i : nat) : ((@dollar A M u i) = (@dollar A M u i)) = True.
Proof. exact (@lem7666248 A (@dollar A M u i)). Qed.
Lemma lem7666250 {A M N : Type'} (v : cart A N) (u : cart A M) (i : nat) (h1 : term296 M i) (h2 : term299 M N i) (h3 : term3 i) : ((term257 A M N u v i) = (@dollar A M u i)) = True.
Proof. exact (TRANS (@lem7666245 A M N v u i h1 h2 h3) (@lem7666249 A M u i)). Qed.
Lemma lem7666251 {A M N : Type'} (v : cart A N) (u : cart A M) (i : nat) (h1 : term296 M i) (h2 : term299 M N i) (h3 : term3 i) : True = ((term257 A M N u v i) = (@dollar A M u i)).
Proof. exact (SYM (@lem7666250 A M N v u i h1 h2 h3)). Qed.
Lemma lem7666252 {A M N : Type'} (v : cart A N) (u : cart A M) (i : nat) (h1 : term296 M i) (h2 : term299 M N i) (h3 : term3 i) : (term257 A M N u v i) = (@dollar A M u i).
Proof. exact (EQ_MP (@lem7666251 A M N v u i h1 h2 h3) (@lem0)). Qed.
Lemma lem7666254 {M N : Type'} : (@dimindex (finite_sum M N) (@UNIV (finite_sum M N))) = (term336 M N).
Proof. exact (EQ_MP (@lem7640410 M N) (@lem7640437 M N)). Qed.
Lemma lem7666259 (i : nat) : (Peano.le i) = (Peano.le i).
Proof. exact (eq_refl (Peano.le i)). Qed.
Lemma lem7666260 {M N : Type'} (i : nat) : (term299 M N i) = (term298 M N i).
Proof. exact (MK_COMB (@lem7666259 i) (@lem7666254 M N)). Qed.
Lemma lem7666261 {M N : Type'} (i : nat) : (term298 M N i) = (term299 M N i).
Proof. exact (SYM (@lem7666260 M N i)). Qed.
Lemma lem7666284 {M N : Type'} (i : nat) : (term337 M N i) = (term338 M N i).
Proof. exact (@lem17265 (term296 M i) (term298 M N i)). Qed.
Lemma lem7666286 (i : nat) : (term339 i) = (term339 i).
Proof. exact (eq_refl (term339 i)). Qed.
Lemma lem7666287 {M N : Type'} (i : nat) : (term340 M N i) = (term341 M N i).
Proof. exact (MK_COMB (@lem7666286 i) (@lem7666284 M N i)). Qed.
Lemma lem7666288 {M N : Type'} (i : nat) : (term342 M N i) = (term340 M N i).
Proof. exact (@lem17265 (term3 i) (term337 M N i)). Qed.
Lemma lem7666336 {M N : Type'} (i : nat) : (term342 M N i) = (term341 M N i).
Proof. exact (TRANS (@lem7666288 M N i) (@lem7666287 M N i)). Qed.
Lemma lem7666338 (m : nat) (n : nat) : (Peano.le m n) = (term4 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7666339 (i : nat) : (term3 i) = (term19 i).
Proof. exact (@lem7666338 term11 i). Qed.
Lemma lem7666340 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7666341 (i : nat) : (term343 i) = (term344 i).
Proof. exact (MK_COMB (@lem7666340) (@lem7666339 i)). Qed.
Lemma lem7666342 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7666343 (i : nat) : (term339 i) = (term345 i).
Proof. exact (MK_COMB (@lem7666342) (@lem7666341 i)). Qed.
Lemma lem7666345 (m : nat) (n : nat) : (Peano.le m n) = (term4 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7666346 {M : Type'} (i : nat) : (term296 M i) = (term346 M i).
Proof. exact (@lem7666345 i (@dimindex M (@UNIV M))). Qed.
Lemma lem7666347 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7666348 {M : Type'} (i : nat) : (term347 M i) = (term348 M i).
Proof. exact (MK_COMB (@lem7666347) (@lem7666346 M i)). Qed.
Lemma lem7666349 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7666350 {M : Type'} (i : nat) : (term349 M i) = (term350 M i).
Proof. exact (MK_COMB (@lem7666349) (@lem7666348 M i)). Qed.
Lemma lem7666352 (m : nat) (n : nat) : (Peano.le m n) = (term4 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7666353 {M N : Type'} (i : nat) : (term298 M N i) = (term351 M N i).
Proof. exact (@lem7666352 i (term336 M N)). Qed.
Lemma lem7666355 (m : nat) (n : nat) : (term7 m n) = (term8 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7666356 {M N : Type'} : (term352 M N) = (term353 M N).
Proof. exact (@lem7666355 (@dimindex M (@UNIV M)) (@dimindex N (@UNIV N))). Qed.
Lemma lem7666357 (i : nat) : (term354 i) = (term354 i).
Proof. exact (eq_refl (term354 i)). Qed.
Lemma lem7666358 {M N : Type'} (i : nat) : (term351 M N i) = (term355 M N i).
Proof. exact (MK_COMB (@lem7666357 i) (@lem7666356 M N)). Qed.
Lemma lem7666359 {M N : Type'} (i : nat) : (term298 M N i) = (term355 M N i).
Proof. exact (TRANS (@lem7666353 M N i) (@lem7666358 M N i)). Qed.
Lemma lem7666360 {M N : Type'} (i : nat) : (term338 M N i) = (term356 M N i).
Proof. exact (MK_COMB (@lem7666350 M i) (@lem7666359 M N i)). Qed.
Lemma lem7666361 {M N : Type'} (i : nat) : (term341 M N i) = (term357 M N i).
Proof. exact (MK_COMB (@lem7666343 i) (@lem7666360 M N i)). Qed.
Lemma lem7666362 {M N : Type'} (i : nat) : (term342 M N i) = (term357 M N i).
Proof. exact (TRANS (@lem7666336 M N i) (@lem7666361 M N i)). Qed.
Lemma lem7666363 (i : nat) : term21 i.
Proof. exact (@lem2307535 i). Qed.
Lemma lem7666364 (i : nat) : (term21 i) = (term22 i).
Proof. exact (eq_refl (term21 i)). Qed.
Lemma lem7666365 (i : nat) : term22 i.
Proof. exact (EQ_MP (@lem7666364 i) (@lem7666363 i)). Qed.
Lemma lem7666366 {M : Type'} : term23 M.
Proof. exact (@lem2307535 (@dimindex M (@UNIV M))). Qed.
Lemma lem7666367 {M : Type'} : (term23 M) = (term24 M).
Proof. exact (eq_refl (term23 M)). Qed.
Lemma lem7666368 {M : Type'} : term24 M.
Proof. exact (EQ_MP (@lem7666367 M) (@lem7666366 M)). Qed.
Lemma lem7666369 {N : Type'} : term23 N.
Proof. exact (@lem2307535 (@dimindex N (@UNIV N))). Qed.
Lemma lem7666370 {N : Type'} : (term23 N) = (term24 N).
Proof. exact (eq_refl (term23 N)). Qed.
Lemma lem7666371 {N : Type'} : term24 N.
Proof. exact (EQ_MP (@lem7666370 N) (@lem7666369 N)). Qed.
Lemma lem7666372 (_98773 : int) (_98774 : int) (_98775 : int) : (term358 _98773 _98774 _98775) = (term359 _98773 _98774 _98775).
Proof. exact (@lem2318604 (term359 _98773 _98774 _98775)). Qed.
Lemma lem7666393 (_98773 : int) : (term360 _98773) = (term36 _98773).
Proof. exact (@lem16933 (term36 _98773)). Qed.
Lemma lem7666396 (_98773 : int) (_98774 : int) : (term361 _98773 _98774) = (int_le _98773 _98774).
Proof. exact (@lem16933 (int_le _98773 _98774)). Qed.
Lemma lem7666397 (_98773 : int) (_98774 : int) (_98775 : int) : (term362 _98773 _98774 _98775) = (term362 _98773 _98774 _98775).
Proof. exact (eq_refl (term362 _98773 _98774 _98775)). Qed.
Lemma lem7666398 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7666399 (_98773 : int) (_98774 : int) : (term363 _98773 _98774) = (term364 _98773 _98774).
Proof. exact (MK_COMB (@lem7666398) (@lem7666396 _98773 _98774)). Qed.
Lemma lem7666400 (_98773 : int) (_98774 : int) (_98775 : int) : (term365 _98773 _98774 _98775) = (term366 _98773 _98774 _98775).
Proof. exact (MK_COMB (@lem7666399 _98773 _98774) (@lem7666397 _98773 _98774 _98775)). Qed.
Lemma lem7666401 (_98773 : int) (_98774 : int) (_98775 : int) : (term367 _98773 _98774 _98775) = (term365 _98773 _98774 _98775).
Proof. exact (@lem17160 (term70 _98773 _98774) (term368 _98773 _98774 _98775)). Qed.
Lemma lem7666402 (_98773 : int) (_98774 : int) (_98775 : int) : (term367 _98773 _98774 _98775) = (term366 _98773 _98774 _98775).
Proof. exact (TRANS (@lem7666401 _98773 _98774 _98775) (@lem7666400 _98773 _98774 _98775)). Qed.
Lemma lem7666403 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7666404 (_98773 : int) : (term369 _98773) = (term370 _98773).
Proof. exact (MK_COMB (@lem7666403) (@lem7666393 _98773)). Qed.
Lemma lem7666405 (_98773 : int) (_98774 : int) (_98775 : int) : (term371 _98773 _98774 _98775) = (term372 _98773 _98774 _98775).
Proof. exact (MK_COMB (@lem7666404 _98773) (@lem7666402 _98773 _98774 _98775)). Qed.
Lemma lem7666406 (_98773 : int) (_98774 : int) (_98775 : int) : (term373 _98773 _98774 _98775) = (term371 _98773 _98774 _98775).
Proof. exact (@lem17160 (term29 _98773) (term374 _98773 _98774 _98775)). Qed.
Lemma lem7666407 (_98773 : int) (_98774 : int) (_98775 : int) : (term373 _98773 _98774 _98775) = (term372 _98773 _98774 _98775).
Proof. exact (TRANS (@lem7666406 _98773 _98774 _98775) (@lem7666405 _98773 _98774 _98775)). Qed.
Lemma lem7666409 (_98775 : int) : (term37 _98775) = (term37 _98775).
Proof. exact (eq_refl (term37 _98775)). Qed.
Lemma lem7666410 (_98773 : int) (_98774 : int) (_98775 : int) : (term375 _98773 _98774 _98775) = (term376 _98773 _98774 _98775).
Proof. exact (MK_COMB (@lem7666409 _98775) (@lem7666407 _98773 _98774 _98775)). Qed.
Lemma lem7666411 (_98773 : int) (_98774 : int) (_98775 : int) : (term377 _98773 _98774 _98775) = (term375 _98773 _98774 _98775).
Proof. exact (@lem17362 (term41 _98775) (term378 _98773 _98774 _98775)). Qed.
Lemma lem7666412 (_98773 : int) (_98774 : int) (_98775 : int) : (term377 _98773 _98774 _98775) = (term376 _98773 _98774 _98775).
Proof. exact (TRANS (@lem7666411 _98773 _98774 _98775) (@lem7666410 _98773 _98774 _98775)). Qed.
Lemma lem7666414 (_98774 : int) : (term37 _98774) = (term37 _98774).
Proof. exact (eq_refl (term37 _98774)). Qed.
Lemma lem7666415 (_98773 : int) (_98774 : int) (_98775 : int) : (term379 _98773 _98774 _98775) = (term380 _98773 _98774 _98775).
Proof. exact (MK_COMB (@lem7666414 _98774) (@lem7666412 _98773 _98774 _98775)). Qed.
Lemma lem7666416 (_98773 : int) (_98774 : int) (_98775 : int) : (term381 _98773 _98774 _98775) = (term379 _98773 _98774 _98775).
Proof. exact (@lem17362 (term41 _98774) (term382 _98773 _98774 _98775)). Qed.
Lemma lem7666417 (_98773 : int) (_98774 : int) (_98775 : int) : (term381 _98773 _98774 _98775) = (term380 _98773 _98774 _98775).
Proof. exact (TRANS (@lem7666416 _98773 _98774 _98775) (@lem7666415 _98773 _98774 _98775)). Qed.
Lemma lem7666419 (_98773 : int) : (term37 _98773) = (term37 _98773).
Proof. exact (eq_refl (term37 _98773)). Qed.
Lemma lem7666420 (_98773 : int) (_98774 : int) (_98775 : int) : (term383 _98773 _98774 _98775) = (term384 _98773 _98774 _98775).
Proof. exact (MK_COMB (@lem7666419 _98773) (@lem7666417 _98773 _98774 _98775)). Qed.
Lemma lem7666421 (_98773 : int) (_98774 : int) (_98775 : int) : (term385 _98773 _98774 _98775) = (term383 _98773 _98774 _98775).
Proof. exact (@lem17362 (term41 _98773) (term386 _98773 _98774 _98775)). Qed.
Lemma lem7666447 (_98773 : int) (_98774 : int) (_98775 : int) : (term385 _98773 _98774 _98775) = (term384 _98773 _98774 _98775).
Proof. exact (TRANS (@lem7666421 _98773 _98774 _98775) (@lem7666420 _98773 _98774 _98775)). Qed.
Lemma lem7666450 (x : int) (y : int) : (int_le x y) = (term47 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7666451 (_98773 : int) : (term41 _98773) = (term48 _98773).
Proof. exact (@lem7666450 term49 _98773). Qed.
Lemma lem7666453 (n : nat) : (term50 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7666454 : term51 = term52.
Proof. exact (@lem7666453 (NUMERAL 0)). Qed.
Lemma lem7666455 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7666456 : term53 = term54.
Proof. exact (MK_COMB (@lem7666455) (@lem7666454)). Qed.
Lemma lem7666457 (_98773 : int) : (real_of_int _98773) = (real_of_int _98773).
Proof. exact (eq_refl (real_of_int _98773)). Qed.
Lemma lem7666458 (_98773 : int) : (term48 _98773) = (term55 _98773).
Proof. exact (MK_COMB (@lem7666456) (@lem7666457 _98773)). Qed.
Lemma lem7666460 (_98773 : int) : (term41 _98773) = (term55 _98773).
Proof. exact (TRANS (@lem7666451 _98773) (@lem7666458 _98773)). Qed.
Lemma lem7666463 (x : int) (y : int) : (int_le x y) = (term47 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7666464 (_98774 : int) : (term41 _98774) = (term48 _98774).
Proof. exact (@lem7666463 term49 _98774). Qed.
Lemma lem7666466 (n : nat) : (term50 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7666467 : term51 = term52.
Proof. exact (@lem7666466 (NUMERAL 0)). Qed.
Lemma lem7666468 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7666469 : term53 = term54.
Proof. exact (MK_COMB (@lem7666468) (@lem7666467)). Qed.
Lemma lem7666470 (_98774 : int) : (real_of_int _98774) = (real_of_int _98774).
Proof. exact (eq_refl (real_of_int _98774)). Qed.
Lemma lem7666471 (_98774 : int) : (term48 _98774) = (term55 _98774).
Proof. exact (MK_COMB (@lem7666469) (@lem7666470 _98774)). Qed.
Lemma lem7666473 (_98774 : int) : (term41 _98774) = (term55 _98774).
Proof. exact (TRANS (@lem7666464 _98774) (@lem7666471 _98774)). Qed.
Lemma lem7666476 (x : int) (y : int) : (int_le x y) = (term47 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7666477 (_98775 : int) : (term41 _98775) = (term48 _98775).
Proof. exact (@lem7666476 term49 _98775). Qed.
Lemma lem7666479 (n : nat) : (term50 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7666480 : term51 = term52.
Proof. exact (@lem7666479 (NUMERAL 0)). Qed.
Lemma lem7666481 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7666482 : term53 = term54.
Proof. exact (MK_COMB (@lem7666481) (@lem7666480)). Qed.
Lemma lem7666483 (_98775 : int) : (real_of_int _98775) = (real_of_int _98775).
Proof. exact (eq_refl (real_of_int _98775)). Qed.
Lemma lem7666484 (_98775 : int) : (term48 _98775) = (term55 _98775).
Proof. exact (MK_COMB (@lem7666482) (@lem7666483 _98775)). Qed.
Lemma lem7666486 (_98775 : int) : (term41 _98775) = (term55 _98775).
Proof. exact (TRANS (@lem7666477 _98775) (@lem7666484 _98775)). Qed.
Lemma lem7666489 (x : int) (y : int) : (int_le x y) = (term47 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7666490 (_98773 : int) : (term36 _98773) = (term387 _98773).
Proof. exact (@lem7666489 term62 _98773). Qed.
Lemma lem7666492 (n : nat) : (term50 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7666493 : term63 = term64.
Proof. exact (@lem7666492 term11). Qed.
Lemma lem7666494 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7666495 : term388 = term389.
Proof. exact (MK_COMB (@lem7666494) (@lem7666493)). Qed.
Lemma lem7666496 (_98773 : int) : (real_of_int _98773) = (real_of_int _98773).
Proof. exact (eq_refl (real_of_int _98773)). Qed.
Lemma lem7666497 (_98773 : int) : (term387 _98773) = (term390 _98773).
Proof. exact (MK_COMB (@lem7666495) (@lem7666496 _98773)). Qed.
Lemma lem7666499 (_98773 : int) : (term36 _98773) = (term390 _98773).
Proof. exact (TRANS (@lem7666490 _98773) (@lem7666497 _98773)). Qed.
Lemma lem7666502 (x : int) (y : int) : (int_le x y) = (term47 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7666504 (_98773 : int) (_98774 : int) : (int_le _98773 _98774) = (term47 _98773 _98774).
Proof. exact (@lem7666502 _98773 _98774). Qed.
Lemma lem7666506 (y : int) (x : int) : (term70 x y) = (term28 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7666507 (_98774 : int) (_98775 : int) (_98773 : int) : (term362 _98773 _98774 _98775) = (term391 _98774 _98775 _98773).
Proof. exact (@lem7666506 (int_add _98774 _98775) _98773). Qed.
Lemma lem7666509 (x : int) (y : int) : (int_le x y) = (term47 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7666510 (_98774 : int) (_98775 : int) (_98773 : int) : (term391 _98774 _98775 _98773) = (term392 _98774 _98775 _98773).
Proof. exact (@lem7666509 (term393 _98774 _98775) _98773). Qed.
Lemma lem7666512 (x : int) (y : int) : (term58 x y) = (term59 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7666513 (_98774 : int) (_98775 : int) : (term394 _98774 _98775) = (term395 _98774 _98775).
Proof. exact (@lem7666512 (int_add _98774 _98775) term62). Qed.
Lemma lem7666515 (x : int) (y : int) : (term58 x y) = (term59 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7666516 (_98774 : int) (_98775 : int) : (term58 _98774 _98775) = (term59 _98774 _98775).
Proof. exact (@lem7666515 _98774 _98775). Qed.
Lemma lem7666517 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7666518 (_98774 : int) (_98775 : int) : (term396 _98774 _98775) = (term397 _98774 _98775).
Proof. exact (MK_COMB (@lem7666517) (@lem7666516 _98774 _98775)). Qed.
Lemma lem7666520 (n : nat) : (term50 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7666521 : term63 = term64.
Proof. exact (@lem7666520 term11). Qed.
Lemma lem7666522 (_98774 : int) (_98775 : int) : (term395 _98774 _98775) = (term398 _98774 _98775).
Proof. exact (MK_COMB (@lem7666518 _98774 _98775) (@lem7666521)). Qed.
Lemma lem7666523 (_98774 : int) (_98775 : int) : (term394 _98774 _98775) = (term398 _98774 _98775).
Proof. exact (TRANS (@lem7666513 _98774 _98775) (@lem7666522 _98774 _98775)). Qed.
Lemma lem7666524 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7666525 (_98774 : int) (_98775 : int) : (term399 _98774 _98775) = (term400 _98774 _98775).
Proof. exact (MK_COMB (@lem7666524) (@lem7666523 _98774 _98775)). Qed.
Lemma lem7666526 (_98773 : int) : (real_of_int _98773) = (real_of_int _98773).
Proof. exact (eq_refl (real_of_int _98773)). Qed.
Lemma lem7666527 (_98774 : int) (_98775 : int) (_98773 : int) : (term392 _98774 _98775 _98773) = (term401 _98774 _98775 _98773).
Proof. exact (MK_COMB (@lem7666525 _98774 _98775) (@lem7666526 _98773)). Qed.
Lemma lem7666528 (_98774 : int) (_98775 : int) (_98773 : int) : (term391 _98774 _98775 _98773) = (term401 _98774 _98775 _98773).
Proof. exact (TRANS (@lem7666510 _98774 _98775 _98773) (@lem7666527 _98774 _98775 _98773)). Qed.
Lemma lem7666529 (_98774 : int) (_98775 : int) (_98773 : int) : (term362 _98773 _98774 _98775) = (term401 _98774 _98775 _98773).
Proof. exact (TRANS (@lem7666507 _98774 _98775 _98773) (@lem7666528 _98774 _98775 _98773)). Qed.
Lemma lem7666530 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7666531 (_98773 : int) (_98774 : int) : (term364 _98773 _98774) = (term402 _98773 _98774).
Proof. exact (MK_COMB (@lem7666530) (@lem7666504 _98773 _98774)). Qed.
Lemma lem7666532 (_98774 : int) (_98775 : int) (_98773 : int) : (term366 _98773 _98774 _98775) = (term403 _98774 _98775 _98773).
Proof. exact (MK_COMB (@lem7666531 _98773 _98774) (@lem7666529 _98774 _98775 _98773)). Qed.
Lemma lem7666533 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7666534 (_98773 : int) : (term370 _98773) = (term404 _98773).
Proof. exact (MK_COMB (@lem7666533) (@lem7666499 _98773)). Qed.
Lemma lem7666535 (_98774 : int) (_98775 : int) (_98773 : int) : (term372 _98773 _98774 _98775) = (term405 _98774 _98775 _98773).
Proof. exact (MK_COMB (@lem7666534 _98773) (@lem7666532 _98774 _98775 _98773)). Qed.
Lemma lem7666536 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7666537 (_98775 : int) : (term37 _98775) = (term76 _98775).
Proof. exact (MK_COMB (@lem7666536) (@lem7666486 _98775)). Qed.
Lemma lem7666538 (_98774 : int) (_98775 : int) (_98773 : int) : (term376 _98773 _98774 _98775) = (term406 _98774 _98775 _98773).
Proof. exact (MK_COMB (@lem7666537 _98775) (@lem7666535 _98774 _98775 _98773)). Qed.
Lemma lem7666539 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7666540 (_98774 : int) : (term37 _98774) = (term76 _98774).
Proof. exact (MK_COMB (@lem7666539) (@lem7666473 _98774)). Qed.
Lemma lem7666541 (_98774 : int) (_98775 : int) (_98773 : int) : (term380 _98773 _98774 _98775) = (term407 _98774 _98775 _98773).
Proof. exact (MK_COMB (@lem7666540 _98774) (@lem7666538 _98774 _98775 _98773)). Qed.
Lemma lem7666542 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7666543 (_98773 : int) : (term37 _98773) = (term76 _98773).
Proof. exact (MK_COMB (@lem7666542) (@lem7666460 _98773)). Qed.
Lemma lem7666544 (_98774 : int) (_98775 : int) (_98773 : int) : (term384 _98773 _98774 _98775) = (term408 _98774 _98775 _98773).
Proof. exact (MK_COMB (@lem7666543 _98773) (@lem7666541 _98774 _98775 _98773)). Qed.
Lemma lem7666545 (_98774 : int) (_98775 : int) (_98773 : int) : (term385 _98773 _98774 _98775) = (term408 _98774 _98775 _98773).
Proof. exact (TRANS (@lem7666447 _98773 _98774 _98775) (@lem7666544 _98774 _98775 _98773)). Qed.
Lemma lem7666549 (t : Prop) : (term79 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7666605 (_98774 : int) (_98775 : int) (_98773 : int) : (term409 _98774 _98775 _98773) = (term408 _98774 _98775 _98773).
Proof. exact (@lem7666549 (term408 _98774 _98775 _98773)). Qed.
Lemma lem7666606 (_98773 : int) : (term55 _98773) = (term81 _98773).
Proof. exact (@lem1988287 (real_of_int _98773) term52). Qed.
Lemma lem7666612 (_98773 : int) : (term82 _98773) = (term83 _98773).
Proof. exact (@lem1982792 (real_of_int _98773) term52). Qed.
Lemma lem7666614 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7666615 : term52 = term85.
Proof. exact (@lem7666614 (NUMERAL 0)). Qed.
Lemma lem7666617 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7666618 : term88 = term89.
Proof. exact (@lem7666617 term11). Qed.
Lemma lem7666619 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7666620 : term90 = term91.
Proof. exact (MK_COMB (@lem7666619) (@lem7666618)). Qed.
Lemma lem7666621 : term92 = term93.
Proof. exact (MK_COMB (@lem7666620) (@lem7666615)). Qed.
Lemma lem7666622 : term93 = term94.
Proof. exact (@lem1981613 term88 term52 term64 term64). Qed.
Lemma lem7666624 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7666625 : term97 = term98.
Proof. exact (@lem7666624 term11 term11). Qed.
Lemma lem7666626 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7666627 : term100 = term11.
Proof. exact (EQ_MP (@lem7666626) (@lem940073)). Qed.
Lemma lem7666628 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7666629 : term98 = term64.
Proof. exact (MK_COMB (@lem7666628) (@lem7666627)). Qed.
Lemma lem7666630 : term97 = term64.
Proof. exact (TRANS (@lem7666625) (@lem7666629)). Qed.
Lemma lem7666632 (x : nat) : (term101 x) = term52.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7666633 : term92 = term52.
Proof. exact (@lem7666632 term11). Qed.
Lemma lem7666634 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7666635 : term102 = term103.
Proof. exact (MK_COMB (@lem7666634) (@lem7666633)). Qed.
Lemma lem7666636 : term94 = term85.
Proof. exact (MK_COMB (@lem7666635) (@lem7666630)). Qed.
Lemma lem7666637 : term93 = term85.
Proof. exact (TRANS (@lem7666622) (@lem7666636)). Qed.
Lemma lem7666638 : term92 = term85.
Proof. exact (TRANS (@lem7666621) (@lem7666637)). Qed.
Lemma lem7666640 (x : real) : (term104 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7666641 : term85 = term52.
Proof. exact (@lem7666640 term52). Qed.
Lemma lem7666642 : term92 = term52.
Proof. exact (TRANS (@lem7666638) (@lem7666641)). Qed.
Lemma lem7666643 (_98773 : int) : (term65 _98773) = (term65 _98773).
Proof. exact (eq_refl (term65 _98773)). Qed.
Lemma lem7666644 (_98773 : int) : (term83 _98773) = (term105 _98773).
Proof. exact (MK_COMB (@lem7666643 _98773) (@lem7666642)). Qed.
Lemma lem7666645 (_98773 : int) : (term105 _98773) = (real_of_int _98773).
Proof. exact (@lem1982723 (real_of_int _98773)). Qed.
Lemma lem7666646 (_98773 : int) : (term83 _98773) = (real_of_int _98773).
Proof. exact (TRANS (@lem7666644 _98773) (@lem7666645 _98773)). Qed.
Lemma lem7666648 (_98773 : int) : (term82 _98773) = (real_of_int _98773).
Proof. exact (TRANS (@lem7666612 _98773) (@lem7666646 _98773)). Qed.
Lemma lem7666649 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7666650 (_98773 : int) : (term106 _98773) = (term107 _98773).
Proof. exact (MK_COMB (@lem7666649) (@lem7666648 _98773)). Qed.
Lemma lem7666651 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7666652 (_98773 : int) : (term81 _98773) = (term108 _98773).
Proof. exact (MK_COMB (@lem7666650 _98773) (@lem7666651)). Qed.
Lemma lem7666653 (_98773 : int) : (term55 _98773) = (term108 _98773).
Proof. exact (TRANS (@lem7666606 _98773) (@lem7666652 _98773)). Qed.
Lemma lem7666654 (_98774 : int) : (term55 _98774) = (term81 _98774).
Proof. exact (@lem1988287 (real_of_int _98774) term52). Qed.
Lemma lem7666660 (_98774 : int) : (term82 _98774) = (term83 _98774).
Proof. exact (@lem1982792 (real_of_int _98774) term52). Qed.
Lemma lem7666662 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7666663 : term52 = term85.
Proof. exact (@lem7666662 (NUMERAL 0)). Qed.
Lemma lem7666665 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7666666 : term88 = term89.
Proof. exact (@lem7666665 term11). Qed.
Lemma lem7666667 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7666668 : term90 = term91.
Proof. exact (MK_COMB (@lem7666667) (@lem7666666)). Qed.
Lemma lem7666669 : term92 = term93.
Proof. exact (MK_COMB (@lem7666668) (@lem7666663)). Qed.
Lemma lem7666670 : term93 = term94.
Proof. exact (@lem1981613 term88 term52 term64 term64). Qed.
Lemma lem7666672 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7666673 : term97 = term98.
Proof. exact (@lem7666672 term11 term11). Qed.
Lemma lem7666674 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7666675 : term100 = term11.
Proof. exact (EQ_MP (@lem7666674) (@lem940073)). Qed.
Lemma lem7666676 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7666677 : term98 = term64.
Proof. exact (MK_COMB (@lem7666676) (@lem7666675)). Qed.
Lemma lem7666678 : term97 = term64.
Proof. exact (TRANS (@lem7666673) (@lem7666677)). Qed.
Lemma lem7666680 (x : nat) : (term101 x) = term52.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7666681 : term92 = term52.
Proof. exact (@lem7666680 term11). Qed.
Lemma lem7666682 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7666683 : term102 = term103.
Proof. exact (MK_COMB (@lem7666682) (@lem7666681)). Qed.
Lemma lem7666684 : term94 = term85.
Proof. exact (MK_COMB (@lem7666683) (@lem7666678)). Qed.
Lemma lem7666685 : term93 = term85.
Proof. exact (TRANS (@lem7666670) (@lem7666684)). Qed.
Lemma lem7666686 : term92 = term85.
Proof. exact (TRANS (@lem7666669) (@lem7666685)). Qed.
Lemma lem7666688 (x : real) : (term104 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7666689 : term85 = term52.
Proof. exact (@lem7666688 term52). Qed.
Lemma lem7666690 : term92 = term52.
Proof. exact (TRANS (@lem7666686) (@lem7666689)). Qed.
Lemma lem7666691 (_98774 : int) : (term65 _98774) = (term65 _98774).
Proof. exact (eq_refl (term65 _98774)). Qed.
Lemma lem7666692 (_98774 : int) : (term83 _98774) = (term105 _98774).
Proof. exact (MK_COMB (@lem7666691 _98774) (@lem7666690)). Qed.
Lemma lem7666693 (_98774 : int) : (term105 _98774) = (real_of_int _98774).
Proof. exact (@lem1982723 (real_of_int _98774)). Qed.
Lemma lem7666694 (_98774 : int) : (term83 _98774) = (real_of_int _98774).
Proof. exact (TRANS (@lem7666692 _98774) (@lem7666693 _98774)). Qed.
Lemma lem7666696 (_98774 : int) : (term82 _98774) = (real_of_int _98774).
Proof. exact (TRANS (@lem7666660 _98774) (@lem7666694 _98774)). Qed.
Lemma lem7666697 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7666698 (_98774 : int) : (term106 _98774) = (term107 _98774).
Proof. exact (MK_COMB (@lem7666697) (@lem7666696 _98774)). Qed.
Lemma lem7666699 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7666700 (_98774 : int) : (term81 _98774) = (term108 _98774).
Proof. exact (MK_COMB (@lem7666698 _98774) (@lem7666699)). Qed.
Lemma lem7666701 (_98774 : int) : (term55 _98774) = (term108 _98774).
Proof. exact (TRANS (@lem7666654 _98774) (@lem7666700 _98774)). Qed.
Lemma lem7666702 (_98775 : int) : (term55 _98775) = (term81 _98775).
Proof. exact (@lem1988287 (real_of_int _98775) term52). Qed.
Lemma lem7666708 (_98775 : int) : (term82 _98775) = (term83 _98775).
Proof. exact (@lem1982792 (real_of_int _98775) term52). Qed.
Lemma lem7666710 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7666711 : term52 = term85.
Proof. exact (@lem7666710 (NUMERAL 0)). Qed.
Lemma lem7666713 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7666714 : term88 = term89.
Proof. exact (@lem7666713 term11). Qed.
Lemma lem7666715 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7666716 : term90 = term91.
Proof. exact (MK_COMB (@lem7666715) (@lem7666714)). Qed.
Lemma lem7666717 : term92 = term93.
Proof. exact (MK_COMB (@lem7666716) (@lem7666711)). Qed.
Lemma lem7666718 : term93 = term94.
Proof. exact (@lem1981613 term88 term52 term64 term64). Qed.
Lemma lem7666720 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7666721 : term97 = term98.
Proof. exact (@lem7666720 term11 term11). Qed.
Lemma lem7666722 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7666723 : term100 = term11.
Proof. exact (EQ_MP (@lem7666722) (@lem940073)). Qed.
Lemma lem7666724 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7666725 : term98 = term64.
Proof. exact (MK_COMB (@lem7666724) (@lem7666723)). Qed.
Lemma lem7666726 : term97 = term64.
Proof. exact (TRANS (@lem7666721) (@lem7666725)). Qed.
Lemma lem7666728 (x : nat) : (term101 x) = term52.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7666729 : term92 = term52.
Proof. exact (@lem7666728 term11). Qed.
Lemma lem7666730 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7666731 : term102 = term103.
Proof. exact (MK_COMB (@lem7666730) (@lem7666729)). Qed.
Lemma lem7666732 : term94 = term85.
Proof. exact (MK_COMB (@lem7666731) (@lem7666726)). Qed.
Lemma lem7666733 : term93 = term85.
Proof. exact (TRANS (@lem7666718) (@lem7666732)). Qed.
Lemma lem7666734 : term92 = term85.
Proof. exact (TRANS (@lem7666717) (@lem7666733)). Qed.
Lemma lem7666736 (x : real) : (term104 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7666737 : term85 = term52.
Proof. exact (@lem7666736 term52). Qed.
Lemma lem7666738 : term92 = term52.
Proof. exact (TRANS (@lem7666734) (@lem7666737)). Qed.
Lemma lem7666739 (_98775 : int) : (term65 _98775) = (term65 _98775).
Proof. exact (eq_refl (term65 _98775)). Qed.
Lemma lem7666740 (_98775 : int) : (term83 _98775) = (term105 _98775).
Proof. exact (MK_COMB (@lem7666739 _98775) (@lem7666738)). Qed.
Lemma lem7666741 (_98775 : int) : (term105 _98775) = (real_of_int _98775).
Proof. exact (@lem1982723 (real_of_int _98775)). Qed.
Lemma lem7666742 (_98775 : int) : (term83 _98775) = (real_of_int _98775).
Proof. exact (TRANS (@lem7666740 _98775) (@lem7666741 _98775)). Qed.
Lemma lem7666744 (_98775 : int) : (term82 _98775) = (real_of_int _98775).
Proof. exact (TRANS (@lem7666708 _98775) (@lem7666742 _98775)). Qed.
Lemma lem7666745 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7666746 (_98775 : int) : (term106 _98775) = (term107 _98775).
Proof. exact (MK_COMB (@lem7666745) (@lem7666744 _98775)). Qed.
Lemma lem7666747 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7666748 (_98775 : int) : (term81 _98775) = (term108 _98775).
Proof. exact (MK_COMB (@lem7666746 _98775) (@lem7666747)). Qed.
Lemma lem7666749 (_98775 : int) : (term55 _98775) = (term108 _98775).
Proof. exact (TRANS (@lem7666702 _98775) (@lem7666748 _98775)). Qed.
Lemma lem7666750 (_98773 : int) : (term390 _98773) = (term410 _98773).
Proof. exact (@lem1988287 (real_of_int _98773) term64). Qed.
Lemma lem7666756 (_98773 : int) : (term411 _98773) = (term412 _98773).
Proof. exact (@lem1982792 (real_of_int _98773) term64). Qed.
Lemma lem7666758 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7666759 : term64 = term114.
Proof. exact (@lem7666758 term11). Qed.
Lemma lem7666761 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7666762 : term88 = term89.
Proof. exact (@lem7666761 term11). Qed.
Lemma lem7666763 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7666764 : term90 = term91.
Proof. exact (MK_COMB (@lem7666763) (@lem7666762)). Qed.
Lemma lem7666765 : term115 = term116.
Proof. exact (MK_COMB (@lem7666764) (@lem7666759)). Qed.
Lemma lem7666766 : term116 = term117.
Proof. exact (@lem1981613 term88 term64 term64 term64). Qed.
Lemma lem7666768 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7666769 : term97 = term98.
Proof. exact (@lem7666768 term11 term11). Qed.
Lemma lem7666770 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7666771 : term100 = term11.
Proof. exact (EQ_MP (@lem7666770) (@lem940073)). Qed.
Lemma lem7666772 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7666773 : term98 = term64.
Proof. exact (MK_COMB (@lem7666772) (@lem7666771)). Qed.
Lemma lem7666774 : term97 = term64.
Proof. exact (TRANS (@lem7666769) (@lem7666773)). Qed.
Lemma lem7666776 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7666777 : term115 = term120.
Proof. exact (@lem7666776 term11 term11). Qed.
Lemma lem7666778 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7666779 : term100 = term11.
Proof. exact (EQ_MP (@lem7666778) (@lem940073)). Qed.
Lemma lem7666780 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7666781 : term98 = term64.
Proof. exact (MK_COMB (@lem7666780) (@lem7666779)). Qed.
Lemma lem7666782 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7666783 : term120 = term88.
Proof. exact (MK_COMB (@lem7666782) (@lem7666781)). Qed.
Lemma lem7666784 : term115 = term88.
Proof. exact (TRANS (@lem7666777) (@lem7666783)). Qed.
Lemma lem7666785 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7666786 : term121 = term122.
Proof. exact (MK_COMB (@lem7666785) (@lem7666784)). Qed.
Lemma lem7666787 : term117 = term89.
Proof. exact (MK_COMB (@lem7666786) (@lem7666774)). Qed.
Lemma lem7666788 : term116 = term89.
Proof. exact (TRANS (@lem7666766) (@lem7666787)). Qed.
Lemma lem7666789 : term115 = term89.
Proof. exact (TRANS (@lem7666765) (@lem7666788)). Qed.
Lemma lem7666791 (x : real) : (term104 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7666792 : term89 = term88.
Proof. exact (@lem7666791 term88). Qed.
Lemma lem7666793 : term115 = term88.
Proof. exact (TRANS (@lem7666789) (@lem7666792)). Qed.
Lemma lem7666794 (_98773 : int) : (term65 _98773) = (term65 _98773).
Proof. exact (eq_refl (term65 _98773)). Qed.
Lemma lem7666797 (_98773 : int) : (term412 _98773) = (term212 _98773).
Proof. exact (MK_COMB (@lem7666794 _98773) (@lem7666793)). Qed.
Lemma lem7666799 (_98773 : int) : (term411 _98773) = (term212 _98773).
Proof. exact (TRANS (@lem7666756 _98773) (@lem7666797 _98773)). Qed.
Lemma lem7666800 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7666801 (_98773 : int) : (term413 _98773) = (term214 _98773).
Proof. exact (MK_COMB (@lem7666800) (@lem7666799 _98773)). Qed.
Lemma lem7666802 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7666803 (_98773 : int) : (term410 _98773) = (term215 _98773).
Proof. exact (MK_COMB (@lem7666801 _98773) (@lem7666802)). Qed.
Lemma lem7666804 (_98773 : int) : (term390 _98773) = (term215 _98773).
Proof. exact (TRANS (@lem7666750 _98773) (@lem7666803 _98773)). Qed.
Lemma lem7666805 (_98774 : int) (_98773 : int) : (term47 _98773 _98774) = (term414 _98774 _98773).
Proof. exact (@lem1988287 (real_of_int _98774) (real_of_int _98773)). Qed.
Lemma lem7666811 (_98774 : int) (_98773 : int) : (term415 _98774 _98773) = (term416 _98774 _98773).
Proof. exact (@lem1982792 (real_of_int _98774) (real_of_int _98773)). Qed.
Lemma lem7666816 (_98773 : int) (_98774 : int) : (term416 _98774 _98773) = (term417 _98773 _98774).
Proof. exact (@lem1982761 (term135 _98773) (real_of_int _98774)). Qed.
Lemma lem7666818 (_98773 : int) (_98774 : int) : (term415 _98774 _98773) = (term417 _98773 _98774).
Proof. exact (TRANS (@lem7666811 _98774 _98773) (@lem7666816 _98773 _98774)). Qed.
Lemma lem7666819 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7666820 (_98773 : int) (_98774 : int) : (term418 _98774 _98773) = (term419 _98773 _98774).
Proof. exact (MK_COMB (@lem7666819) (@lem7666818 _98773 _98774)). Qed.
Lemma lem7666821 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7666822 (_98773 : int) (_98774 : int) : (term414 _98774 _98773) = (term420 _98773 _98774).
Proof. exact (MK_COMB (@lem7666820 _98773 _98774) (@lem7666821)). Qed.
Lemma lem7666823 (_98773 : int) (_98774 : int) : (term47 _98773 _98774) = (term420 _98773 _98774).
Proof. exact (TRANS (@lem7666805 _98774 _98773) (@lem7666822 _98773 _98774)). Qed.
Lemma lem7666824 (_98773 : int) (_98774 : int) (_98775 : int) : (term401 _98774 _98775 _98773) = (term421 _98773 _98774 _98775).
Proof. exact (@lem1988287 (real_of_int _98773) (term398 _98774 _98775)). Qed.
Lemma lem7666841 (_98774 : int) (_98775 : int) : (term398 _98774 _98775) = (term422 _98774 _98775).
Proof. exact (@lem1982755 (real_of_int _98774) (real_of_int _98775) term64). Qed.
Lemma lem7666844 (_98773 : int) : (term423 _98773) = (term423 _98773).
Proof. exact (eq_refl (term423 _98773)). Qed.
Lemma lem7666845 (_98773 : int) (_98774 : int) (_98775 : int) : (term424 _98773 _98774 _98775) = (term425 _98773 _98774 _98775).
Proof. exact (MK_COMB (@lem7666844 _98773) (@lem7666841 _98774 _98775)). Qed.
Lemma lem7666846 (_98773 : int) (_98774 : int) (_98775 : int) : (term425 _98773 _98774 _98775) = (term426 _98773 _98774 _98775).
Proof. exact (@lem1982792 (real_of_int _98773) (term422 _98774 _98775)). Qed.
Lemma lem7666847 (_98774 : int) (_98775 : int) : (term427 _98774 _98775) = (term428 _98774 _98775).
Proof. exact (@lem1982781 (real_of_int _98774) term88 (term66 _98775)). Qed.
Lemma lem7666848 (_98775 : int) : (term112 _98775) = (term113 _98775).
Proof. exact (@lem1982781 (real_of_int _98775) term88 term64). Qed.
Lemma lem7666850 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7666851 : term64 = term114.
Proof. exact (@lem7666850 term11). Qed.
Lemma lem7666853 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7666854 : term88 = term89.
Proof. exact (@lem7666853 term11). Qed.
Lemma lem7666855 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7666856 : term90 = term91.
Proof. exact (MK_COMB (@lem7666855) (@lem7666854)). Qed.
Lemma lem7666857 : term115 = term116.
Proof. exact (MK_COMB (@lem7666856) (@lem7666851)). Qed.
Lemma lem7666858 : term116 = term117.
Proof. exact (@lem1981613 term88 term64 term64 term64). Qed.
Lemma lem7666860 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7666861 : term97 = term98.
Proof. exact (@lem7666860 term11 term11). Qed.
Lemma lem7666862 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7666863 : term100 = term11.
Proof. exact (EQ_MP (@lem7666862) (@lem940073)). Qed.
Lemma lem7666864 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7666865 : term98 = term64.
Proof. exact (MK_COMB (@lem7666864) (@lem7666863)). Qed.
Lemma lem7666866 : term97 = term64.
Proof. exact (TRANS (@lem7666861) (@lem7666865)). Qed.
Lemma lem7666868 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7666869 : term115 = term120.
Proof. exact (@lem7666868 term11 term11). Qed.
Lemma lem7666870 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7666871 : term100 = term11.
Proof. exact (EQ_MP (@lem7666870) (@lem940073)). Qed.
Lemma lem7666872 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7666873 : term98 = term64.
Proof. exact (MK_COMB (@lem7666872) (@lem7666871)). Qed.
Lemma lem7666874 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7666875 : term120 = term88.
Proof. exact (MK_COMB (@lem7666874) (@lem7666873)). Qed.
Lemma lem7666876 : term115 = term88.
Proof. exact (TRANS (@lem7666869) (@lem7666875)). Qed.
Lemma lem7666877 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7666878 : term121 = term122.
Proof. exact (MK_COMB (@lem7666877) (@lem7666876)). Qed.
Lemma lem7666879 : term117 = term89.
Proof. exact (MK_COMB (@lem7666878) (@lem7666866)). Qed.
Lemma lem7666880 : term116 = term89.
Proof. exact (TRANS (@lem7666858) (@lem7666879)). Qed.
Lemma lem7666881 : term115 = term89.
Proof. exact (TRANS (@lem7666857) (@lem7666880)). Qed.
Lemma lem7666883 (x : real) : (term104 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7666884 : term89 = term88.
Proof. exact (@lem7666883 term88). Qed.
Lemma lem7666885 : term115 = term88.
Proof. exact (TRANS (@lem7666881) (@lem7666884)). Qed.
Lemma lem7666888 (_98775 : int) : (term123 _98775) = (term123 _98775).
Proof. exact (eq_refl (term123 _98775)). Qed.
Lemma lem7666889 (_98775 : int) : (term113 _98775) = (term124 _98775).
Proof. exact (MK_COMB (@lem7666888 _98775) (@lem7666885)). Qed.
Lemma lem7666890 (_98775 : int) : (term112 _98775) = (term124 _98775).
Proof. exact (TRANS (@lem7666848 _98775) (@lem7666889 _98775)). Qed.
Lemma lem7666893 (_98774 : int) : (term123 _98774) = (term123 _98774).
Proof. exact (eq_refl (term123 _98774)). Qed.
Lemma lem7666894 (_98774 : int) (_98775 : int) : (term428 _98774 _98775) = (term429 _98774 _98775).
Proof. exact (MK_COMB (@lem7666893 _98774) (@lem7666890 _98775)). Qed.
Lemma lem7666895 (_98774 : int) (_98775 : int) : (term427 _98774 _98775) = (term429 _98774 _98775).
Proof. exact (TRANS (@lem7666847 _98774 _98775) (@lem7666894 _98774 _98775)). Qed.
Lemma lem7666896 (_98773 : int) : (term65 _98773) = (term65 _98773).
Proof. exact (eq_refl (term65 _98773)). Qed.
Lemma lem7666899 (_98773 : int) (_98774 : int) (_98775 : int) : (term426 _98773 _98774 _98775) = (term430 _98773 _98774 _98775).
Proof. exact (MK_COMB (@lem7666896 _98773) (@lem7666895 _98774 _98775)). Qed.
Lemma lem7666900 (_98773 : int) (_98774 : int) (_98775 : int) : (term425 _98773 _98774 _98775) = (term430 _98773 _98774 _98775).
Proof. exact (TRANS (@lem7666846 _98773 _98774 _98775) (@lem7666899 _98773 _98774 _98775)). Qed.
Lemma lem7666901 (_98773 : int) (_98774 : int) (_98775 : int) : (term424 _98773 _98774 _98775) = (term430 _98773 _98774 _98775).
Proof. exact (TRANS (@lem7666845 _98773 _98774 _98775) (@lem7666900 _98773 _98774 _98775)). Qed.
Lemma lem7666902 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7666903 (_98773 : int) (_98774 : int) (_98775 : int) : (term431 _98773 _98774 _98775) = (term432 _98773 _98774 _98775).
Proof. exact (MK_COMB (@lem7666902) (@lem7666901 _98773 _98774 _98775)). Qed.
Lemma lem7666904 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7666905 (_98773 : int) (_98774 : int) (_98775 : int) : (term421 _98773 _98774 _98775) = (term433 _98773 _98774 _98775).
Proof. exact (MK_COMB (@lem7666903 _98773 _98774 _98775) (@lem7666904)). Qed.
Lemma lem7666906 (_98773 : int) (_98774 : int) (_98775 : int) : (term401 _98774 _98775 _98773) = (term433 _98773 _98774 _98775).
Proof. exact (TRANS (@lem7666824 _98773 _98774 _98775) (@lem7666905 _98773 _98774 _98775)). Qed.
Lemma lem7666907 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7666908 (_98773 : int) (_98774 : int) : (term402 _98773 _98774) = (term434 _98773 _98774).
Proof. exact (MK_COMB (@lem7666907) (@lem7666823 _98773 _98774)). Qed.
Lemma lem7666909 (_98773 : int) (_98774 : int) (_98775 : int) : (term403 _98774 _98775 _98773) = (term435 _98773 _98774 _98775).
Proof. exact (MK_COMB (@lem7666908 _98773 _98774) (@lem7666906 _98773 _98774 _98775)). Qed.
Lemma lem7666910 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7666911 (_98773 : int) : (term404 _98773) = (term436 _98773).
Proof. exact (MK_COMB (@lem7666910) (@lem7666804 _98773)). Qed.
Lemma lem7666912 (_98773 : int) (_98774 : int) (_98775 : int) : (term405 _98774 _98775 _98773) = (term437 _98773 _98774 _98775).
Proof. exact (MK_COMB (@lem7666911 _98773) (@lem7666909 _98773 _98774 _98775)). Qed.
Lemma lem7666913 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7666914 (_98775 : int) : (term76 _98775) = (term162 _98775).
Proof. exact (MK_COMB (@lem7666913) (@lem7666749 _98775)). Qed.
Lemma lem7666915 (_98773 : int) (_98774 : int) (_98775 : int) : (term406 _98774 _98775 _98773) = (term438 _98773 _98774 _98775).
Proof. exact (MK_COMB (@lem7666914 _98775) (@lem7666912 _98773 _98774 _98775)). Qed.
Lemma lem7666916 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7666917 (_98774 : int) : (term76 _98774) = (term162 _98774).
Proof. exact (MK_COMB (@lem7666916) (@lem7666701 _98774)). Qed.
Lemma lem7666918 (_98773 : int) (_98774 : int) (_98775 : int) : (term407 _98774 _98775 _98773) = (term439 _98773 _98774 _98775).
Proof. exact (MK_COMB (@lem7666917 _98774) (@lem7666915 _98773 _98774 _98775)). Qed.
Lemma lem7666919 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7666920 (_98773 : int) : (term76 _98773) = (term162 _98773).
Proof. exact (MK_COMB (@lem7666919) (@lem7666653 _98773)). Qed.
Lemma lem7666921 (_98773 : int) (_98774 : int) (_98775 : int) : (term408 _98774 _98775 _98773) = (term440 _98773 _98774 _98775).
Proof. exact (MK_COMB (@lem7666920 _98773) (@lem7666918 _98773 _98774 _98775)). Qed.
Lemma lem7666960 (_98773 : int) (_98774 : int) (_98775 : int) : (term409 _98774 _98775 _98773) = (term440 _98773 _98774 _98775).
Proof. exact (TRANS (@lem7666605 _98774 _98775 _98773) (@lem7666921 _98773 _98774 _98775)). Qed.
Lemma lem7666964 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : term440 _98773 _98774 _98775.
Proof. exact (h1). Qed.
Lemma lem7666965 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : term439 _98773 _98774 _98775.
Proof. exact (proj2 (@lem7666964 _98773 _98774 _98775 h1)). Qed.
Lemma lem7666967 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : term438 _98773 _98774 _98775.
Proof. exact (proj2 (@lem7666965 _98773 _98774 _98775 h1)). Qed.
Lemma lem7666969 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : term437 _98773 _98774 _98775.
Proof. exact (proj2 (@lem7666967 _98773 _98774 _98775 h1)). Qed.
Lemma lem7666970 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : term108 _98775.
Proof. exact (proj1 (@lem7666967 _98773 _98774 _98775 h1)). Qed.
Lemma lem7666971 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : term435 _98773 _98774 _98775.
Proof. exact (proj2 (@lem7666969 _98773 _98774 _98775 h1)). Qed.
Lemma lem7666973 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : term433 _98773 _98774 _98775.
Proof. exact (proj2 (@lem7666971 _98773 _98774 _98775 h1)). Qed.
Lemma lem7666974 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : term420 _98773 _98774.
Proof. exact (proj1 (@lem7666971 _98773 _98774 _98775 h1)). Qed.
Lemma lem7666976 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7666977 : term165 = term141.
Proof. exact (@lem7666976 term52 term64). Qed.
Lemma lem7666979 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7666980 : term64 = term114.
Proof. exact (@lem7666979 term11). Qed.
Lemma lem7666982 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7666983 : term52 = term85.
Proof. exact (@lem7666982 (NUMERAL 0)). Qed.
Lemma lem7666984 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7666985 : term166 = term167.
Proof. exact (MK_COMB (@lem7666984) (@lem7666983)). Qed.
Lemma lem7666986 : term141 = term168.
Proof. exact (MK_COMB (@lem7666985) (@lem7666980)). Qed.
Lemma lem7666987 : term169.
Proof. exact (@lem1980255 term52 term64 term64 term64). Qed.
Lemma lem7666989 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7666990 : term141 = term142.
Proof. exact (@lem7666989 (NUMERAL 0) term11). Qed.
Lemma lem7666991 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7666992 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7666993 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7666992 h1) (fun h1 : term142 = True => @lem7666991)). Qed.
Lemma lem7666994 : term142 = True.
Proof. exact (EQ_MP (@lem7666993) (@lem7666991)). Qed.
Lemma lem7666995 : term141 = True.
Proof. exact (TRANS (@lem7666990) (@lem7666994)). Qed.
Lemma lem7666996 : True = term141.
Proof. exact (SYM (@lem7666995)). Qed.
Lemma lem7666997 : term141.
Proof. exact (EQ_MP (@lem7666996) (@lem0)). Qed.
Lemma lem7666998 : term170.
Proof. exact (@lem7666987 (@lem7666997)). Qed.
Lemma lem7667000 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7667001 : term141 = term142.
Proof. exact (@lem7667000 (NUMERAL 0) term11). Qed.
Lemma lem7667002 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7667003 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7667004 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7667003 h1) (fun h1 : term142 = True => @lem7667002)). Qed.
Lemma lem7667005 : term142 = True.
Proof. exact (EQ_MP (@lem7667004) (@lem7667002)). Qed.
Lemma lem7667006 : term141 = True.
Proof. exact (TRANS (@lem7667001) (@lem7667005)). Qed.
Lemma lem7667007 : True = term141.
Proof. exact (SYM (@lem7667006)). Qed.
Lemma lem7667008 : term141.
Proof. exact (EQ_MP (@lem7667007) (@lem0)). Qed.
Lemma lem7667009 : term168 = term171.
Proof. exact (@lem7666998 (@lem7667008)). Qed.
Lemma lem7667011 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7667012 : term97 = term98.
Proof. exact (@lem7667011 term11 term11). Qed.
Lemma lem7667013 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7667014 : term100 = term11.
Proof. exact (EQ_MP (@lem7667013) (@lem940073)). Qed.
Lemma lem7667015 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7667016 : term98 = term64.
Proof. exact (MK_COMB (@lem7667015) (@lem7667014)). Qed.
Lemma lem7667017 : term97 = term64.
Proof. exact (TRANS (@lem7667012) (@lem7667016)). Qed.
Lemma lem7667019 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7667020 : term153 = term52.
Proof. exact (@lem7667019 term11). Qed.
Lemma lem7667021 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7667022 : term172 = term166.
Proof. exact (MK_COMB (@lem7667021) (@lem7667020)). Qed.
Lemma lem7667023 : term171 = term141.
Proof. exact (MK_COMB (@lem7667022) (@lem7667017)). Qed.
Lemma lem7667025 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7667026 : term141 = term142.
Proof. exact (@lem7667025 (NUMERAL 0) term11). Qed.
Lemma lem7667027 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7667028 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7667029 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7667028 h1) (fun h1 : term142 = True => @lem7667027)). Qed.
Lemma lem7667030 : term142 = True.
Proof. exact (EQ_MP (@lem7667029) (@lem7667027)). Qed.
Lemma lem7667031 : term141 = True.
Proof. exact (TRANS (@lem7667026) (@lem7667030)). Qed.
Lemma lem7667032 : term171 = True.
Proof. exact (TRANS (@lem7667023) (@lem7667031)). Qed.
Lemma lem7667033 : term168 = True.
Proof. exact (TRANS (@lem7667009) (@lem7667032)). Qed.
Lemma lem7667034 : term141 = True.
Proof. exact (TRANS (@lem7666986) (@lem7667033)). Qed.
Lemma lem7667035 : term165 = True.
Proof. exact (TRANS (@lem7666977) (@lem7667034)). Qed.
Lemma lem7667036 : True = term165.
Proof. exact (SYM (@lem7667035)). Qed.
Lemma lem7667037 : term165.
Proof. exact (EQ_MP (@lem7667036) (@lem0)). Qed.
Lemma lem7667038 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : term441 _98773 _98774.
Proof. exact (conj (@lem7667037) (@lem7666974 _98773 _98774 _98775 h1)). Qed.
Lemma lem7667040 (x : real) (y : real) : term174 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7667041 (_98773 : int) (_98774 : int) : term442 _98773 _98774.
Proof. exact (@lem7667040 term64 (term417 _98773 _98774)). Qed.
Lemma lem7667042 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : term443 _98773 _98774.
Proof. exact (@lem7667041 _98773 _98774 (@lem7667038 _98773 _98774 _98775 h1)). Qed.
Lemma lem7667043 (_98773 : int) (_98774 : int) : (term444 _98773 _98774) = (term417 _98773 _98774).
Proof. exact (@lem1982733 (term417 _98773 _98774)). Qed.
Lemma lem7667044 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7667045 (_98773 : int) (_98774 : int) : (term445 _98773 _98774) = (term419 _98773 _98774).
Proof. exact (MK_COMB (@lem7667044) (@lem7667043 _98773 _98774)). Qed.
Lemma lem7667046 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7667047 (_98773 : int) (_98774 : int) : (term443 _98773 _98774) = (term420 _98773 _98774).
Proof. exact (MK_COMB (@lem7667045 _98773 _98774) (@lem7667046)). Qed.
Lemma lem7667048 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : term420 _98773 _98774.
Proof. exact (EQ_MP (@lem7667047 _98773 _98774) (@lem7667042 _98773 _98774 _98775 h1)). Qed.
Lemma lem7667050 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7667051 : term165 = term141.
Proof. exact (@lem7667050 term52 term64). Qed.
Lemma lem7667053 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7667054 : term64 = term114.
Proof. exact (@lem7667053 term11). Qed.
Lemma lem7667056 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7667057 : term52 = term85.
Proof. exact (@lem7667056 (NUMERAL 0)). Qed.
Lemma lem7667058 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7667059 : term166 = term167.
Proof. exact (MK_COMB (@lem7667058) (@lem7667057)). Qed.
Lemma lem7667060 : term141 = term168.
Proof. exact (MK_COMB (@lem7667059) (@lem7667054)). Qed.
Lemma lem7667061 : term169.
Proof. exact (@lem1980255 term52 term64 term64 term64). Qed.
Lemma lem7667063 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7667064 : term141 = term142.
Proof. exact (@lem7667063 (NUMERAL 0) term11). Qed.
Lemma lem7667065 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7667066 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7667067 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7667066 h1) (fun h1 : term142 = True => @lem7667065)). Qed.
Lemma lem7667068 : term142 = True.
Proof. exact (EQ_MP (@lem7667067) (@lem7667065)). Qed.
Lemma lem7667069 : term141 = True.
Proof. exact (TRANS (@lem7667064) (@lem7667068)). Qed.
Lemma lem7667070 : True = term141.
Proof. exact (SYM (@lem7667069)). Qed.
Lemma lem7667071 : term141.
Proof. exact (EQ_MP (@lem7667070) (@lem0)). Qed.
Lemma lem7667072 : term170.
Proof. exact (@lem7667061 (@lem7667071)). Qed.
Lemma lem7667074 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7667075 : term141 = term142.
Proof. exact (@lem7667074 (NUMERAL 0) term11). Qed.
Lemma lem7667076 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7667077 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7667078 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7667077 h1) (fun h1 : term142 = True => @lem7667076)). Qed.
Lemma lem7667079 : term142 = True.
Proof. exact (EQ_MP (@lem7667078) (@lem7667076)). Qed.
Lemma lem7667080 : term141 = True.
Proof. exact (TRANS (@lem7667075) (@lem7667079)). Qed.
Lemma lem7667081 : True = term141.
Proof. exact (SYM (@lem7667080)). Qed.
Lemma lem7667082 : term141.
Proof. exact (EQ_MP (@lem7667081) (@lem0)). Qed.
Lemma lem7667083 : term168 = term171.
Proof. exact (@lem7667072 (@lem7667082)). Qed.
Lemma lem7667085 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7667086 : term97 = term98.
Proof. exact (@lem7667085 term11 term11). Qed.
Lemma lem7667087 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7667088 : term100 = term11.
Proof. exact (EQ_MP (@lem7667087) (@lem940073)). Qed.
Lemma lem7667089 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7667090 : term98 = term64.
Proof. exact (MK_COMB (@lem7667089) (@lem7667088)). Qed.
Lemma lem7667091 : term97 = term64.
Proof. exact (TRANS (@lem7667086) (@lem7667090)). Qed.
Lemma lem7667093 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7667094 : term153 = term52.
Proof. exact (@lem7667093 term11). Qed.
Lemma lem7667095 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7667096 : term172 = term166.
Proof. exact (MK_COMB (@lem7667095) (@lem7667094)). Qed.
Lemma lem7667097 : term171 = term141.
Proof. exact (MK_COMB (@lem7667096) (@lem7667091)). Qed.
Lemma lem7667099 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7667100 : term141 = term142.
Proof. exact (@lem7667099 (NUMERAL 0) term11). Qed.
Lemma lem7667101 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7667102 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7667103 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7667102 h1) (fun h1 : term142 = True => @lem7667101)). Qed.
Lemma lem7667104 : term142 = True.
Proof. exact (EQ_MP (@lem7667103) (@lem7667101)). Qed.
Lemma lem7667105 : term141 = True.
Proof. exact (TRANS (@lem7667100) (@lem7667104)). Qed.
Lemma lem7667106 : term171 = True.
Proof. exact (TRANS (@lem7667097) (@lem7667105)). Qed.
Lemma lem7667107 : term168 = True.
Proof. exact (TRANS (@lem7667083) (@lem7667106)). Qed.
Lemma lem7667108 : term141 = True.
Proof. exact (TRANS (@lem7667060) (@lem7667107)). Qed.
Lemma lem7667109 : term165 = True.
Proof. exact (TRANS (@lem7667051) (@lem7667108)). Qed.
Lemma lem7667110 : True = term165.
Proof. exact (SYM (@lem7667109)). Qed.
Lemma lem7667111 : term165.
Proof. exact (EQ_MP (@lem7667110) (@lem0)). Qed.
Lemma lem7667112 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : term173 _98775.
Proof. exact (conj (@lem7667111) (@lem7666970 _98773 _98774 _98775 h1)). Qed.
Lemma lem7667114 (x : real) (y : real) : term174 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7667115 (_98775 : int) : term175 _98775.
Proof. exact (@lem7667114 term64 (real_of_int _98775)). Qed.
Lemma lem7667116 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : term176 _98775.
Proof. exact (@lem7667115 _98775 (@lem7667112 _98773 _98774 _98775 h1)). Qed.
Lemma lem7667117 (_98775 : int) : (term177 _98775) = (real_of_int _98775).
Proof. exact (@lem1982733 (real_of_int _98775)). Qed.
Lemma lem7667118 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7667119 (_98775 : int) : (term178 _98775) = (term107 _98775).
Proof. exact (MK_COMB (@lem7667118) (@lem7667117 _98775)). Qed.
Lemma lem7667120 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7667121 (_98775 : int) : (term176 _98775) = (term108 _98775).
Proof. exact (MK_COMB (@lem7667119 _98775) (@lem7667120)). Qed.
Lemma lem7667122 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : term108 _98775.
Proof. exact (EQ_MP (@lem7667121 _98775) (@lem7667116 _98773 _98774 _98775 h1)). Qed.
Lemma lem7667124 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7667125 : term165 = term141.
Proof. exact (@lem7667124 term52 term64). Qed.
Lemma lem7667127 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7667128 : term64 = term114.
Proof. exact (@lem7667127 term11). Qed.
Lemma lem7667130 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7667131 : term52 = term85.
Proof. exact (@lem7667130 (NUMERAL 0)). Qed.
Lemma lem7667132 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7667133 : term166 = term167.
Proof. exact (MK_COMB (@lem7667132) (@lem7667131)). Qed.
Lemma lem7667134 : term141 = term168.
Proof. exact (MK_COMB (@lem7667133) (@lem7667128)). Qed.
Lemma lem7667135 : term169.
Proof. exact (@lem1980255 term52 term64 term64 term64). Qed.
Lemma lem7667137 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7667138 : term141 = term142.
Proof. exact (@lem7667137 (NUMERAL 0) term11). Qed.
Lemma lem7667139 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7667140 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7667141 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7667140 h1) (fun h1 : term142 = True => @lem7667139)). Qed.
Lemma lem7667142 : term142 = True.
Proof. exact (EQ_MP (@lem7667141) (@lem7667139)). Qed.
Lemma lem7667143 : term141 = True.
Proof. exact (TRANS (@lem7667138) (@lem7667142)). Qed.
Lemma lem7667144 : True = term141.
Proof. exact (SYM (@lem7667143)). Qed.
Lemma lem7667145 : term141.
Proof. exact (EQ_MP (@lem7667144) (@lem0)). Qed.
Lemma lem7667146 : term170.
Proof. exact (@lem7667135 (@lem7667145)). Qed.
Lemma lem7667148 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7667149 : term141 = term142.
Proof. exact (@lem7667148 (NUMERAL 0) term11). Qed.
Lemma lem7667150 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7667151 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7667152 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7667151 h1) (fun h1 : term142 = True => @lem7667150)). Qed.
Lemma lem7667153 : term142 = True.
Proof. exact (EQ_MP (@lem7667152) (@lem7667150)). Qed.
Lemma lem7667154 : term141 = True.
Proof. exact (TRANS (@lem7667149) (@lem7667153)). Qed.
Lemma lem7667155 : True = term141.
Proof. exact (SYM (@lem7667154)). Qed.
Lemma lem7667156 : term141.
Proof. exact (EQ_MP (@lem7667155) (@lem0)). Qed.
Lemma lem7667157 : term168 = term171.
Proof. exact (@lem7667146 (@lem7667156)). Qed.
Lemma lem7667159 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7667160 : term97 = term98.
Proof. exact (@lem7667159 term11 term11). Qed.
Lemma lem7667161 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7667162 : term100 = term11.
Proof. exact (EQ_MP (@lem7667161) (@lem940073)). Qed.
Lemma lem7667163 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7667164 : term98 = term64.
Proof. exact (MK_COMB (@lem7667163) (@lem7667162)). Qed.
Lemma lem7667165 : term97 = term64.
Proof. exact (TRANS (@lem7667160) (@lem7667164)). Qed.
Lemma lem7667167 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7667168 : term153 = term52.
Proof. exact (@lem7667167 term11). Qed.
Lemma lem7667169 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7667170 : term172 = term166.
Proof. exact (MK_COMB (@lem7667169) (@lem7667168)). Qed.
Lemma lem7667171 : term171 = term141.
Proof. exact (MK_COMB (@lem7667170) (@lem7667165)). Qed.
Lemma lem7667173 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7667174 : term141 = term142.
Proof. exact (@lem7667173 (NUMERAL 0) term11). Qed.
Lemma lem7667175 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7667176 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7667177 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7667176 h1) (fun h1 : term142 = True => @lem7667175)). Qed.
Lemma lem7667178 : term142 = True.
Proof. exact (EQ_MP (@lem7667177) (@lem7667175)). Qed.
Lemma lem7667179 : term141 = True.
Proof. exact (TRANS (@lem7667174) (@lem7667178)). Qed.
Lemma lem7667180 : term171 = True.
Proof. exact (TRANS (@lem7667171) (@lem7667179)). Qed.
Lemma lem7667181 : term168 = True.
Proof. exact (TRANS (@lem7667157) (@lem7667180)). Qed.
Lemma lem7667182 : term141 = True.
Proof. exact (TRANS (@lem7667134) (@lem7667181)). Qed.
Lemma lem7667183 : term165 = True.
Proof. exact (TRANS (@lem7667125) (@lem7667182)). Qed.
Lemma lem7667184 : True = term165.
Proof. exact (SYM (@lem7667183)). Qed.
Lemma lem7667185 : term165.
Proof. exact (EQ_MP (@lem7667184) (@lem0)). Qed.
Lemma lem7667186 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : term446 _98773 _98774 _98775.
Proof. exact (conj (@lem7667185) (@lem7666973 _98773 _98774 _98775 h1)). Qed.
Lemma lem7667188 (x : real) (y : real) : term174 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7667189 (_98773 : int) (_98774 : int) (_98775 : int) : term447 _98773 _98774 _98775.
Proof. exact (@lem7667188 term64 (term430 _98773 _98774 _98775)). Qed.
Lemma lem7667190 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : term448 _98773 _98774 _98775.
Proof. exact (@lem7667189 _98773 _98774 _98775 (@lem7667186 _98773 _98774 _98775 h1)). Qed.
Lemma lem7667191 (_98773 : int) (_98774 : int) (_98775 : int) : (term449 _98773 _98774 _98775) = (term430 _98773 _98774 _98775).
Proof. exact (@lem1982733 (term430 _98773 _98774 _98775)). Qed.
Lemma lem7667192 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7667193 (_98773 : int) (_98774 : int) (_98775 : int) : (term450 _98773 _98774 _98775) = (term432 _98773 _98774 _98775).
Proof. exact (MK_COMB (@lem7667192) (@lem7667191 _98773 _98774 _98775)). Qed.
Lemma lem7667194 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7667195 (_98773 : int) (_98774 : int) (_98775 : int) : (term448 _98773 _98774 _98775) = (term433 _98773 _98774 _98775).
Proof. exact (MK_COMB (@lem7667193 _98773 _98774 _98775) (@lem7667194)). Qed.
Lemma lem7667196 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : term433 _98773 _98774 _98775.
Proof. exact (EQ_MP (@lem7667195 _98773 _98774 _98775) (@lem7667190 _98773 _98774 _98775 h1)). Qed.
Lemma lem7667197 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : term451 _98773 _98774 _98775.
Proof. exact (conj (@lem7667196 _98773 _98774 _98775 h1) (@lem7667122 _98773 _98774 _98775 h1)). Qed.
Lemma lem7667199 (x : real) (y : real) : term185 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7667200 (_98773 : int) (_98774 : int) (_98775 : int) : term452 _98773 _98774 _98775.
Proof. exact (@lem7667199 (term430 _98773 _98774 _98775) (real_of_int _98775)). Qed.
Lemma lem7667201 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : term453 _98773 _98774 _98775.
Proof. exact (@lem7667200 _98773 _98774 _98775 (@lem7667197 _98773 _98774 _98775 h1)). Qed.
Lemma lem7667202 (_98773 : int) (_98774 : int) (_98775 : int) : (term454 _98773 _98774 _98775) = (term455 _98773 _98774 _98775).
Proof. exact (@lem1982755 (real_of_int _98773) (term429 _98774 _98775) (real_of_int _98775)). Qed.
Lemma lem7667203 (_98774 : int) (_98775 : int) : (term456 _98774 _98775) = (term457 _98774 _98775).
Proof. exact (@lem1982755 (term135 _98774) (term124 _98775) (real_of_int _98775)). Qed.
Lemma lem7667204 (_98775 : int) : (term190 _98775) = (term191 _98775).
Proof. exact (@lem1982759 (term135 _98775) (real_of_int _98775) term88). Qed.
Lemma lem7667205 (_98775 : int) : (term192 _98775) = (term193 _98775).
Proof. exact (@lem1982713 term88 (real_of_int _98775)). Qed.
Lemma lem7667207 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7667208 : term64 = term114.
Proof. exact (@lem7667207 term11). Qed.
Lemma lem7667210 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7667211 : term88 = term89.
Proof. exact (@lem7667210 term11). Qed.
Lemma lem7667212 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7667213 : term194 = term195.
Proof. exact (MK_COMB (@lem7667212) (@lem7667211)). Qed.
Lemma lem7667214 : term196 = term197.
Proof. exact (MK_COMB (@lem7667213) (@lem7667208)). Qed.
Lemma lem7667215 : term198.
Proof. exact (@lem1981473 term88 term64 term64 term64 term52 term64). Qed.
Lemma lem7667217 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7667218 : term141 = term142.
Proof. exact (@lem7667217 (NUMERAL 0) term11). Qed.
Lemma lem7667219 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7667220 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7667221 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7667220 h1) (fun h1 : term142 = True => @lem7667219)). Qed.
Lemma lem7667222 : term142 = True.
Proof. exact (EQ_MP (@lem7667221) (@lem7667219)). Qed.
Lemma lem7667223 : term141 = True.
Proof. exact (TRANS (@lem7667218) (@lem7667222)). Qed.
Lemma lem7667224 : True = term141.
Proof. exact (SYM (@lem7667223)). Qed.
Lemma lem7667225 : term141.
Proof. exact (EQ_MP (@lem7667224) (@lem0)). Qed.
Lemma lem7667226 : term199.
Proof. exact (@lem7667215 (@lem7667225)). Qed.
Lemma lem7667228 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7667229 : term141 = term142.
Proof. exact (@lem7667228 (NUMERAL 0) term11). Qed.
Lemma lem7667230 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7667231 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7667232 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7667231 h1) (fun h1 : term142 = True => @lem7667230)). Qed.
Lemma lem7667233 : term142 = True.
Proof. exact (EQ_MP (@lem7667232) (@lem7667230)). Qed.
Lemma lem7667234 : term141 = True.
Proof. exact (TRANS (@lem7667229) (@lem7667233)). Qed.
Lemma lem7667235 : True = term141.
Proof. exact (SYM (@lem7667234)). Qed.
Lemma lem7667236 : term141.
Proof. exact (EQ_MP (@lem7667235) (@lem0)). Qed.
Lemma lem7667237 : term200.
Proof. exact (@lem7667226 (@lem7667236)). Qed.
Lemma lem7667239 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7667240 : term141 = term142.
Proof. exact (@lem7667239 (NUMERAL 0) term11). Qed.
Lemma lem7667241 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7667242 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7667243 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7667242 h1) (fun h1 : term142 = True => @lem7667241)). Qed.
Lemma lem7667244 : term142 = True.
Proof. exact (EQ_MP (@lem7667243) (@lem7667241)). Qed.
Lemma lem7667245 : term141 = True.
Proof. exact (TRANS (@lem7667240) (@lem7667244)). Qed.
Lemma lem7667246 : True = term141.
Proof. exact (SYM (@lem7667245)). Qed.
Lemma lem7667247 : term141.
Proof. exact (EQ_MP (@lem7667246) (@lem0)). Qed.
Lemma lem7667248 : term201.
Proof. exact (@lem7667237 (@lem7667247)). Qed.
Lemma lem7667250 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7667251 : term97 = term98.
Proof. exact (@lem7667250 term11 term11). Qed.
Lemma lem7667252 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7667253 : term100 = term11.
Proof. exact (EQ_MP (@lem7667252) (@lem940073)). Qed.
Lemma lem7667254 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7667255 : term98 = term64.
Proof. exact (MK_COMB (@lem7667254) (@lem7667253)). Qed.
Lemma lem7667256 : term97 = term64.
Proof. exact (TRANS (@lem7667251) (@lem7667255)). Qed.
Lemma lem7667258 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7667259 : term115 = term120.
Proof. exact (@lem7667258 term11 term11). Qed.
Lemma lem7667260 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7667261 : term100 = term11.
Proof. exact (EQ_MP (@lem7667260) (@lem940073)). Qed.
Lemma lem7667262 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7667263 : term98 = term64.
Proof. exact (MK_COMB (@lem7667262) (@lem7667261)). Qed.
Lemma lem7667264 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7667265 : term120 = term88.
Proof. exact (MK_COMB (@lem7667264) (@lem7667263)). Qed.
Lemma lem7667266 : term115 = term88.
Proof. exact (TRANS (@lem7667259) (@lem7667265)). Qed.
Lemma lem7667267 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7667268 : term202 = term194.
Proof. exact (MK_COMB (@lem7667267) (@lem7667266)). Qed.
Lemma lem7667269 : term203 = term196.
Proof. exact (MK_COMB (@lem7667268) (@lem7667256)). Qed.
Lemma lem7667271 (m : nat) : (term204 m) = term52.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7667272 : term196 = term52.
Proof. exact (@lem7667271 term11). Qed.
Lemma lem7667273 : term203 = term52.
Proof. exact (TRANS (@lem7667269) (@lem7667272)). Qed.
Lemma lem7667274 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7667275 : term205 = term151.
Proof. exact (MK_COMB (@lem7667274) (@lem7667273)). Qed.
Lemma lem7667276 : term64 = term64.
Proof. exact (eq_refl term64). Qed.
Lemma lem7667277 : term206 = term153.
Proof. exact (MK_COMB (@lem7667275) (@lem7667276)). Qed.
Lemma lem7667279 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7667280 : term153 = term52.
Proof. exact (@lem7667279 term11). Qed.
Lemma lem7667281 : term206 = term52.
Proof. exact (TRANS (@lem7667277) (@lem7667280)). Qed.
Lemma lem7667283 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7667284 : term97 = term98.
Proof. exact (@lem7667283 term11 term11). Qed.
Lemma lem7667285 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7667286 : term100 = term11.
Proof. exact (EQ_MP (@lem7667285) (@lem940073)). Qed.
Lemma lem7667287 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7667288 : term98 = term64.
Proof. exact (MK_COMB (@lem7667287) (@lem7667286)). Qed.
Lemma lem7667289 : term97 = term64.
Proof. exact (TRANS (@lem7667284) (@lem7667288)). Qed.
Lemma lem7667290 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem7667291 : term155 = term153.
Proof. exact (MK_COMB (@lem7667290) (@lem7667289)). Qed.
Lemma lem7667293 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7667294 : term153 = term52.
Proof. exact (@lem7667293 term11). Qed.
Lemma lem7667295 : term155 = term52.
Proof. exact (TRANS (@lem7667291) (@lem7667294)). Qed.
Lemma lem7667296 : term52 = term155.
Proof. exact (SYM (@lem7667295)). Qed.
Lemma lem7667297 : term206 = term155.
Proof. exact (TRANS (@lem7667281) (@lem7667296)). Qed.
Lemma lem7667298 : term197 = term85.
Proof. exact (@lem7667248 (@lem7667297)). Qed.
Lemma lem7667299 : term196 = term85.
Proof. exact (TRANS (@lem7667214) (@lem7667298)). Qed.
Lemma lem7667301 (x : real) : (term104 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7667302 : term85 = term52.
Proof. exact (@lem7667301 term52). Qed.
Lemma lem7667303 : term196 = term52.
Proof. exact (TRANS (@lem7667299) (@lem7667302)). Qed.
Lemma lem7667304 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7667305 : term207 = term151.
Proof. exact (MK_COMB (@lem7667304) (@lem7667303)). Qed.
Lemma lem7667306 (_98775 : int) : (real_of_int _98775) = (real_of_int _98775).
Proof. exact (eq_refl (real_of_int _98775)). Qed.
Lemma lem7667307 (_98775 : int) : (term193 _98775) = (term208 _98775).
Proof. exact (MK_COMB (@lem7667305) (@lem7667306 _98775)). Qed.
Lemma lem7667308 (_98775 : int) : (term192 _98775) = (term208 _98775).
Proof. exact (TRANS (@lem7667205 _98775) (@lem7667307 _98775)). Qed.
Lemma lem7667309 (_98775 : int) : (term208 _98775) = term52.
Proof. exact (@lem1982719 (real_of_int _98775)). Qed.
Lemma lem7667310 (_98775 : int) : (term192 _98775) = term52.
Proof. exact (TRANS (@lem7667308 _98775) (@lem7667309 _98775)). Qed.
Lemma lem7667311 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7667312 (_98775 : int) : (term209 _98775) = term210.
Proof. exact (MK_COMB (@lem7667311) (@lem7667310 _98775)). Qed.
Lemma lem7667313 : term88 = term88.
Proof. exact (eq_refl term88). Qed.
Lemma lem7667314 (_98775 : int) : (term191 _98775) = term211.
Proof. exact (MK_COMB (@lem7667312 _98775) (@lem7667313)). Qed.
Lemma lem7667315 (_98775 : int) : (term190 _98775) = term211.
Proof. exact (TRANS (@lem7667204 _98775) (@lem7667314 _98775)). Qed.
Lemma lem7667316 : term211 = term88.
Proof. exact (@lem1982721 term88). Qed.
Lemma lem7667317 (_98775 : int) : (term190 _98775) = term88.
Proof. exact (TRANS (@lem7667315 _98775) (@lem7667316)). Qed.
Lemma lem7667318 (_98774 : int) : (term123 _98774) = (term123 _98774).
Proof. exact (eq_refl (term123 _98774)). Qed.
Lemma lem7667319 (_98775 : int) (_98774 : int) : (term457 _98774 _98775) = (term124 _98774).
Proof. exact (MK_COMB (@lem7667318 _98774) (@lem7667317 _98775)). Qed.
Lemma lem7667320 (_98775 : int) (_98774 : int) : (term456 _98774 _98775) = (term124 _98774).
Proof. exact (TRANS (@lem7667203 _98774 _98775) (@lem7667319 _98775 _98774)). Qed.
Lemma lem7667321 (_98773 : int) : (term65 _98773) = (term65 _98773).
Proof. exact (eq_refl (term65 _98773)). Qed.
Lemma lem7667322 (_98775 : int) (_98773 : int) (_98774 : int) : (term455 _98773 _98774 _98775) = (term125 _98773 _98774).
Proof. exact (MK_COMB (@lem7667321 _98773) (@lem7667320 _98775 _98774)). Qed.
Lemma lem7667323 (_98775 : int) (_98773 : int) (_98774 : int) : (term454 _98773 _98774 _98775) = (term125 _98773 _98774).
Proof. exact (TRANS (@lem7667202 _98773 _98774 _98775) (@lem7667322 _98775 _98773 _98774)). Qed.
Lemma lem7667324 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7667325 (_98775 : int) (_98773 : int) (_98774 : int) : (term458 _98773 _98774 _98775) = (term127 _98773 _98774).
Proof. exact (MK_COMB (@lem7667324) (@lem7667323 _98775 _98773 _98774)). Qed.
Lemma lem7667326 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7667327 (_98775 : int) (_98773 : int) (_98774 : int) : (term453 _98773 _98774 _98775) = (term128 _98773 _98774).
Proof. exact (MK_COMB (@lem7667325 _98775 _98773 _98774) (@lem7667326)). Qed.
Lemma lem7667328 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : term128 _98773 _98774.
Proof. exact (EQ_MP (@lem7667327 _98775 _98773 _98774) (@lem7667201 _98773 _98774 _98775 h1)). Qed.
Lemma lem7667330 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7667331 : term165 = term141.
Proof. exact (@lem7667330 term52 term64). Qed.
Lemma lem7667333 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7667334 : term64 = term114.
Proof. exact (@lem7667333 term11). Qed.
Lemma lem7667336 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7667337 : term52 = term85.
Proof. exact (@lem7667336 (NUMERAL 0)). Qed.
Lemma lem7667338 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7667339 : term166 = term167.
Proof. exact (MK_COMB (@lem7667338) (@lem7667337)). Qed.
Lemma lem7667340 : term141 = term168.
Proof. exact (MK_COMB (@lem7667339) (@lem7667334)). Qed.
Lemma lem7667341 : term169.
Proof. exact (@lem1980255 term52 term64 term64 term64). Qed.
Lemma lem7667343 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7667344 : term141 = term142.
Proof. exact (@lem7667343 (NUMERAL 0) term11). Qed.
Lemma lem7667345 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7667346 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7667347 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7667346 h1) (fun h1 : term142 = True => @lem7667345)). Qed.
Lemma lem7667348 : term142 = True.
Proof. exact (EQ_MP (@lem7667347) (@lem7667345)). Qed.
Lemma lem7667349 : term141 = True.
Proof. exact (TRANS (@lem7667344) (@lem7667348)). Qed.
Lemma lem7667350 : True = term141.
Proof. exact (SYM (@lem7667349)). Qed.
Lemma lem7667351 : term141.
Proof. exact (EQ_MP (@lem7667350) (@lem0)). Qed.
Lemma lem7667352 : term170.
Proof. exact (@lem7667341 (@lem7667351)). Qed.
Lemma lem7667354 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7667355 : term141 = term142.
Proof. exact (@lem7667354 (NUMERAL 0) term11). Qed.
Lemma lem7667356 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7667357 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7667358 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7667357 h1) (fun h1 : term142 = True => @lem7667356)). Qed.
Lemma lem7667359 : term142 = True.
Proof. exact (EQ_MP (@lem7667358) (@lem7667356)). Qed.
Lemma lem7667360 : term141 = True.
Proof. exact (TRANS (@lem7667355) (@lem7667359)). Qed.
Lemma lem7667361 : True = term141.
Proof. exact (SYM (@lem7667360)). Qed.
Lemma lem7667362 : term141.
Proof. exact (EQ_MP (@lem7667361) (@lem0)). Qed.
Lemma lem7667363 : term168 = term171.
Proof. exact (@lem7667352 (@lem7667362)). Qed.
Lemma lem7667365 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7667366 : term97 = term98.
Proof. exact (@lem7667365 term11 term11). Qed.
Lemma lem7667367 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7667368 : term100 = term11.
Proof. exact (EQ_MP (@lem7667367) (@lem940073)). Qed.
Lemma lem7667369 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7667370 : term98 = term64.
Proof. exact (MK_COMB (@lem7667369) (@lem7667368)). Qed.
Lemma lem7667371 : term97 = term64.
Proof. exact (TRANS (@lem7667366) (@lem7667370)). Qed.
Lemma lem7667373 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7667374 : term153 = term52.
Proof. exact (@lem7667373 term11). Qed.
Lemma lem7667375 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7667376 : term172 = term166.
Proof. exact (MK_COMB (@lem7667375) (@lem7667374)). Qed.
Lemma lem7667377 : term171 = term141.
Proof. exact (MK_COMB (@lem7667376) (@lem7667371)). Qed.
Lemma lem7667379 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7667380 : term141 = term142.
Proof. exact (@lem7667379 (NUMERAL 0) term11). Qed.
Lemma lem7667381 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7667382 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7667383 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7667382 h1) (fun h1 : term142 = True => @lem7667381)). Qed.
Lemma lem7667384 : term142 = True.
Proof. exact (EQ_MP (@lem7667383) (@lem7667381)). Qed.
Lemma lem7667385 : term141 = True.
Proof. exact (TRANS (@lem7667380) (@lem7667384)). Qed.
Lemma lem7667386 : term171 = True.
Proof. exact (TRANS (@lem7667377) (@lem7667385)). Qed.
Lemma lem7667387 : term168 = True.
Proof. exact (TRANS (@lem7667363) (@lem7667386)). Qed.
Lemma lem7667388 : term141 = True.
Proof. exact (TRANS (@lem7667340) (@lem7667387)). Qed.
Lemma lem7667389 : term165 = True.
Proof. exact (TRANS (@lem7667331) (@lem7667388)). Qed.
Lemma lem7667390 : True = term165.
Proof. exact (SYM (@lem7667389)). Qed.
Lemma lem7667391 : term165.
Proof. exact (EQ_MP (@lem7667390) (@lem0)). Qed.
Lemma lem7667392 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : term179 _98773 _98774.
Proof. exact (conj (@lem7667391) (@lem7667328 _98773 _98774 _98775 h1)). Qed.
Lemma lem7667394 (x : real) (y : real) : term174 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7667395 (_98773 : int) (_98774 : int) : term180 _98773 _98774.
Proof. exact (@lem7667394 term64 (term125 _98773 _98774)). Qed.
Lemma lem7667396 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : term181 _98773 _98774.
Proof. exact (@lem7667395 _98773 _98774 (@lem7667392 _98773 _98774 _98775 h1)). Qed.
Lemma lem7667397 (_98773 : int) (_98774 : int) : (term182 _98773 _98774) = (term125 _98773 _98774).
Proof. exact (@lem1982733 (term125 _98773 _98774)). Qed.
Lemma lem7667398 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7667399 (_98773 : int) (_98774 : int) : (term183 _98773 _98774) = (term127 _98773 _98774).
Proof. exact (MK_COMB (@lem7667398) (@lem7667397 _98773 _98774)). Qed.
Lemma lem7667400 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7667401 (_98773 : int) (_98774 : int) : (term181 _98773 _98774) = (term128 _98773 _98774).
Proof. exact (MK_COMB (@lem7667399 _98773 _98774) (@lem7667400)). Qed.
Lemma lem7667402 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : term128 _98773 _98774.
Proof. exact (EQ_MP (@lem7667401 _98773 _98774) (@lem7667396 _98773 _98774 _98775 h1)). Qed.
Lemma lem7667403 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : term459 _98773 _98774.
Proof. exact (conj (@lem7667402 _98773 _98774 _98775 h1) (@lem7667048 _98773 _98774 _98775 h1)). Qed.
Lemma lem7667405 (x : real) (y : real) : term185 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7667406 (_98773 : int) (_98774 : int) : term460 _98773 _98774.
Proof. exact (@lem7667405 (term125 _98773 _98774) (term417 _98773 _98774)). Qed.
Lemma lem7667407 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : term461 _98773 _98774.
Proof. exact (@lem7667406 _98773 _98774 (@lem7667403 _98773 _98774 _98775 h1)). Qed.
Lemma lem7667408 (_98773 : int) (_98774 : int) : (term462 _98773 _98774) = (term463 _98773 _98774).
Proof. exact (@lem1982753 (real_of_int _98773) (term135 _98773) (term124 _98774) (real_of_int _98774)). Qed.
Lemma lem7667409 (_98773 : int) : (term464 _98773) = (term193 _98773).
Proof. exact (@lem1982715 term88 (real_of_int _98773)). Qed.
Lemma lem7667411 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7667412 : term64 = term114.
Proof. exact (@lem7667411 term11). Qed.
Lemma lem7667414 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7667415 : term88 = term89.
Proof. exact (@lem7667414 term11). Qed.
Lemma lem7667416 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7667417 : term194 = term195.
Proof. exact (MK_COMB (@lem7667416) (@lem7667415)). Qed.
Lemma lem7667418 : term196 = term197.
Proof. exact (MK_COMB (@lem7667417) (@lem7667412)). Qed.
Lemma lem7667419 : term198.
Proof. exact (@lem1981473 term88 term64 term64 term64 term52 term64). Qed.
Lemma lem7667421 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7667422 : term141 = term142.
Proof. exact (@lem7667421 (NUMERAL 0) term11). Qed.
Lemma lem7667423 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7667424 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7667425 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7667424 h1) (fun h1 : term142 = True => @lem7667423)). Qed.
Lemma lem7667426 : term142 = True.
Proof. exact (EQ_MP (@lem7667425) (@lem7667423)). Qed.
Lemma lem7667427 : term141 = True.
Proof. exact (TRANS (@lem7667422) (@lem7667426)). Qed.
Lemma lem7667428 : True = term141.
Proof. exact (SYM (@lem7667427)). Qed.
Lemma lem7667429 : term141.
Proof. exact (EQ_MP (@lem7667428) (@lem0)). Qed.
Lemma lem7667430 : term199.
Proof. exact (@lem7667419 (@lem7667429)). Qed.
Lemma lem7667432 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7667433 : term141 = term142.
Proof. exact (@lem7667432 (NUMERAL 0) term11). Qed.
Lemma lem7667434 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7667435 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7667436 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7667435 h1) (fun h1 : term142 = True => @lem7667434)). Qed.
Lemma lem7667437 : term142 = True.
Proof. exact (EQ_MP (@lem7667436) (@lem7667434)). Qed.
Lemma lem7667438 : term141 = True.
Proof. exact (TRANS (@lem7667433) (@lem7667437)). Qed.
Lemma lem7667439 : True = term141.
Proof. exact (SYM (@lem7667438)). Qed.
Lemma lem7667440 : term141.
Proof. exact (EQ_MP (@lem7667439) (@lem0)). Qed.
Lemma lem7667441 : term200.
Proof. exact (@lem7667430 (@lem7667440)). Qed.
Lemma lem7667443 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7667444 : term141 = term142.
Proof. exact (@lem7667443 (NUMERAL 0) term11). Qed.
Lemma lem7667445 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7667446 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7667447 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7667446 h1) (fun h1 : term142 = True => @lem7667445)). Qed.
Lemma lem7667448 : term142 = True.
Proof. exact (EQ_MP (@lem7667447) (@lem7667445)). Qed.
Lemma lem7667449 : term141 = True.
Proof. exact (TRANS (@lem7667444) (@lem7667448)). Qed.
Lemma lem7667450 : True = term141.
Proof. exact (SYM (@lem7667449)). Qed.
Lemma lem7667451 : term141.
Proof. exact (EQ_MP (@lem7667450) (@lem0)). Qed.
Lemma lem7667452 : term201.
Proof. exact (@lem7667441 (@lem7667451)). Qed.
Lemma lem7667454 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7667455 : term97 = term98.
Proof. exact (@lem7667454 term11 term11). Qed.
Lemma lem7667456 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7667457 : term100 = term11.
Proof. exact (EQ_MP (@lem7667456) (@lem940073)). Qed.
Lemma lem7667458 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7667459 : term98 = term64.
Proof. exact (MK_COMB (@lem7667458) (@lem7667457)). Qed.
Lemma lem7667460 : term97 = term64.
Proof. exact (TRANS (@lem7667455) (@lem7667459)). Qed.
Lemma lem7667462 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7667463 : term115 = term120.
Proof. exact (@lem7667462 term11 term11). Qed.
Lemma lem7667464 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7667465 : term100 = term11.
Proof. exact (EQ_MP (@lem7667464) (@lem940073)). Qed.
Lemma lem7667466 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7667467 : term98 = term64.
Proof. exact (MK_COMB (@lem7667466) (@lem7667465)). Qed.
Lemma lem7667468 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7667469 : term120 = term88.
Proof. exact (MK_COMB (@lem7667468) (@lem7667467)). Qed.
Lemma lem7667470 : term115 = term88.
Proof. exact (TRANS (@lem7667463) (@lem7667469)). Qed.
Lemma lem7667471 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7667472 : term202 = term194.
Proof. exact (MK_COMB (@lem7667471) (@lem7667470)). Qed.
Lemma lem7667473 : term203 = term196.
Proof. exact (MK_COMB (@lem7667472) (@lem7667460)). Qed.
Lemma lem7667475 (m : nat) : (term204 m) = term52.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7667476 : term196 = term52.
Proof. exact (@lem7667475 term11). Qed.
Lemma lem7667477 : term203 = term52.
Proof. exact (TRANS (@lem7667473) (@lem7667476)). Qed.
Lemma lem7667478 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7667479 : term205 = term151.
Proof. exact (MK_COMB (@lem7667478) (@lem7667477)). Qed.
Lemma lem7667480 : term64 = term64.
Proof. exact (eq_refl term64). Qed.
Lemma lem7667481 : term206 = term153.
Proof. exact (MK_COMB (@lem7667479) (@lem7667480)). Qed.
Lemma lem7667483 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7667484 : term153 = term52.
Proof. exact (@lem7667483 term11). Qed.
Lemma lem7667485 : term206 = term52.
Proof. exact (TRANS (@lem7667481) (@lem7667484)). Qed.
Lemma lem7667487 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7667488 : term97 = term98.
Proof. exact (@lem7667487 term11 term11). Qed.
Lemma lem7667489 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7667490 : term100 = term11.
Proof. exact (EQ_MP (@lem7667489) (@lem940073)). Qed.
Lemma lem7667491 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7667492 : term98 = term64.
Proof. exact (MK_COMB (@lem7667491) (@lem7667490)). Qed.
Lemma lem7667493 : term97 = term64.
Proof. exact (TRANS (@lem7667488) (@lem7667492)). Qed.
Lemma lem7667494 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem7667495 : term155 = term153.
Proof. exact (MK_COMB (@lem7667494) (@lem7667493)). Qed.
Lemma lem7667497 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7667498 : term153 = term52.
Proof. exact (@lem7667497 term11). Qed.
Lemma lem7667499 : term155 = term52.
Proof. exact (TRANS (@lem7667495) (@lem7667498)). Qed.
Lemma lem7667500 : term52 = term155.
Proof. exact (SYM (@lem7667499)). Qed.
Lemma lem7667501 : term206 = term155.
Proof. exact (TRANS (@lem7667485) (@lem7667500)). Qed.
Lemma lem7667502 : term197 = term85.
Proof. exact (@lem7667452 (@lem7667501)). Qed.
Lemma lem7667503 : term196 = term85.
Proof. exact (TRANS (@lem7667418) (@lem7667502)). Qed.
Lemma lem7667505 (x : real) : (term104 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7667506 : term85 = term52.
Proof. exact (@lem7667505 term52). Qed.
Lemma lem7667507 : term196 = term52.
Proof. exact (TRANS (@lem7667503) (@lem7667506)). Qed.
Lemma lem7667508 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7667509 : term207 = term151.
Proof. exact (MK_COMB (@lem7667508) (@lem7667507)). Qed.
Lemma lem7667510 (_98773 : int) : (real_of_int _98773) = (real_of_int _98773).
Proof. exact (eq_refl (real_of_int _98773)). Qed.
Lemma lem7667511 (_98773 : int) : (term193 _98773) = (term208 _98773).
Proof. exact (MK_COMB (@lem7667509) (@lem7667510 _98773)). Qed.
Lemma lem7667512 (_98773 : int) : (term464 _98773) = (term208 _98773).
Proof. exact (TRANS (@lem7667409 _98773) (@lem7667511 _98773)). Qed.
Lemma lem7667513 (_98773 : int) : (term208 _98773) = term52.
Proof. exact (@lem1982719 (real_of_int _98773)). Qed.
Lemma lem7667514 (_98773 : int) : (term464 _98773) = term52.
Proof. exact (TRANS (@lem7667512 _98773) (@lem7667513 _98773)). Qed.
Lemma lem7667515 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7667516 (_98773 : int) : (term465 _98773) = term210.
Proof. exact (MK_COMB (@lem7667515) (@lem7667514 _98773)). Qed.
Lemma lem7667517 (_98774 : int) : (term190 _98774) = (term191 _98774).
Proof. exact (@lem1982759 (term135 _98774) (real_of_int _98774) term88). Qed.
Lemma lem7667518 (_98774 : int) : (term192 _98774) = (term193 _98774).
Proof. exact (@lem1982713 term88 (real_of_int _98774)). Qed.
Lemma lem7667520 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7667521 : term64 = term114.
Proof. exact (@lem7667520 term11). Qed.
Lemma lem7667523 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7667524 : term88 = term89.
Proof. exact (@lem7667523 term11). Qed.
Lemma lem7667525 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7667526 : term194 = term195.
Proof. exact (MK_COMB (@lem7667525) (@lem7667524)). Qed.
Lemma lem7667527 : term196 = term197.
Proof. exact (MK_COMB (@lem7667526) (@lem7667521)). Qed.
Lemma lem7667528 : term198.
Proof. exact (@lem1981473 term88 term64 term64 term64 term52 term64). Qed.
Lemma lem7667530 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7667531 : term141 = term142.
Proof. exact (@lem7667530 (NUMERAL 0) term11). Qed.
Lemma lem7667532 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7667533 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7667534 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7667533 h1) (fun h1 : term142 = True => @lem7667532)). Qed.
Lemma lem7667535 : term142 = True.
Proof. exact (EQ_MP (@lem7667534) (@lem7667532)). Qed.
Lemma lem7667536 : term141 = True.
Proof. exact (TRANS (@lem7667531) (@lem7667535)). Qed.
Lemma lem7667537 : True = term141.
Proof. exact (SYM (@lem7667536)). Qed.
Lemma lem7667538 : term141.
Proof. exact (EQ_MP (@lem7667537) (@lem0)). Qed.
Lemma lem7667539 : term199.
Proof. exact (@lem7667528 (@lem7667538)). Qed.
Lemma lem7667541 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7667542 : term141 = term142.
Proof. exact (@lem7667541 (NUMERAL 0) term11). Qed.
Lemma lem7667543 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7667544 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7667545 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7667544 h1) (fun h1 : term142 = True => @lem7667543)). Qed.
Lemma lem7667546 : term142 = True.
Proof. exact (EQ_MP (@lem7667545) (@lem7667543)). Qed.
Lemma lem7667547 : term141 = True.
Proof. exact (TRANS (@lem7667542) (@lem7667546)). Qed.
Lemma lem7667548 : True = term141.
Proof. exact (SYM (@lem7667547)). Qed.
Lemma lem7667549 : term141.
Proof. exact (EQ_MP (@lem7667548) (@lem0)). Qed.
Lemma lem7667550 : term200.
Proof. exact (@lem7667539 (@lem7667549)). Qed.
Lemma lem7667552 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7667553 : term141 = term142.
Proof. exact (@lem7667552 (NUMERAL 0) term11). Qed.
Lemma lem7667554 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7667555 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7667556 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7667555 h1) (fun h1 : term142 = True => @lem7667554)). Qed.
Lemma lem7667557 : term142 = True.
Proof. exact (EQ_MP (@lem7667556) (@lem7667554)). Qed.
Lemma lem7667558 : term141 = True.
Proof. exact (TRANS (@lem7667553) (@lem7667557)). Qed.
Lemma lem7667559 : True = term141.
Proof. exact (SYM (@lem7667558)). Qed.
Lemma lem7667560 : term141.
Proof. exact (EQ_MP (@lem7667559) (@lem0)). Qed.
Lemma lem7667561 : term201.
Proof. exact (@lem7667550 (@lem7667560)). Qed.
Lemma lem7667563 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7667564 : term97 = term98.
Proof. exact (@lem7667563 term11 term11). Qed.
Lemma lem7667565 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7667566 : term100 = term11.
Proof. exact (EQ_MP (@lem7667565) (@lem940073)). Qed.
Lemma lem7667567 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7667568 : term98 = term64.
Proof. exact (MK_COMB (@lem7667567) (@lem7667566)). Qed.
Lemma lem7667569 : term97 = term64.
Proof. exact (TRANS (@lem7667564) (@lem7667568)). Qed.
Lemma lem7667571 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7667572 : term115 = term120.
Proof. exact (@lem7667571 term11 term11). Qed.
Lemma lem7667573 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7667574 : term100 = term11.
Proof. exact (EQ_MP (@lem7667573) (@lem940073)). Qed.
Lemma lem7667575 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7667576 : term98 = term64.
Proof. exact (MK_COMB (@lem7667575) (@lem7667574)). Qed.
Lemma lem7667577 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7667578 : term120 = term88.
Proof. exact (MK_COMB (@lem7667577) (@lem7667576)). Qed.
Lemma lem7667579 : term115 = term88.
Proof. exact (TRANS (@lem7667572) (@lem7667578)). Qed.
Lemma lem7667580 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7667581 : term202 = term194.
Proof. exact (MK_COMB (@lem7667580) (@lem7667579)). Qed.
Lemma lem7667582 : term203 = term196.
Proof. exact (MK_COMB (@lem7667581) (@lem7667569)). Qed.
Lemma lem7667584 (m : nat) : (term204 m) = term52.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7667585 : term196 = term52.
Proof. exact (@lem7667584 term11). Qed.
Lemma lem7667586 : term203 = term52.
Proof. exact (TRANS (@lem7667582) (@lem7667585)). Qed.
Lemma lem7667587 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7667588 : term205 = term151.
Proof. exact (MK_COMB (@lem7667587) (@lem7667586)). Qed.
Lemma lem7667589 : term64 = term64.
Proof. exact (eq_refl term64). Qed.
Lemma lem7667590 : term206 = term153.
Proof. exact (MK_COMB (@lem7667588) (@lem7667589)). Qed.
Lemma lem7667592 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7667593 : term153 = term52.
Proof. exact (@lem7667592 term11). Qed.
Lemma lem7667594 : term206 = term52.
Proof. exact (TRANS (@lem7667590) (@lem7667593)). Qed.
Lemma lem7667596 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7667597 : term97 = term98.
Proof. exact (@lem7667596 term11 term11). Qed.
Lemma lem7667598 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7667599 : term100 = term11.
Proof. exact (EQ_MP (@lem7667598) (@lem940073)). Qed.
Lemma lem7667600 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7667601 : term98 = term64.
Proof. exact (MK_COMB (@lem7667600) (@lem7667599)). Qed.
Lemma lem7667602 : term97 = term64.
Proof. exact (TRANS (@lem7667597) (@lem7667601)). Qed.
Lemma lem7667603 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem7667604 : term155 = term153.
Proof. exact (MK_COMB (@lem7667603) (@lem7667602)). Qed.
Lemma lem7667606 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7667607 : term153 = term52.
Proof. exact (@lem7667606 term11). Qed.
Lemma lem7667608 : term155 = term52.
Proof. exact (TRANS (@lem7667604) (@lem7667607)). Qed.
Lemma lem7667609 : term52 = term155.
Proof. exact (SYM (@lem7667608)). Qed.
Lemma lem7667610 : term206 = term155.
Proof. exact (TRANS (@lem7667594) (@lem7667609)). Qed.
Lemma lem7667611 : term197 = term85.
Proof. exact (@lem7667561 (@lem7667610)). Qed.
Lemma lem7667612 : term196 = term85.
Proof. exact (TRANS (@lem7667527) (@lem7667611)). Qed.
Lemma lem7667614 (x : real) : (term104 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7667615 : term85 = term52.
Proof. exact (@lem7667614 term52). Qed.
Lemma lem7667616 : term196 = term52.
Proof. exact (TRANS (@lem7667612) (@lem7667615)). Qed.
Lemma lem7667617 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7667618 : term207 = term151.
Proof. exact (MK_COMB (@lem7667617) (@lem7667616)). Qed.
Lemma lem7667619 (_98774 : int) : (real_of_int _98774) = (real_of_int _98774).
Proof. exact (eq_refl (real_of_int _98774)). Qed.
Lemma lem7667620 (_98774 : int) : (term193 _98774) = (term208 _98774).
Proof. exact (MK_COMB (@lem7667618) (@lem7667619 _98774)). Qed.
Lemma lem7667621 (_98774 : int) : (term192 _98774) = (term208 _98774).
Proof. exact (TRANS (@lem7667518 _98774) (@lem7667620 _98774)). Qed.
Lemma lem7667622 (_98774 : int) : (term208 _98774) = term52.
Proof. exact (@lem1982719 (real_of_int _98774)). Qed.
Lemma lem7667623 (_98774 : int) : (term192 _98774) = term52.
Proof. exact (TRANS (@lem7667621 _98774) (@lem7667622 _98774)). Qed.
Lemma lem7667624 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7667625 (_98774 : int) : (term209 _98774) = term210.
Proof. exact (MK_COMB (@lem7667624) (@lem7667623 _98774)). Qed.
Lemma lem7667626 : term88 = term88.
Proof. exact (eq_refl term88). Qed.
Lemma lem7667627 (_98774 : int) : (term191 _98774) = term211.
Proof. exact (MK_COMB (@lem7667625 _98774) (@lem7667626)). Qed.
Lemma lem7667628 (_98774 : int) : (term190 _98774) = term211.
Proof. exact (TRANS (@lem7667517 _98774) (@lem7667627 _98774)). Qed.
Lemma lem7667629 : term211 = term88.
Proof. exact (@lem1982721 term88). Qed.
Lemma lem7667630 (_98774 : int) : (term190 _98774) = term88.
Proof. exact (TRANS (@lem7667628 _98774) (@lem7667629)). Qed.
Lemma lem7667631 (_98773 : int) (_98774 : int) : (term463 _98773 _98774) = term211.
Proof. exact (MK_COMB (@lem7667516 _98773) (@lem7667630 _98774)). Qed.
Lemma lem7667632 (_98773 : int) (_98774 : int) : (term462 _98773 _98774) = term211.
Proof. exact (TRANS (@lem7667408 _98773 _98774) (@lem7667631 _98773 _98774)). Qed.
Lemma lem7667633 : term211 = term88.
Proof. exact (@lem1982721 term88). Qed.
Lemma lem7667634 (_98773 : int) (_98774 : int) : (term462 _98773 _98774) = term88.
Proof. exact (TRANS (@lem7667632 _98773 _98774) (@lem7667633)). Qed.
Lemma lem7667635 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7667636 (_98773 : int) (_98774 : int) : (term466 _98773 _98774) = term231.
Proof. exact (MK_COMB (@lem7667635) (@lem7667634 _98773 _98774)). Qed.
Lemma lem7667637 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7667638 (_98773 : int) (_98774 : int) : (term461 _98773 _98774) = term232.
Proof. exact (MK_COMB (@lem7667636 _98773 _98774) (@lem7667637)). Qed.
Lemma lem7667639 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : term232.
Proof. exact (EQ_MP (@lem7667638 _98773 _98774) (@lem7667407 _98773 _98774 _98775 h1)). Qed.
Lemma lem7667641 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7667642 : term232 = term233.
Proof. exact (@lem7667641 term52 term88). Qed.
Lemma lem7667644 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7667645 : term88 = term89.
Proof. exact (@lem7667644 term11). Qed.
Lemma lem7667647 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7667648 : term52 = term85.
Proof. exact (@lem7667647 (NUMERAL 0)). Qed.
Lemma lem7667649 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7667650 : term54 = term234.
Proof. exact (MK_COMB (@lem7667649) (@lem7667648)). Qed.
Lemma lem7667651 : term233 = term235.
Proof. exact (MK_COMB (@lem7667650) (@lem7667645)). Qed.
Lemma lem7667652 : term236.
Proof. exact (@lem1980026 term52 term64 term88 term64). Qed.
Lemma lem7667654 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7667655 : term141 = term142.
Proof. exact (@lem7667654 (NUMERAL 0) term11). Qed.
Lemma lem7667656 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7667657 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7667658 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7667657 h1) (fun h1 : term142 = True => @lem7667656)). Qed.
Lemma lem7667659 : term142 = True.
Proof. exact (EQ_MP (@lem7667658) (@lem7667656)). Qed.
Lemma lem7667660 : term141 = True.
Proof. exact (TRANS (@lem7667655) (@lem7667659)). Qed.
Lemma lem7667661 : True = term141.
Proof. exact (SYM (@lem7667660)). Qed.
Lemma lem7667662 : term141.
Proof. exact (EQ_MP (@lem7667661) (@lem0)). Qed.
Lemma lem7667663 : term237.
Proof. exact (@lem7667652 (@lem7667662)). Qed.
Lemma lem7667665 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7667666 : term141 = term142.
Proof. exact (@lem7667665 (NUMERAL 0) term11). Qed.
Lemma lem7667667 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7667668 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7667669 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7667668 h1) (fun h1 : term142 = True => @lem7667667)). Qed.
Lemma lem7667670 : term142 = True.
Proof. exact (EQ_MP (@lem7667669) (@lem7667667)). Qed.
Lemma lem7667671 : term141 = True.
Proof. exact (TRANS (@lem7667666) (@lem7667670)). Qed.
Lemma lem7667672 : True = term141.
Proof. exact (SYM (@lem7667671)). Qed.
Lemma lem7667673 : term141.
Proof. exact (EQ_MP (@lem7667672) (@lem0)). Qed.
Lemma lem7667674 : term235 = term238.
Proof. exact (@lem7667663 (@lem7667673)). Qed.
Lemma lem7667676 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7667677 : term115 = term120.
Proof. exact (@lem7667676 term11 term11). Qed.
Lemma lem7667678 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7667679 : term100 = term11.
Proof. exact (EQ_MP (@lem7667678) (@lem940073)). Qed.
Lemma lem7667680 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7667681 : term98 = term64.
Proof. exact (MK_COMB (@lem7667680) (@lem7667679)). Qed.
Lemma lem7667682 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7667683 : term120 = term88.
Proof. exact (MK_COMB (@lem7667682) (@lem7667681)). Qed.
Lemma lem7667684 : term115 = term88.
Proof. exact (TRANS (@lem7667677) (@lem7667683)). Qed.
Lemma lem7667686 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7667687 : term153 = term52.
Proof. exact (@lem7667686 term11). Qed.
Lemma lem7667688 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7667689 : term239 = term54.
Proof. exact (MK_COMB (@lem7667688) (@lem7667687)). Qed.
Lemma lem7667690 : term238 = term233.
Proof. exact (MK_COMB (@lem7667689) (@lem7667684)). Qed.
Lemma lem7667692 (m : nat) (n : nat) : (term240 m n) = (term241 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7667693 : term233 = term242.
Proof. exact (@lem7667692 (NUMERAL 0) term11). Qed.
Lemma lem7667694 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7667695 (h1 : term143 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7667696 : (term143 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7667695 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem7667694)). Qed.
Lemma lem7667697 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7667696) (@lem7667694)). Qed.
Lemma lem7667698 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7667699 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7667700 : term243 = (and True).
Proof. exact (MK_COMB (@lem7667699) (@lem7667698)). Qed.
Lemma lem7667701 : term242 = (True /\ False).
Proof. exact (MK_COMB (@lem7667700) (@lem7667697)). Qed.
Lemma lem7667703 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7667704 : term242 = False.
Proof. exact (TRANS (@lem7667701) (@lem7667703)). Qed.
Lemma lem7667705 : term233 = False.
Proof. exact (TRANS (@lem7667693) (@lem7667704)). Qed.
Lemma lem7667706 : term238 = False.
Proof. exact (TRANS (@lem7667690) (@lem7667705)). Qed.
Lemma lem7667707 : term235 = False.
Proof. exact (TRANS (@lem7667674) (@lem7667706)). Qed.
Lemma lem7667708 : term233 = False.
Proof. exact (TRANS (@lem7667651) (@lem7667707)). Qed.
Lemma lem7667709 : term232 = False.
Proof. exact (TRANS (@lem7667642) (@lem7667708)). Qed.
Lemma lem7667710 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : False.
Proof. exact (EQ_MP (@lem7667709) (@lem7667639 _98773 _98774 _98775 h1)). Qed.
Lemma lem7667712 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : term440 _98773 _98774 _98775.
Proof. exact (h1). Qed.
Lemma lem7667713 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : (term440 _98773 _98774 _98775) = False.
Proof. exact (prop_ext (fun h2 : term440 _98773 _98774 _98775 => @lem7667710 _98773 _98774 _98775 h1) (fun h2 : False => @lem7667712 _98773 _98774 _98775 h1)). Qed.
Lemma lem7667714 (_98773 : int) (_98774 : int) (_98775 : int) (h1 : term440 _98773 _98774 _98775) : False.
Proof. exact (EQ_MP (@lem7667713 _98773 _98774 _98775 h1) (@lem7667712 _98773 _98774 _98775 h1)). Qed.
Lemma lem7667715 (_98774 : int) (_98775 : int) (_98773 : int) (h1 : term409 _98774 _98775 _98773) : term409 _98774 _98775 _98773.
Proof. exact (h1). Qed.
Lemma lem7667716 (_98774 : int) (_98775 : int) (_98773 : int) (h1 : term409 _98774 _98775 _98773) : term440 _98773 _98774 _98775.
Proof. exact (EQ_MP (@lem7666960 _98773 _98774 _98775) (@lem7667715 _98774 _98775 _98773 h1)). Qed.
Lemma lem7667717 (_98774 : int) (_98775 : int) (_98773 : int) (h1 : term409 _98774 _98775 _98773) : (term440 _98773 _98774 _98775) = False.
Proof. exact (prop_ext (fun h2 : term440 _98773 _98774 _98775 => @lem7667714 _98773 _98774 _98775 h2) (fun h2 : False => @lem7667716 _98774 _98775 _98773 h1)). Qed.
Lemma lem7667718 (_98774 : int) (_98775 : int) (_98773 : int) (h1 : term409 _98774 _98775 _98773) : False.
Proof. exact (EQ_MP (@lem7667717 _98774 _98775 _98773 h1) (@lem7667716 _98774 _98775 _98773 h1)). Qed.
Lemma lem7667719 (_98774 : int) (_98775 : int) (_98773 : int) : term467 _98774 _98775 _98773.
Proof. exact (fun h0 : term409 _98774 _98775 _98773 => @lem7667718 _98774 _98775 _98773 h0). Qed.
Lemma lem7667720 (_98774 : int) (_98775 : int) (_98773 : int) : term468 _98774 _98775 _98773.
Proof. exact (@lem1386578 (term469 _98774 _98775 _98773)). Qed.
Lemma lem7667723 (_98774 : int) (_98775 : int) (_98773 : int) : term469 _98774 _98775 _98773.
Proof. exact (@lem7667720 _98774 _98775 _98773 (@lem7667719 _98774 _98775 _98773)). Qed.
Lemma lem7667724 (_98773 : int) (_98774 : int) (_98775 : int) : (term408 _98774 _98775 _98773) = (term385 _98773 _98774 _98775).
Proof. exact (SYM (@lem7666545 _98774 _98775 _98773)). Qed.
Lemma lem7667725 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7667726 (_98773 : int) (_98774 : int) (_98775 : int) : (term469 _98774 _98775 _98773) = (term358 _98773 _98774 _98775).
Proof. exact (MK_COMB (@lem7667725) (@lem7667724 _98773 _98774 _98775)). Qed.
Lemma lem7667727 (_98773 : int) (_98774 : int) (_98775 : int) : term358 _98773 _98774 _98775.
Proof. exact (EQ_MP (@lem7667726 _98773 _98774 _98775) (@lem7667723 _98774 _98775 _98773)). Qed.
Lemma lem7667728 (_98773 : int) (_98774 : int) (_98775 : int) : term359 _98773 _98774 _98775.
Proof. exact (EQ_MP (@lem7666372 _98773 _98774 _98775) (@lem7667727 _98773 _98774 _98775)). Qed.
Lemma lem7667729 {M N : Type'} (i : nat) : term470 M N i.
Proof. exact (@lem7667728 (int_of_num i) (term248 M) (term248 N)). Qed.
Lemma lem7667730 {M N : Type'} (i : nat) : term471 M N i.
Proof. exact (@lem7667729 M N i (@lem7666365 i)). Qed.
Lemma lem7667731 {M N : Type'} (i : nat) : term472 M N i.
Proof. exact (@lem7667730 M N i (@lem7666368 M)). Qed.
Lemma lem7667732 {M N : Type'} (i : nat) : term357 M N i.
Proof. exact (@lem7667731 M N i (@lem7666371 N)). Qed.
Lemma lem7667733 {M N : Type'} (i : nat) : (term357 M N i) = (term342 M N i).
Proof. exact (SYM (@lem7666362 M N i)). Qed.
Lemma lem7667734 {M N : Type'} (i : nat) : term342 M N i.
Proof. exact (EQ_MP (@lem7667733 M N i) (@lem7667732 M N i)). Qed.
Lemma lem7667735 {M N : Type'} (i : nat) : (term342 M N i) = ((term342 M N i) = True).
Proof. exact (@lem7 (term342 M N i)). Qed.
Lemma lem7667736 {M N : Type'} (i : nat) : (term342 M N i) = True.
Proof. exact (EQ_MP (@lem7667735 M N i) (@lem7667734 M N i)). Qed.
Lemma lem7667737 {M N : Type'} (i : nat) : True = (term342 M N i).
Proof. exact (SYM (@lem7667736 M N i)). Qed.
Lemma lem7667738 {M N : Type'} (i : nat) : term342 M N i.
Proof. exact (EQ_MP (@lem7667737 M N i) (@lem0)). Qed.
Lemma lem7667739 {M N : Type'} (i : nat) (h1 : term3 i) : term337 M N i.
Proof. exact (@lem7667738 M N i (@lem7666141 i h1)). Qed.
Lemma lem7667740 {M N : Type'} (i : nat) (h1 : term296 M i) (h2 : term3 i) : term298 M N i.
Proof. exact (@lem7667739 M N i h2 (@lem7666140 M i h1)). Qed.
Lemma lem7667741 {M N : Type'} (i : nat) (h1 : term296 M i) (h2 : term3 i) : term299 M N i.
Proof. exact (EQ_MP (@lem7666261 M N i) (@lem7667740 M N i h1 h2)). Qed.
Lemma lem7667742 {A M N : Type'} (v : cart A N) (u : cart A M) (i : nat) (h1 : term296 M i) (h2 : term3 i) : (term299 M N i) = ((term257 A M N u v i) = (@dollar A M u i)).
Proof. exact (prop_ext (fun h3 : term299 M N i => @lem7666252 A M N v u i h1 h3 h2) (fun h3 : (term257 A M N u v i) = (@dollar A M u i) => @lem7667741 M N i h1 h2)). Qed.
Lemma lem7667743 {A M N : Type'} (v : cart A N) (u : cart A M) (i : nat) (h1 : term296 M i) (h2 : term3 i) : (term257 A M N u v i) = (@dollar A M u i).
Proof. exact (EQ_MP (@lem7667742 A M N v u i h1 h2) (@lem7667741 M N i h1 h2)). Qed.
Lemma lem7667744 {M : Type'} (i : nat) (h1 : term2 M i) : term2 M i.
Proof. exact (h1). Qed.
Lemma lem7667745 {M : Type'} (i : nat) (h1 : term2 M i) : term3 i.
Proof. exact (@lem7666010 M i (@lem7667744 M i h1)). Qed.
Lemma lem7667746 (i : nat) : (term3 i) = ((term3 i) = True).
Proof. exact (@lem7 (term3 i)). Qed.
Lemma lem7667747 {M : Type'} (i : nat) (h1 : term2 M i) : (term3 i) = True.
Proof. exact (EQ_MP (@lem7667746 i) (@lem7667745 M i h1)). Qed.
Lemma lem7667753 {A B : Type'} (g : nat -> A) (i : nat) : term300 A B g i.
Proof. exact (@lem7622314 A B g i). Qed.
Lemma lem7667754 {A B : Type'} (g : nat -> A) (i : nat) : (term300 A B g i) = (term301 A B g i).
Proof. exact (eq_refl (term300 A B g i)). Qed.
Lemma lem7667755 {A B : Type'} (g : nat -> A) (i : nat) : term301 A B g i.
Proof. exact (EQ_MP (@lem7667754 A B g i) (@lem7667753 A B g i)). Qed.
Lemma lem7667756 {B : Type'} (i : nat) (h1 : term295 B i) : term295 B i.
Proof. exact (h1). Qed.
Lemma lem7667757 {A B : Type'} (g : nat -> A) (i : nat) (h1 : term295 B i) : (term302 A B g i) = (g i).
Proof. exact (@lem7667755 A B g i (@lem7667756 B i h1)). Qed.
Lemma lem7667763 {M : Type'} (i : nat) : (term2 M i) = ((term2 M i) = True).
Proof. exact (@lem7 (term2 M i)). Qed.
Lemma lem7667765 {M N : Type'} (i : nat) : (term298 M N i) = ((term298 M N i) = True).
Proof. exact (@lem7 (term298 M N i)). Qed.
Lemma lem7667770 {A B : Type'} (g : nat -> A) (i : nat) : term301 A B g i.
Proof. exact (fun h0 : term295 B i => @lem7667757 A B g i h0). Qed.
Lemma lem7667771 {A M N : Type'} (g : nat -> A) (i : nat) : term303 A M N g i.
Proof. exact (@lem7667770 A (finite_sum M N) g i). Qed.
Lemma lem7667772 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : term304 A M N u v i.
Proof. exact (@lem7667771 A M N (term305 A M N u v) i). Qed.
Lemma lem7667776 {M : Type'} (i : nat) : term473 M i.
Proof. exact (fun h0 : term2 M i => @lem7667747 M i h0). Qed.
Lemma lem7667778 {M : Type'} (i : nat) (h1 : term2 M i) : (term2 M i) = True.
Proof. exact (EQ_MP (@lem7667763 M i) (@lem7666144 M i h1)). Qed.
Lemma lem7667779 {M : Type'} (i : nat) (h1 : term2 M i) : True = (term2 M i).
Proof. exact (SYM (@lem7667778 M i h1)). Qed.
Lemma lem7667780 {M : Type'} (i : nat) (h1 : term2 M i) : term2 M i.
Proof. exact (EQ_MP (@lem7667779 M i h1) (@lem0)). Qed.
Lemma lem7667781 {M : Type'} (i : nat) (h1 : term2 M i) : (term3 i) = True.
Proof. exact (@lem7667776 M i (@lem7667780 M i h1)). Qed.
Lemma lem7667782 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7667783 {M : Type'} (i : nat) (h1 : term2 M i) : (term306 i) = (and True).
Proof. exact (MK_COMB (@lem7667782) (@lem7667781 M i h1)). Qed.
Lemma lem7667785 {M N : Type'} : (@dimindex (finite_sum M N) (@UNIV (finite_sum M N))) = (term336 M N).
Proof. exact (EQ_MP (@lem7640410 M N) (@lem7640437 M N)). Qed.
Lemma lem7667790 (i : nat) : (Peano.le i) = (Peano.le i).
Proof. exact (eq_refl (Peano.le i)). Qed.
Lemma lem7667791 {M N : Type'} (i : nat) : (term299 M N i) = (term298 M N i).
Proof. exact (MK_COMB (@lem7667790 i) (@lem7667785 M N)). Qed.
Lemma lem7667793 {M N : Type'} (i : nat) (h1 : term298 M N i) : (term298 M N i) = True.
Proof. exact (EQ_MP (@lem7667765 M N i) (@lem7666143 M N i h1)). Qed.
Lemma lem7667794 {M N : Type'} (i : nat) (h1 : term298 M N i) : (term299 M N i) = True.
Proof. exact (TRANS (@lem7667791 M N i) (@lem7667793 M N i h1)). Qed.
Lemma lem7667795 {M N : Type'} (i : nat) (h1 : term298 M N i) (h2 : term2 M i) : (term307 M N i) = (True /\ True).
Proof. exact (MK_COMB (@lem7667783 M i h2) (@lem7667794 M N i h1)). Qed.
Lemma lem7667797 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7667798 : (True /\ True) = True.
Proof. exact (@lem7667797 True). Qed.
Lemma lem7667799 {M N : Type'} (i : nat) (h1 : term298 M N i) (h2 : term2 M i) : (term307 M N i) = True.
Proof. exact (TRANS (@lem7667795 M N i h1 h2) (@lem7667798)). Qed.
Lemma lem7667800 {M N : Type'} (i : nat) (h1 : term298 M N i) (h2 : term2 M i) : True = (term307 M N i).
Proof. exact (SYM (@lem7667799 M N i h1 h2)). Qed.
Lemma lem7667801 {M N : Type'} (i : nat) (h1 : term298 M N i) (h2 : term2 M i) : term307 M N i.
Proof. exact (EQ_MP (@lem7667800 M N i h1 h2) (@lem0)). Qed.
Lemma lem7667802 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (h1 : term298 M N i) (h2 : term2 M i) : (term257 A M N u v i) = (term308 A M N u v i).
Proof. exact (@lem7667772 A M N u v i (@lem7667801 M N i h1 h2)). Qed.
Lemma lem7667804 {A B : Type'} (f : A -> B) (y : A) : (term309 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7667805 {A : Type'} (f : nat -> A) (y : nat) : (term310 A f y) = (f y).
Proof. exact (@lem7667804 nat A f y). Qed.
Lemma lem7667806 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term311 A M N u v i) = (term308 A M N u v i).
Proof. exact (@lem7667805 A (term305 A M N u v) i). Qed.
Lemma lem7667807 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term308 A M N u v i) = (term312 A M N u v i).
Proof. exact (eq_refl (term308 A M N u v i)). Qed.
Lemma lem7667808 {A M N : Type'} (u : cart A M) (v : cart A N) : (term313 A M N u v) = (term305 A M N u v).
Proof. exact (fun_ext (fun i : nat => @lem7667807 A M N u v i)). Qed.
Lemma lem7667809 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7667810 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term311 A M N u v i) = (term308 A M N u v i).
Proof. exact (MK_COMB (@lem7667808 A M N u v) (@lem7667809 i)). Qed.
Lemma lem7667811 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem7667812 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term314 A M N u v i) = (term315 A M N u v i).
Proof. exact (MK_COMB (@lem7667811 A) (@lem7667810 A M N u v i)). Qed.
Lemma lem7667813 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term308 A M N u v i) = (term312 A M N u v i).
Proof. exact (eq_refl (term308 A M N u v i)). Qed.
Lemma lem7667814 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : ((term311 A M N u v i) = (term308 A M N u v i)) = ((term308 A M N u v i) = (term312 A M N u v i)).
Proof. exact (MK_COMB (@lem7667812 A M N u v i) (@lem7667813 A M N u v i)). Qed.
Lemma lem7667815 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term308 A M N u v i) = (term312 A M N u v i).
Proof. exact (EQ_MP (@lem7667814 A M N u v i) (@lem7667806 A M N u v i)). Qed.
Lemma lem7667857 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (h1 : term298 M N i) (h2 : term2 M i) : (term257 A M N u v i) = (term312 A M N u v i).
Proof. exact (TRANS (@lem7667802 A M N u v i h1 h2) (@lem7667815 A M N u v i)). Qed.
Lemma lem7667858 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem7667859 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (h1 : term298 M N i) (h2 : term2 M i) : (term259 A M N u v i) = (term474 A M N u v i).
Proof. exact (MK_COMB (@lem7667858 A) (@lem7667857 A M N u v i h1 h2)). Qed.
Lemma lem7667903 {A M N : Type'} (v : cart A N) (i : nat) : (term277 A M N v i) = (term277 A M N v i).
Proof. exact (eq_refl (term277 A M N v i)). Qed.
Lemma lem7667904 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (h1 : term298 M N i) (h2 : term2 M i) : ((term257 A M N u v i) = (term277 A M N v i)) = ((term312 A M N u v i) = (term277 A M N v i)).
Proof. exact (MK_COMB (@lem7667859 A M N u v i h1 h2) (@lem7667903 A M N v i)). Qed.
Lemma lem7667950 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (h1 : term298 M N i) (h2 : term2 M i) : ((term312 A M N u v i) = (term277 A M N v i)) = ((term257 A M N u v i) = (term277 A M N v i)).
Proof. exact (SYM (@lem7667904 A M N u v i h1 h2)). Qed.
Lemma lem7667951 {A : Type'} (_474 : A) (_475 : Prop) (_476 : A -> Prop) (_477 : A) : (term475 A _476 _475 _474 _477) = (term476 A _474 _475 _476 _477).
Proof. exact (@lem13473 A _474 _475 _476 _477). Qed.
Lemma lem7667952 {A M N : Type'} (_474 : A) (_475 : Prop) (v : cart A N) (i : nat) (_477 : A) : (term477 A M N v i _475 _474 _477) = (term478 A M N _474 _475 v i _477).
Proof. exact (@lem7667951 A _474 _475 (term479 A M N v i) _477). Qed.
Lemma lem7667953 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term480 A M N u v i) = (term481 A M N u v i).
Proof. exact (@lem7667952 A M N (@dollar A M u i) (term296 M i) v i (term277 A M N v i)). Qed.
Lemma lem7667954 {A M N : Type'} (v : cart A N) (i : nat) : (term482 A M N v i) = ((term277 A M N v i) = (term277 A M N v i)).
Proof. exact (eq_refl (term482 A M N v i)). Qed.
Lemma lem7667955 {M : Type'} (i : nat) : (term483 M i) = (term483 M i).
Proof. exact (eq_refl (term483 M i)). Qed.
Lemma lem7667956 {A M N : Type'} (v : cart A N) (i : nat) : (term484 A M N v i) = (term485 A M N v i).
Proof. exact (MK_COMB (@lem7667955 M i) (@lem7667954 A M N v i)). Qed.
Lemma lem7667957 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term486 A M N v u i) = ((@dollar A M u i) = (term277 A M N v i)).
Proof. exact (eq_refl (term486 A M N v u i)). Qed.
Lemma lem7667958 {M : Type'} (i : nat) : (term487 M i) = (term487 M i).
Proof. exact (eq_refl (term487 M i)). Qed.
Lemma lem7667959 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term488 A M N v u i) = (term489 A M N u v i).
Proof. exact (MK_COMB (@lem7667958 M i) (@lem7667957 A M N u v i)). Qed.
Lemma lem7667960 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7667961 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term490 A M N v u i) = (term491 A M N u v i).
Proof. exact (MK_COMB (@lem7667960) (@lem7667959 A M N u v i)). Qed.
Lemma lem7667962 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term481 A M N u v i) = (term492 A M N u v i).
Proof. exact (MK_COMB (@lem7667961 A M N u v i) (@lem7667956 A M N v i)). Qed.
Lemma lem7667963 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term480 A M N u v i) = ((term312 A M N u v i) = (term277 A M N v i)).
Proof. exact (eq_refl (term480 A M N u v i)). Qed.
Lemma lem7667964 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7667965 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term493 A M N u v i) = (term494 A M N u v i).
Proof. exact (MK_COMB (@lem7667964) (@lem7667963 A M N u v i)). Qed.
Lemma lem7667966 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : ((term480 A M N u v i) = (term481 A M N u v i)) = (((term312 A M N u v i) = (term277 A M N v i)) = (term492 A M N u v i)).
Proof. exact (MK_COMB (@lem7667965 A M N u v i) (@lem7667962 A M N u v i)). Qed.
Lemma lem7667967 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : ((term312 A M N u v i) = (term277 A M N v i)) = (term492 A M N u v i).
Proof. exact (EQ_MP (@lem7667966 A M N u v i) (@lem7667953 A M N u v i)). Qed.
Lemma lem7667968 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term492 A M N u v i) = ((term312 A M N u v i) = (term277 A M N v i)).
Proof. exact (SYM (@lem7667967 A M N u v i)). Qed.
Lemma lem7667969 {M : Type'} (i : nat) (h1 : term296 M i) : term296 M i.
Proof. exact (h1). Qed.
Lemma lem7668008 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7668009 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem7668008 A x). Qed.
Lemma lem7668010 {A M N : Type'} (v : cart A N) (i : nat) : ((term277 A M N v i) = (term277 A M N v i)) = True.
Proof. exact (@lem7668009 A (term277 A M N v i)). Qed.
Lemma lem7668011 {A M N : Type'} (v : cart A N) (i : nat) : True = ((term277 A M N v i) = (term277 A M N v i)).
Proof. exact (SYM (@lem7668010 A M N v i)). Qed.
Lemma lem7668044 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term489 A M N u v i) = (term495 A M N u v i).
Proof. exact (@lem17265 (term296 M i) ((@dollar A M u i) = (term277 A M N v i))). Qed.
Lemma lem7668046 {M N : Type'} (i : nat) : (term496 M N i) = (term496 M N i).
Proof. exact (eq_refl (term496 M N i)). Qed.
Lemma lem7668047 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term497 A M N u v i) = (term498 A M N u v i).
Proof. exact (MK_COMB (@lem7668046 M N i) (@lem7668044 A M N u v i)). Qed.
Lemma lem7668048 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term499 A M N u v i) = (term497 A M N u v i).
Proof. exact (@lem17265 (term298 M N i) (term489 A M N u v i)). Qed.
Lemma lem7668049 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term499 A M N u v i) = (term498 A M N u v i).
Proof. exact (TRANS (@lem7668048 A M N u v i) (@lem7668047 A M N u v i)). Qed.
Lemma lem7668051 {M : Type'} (i : nat) : (term17 M i) = (term17 M i).
Proof. exact (eq_refl (term17 M i)). Qed.
Lemma lem7668052 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term500 A M N u v i) = (term501 A M N u v i).
Proof. exact (MK_COMB (@lem7668051 M i) (@lem7668049 A M N u v i)). Qed.
Lemma lem7668053 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term502 A M N u v i) = (term500 A M N u v i).
Proof. exact (@lem17265 (term2 M i) (term499 A M N u v i)). Qed.
Lemma lem7668055 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term502 A M N u v i) = (term501 A M N u v i).
Proof. exact (TRANS (@lem7668053 A M N u v i) (@lem7668052 A M N u v i)). Qed.
Lemma lem7668056 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) : (term503 A M N u v i) = (term504 A M N u i v).
Proof. exact (@lem1032781 i (@dimindex M (@UNIV M)) (term505 A M N u i v)). Qed.
Lemma lem7668057 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term506 A M N u i v d) = (term507 A M N u i v d).
Proof. exact (eq_refl (term506 A M N u i v d)). Qed.
Lemma lem7668058 {M : Type'} (i : nat) (d : nat) : (term508 M i d) = (term508 M i d).
Proof. exact (eq_refl (term508 M i d)). Qed.
Lemma lem7668059 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term509 A M N u i v d) = (term510 A M N u i v d).
Proof. exact (MK_COMB (@lem7668058 M i d) (@lem7668057 A M N u i v d)). Qed.
Lemma lem7668060 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) : (term511 A M N u i v) = (term512 A M N u i v).
Proof. exact (fun_ext (fun d : nat => @lem7668059 A M N u i v d)). Qed.
Lemma lem7668061 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7668062 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) : (term504 A M N u i v) = (term513 A M N u i v).
Proof. exact (MK_COMB (@lem7668061) (@lem7668060 A M N u i v)). Qed.
Lemma lem7668063 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term503 A M N u v i) = (term501 A M N u v i).
Proof. exact (eq_refl (term503 A M N u v i)). Qed.
Lemma lem7668064 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7668065 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term514 A M N u v i) = (term515 A M N u v i).
Proof. exact (MK_COMB (@lem7668064) (@lem7668063 A M N u v i)). Qed.
Lemma lem7668066 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) : ((term503 A M N u v i) = (term504 A M N u i v)) = ((term501 A M N u v i) = (term513 A M N u i v)).
Proof. exact (MK_COMB (@lem7668065 A M N u v i) (@lem7668062 A M N u i v)). Qed.
Lemma lem7668067 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) : (term501 A M N u v i) = (term513 A M N u i v).
Proof. exact (EQ_MP (@lem7668066 A M N u i v) (@lem7668056 A M N u i v)). Qed.
Lemma lem7668068 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term510 A M N u i v d) = (term510 A M N u i v d).
Proof. exact (eq_refl (term510 A M N u i v d)). Qed.
Lemma lem7668069 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) : (term512 A M N u i v) = (term512 A M N u i v).
Proof. exact (fun_ext (fun d : nat => @lem7668068 A M N u i v d)). Qed.
Lemma lem7668070 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7668071 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) : (term513 A M N u i v) = (term513 A M N u i v).
Proof. exact (MK_COMB (@lem7668070) (@lem7668069 A M N u i v)). Qed.
Lemma lem7668072 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term515 A M N u v i) = (term515 A M N u v i).
Proof. exact (eq_refl (term515 A M N u v i)). Qed.
Lemma lem7668073 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) : ((term501 A M N u v i) = (term513 A M N u i v)) = ((term501 A M N u v i) = (term513 A M N u i v)).
Proof. exact (MK_COMB (@lem7668072 A M N u v i) (@lem7668071 A M N u i v)). Qed.
Lemma lem7668074 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) : (term501 A M N u v i) = (term513 A M N u i v).
Proof. exact (EQ_MP (@lem7668073 A M N u i v) (@lem7668067 A M N u i v)). Qed.
Lemma lem7668103 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) : (term502 A M N u v i) = (term513 A M N u i v).
Proof. exact (TRANS (@lem7668055 A M N u v i) (@lem7668074 A M N u i v)). Qed.
Lemma lem7668150 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term507 A M N u i v d) = (term507 A M N u i v d).
Proof. exact (eq_refl (term507 A M N u i v d)). Qed.
Lemma lem7668167 {M : Type'} (i : nat) (d : nat) : (term516 M i d) = (term516 M i d).
Proof. exact (eq_refl (term516 M i d)). Qed.
Lemma lem7668174 {M : Type'} (d : nat) : (term517 M d) = (term518 M d).
Proof. exact (@lem1032098 d (@dimindex M (@UNIV M))). Qed.
Lemma lem7668177 (i : nat) : (@eq nat i) = (@eq nat i).
Proof. exact (eq_refl (@eq nat i)). Qed.
Lemma lem7668178 {M : Type'} (i : nat) (d : nat) : (i = (term517 M d)) = (i = (term518 M d)).
Proof. exact (MK_COMB (@lem7668177 i) (@lem7668174 M d)). Qed.
Lemma lem7668179 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7668180 {M : Type'} (i : nat) (d : nat) : (term519 M i d) = (term520 M i d).
Proof. exact (MK_COMB (@lem7668179) (@lem7668178 M i d)). Qed.
Lemma lem7668181 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7668182 {M : Type'} (i : nat) (d : nat) : (term521 M i d) = (term522 M i d).
Proof. exact (MK_COMB (@lem7668181) (@lem7668180 M i d)). Qed.
Lemma lem7668183 {M : Type'} (i : nat) (d : nat) : (term523 M i d) = (term524 M i d).
Proof. exact (MK_COMB (@lem7668182 M i d) (@lem7668167 M i d)). Qed.
Lemma lem7668184 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7668185 {M : Type'} (i : nat) (d : nat) : (term508 M i d) = (term525 M i d).
Proof. exact (MK_COMB (@lem7668184) (@lem7668183 M i d)). Qed.
Lemma lem7668186 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term510 A M N u i v d) = (term526 A M N u i v d).
Proof. exact (MK_COMB (@lem7668185 M i d) (@lem7668150 A M N u i v d)). Qed.
Lemma lem7668187 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) : (term512 A M N u i v) = (term527 A M N u i v).
Proof. exact (fun_ext (fun d : nat => @lem7668186 A M N u i v d)). Qed.
Lemma lem7668188 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7668189 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) : (term513 A M N u i v) = (term528 A M N u i v).
Proof. exact (MK_COMB (@lem7668188) (@lem7668187 A M N u i v)). Qed.
Lemma lem7668192 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) : (term502 A M N u v i) = (term528 A M N u i v).
Proof. exact (TRANS (@lem7668103 A M N u i v) (@lem7668189 A M N u i v)). Qed.
Lemma lem7668194 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem7668195 {M : Type'} (i : nat) (d : nat) : (i = (term518 M d)) = ((int_of_num i) = (term529 M d)).
Proof. exact (@lem7668194 i (term518 M d)). Qed.
Lemma lem7668199 (m : nat) (n : nat) : (term7 m n) = (term8 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7668200 {M : Type'} (d : nat) : (term529 M d) = (term530 M d).
Proof. exact (@lem7668199 d (@dimindex M (@UNIV M))). Qed.
Lemma lem7668201 (i : nat) : (term531 i) = (term531 i).
Proof. exact (eq_refl (term531 i)). Qed.
Lemma lem7668202 {M : Type'} (i : nat) (d : nat) : ((int_of_num i) = (term529 M d)) = ((int_of_num i) = (term530 M d)).
Proof. exact (MK_COMB (@lem7668201 i) (@lem7668200 M d)). Qed.
Lemma lem7668203 {M : Type'} (i : nat) (d : nat) : (i = (term518 M d)) = ((int_of_num i) = (term530 M d)).
Proof. exact (TRANS (@lem7668195 M i d) (@lem7668202 M i d)). Qed.
Lemma lem7668204 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7668205 {M : Type'} (i : nat) (d : nat) : (term520 M i d) = (term532 M i d).
Proof. exact (MK_COMB (@lem7668204) (@lem7668203 M i d)). Qed.
Lemma lem7668206 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7668207 {M : Type'} (i : nat) (d : nat) : (term522 M i d) = (term533 M i d).
Proof. exact (MK_COMB (@lem7668206) (@lem7668205 M i d)). Qed.
Lemma lem7668209 (m : nat) (n : nat) : (Peano.lt m n) = (term534 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem7668210 {M : Type'} (i : nat) : (term535 M i) = (term536 M i).
Proof. exact (@lem7668209 i (@dimindex M (@UNIV M))). Qed.
Lemma lem7668211 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7668212 {M : Type'} (i : nat) : (term537 M i) = (term538 M i).
Proof. exact (MK_COMB (@lem7668211) (@lem7668210 M i)). Qed.
Lemma lem7668213 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7668214 {M : Type'} (i : nat) : (term539 M i) = (term540 M i).
Proof. exact (MK_COMB (@lem7668213) (@lem7668212 M i)). Qed.
Lemma lem7668216 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem7668217 (d : nat) : (d = (NUMERAL 0)) = ((int_of_num d) = term49).
Proof. exact (@lem7668216 d (NUMERAL 0)). Qed.
Lemma lem7668220 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7668221 (d : nat) : (term541 d) = (term542 d).
Proof. exact (MK_COMB (@lem7668220) (@lem7668217 d)). Qed.
Lemma lem7668222 {M : Type'} (i : nat) (d : nat) : (term516 M i d) = (term543 M i d).
Proof. exact (MK_COMB (@lem7668214 M i) (@lem7668221 d)). Qed.
Lemma lem7668223 {M : Type'} (i : nat) (d : nat) : (term524 M i d) = (term544 M i d).
Proof. exact (MK_COMB (@lem7668207 M i d) (@lem7668222 M i d)). Qed.
Lemma lem7668224 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7668225 {M : Type'} (i : nat) (d : nat) : (term525 M i d) = (term545 M i d).
Proof. exact (MK_COMB (@lem7668224) (@lem7668223 M i d)). Qed.
Lemma lem7668227 (m : nat) (n : nat) : (Peano.le m n) = (term4 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7668228 {M : Type'} (i : nat) : (term2 M i) = (term5 M i).
Proof. exact (@lem7668227 (term6 M) i). Qed.
Lemma lem7668230 (m : nat) (n : nat) : (term7 m n) = (term8 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7668231 {M : Type'} : (term9 M) = (term10 M).
Proof. exact (@lem7668230 (@dimindex M (@UNIV M)) term11). Qed.
Lemma lem7668232 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem7668233 {M : Type'} : (term12 M) = (term13 M).
Proof. exact (MK_COMB (@lem7668232) (@lem7668231 M)). Qed.
Lemma lem7668234 (i : nat) : (int_of_num i) = (int_of_num i).
Proof. exact (eq_refl (int_of_num i)). Qed.
Lemma lem7668235 {M : Type'} (i : nat) : (term5 M i) = (term14 M i).
Proof. exact (MK_COMB (@lem7668233 M) (@lem7668234 i)). Qed.
Lemma lem7668236 {M : Type'} (i : nat) : (term2 M i) = (term14 M i).
Proof. exact (TRANS (@lem7668228 M i) (@lem7668235 M i)). Qed.
Lemma lem7668237 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7668238 {M : Type'} (i : nat) : (term15 M i) = (term16 M i).
Proof. exact (MK_COMB (@lem7668237) (@lem7668236 M i)). Qed.
Lemma lem7668239 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7668240 {M : Type'} (i : nat) : (term17 M i) = (term18 M i).
Proof. exact (MK_COMB (@lem7668239) (@lem7668238 M i)). Qed.
Lemma lem7668242 (m : nat) (n : nat) : (Peano.le m n) = (term4 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7668243 {M N : Type'} (i : nat) : (term298 M N i) = (term351 M N i).
Proof. exact (@lem7668242 i (term336 M N)). Qed.
Lemma lem7668245 (m : nat) (n : nat) : (term7 m n) = (term8 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7668246 {M N : Type'} : (term352 M N) = (term353 M N).
Proof. exact (@lem7668245 (@dimindex M (@UNIV M)) (@dimindex N (@UNIV N))). Qed.
Lemma lem7668247 (i : nat) : (term354 i) = (term354 i).
Proof. exact (eq_refl (term354 i)). Qed.
Lemma lem7668248 {M N : Type'} (i : nat) : (term351 M N i) = (term355 M N i).
Proof. exact (MK_COMB (@lem7668247 i) (@lem7668246 M N)). Qed.
Lemma lem7668249 {M N : Type'} (i : nat) : (term298 M N i) = (term355 M N i).
Proof. exact (TRANS (@lem7668243 M N i) (@lem7668248 M N i)). Qed.
Lemma lem7668250 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7668251 {M N : Type'} (i : nat) : (term546 M N i) = (term547 M N i).
Proof. exact (MK_COMB (@lem7668250) (@lem7668249 M N i)). Qed.
Lemma lem7668252 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7668253 {M N : Type'} (i : nat) : (term496 M N i) = (term548 M N i).
Proof. exact (MK_COMB (@lem7668252) (@lem7668251 M N i)). Qed.
Lemma lem7668255 (m : nat) (n : nat) : (Peano.le m n) = (term4 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7668256 {M : Type'} (i : nat) : (term296 M i) = (term346 M i).
Proof. exact (@lem7668255 i (@dimindex M (@UNIV M))). Qed.
Lemma lem7668257 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7668258 {M : Type'} (i : nat) : (term347 M i) = (term348 M i).
Proof. exact (MK_COMB (@lem7668257) (@lem7668256 M i)). Qed.
Lemma lem7668259 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7668260 {M : Type'} (i : nat) : (term349 M i) = (term350 M i).
Proof. exact (MK_COMB (@lem7668259) (@lem7668258 M i)). Qed.
Lemma lem7668263 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) (d : nat) : ((@dollar A M u i) = (@dollar A N v d)) = ((@dollar A M u i) = (@dollar A N v d)).
Proof. exact (eq_refl ((@dollar A M u i) = (@dollar A N v d))). Qed.
Lemma lem7668264 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term549 A M N u i v d) = (term550 A M N u i v d).
Proof. exact (MK_COMB (@lem7668260 M i) (@lem7668263 A M N u i v d)). Qed.
Lemma lem7668265 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term551 A M N u i v d) = (term552 A M N u i v d).
Proof. exact (MK_COMB (@lem7668253 M N i) (@lem7668264 A M N u i v d)). Qed.
Lemma lem7668266 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term507 A M N u i v d) = (term553 A M N u i v d).
Proof. exact (MK_COMB (@lem7668240 M i) (@lem7668265 A M N u i v d)). Qed.
Lemma lem7668267 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term526 A M N u i v d) = (term554 A M N u i v d).
Proof. exact (MK_COMB (@lem7668225 M i d) (@lem7668266 A M N u i v d)). Qed.
Lemma lem7668268 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) : (term527 A M N u i v) = (term555 A M N u i v).
Proof. exact (fun_ext (fun d : nat => @lem7668267 A M N u i v d)). Qed.
Lemma lem7668269 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7668270 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) : (term528 A M N u i v) = (term556 A M N u i v).
Proof. exact (MK_COMB (@lem7668269) (@lem7668268 A M N u i v)). Qed.
Lemma lem7668271 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) : (term502 A M N u v i) = (term556 A M N u i v).
Proof. exact (TRANS (@lem7668192 A M N u i v) (@lem7668270 A M N u i v)). Qed.
Lemma lem7668272 (d : nat) : term21 d.
Proof. exact (@lem2307535 d). Qed.
Lemma lem7668273 (d : nat) : (term21 d) = (term22 d).
Proof. exact (eq_refl (term21 d)). Qed.
Lemma lem7668274 (d : nat) : term22 d.
Proof. exact (EQ_MP (@lem7668273 d) (@lem7668272 d)). Qed.
Lemma lem7668275 (i : nat) : term21 i.
Proof. exact (@lem2307535 i). Qed.
Lemma lem7668276 (i : nat) : (term21 i) = (term22 i).
Proof. exact (eq_refl (term21 i)). Qed.
Lemma lem7668277 (i : nat) : term22 i.
Proof. exact (EQ_MP (@lem7668276 i) (@lem7668275 i)). Qed.
Lemma lem7668278 {M : Type'} : term23 M.
Proof. exact (@lem2307535 (@dimindex M (@UNIV M))). Qed.
Lemma lem7668279 {M : Type'} : (term23 M) = (term24 M).
Proof. exact (eq_refl (term23 M)). Qed.
Lemma lem7668280 {M : Type'} : term24 M.
Proof. exact (EQ_MP (@lem7668279 M) (@lem7668278 M)). Qed.
Lemma lem7668281 {N : Type'} : term23 N.
Proof. exact (@lem2307535 (@dimindex N (@UNIV N))). Qed.
Lemma lem7668282 {N : Type'} : (term23 N) = (term24 N).
Proof. exact (eq_refl (term23 N)). Qed.
Lemma lem7668283 {N : Type'} : term24 N.
Proof. exact (EQ_MP (@lem7668282 N) (@lem7668281 N)). Qed.
Lemma lem7668284 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term557 A M N _98787 _98790 _98788 _98789 u i v d) = (term558 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (@lem2318604 (term558 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668316 (_98788 : int) (_98787 : int) (_98789 : int) : (term559 _98788 _98787 _98789) = (_98788 = (int_add _98787 _98789)).
Proof. exact (@lem16933 (_98788 = (int_add _98787 _98789))). Qed.
Lemma lem7668319 (_98788 : int) (_98789 : int) : (term560 _98788 _98789) = (int_lt _98788 _98789).
Proof. exact (@lem16933 (int_lt _98788 _98789)). Qed.
Lemma lem7668322 (_98787 : int) : (term561 _98787) = (_98787 = term49).
Proof. exact (@lem16933 (_98787 = term49)). Qed.
Lemma lem7668323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7668324 (_98788 : int) (_98789 : int) : (term562 _98788 _98789) = (term563 _98788 _98789).
Proof. exact (MK_COMB (@lem7668323) (@lem7668319 _98788 _98789)). Qed.
Lemma lem7668325 (_98788 : int) (_98789 : int) (_98787 : int) : (term564 _98788 _98789 _98787) = (term565 _98788 _98789 _98787).
Proof. exact (MK_COMB (@lem7668324 _98788 _98789) (@lem7668322 _98787)). Qed.
Lemma lem7668326 (_98788 : int) (_98789 : int) (_98787 : int) : (term566 _98788 _98789 _98787) = (term564 _98788 _98789 _98787).
Proof. exact (@lem17160 (term567 _98788 _98789) (term568 _98787)). Qed.
Lemma lem7668327 (_98788 : int) (_98789 : int) (_98787 : int) : (term566 _98788 _98789 _98787) = (term565 _98788 _98789 _98787).
Proof. exact (TRANS (@lem7668326 _98788 _98789 _98787) (@lem7668325 _98788 _98789 _98787)). Qed.
Lemma lem7668328 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7668329 (_98788 : int) (_98787 : int) (_98789 : int) : (term569 _98788 _98787 _98789) = (term570 _98788 _98787 _98789).
Proof. exact (MK_COMB (@lem7668328) (@lem7668316 _98788 _98787 _98789)). Qed.
Lemma lem7668330 (_98788 : int) (_98789 : int) (_98787 : int) : (term571 _98788 _98789 _98787) = (term572 _98788 _98789 _98787).
Proof. exact (MK_COMB (@lem7668329 _98788 _98787 _98789) (@lem7668327 _98788 _98789 _98787)). Qed.
Lemma lem7668331 (_98788 : int) (_98789 : int) (_98787 : int) : (term573 _98788 _98789 _98787) = (term571 _98788 _98789 _98787).
Proof. exact (@lem17045 (term574 _98788 _98787 _98789) (term575 _98788 _98789 _98787)). Qed.
Lemma lem7668332 (_98788 : int) (_98789 : int) (_98787 : int) : (term573 _98788 _98789 _98787) = (term572 _98788 _98789 _98787).
Proof. exact (TRANS (@lem7668331 _98788 _98789 _98787) (@lem7668330 _98788 _98789 _98787)). Qed.
Lemma lem7668335 (_98789 : int) (_98788 : int) : (term27 _98789 _98788) = (term28 _98789 _98788).
Proof. exact (@lem16933 (term28 _98789 _98788)). Qed.
Lemma lem7668338 (_98788 : int) (_98789 : int) (_98790 : int) : (term576 _98788 _98789 _98790) = (term368 _98788 _98789 _98790).
Proof. exact (@lem16933 (term368 _98788 _98789 _98790)). Qed.
Lemma lem7668341 (_98788 : int) (_98789 : int) : (term361 _98788 _98789) = (int_le _98788 _98789).
Proof. exact (@lem16933 (int_le _98788 _98789)). Qed.
Lemma lem7668342 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term577 A M N u i v d) = (term577 A M N u i v d).
Proof. exact (eq_refl (term577 A M N u i v d)). Qed.
Lemma lem7668343 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7668344 (_98788 : int) (_98789 : int) : (term363 _98788 _98789) = (term364 _98788 _98789).
Proof. exact (MK_COMB (@lem7668343) (@lem7668341 _98788 _98789)). Qed.
Lemma lem7668345 {A M N : Type'} (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term578 A M N _98788 _98789 u i v d) = (term579 A M N _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7668344 _98788 _98789) (@lem7668342 A M N u i v d)). Qed.
Lemma lem7668346 {A M N : Type'} (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term580 A M N _98788 _98789 u i v d) = (term578 A M N _98788 _98789 u i v d).
Proof. exact (@lem17160 (term70 _98788 _98789) ((@dollar A M u i) = (@dollar A N v d))). Qed.
Lemma lem7668347 {A M N : Type'} (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term580 A M N _98788 _98789 u i v d) = (term579 A M N _98788 _98789 u i v d).
Proof. exact (TRANS (@lem7668346 A M N _98788 _98789 u i v d) (@lem7668345 A M N _98788 _98789 u i v d)). Qed.
Lemma lem7668348 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7668349 (_98788 : int) (_98789 : int) (_98790 : int) : (term581 _98788 _98789 _98790) = (term582 _98788 _98789 _98790).
Proof. exact (MK_COMB (@lem7668348) (@lem7668338 _98788 _98789 _98790)). Qed.
Lemma lem7668350 {A M N : Type'} (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term583 A M N _98790 _98788 _98789 u i v d) = (term584 A M N _98790 _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7668349 _98788 _98789 _98790) (@lem7668347 A M N _98788 _98789 u i v d)). Qed.
Lemma lem7668351 {A M N : Type'} (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term585 A M N _98790 _98788 _98789 u i v d) = (term583 A M N _98790 _98788 _98789 u i v d).
Proof. exact (@lem17160 (term362 _98788 _98789 _98790) (term586 A M N _98788 _98789 u i v d)). Qed.
Lemma lem7668352 {A M N : Type'} (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term585 A M N _98790 _98788 _98789 u i v d) = (term584 A M N _98790 _98788 _98789 u i v d).
Proof. exact (TRANS (@lem7668351 A M N _98790 _98788 _98789 u i v d) (@lem7668350 A M N _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668353 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7668354 (_98789 : int) (_98788 : int) : (term30 _98789 _98788) = (term31 _98789 _98788).
Proof. exact (MK_COMB (@lem7668353) (@lem7668335 _98789 _98788)). Qed.
Lemma lem7668355 {A M N : Type'} (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term587 A M N _98790 _98788 _98789 u i v d) = (term588 A M N _98790 _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7668354 _98789 _98788) (@lem7668352 A M N _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668356 {A M N : Type'} (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term589 A M N _98790 _98788 _98789 u i v d) = (term587 A M N _98790 _98788 _98789 u i v d).
Proof. exact (@lem17160 (term35 _98789 _98788) (term590 A M N _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668357 {A M N : Type'} (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term589 A M N _98790 _98788 _98789 u i v d) = (term588 A M N _98790 _98788 _98789 u i v d).
Proof. exact (TRANS (@lem7668356 A M N _98790 _98788 _98789 u i v d) (@lem7668355 A M N _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668358 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7668359 (_98788 : int) (_98789 : int) (_98787 : int) : (term591 _98788 _98789 _98787) = (term592 _98788 _98789 _98787).
Proof. exact (MK_COMB (@lem7668358) (@lem7668332 _98788 _98789 _98787)). Qed.
Lemma lem7668360 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term593 A M N _98787 _98790 _98788 _98789 u i v d) = (term594 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7668359 _98788 _98789 _98787) (@lem7668357 A M N _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668361 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term595 A M N _98787 _98790 _98788 _98789 u i v d) = (term593 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (@lem17160 (term596 _98788 _98789 _98787) (term597 A M N _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668362 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term595 A M N _98787 _98790 _98788 _98789 u i v d) = (term594 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (TRANS (@lem7668361 A M N _98787 _98790 _98788 _98789 u i v d) (@lem7668360 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668364 (_98790 : int) : (term37 _98790) = (term37 _98790).
Proof. exact (eq_refl (term37 _98790)). Qed.
Lemma lem7668365 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term598 A M N _98787 _98790 _98788 _98789 u i v d) = (term599 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7668364 _98790) (@lem7668362 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668366 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term600 A M N _98787 _98790 _98788 _98789 u i v d) = (term598 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (@lem17362 (term41 _98790) (term601 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668367 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term600 A M N _98787 _98790 _98788 _98789 u i v d) = (term599 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (TRANS (@lem7668366 A M N _98787 _98790 _98788 _98789 u i v d) (@lem7668365 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668369 (_98789 : int) : (term37 _98789) = (term37 _98789).
Proof. exact (eq_refl (term37 _98789)). Qed.
Lemma lem7668370 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term602 A M N _98787 _98790 _98788 _98789 u i v d) = (term603 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7668369 _98789) (@lem7668367 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668371 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term604 A M N _98787 _98790 _98788 _98789 u i v d) = (term602 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (@lem17362 (term41 _98789) (term605 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668372 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term604 A M N _98787 _98790 _98788 _98789 u i v d) = (term603 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (TRANS (@lem7668371 A M N _98787 _98790 _98788 _98789 u i v d) (@lem7668370 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668374 (_98788 : int) : (term37 _98788) = (term37 _98788).
Proof. exact (eq_refl (term37 _98788)). Qed.
Lemma lem7668375 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term606 A M N _98787 _98790 _98788 _98789 u i v d) = (term607 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7668374 _98788) (@lem7668372 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668376 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term608 A M N _98787 _98790 _98788 _98789 u i v d) = (term606 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (@lem17362 (term41 _98788) (term609 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668377 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term608 A M N _98787 _98790 _98788 _98789 u i v d) = (term607 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (TRANS (@lem7668376 A M N _98787 _98790 _98788 _98789 u i v d) (@lem7668375 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668379 (_98787 : int) : (term37 _98787) = (term37 _98787).
Proof. exact (eq_refl (term37 _98787)). Qed.
Lemma lem7668380 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term610 A M N _98787 _98790 _98788 _98789 u i v d) = (term611 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7668379 _98787) (@lem7668377 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668381 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term612 A M N _98787 _98790 _98788 _98789 u i v d) = (term610 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (@lem17362 (term41 _98787) (term613 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668427 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term612 A M N _98787 _98790 _98788 _98789 u i v d) = (term611 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (TRANS (@lem7668381 A M N _98787 _98790 _98788 _98789 u i v d) (@lem7668380 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668430 (x : int) (y : int) : (int_le x y) = (term47 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7668431 (_98787 : int) : (term41 _98787) = (term48 _98787).
Proof. exact (@lem7668430 term49 _98787). Qed.
Lemma lem7668433 (n : nat) : (term50 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7668434 : term51 = term52.
Proof. exact (@lem7668433 (NUMERAL 0)). Qed.
Lemma lem7668435 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7668436 : term53 = term54.
Proof. exact (MK_COMB (@lem7668435) (@lem7668434)). Qed.
Lemma lem7668437 (_98787 : int) : (real_of_int _98787) = (real_of_int _98787).
Proof. exact (eq_refl (real_of_int _98787)). Qed.
Lemma lem7668438 (_98787 : int) : (term48 _98787) = (term55 _98787).
Proof. exact (MK_COMB (@lem7668436) (@lem7668437 _98787)). Qed.
Lemma lem7668440 (_98787 : int) : (term41 _98787) = (term55 _98787).
Proof. exact (TRANS (@lem7668431 _98787) (@lem7668438 _98787)). Qed.
Lemma lem7668443 (x : int) (y : int) : (int_le x y) = (term47 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7668444 (_98788 : int) : (term41 _98788) = (term48 _98788).
Proof. exact (@lem7668443 term49 _98788). Qed.
Lemma lem7668446 (n : nat) : (term50 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7668447 : term51 = term52.
Proof. exact (@lem7668446 (NUMERAL 0)). Qed.
Lemma lem7668448 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7668449 : term53 = term54.
Proof. exact (MK_COMB (@lem7668448) (@lem7668447)). Qed.
Lemma lem7668450 (_98788 : int) : (real_of_int _98788) = (real_of_int _98788).
Proof. exact (eq_refl (real_of_int _98788)). Qed.
Lemma lem7668451 (_98788 : int) : (term48 _98788) = (term55 _98788).
Proof. exact (MK_COMB (@lem7668449) (@lem7668450 _98788)). Qed.
Lemma lem7668453 (_98788 : int) : (term41 _98788) = (term55 _98788).
Proof. exact (TRANS (@lem7668444 _98788) (@lem7668451 _98788)). Qed.
Lemma lem7668456 (x : int) (y : int) : (int_le x y) = (term47 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7668457 (_98789 : int) : (term41 _98789) = (term48 _98789).
Proof. exact (@lem7668456 term49 _98789). Qed.
Lemma lem7668459 (n : nat) : (term50 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7668460 : term51 = term52.
Proof. exact (@lem7668459 (NUMERAL 0)). Qed.
Lemma lem7668461 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7668462 : term53 = term54.
Proof. exact (MK_COMB (@lem7668461) (@lem7668460)). Qed.
Lemma lem7668463 (_98789 : int) : (real_of_int _98789) = (real_of_int _98789).
Proof. exact (eq_refl (real_of_int _98789)). Qed.
Lemma lem7668464 (_98789 : int) : (term48 _98789) = (term55 _98789).
Proof. exact (MK_COMB (@lem7668462) (@lem7668463 _98789)). Qed.
Lemma lem7668466 (_98789 : int) : (term41 _98789) = (term55 _98789).
Proof. exact (TRANS (@lem7668457 _98789) (@lem7668464 _98789)). Qed.
Lemma lem7668469 (x : int) (y : int) : (int_le x y) = (term47 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7668470 (_98790 : int) : (term41 _98790) = (term48 _98790).
Proof. exact (@lem7668469 term49 _98790). Qed.
Lemma lem7668472 (n : nat) : (term50 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7668473 : term51 = term52.
Proof. exact (@lem7668472 (NUMERAL 0)). Qed.
Lemma lem7668474 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7668475 : term53 = term54.
Proof. exact (MK_COMB (@lem7668474) (@lem7668473)). Qed.
Lemma lem7668476 (_98790 : int) : (real_of_int _98790) = (real_of_int _98790).
Proof. exact (eq_refl (real_of_int _98790)). Qed.
Lemma lem7668477 (_98790 : int) : (term48 _98790) = (term55 _98790).
Proof. exact (MK_COMB (@lem7668475) (@lem7668476 _98790)). Qed.
Lemma lem7668479 (_98790 : int) : (term41 _98790) = (term55 _98790).
Proof. exact (TRANS (@lem7668470 _98790) (@lem7668477 _98790)). Qed.
Lemma lem7668482 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem7668483 (_98788 : int) (_98787 : int) (_98789 : int) : (_98788 = (int_add _98787 _98789)) = ((real_of_int _98788) = (term58 _98787 _98789)).
Proof. exact (@lem7668482 _98788 (int_add _98787 _98789)). Qed.
Lemma lem7668487 (x : int) (y : int) : (term58 x y) = (term59 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7668488 (_98787 : int) (_98789 : int) : (term58 _98787 _98789) = (term59 _98787 _98789).
Proof. exact (@lem7668487 _98787 _98789). Qed.
Lemma lem7668489 (_98788 : int) : (term614 _98788) = (term614 _98788).
Proof. exact (eq_refl (term614 _98788)). Qed.
Lemma lem7668490 (_98788 : int) (_98787 : int) (_98789 : int) : ((real_of_int _98788) = (term58 _98787 _98789)) = ((real_of_int _98788) = (term59 _98787 _98789)).
Proof. exact (MK_COMB (@lem7668489 _98788) (@lem7668488 _98787 _98789)). Qed.
Lemma lem7668492 (_98788 : int) (_98787 : int) (_98789 : int) : (_98788 = (int_add _98787 _98789)) = ((real_of_int _98788) = (term59 _98787 _98789)).
Proof. exact (TRANS (@lem7668483 _98788 _98787 _98789) (@lem7668490 _98788 _98787 _98789)). Qed.
Lemma lem7668494 (x : int) (y : int) : (int_lt x y) = (term28 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem7668495 (_98788 : int) (_98789 : int) : (int_lt _98788 _98789) = (term28 _98788 _98789).
Proof. exact (@lem7668494 _98788 _98789). Qed.
Lemma lem7668497 (x : int) (y : int) : (int_le x y) = (term47 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7668498 (_98788 : int) (_98789 : int) : (term28 _98788 _98789) = (term56 _98788 _98789).
Proof. exact (@lem7668497 (term57 _98788) _98789). Qed.
Lemma lem7668500 (x : int) (y : int) : (term58 x y) = (term59 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7668501 (_98788 : int) : (term60 _98788) = (term61 _98788).
Proof. exact (@lem7668500 _98788 term62). Qed.
Lemma lem7668503 (n : nat) : (term50 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7668504 : term63 = term64.
Proof. exact (@lem7668503 term11). Qed.
Lemma lem7668505 (_98788 : int) : (term65 _98788) = (term65 _98788).
Proof. exact (eq_refl (term65 _98788)). Qed.
Lemma lem7668506 (_98788 : int) : (term61 _98788) = (term66 _98788).
Proof. exact (MK_COMB (@lem7668505 _98788) (@lem7668504)). Qed.
Lemma lem7668507 (_98788 : int) : (term60 _98788) = (term66 _98788).
Proof. exact (TRANS (@lem7668501 _98788) (@lem7668506 _98788)). Qed.
Lemma lem7668508 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7668509 (_98788 : int) : (term67 _98788) = (term68 _98788).
Proof. exact (MK_COMB (@lem7668508) (@lem7668507 _98788)). Qed.
Lemma lem7668510 (_98789 : int) : (real_of_int _98789) = (real_of_int _98789).
Proof. exact (eq_refl (real_of_int _98789)). Qed.
Lemma lem7668511 (_98788 : int) (_98789 : int) : (term56 _98788 _98789) = (term69 _98788 _98789).
Proof. exact (MK_COMB (@lem7668509 _98788) (@lem7668510 _98789)). Qed.
Lemma lem7668512 (_98788 : int) (_98789 : int) : (term28 _98788 _98789) = (term69 _98788 _98789).
Proof. exact (TRANS (@lem7668498 _98788 _98789) (@lem7668511 _98788 _98789)). Qed.
Lemma lem7668513 (_98788 : int) (_98789 : int) : (int_lt _98788 _98789) = (term69 _98788 _98789).
Proof. exact (TRANS (@lem7668495 _98788 _98789) (@lem7668512 _98788 _98789)). Qed.
Lemma lem7668516 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem7668517 (_98787 : int) : (_98787 = term49) = ((real_of_int _98787) = term51).
Proof. exact (@lem7668516 _98787 term49). Qed.
Lemma lem7668521 (n : nat) : (term50 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7668522 : term51 = term52.
Proof. exact (@lem7668521 (NUMERAL 0)). Qed.
Lemma lem7668523 (_98787 : int) : (term614 _98787) = (term614 _98787).
Proof. exact (eq_refl (term614 _98787)). Qed.
Lemma lem7668524 (_98787 : int) : ((real_of_int _98787) = term51) = ((real_of_int _98787) = term52).
Proof. exact (MK_COMB (@lem7668523 _98787) (@lem7668522)). Qed.
Lemma lem7668526 (_98787 : int) : (_98787 = term49) = ((real_of_int _98787) = term52).
Proof. exact (TRANS (@lem7668517 _98787) (@lem7668524 _98787)). Qed.
Lemma lem7668527 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7668528 (_98788 : int) (_98789 : int) : (term563 _98788 _98789) = (term74 _98788 _98789).
Proof. exact (MK_COMB (@lem7668527) (@lem7668513 _98788 _98789)). Qed.
Lemma lem7668529 (_98788 : int) (_98789 : int) (_98787 : int) : (term565 _98788 _98789 _98787) = (term615 _98788 _98789 _98787).
Proof. exact (MK_COMB (@lem7668528 _98788 _98789) (@lem7668526 _98787)). Qed.
Lemma lem7668530 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7668531 (_98788 : int) (_98787 : int) (_98789 : int) : (term570 _98788 _98787 _98789) = (term616 _98788 _98787 _98789).
Proof. exact (MK_COMB (@lem7668530) (@lem7668492 _98788 _98787 _98789)). Qed.
Lemma lem7668532 (_98788 : int) (_98789 : int) (_98787 : int) : (term572 _98788 _98789 _98787) = (term617 _98788 _98789 _98787).
Proof. exact (MK_COMB (@lem7668531 _98788 _98787 _98789) (@lem7668529 _98788 _98789 _98787)). Qed.
Lemma lem7668535 (x : int) (y : int) : (int_le x y) = (term47 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7668536 (_98789 : int) (_98788 : int) : (term28 _98789 _98788) = (term56 _98789 _98788).
Proof. exact (@lem7668535 (term57 _98789) _98788). Qed.
Lemma lem7668538 (x : int) (y : int) : (term58 x y) = (term59 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7668539 (_98789 : int) : (term60 _98789) = (term61 _98789).
Proof. exact (@lem7668538 _98789 term62). Qed.
Lemma lem7668541 (n : nat) : (term50 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7668542 : term63 = term64.
Proof. exact (@lem7668541 term11). Qed.
Lemma lem7668543 (_98789 : int) : (term65 _98789) = (term65 _98789).
Proof. exact (eq_refl (term65 _98789)). Qed.
Lemma lem7668544 (_98789 : int) : (term61 _98789) = (term66 _98789).
Proof. exact (MK_COMB (@lem7668543 _98789) (@lem7668542)). Qed.
Lemma lem7668545 (_98789 : int) : (term60 _98789) = (term66 _98789).
Proof. exact (TRANS (@lem7668539 _98789) (@lem7668544 _98789)). Qed.
Lemma lem7668546 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7668547 (_98789 : int) : (term67 _98789) = (term68 _98789).
Proof. exact (MK_COMB (@lem7668546) (@lem7668545 _98789)). Qed.
Lemma lem7668548 (_98788 : int) : (real_of_int _98788) = (real_of_int _98788).
Proof. exact (eq_refl (real_of_int _98788)). Qed.
Lemma lem7668549 (_98789 : int) (_98788 : int) : (term56 _98789 _98788) = (term69 _98789 _98788).
Proof. exact (MK_COMB (@lem7668547 _98789) (@lem7668548 _98788)). Qed.
Lemma lem7668551 (_98789 : int) (_98788 : int) : (term28 _98789 _98788) = (term69 _98789 _98788).
Proof. exact (TRANS (@lem7668536 _98789 _98788) (@lem7668549 _98789 _98788)). Qed.
Lemma lem7668554 (x : int) (y : int) : (int_le x y) = (term47 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7668555 (_98788 : int) (_98789 : int) (_98790 : int) : (term368 _98788 _98789 _98790) = (term618 _98788 _98789 _98790).
Proof. exact (@lem7668554 _98788 (int_add _98789 _98790)). Qed.
Lemma lem7668557 (x : int) (y : int) : (term58 x y) = (term59 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7668558 (_98789 : int) (_98790 : int) : (term58 _98789 _98790) = (term59 _98789 _98790).
Proof. exact (@lem7668557 _98789 _98790). Qed.
Lemma lem7668559 (_98788 : int) : (term619 _98788) = (term619 _98788).
Proof. exact (eq_refl (term619 _98788)). Qed.
Lemma lem7668560 (_98788 : int) (_98789 : int) (_98790 : int) : (term618 _98788 _98789 _98790) = (term620 _98788 _98789 _98790).
Proof. exact (MK_COMB (@lem7668559 _98788) (@lem7668558 _98789 _98790)). Qed.
Lemma lem7668562 (_98788 : int) (_98789 : int) (_98790 : int) : (term368 _98788 _98789 _98790) = (term620 _98788 _98789 _98790).
Proof. exact (TRANS (@lem7668555 _98788 _98789 _98790) (@lem7668560 _98788 _98789 _98790)). Qed.
Lemma lem7668565 (x : int) (y : int) : (int_le x y) = (term47 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7668567 (_98788 : int) (_98789 : int) : (int_le _98788 _98789) = (term47 _98788 _98789).
Proof. exact (@lem7668565 _98788 _98789). Qed.
Lemma lem7668574 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term577 A M N u i v d) = (term577 A M N u i v d).
Proof. exact (eq_refl (term577 A M N u i v d)). Qed.
Lemma lem7668575 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7668576 (_98788 : int) (_98789 : int) : (term364 _98788 _98789) = (term402 _98788 _98789).
Proof. exact (MK_COMB (@lem7668575) (@lem7668567 _98788 _98789)). Qed.
Lemma lem7668577 {A M N : Type'} (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term579 A M N _98788 _98789 u i v d) = (term621 A M N _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7668576 _98788 _98789) (@lem7668574 A M N u i v d)). Qed.
Lemma lem7668578 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7668579 (_98788 : int) (_98789 : int) (_98790 : int) : (term582 _98788 _98789 _98790) = (term622 _98788 _98789 _98790).
Proof. exact (MK_COMB (@lem7668578) (@lem7668562 _98788 _98789 _98790)). Qed.
Lemma lem7668580 {A M N : Type'} (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term584 A M N _98790 _98788 _98789 u i v d) = (term623 A M N _98790 _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7668579 _98788 _98789 _98790) (@lem7668577 A M N _98788 _98789 u i v d)). Qed.
Lemma lem7668581 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7668582 (_98789 : int) (_98788 : int) : (term31 _98789 _98788) = (term74 _98789 _98788).
Proof. exact (MK_COMB (@lem7668581) (@lem7668551 _98789 _98788)). Qed.
Lemma lem7668583 {A M N : Type'} (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term588 A M N _98790 _98788 _98789 u i v d) = (term624 A M N _98790 _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7668582 _98789 _98788) (@lem7668580 A M N _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668584 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7668585 (_98788 : int) (_98789 : int) (_98787 : int) : (term592 _98788 _98789 _98787) = (term625 _98788 _98789 _98787).
Proof. exact (MK_COMB (@lem7668584) (@lem7668532 _98788 _98789 _98787)). Qed.
Lemma lem7668586 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term594 A M N _98787 _98790 _98788 _98789 u i v d) = (term626 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7668585 _98788 _98789 _98787) (@lem7668583 A M N _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7668588 (_98790 : int) : (term37 _98790) = (term76 _98790).
Proof. exact (MK_COMB (@lem7668587) (@lem7668479 _98790)). Qed.
Lemma lem7668589 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term599 A M N _98787 _98790 _98788 _98789 u i v d) = (term627 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7668588 _98790) (@lem7668586 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668590 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7668591 (_98789 : int) : (term37 _98789) = (term76 _98789).
Proof. exact (MK_COMB (@lem7668590) (@lem7668466 _98789)). Qed.
Lemma lem7668592 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term603 A M N _98787 _98790 _98788 _98789 u i v d) = (term628 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7668591 _98789) (@lem7668589 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668593 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7668594 (_98788 : int) : (term37 _98788) = (term76 _98788).
Proof. exact (MK_COMB (@lem7668593) (@lem7668453 _98788)). Qed.
Lemma lem7668595 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term607 A M N _98787 _98790 _98788 _98789 u i v d) = (term629 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7668594 _98788) (@lem7668592 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668596 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7668597 (_98787 : int) : (term37 _98787) = (term76 _98787).
Proof. exact (MK_COMB (@lem7668596) (@lem7668440 _98787)). Qed.
Lemma lem7668598 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term611 A M N _98787 _98790 _98788 _98789 u i v d) = (term630 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7668597 _98787) (@lem7668595 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668599 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term612 A M N _98787 _98790 _98788 _98789 u i v d) = (term630 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (TRANS (@lem7668427 A M N _98787 _98790 _98788 _98789 u i v d) (@lem7668598 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668603 (t : Prop) : (term79 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7668711 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term631 A M N _98787 _98790 _98788 _98789 u i v d) = (term630 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (@lem7668603 (term630 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7668712 (_98787 : int) : (term55 _98787) = (term81 _98787).
Proof. exact (@lem1988287 (real_of_int _98787) term52). Qed.
Lemma lem7668718 (_98787 : int) : (term82 _98787) = (term83 _98787).
Proof. exact (@lem1982792 (real_of_int _98787) term52). Qed.
Lemma lem7668720 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7668721 : term52 = term85.
Proof. exact (@lem7668720 (NUMERAL 0)). Qed.
Lemma lem7668723 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7668724 : term88 = term89.
Proof. exact (@lem7668723 term11). Qed.
Lemma lem7668725 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7668726 : term90 = term91.
Proof. exact (MK_COMB (@lem7668725) (@lem7668724)). Qed.
Lemma lem7668727 : term92 = term93.
Proof. exact (MK_COMB (@lem7668726) (@lem7668721)). Qed.
Lemma lem7668728 : term93 = term94.
Proof. exact (@lem1981613 term88 term52 term64 term64). Qed.
Lemma lem7668730 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7668731 : term97 = term98.
Proof. exact (@lem7668730 term11 term11). Qed.
Lemma lem7668732 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7668733 : term100 = term11.
Proof. exact (EQ_MP (@lem7668732) (@lem940073)). Qed.
Lemma lem7668734 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7668735 : term98 = term64.
Proof. exact (MK_COMB (@lem7668734) (@lem7668733)). Qed.
Lemma lem7668736 : term97 = term64.
Proof. exact (TRANS (@lem7668731) (@lem7668735)). Qed.
Lemma lem7668738 (x : nat) : (term101 x) = term52.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7668739 : term92 = term52.
Proof. exact (@lem7668738 term11). Qed.
Lemma lem7668740 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7668741 : term102 = term103.
Proof. exact (MK_COMB (@lem7668740) (@lem7668739)). Qed.
Lemma lem7668742 : term94 = term85.
Proof. exact (MK_COMB (@lem7668741) (@lem7668736)). Qed.
Lemma lem7668743 : term93 = term85.
Proof. exact (TRANS (@lem7668728) (@lem7668742)). Qed.
Lemma lem7668744 : term92 = term85.
Proof. exact (TRANS (@lem7668727) (@lem7668743)). Qed.
Lemma lem7668746 (x : real) : (term104 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7668747 : term85 = term52.
Proof. exact (@lem7668746 term52). Qed.
Lemma lem7668748 : term92 = term52.
Proof. exact (TRANS (@lem7668744) (@lem7668747)). Qed.
Lemma lem7668749 (_98787 : int) : (term65 _98787) = (term65 _98787).
Proof. exact (eq_refl (term65 _98787)). Qed.
Lemma lem7668750 (_98787 : int) : (term83 _98787) = (term105 _98787).
Proof. exact (MK_COMB (@lem7668749 _98787) (@lem7668748)). Qed.
Lemma lem7668751 (_98787 : int) : (term105 _98787) = (real_of_int _98787).
Proof. exact (@lem1982723 (real_of_int _98787)). Qed.
Lemma lem7668752 (_98787 : int) : (term83 _98787) = (real_of_int _98787).
Proof. exact (TRANS (@lem7668750 _98787) (@lem7668751 _98787)). Qed.
Lemma lem7668754 (_98787 : int) : (term82 _98787) = (real_of_int _98787).
Proof. exact (TRANS (@lem7668718 _98787) (@lem7668752 _98787)). Qed.
Lemma lem7668755 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7668756 (_98787 : int) : (term106 _98787) = (term107 _98787).
Proof. exact (MK_COMB (@lem7668755) (@lem7668754 _98787)). Qed.
Lemma lem7668757 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7668758 (_98787 : int) : (term81 _98787) = (term108 _98787).
Proof. exact (MK_COMB (@lem7668756 _98787) (@lem7668757)). Qed.
Lemma lem7668759 (_98787 : int) : (term55 _98787) = (term108 _98787).
Proof. exact (TRANS (@lem7668712 _98787) (@lem7668758 _98787)). Qed.
Lemma lem7668760 (_98788 : int) : (term55 _98788) = (term81 _98788).
Proof. exact (@lem1988287 (real_of_int _98788) term52). Qed.
Lemma lem7668766 (_98788 : int) : (term82 _98788) = (term83 _98788).
Proof. exact (@lem1982792 (real_of_int _98788) term52). Qed.
Lemma lem7668768 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7668769 : term52 = term85.
Proof. exact (@lem7668768 (NUMERAL 0)). Qed.
Lemma lem7668771 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7668772 : term88 = term89.
Proof. exact (@lem7668771 term11). Qed.
Lemma lem7668773 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7668774 : term90 = term91.
Proof. exact (MK_COMB (@lem7668773) (@lem7668772)). Qed.
Lemma lem7668775 : term92 = term93.
Proof. exact (MK_COMB (@lem7668774) (@lem7668769)). Qed.
Lemma lem7668776 : term93 = term94.
Proof. exact (@lem1981613 term88 term52 term64 term64). Qed.
Lemma lem7668778 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7668779 : term97 = term98.
Proof. exact (@lem7668778 term11 term11). Qed.
Lemma lem7668780 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7668781 : term100 = term11.
Proof. exact (EQ_MP (@lem7668780) (@lem940073)). Qed.
Lemma lem7668782 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7668783 : term98 = term64.
Proof. exact (MK_COMB (@lem7668782) (@lem7668781)). Qed.
Lemma lem7668784 : term97 = term64.
Proof. exact (TRANS (@lem7668779) (@lem7668783)). Qed.
Lemma lem7668786 (x : nat) : (term101 x) = term52.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7668787 : term92 = term52.
Proof. exact (@lem7668786 term11). Qed.
Lemma lem7668788 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7668789 : term102 = term103.
Proof. exact (MK_COMB (@lem7668788) (@lem7668787)). Qed.
Lemma lem7668790 : term94 = term85.
Proof. exact (MK_COMB (@lem7668789) (@lem7668784)). Qed.
Lemma lem7668791 : term93 = term85.
Proof. exact (TRANS (@lem7668776) (@lem7668790)). Qed.
Lemma lem7668792 : term92 = term85.
Proof. exact (TRANS (@lem7668775) (@lem7668791)). Qed.
Lemma lem7668794 (x : real) : (term104 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7668795 : term85 = term52.
Proof. exact (@lem7668794 term52). Qed.
Lemma lem7668796 : term92 = term52.
Proof. exact (TRANS (@lem7668792) (@lem7668795)). Qed.
Lemma lem7668797 (_98788 : int) : (term65 _98788) = (term65 _98788).
Proof. exact (eq_refl (term65 _98788)). Qed.
Lemma lem7668798 (_98788 : int) : (term83 _98788) = (term105 _98788).
Proof. exact (MK_COMB (@lem7668797 _98788) (@lem7668796)). Qed.
Lemma lem7668799 (_98788 : int) : (term105 _98788) = (real_of_int _98788).
Proof. exact (@lem1982723 (real_of_int _98788)). Qed.
Lemma lem7668800 (_98788 : int) : (term83 _98788) = (real_of_int _98788).
Proof. exact (TRANS (@lem7668798 _98788) (@lem7668799 _98788)). Qed.
Lemma lem7668802 (_98788 : int) : (term82 _98788) = (real_of_int _98788).
Proof. exact (TRANS (@lem7668766 _98788) (@lem7668800 _98788)). Qed.
Lemma lem7668803 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7668804 (_98788 : int) : (term106 _98788) = (term107 _98788).
Proof. exact (MK_COMB (@lem7668803) (@lem7668802 _98788)). Qed.
Lemma lem7668805 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7668806 (_98788 : int) : (term81 _98788) = (term108 _98788).
Proof. exact (MK_COMB (@lem7668804 _98788) (@lem7668805)). Qed.
Lemma lem7668807 (_98788 : int) : (term55 _98788) = (term108 _98788).
Proof. exact (TRANS (@lem7668760 _98788) (@lem7668806 _98788)). Qed.
Lemma lem7668808 (_98789 : int) : (term55 _98789) = (term81 _98789).
Proof. exact (@lem1988287 (real_of_int _98789) term52). Qed.
Lemma lem7668814 (_98789 : int) : (term82 _98789) = (term83 _98789).
Proof. exact (@lem1982792 (real_of_int _98789) term52). Qed.
Lemma lem7668816 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7668817 : term52 = term85.
Proof. exact (@lem7668816 (NUMERAL 0)). Qed.
Lemma lem7668819 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7668820 : term88 = term89.
Proof. exact (@lem7668819 term11). Qed.
Lemma lem7668821 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7668822 : term90 = term91.
Proof. exact (MK_COMB (@lem7668821) (@lem7668820)). Qed.
Lemma lem7668823 : term92 = term93.
Proof. exact (MK_COMB (@lem7668822) (@lem7668817)). Qed.
Lemma lem7668824 : term93 = term94.
Proof. exact (@lem1981613 term88 term52 term64 term64). Qed.
Lemma lem7668826 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7668827 : term97 = term98.
Proof. exact (@lem7668826 term11 term11). Qed.
Lemma lem7668828 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7668829 : term100 = term11.
Proof. exact (EQ_MP (@lem7668828) (@lem940073)). Qed.
Lemma lem7668830 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7668831 : term98 = term64.
Proof. exact (MK_COMB (@lem7668830) (@lem7668829)). Qed.
Lemma lem7668832 : term97 = term64.
Proof. exact (TRANS (@lem7668827) (@lem7668831)). Qed.
Lemma lem7668834 (x : nat) : (term101 x) = term52.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7668835 : term92 = term52.
Proof. exact (@lem7668834 term11). Qed.
Lemma lem7668836 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7668837 : term102 = term103.
Proof. exact (MK_COMB (@lem7668836) (@lem7668835)). Qed.
Lemma lem7668838 : term94 = term85.
Proof. exact (MK_COMB (@lem7668837) (@lem7668832)). Qed.
Lemma lem7668839 : term93 = term85.
Proof. exact (TRANS (@lem7668824) (@lem7668838)). Qed.
Lemma lem7668840 : term92 = term85.
Proof. exact (TRANS (@lem7668823) (@lem7668839)). Qed.
Lemma lem7668842 (x : real) : (term104 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7668843 : term85 = term52.
Proof. exact (@lem7668842 term52). Qed.
Lemma lem7668844 : term92 = term52.
Proof. exact (TRANS (@lem7668840) (@lem7668843)). Qed.
Lemma lem7668845 (_98789 : int) : (term65 _98789) = (term65 _98789).
Proof. exact (eq_refl (term65 _98789)). Qed.
Lemma lem7668846 (_98789 : int) : (term83 _98789) = (term105 _98789).
Proof. exact (MK_COMB (@lem7668845 _98789) (@lem7668844)). Qed.
Lemma lem7668847 (_98789 : int) : (term105 _98789) = (real_of_int _98789).
Proof. exact (@lem1982723 (real_of_int _98789)). Qed.
Lemma lem7668848 (_98789 : int) : (term83 _98789) = (real_of_int _98789).
Proof. exact (TRANS (@lem7668846 _98789) (@lem7668847 _98789)). Qed.
Lemma lem7668850 (_98789 : int) : (term82 _98789) = (real_of_int _98789).
Proof. exact (TRANS (@lem7668814 _98789) (@lem7668848 _98789)). Qed.
Lemma lem7668851 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7668852 (_98789 : int) : (term106 _98789) = (term107 _98789).
Proof. exact (MK_COMB (@lem7668851) (@lem7668850 _98789)). Qed.
Lemma lem7668853 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7668854 (_98789 : int) : (term81 _98789) = (term108 _98789).
Proof. exact (MK_COMB (@lem7668852 _98789) (@lem7668853)). Qed.
Lemma lem7668855 (_98789 : int) : (term55 _98789) = (term108 _98789).
Proof. exact (TRANS (@lem7668808 _98789) (@lem7668854 _98789)). Qed.
Lemma lem7668856 (_98790 : int) : (term55 _98790) = (term81 _98790).
Proof. exact (@lem1988287 (real_of_int _98790) term52). Qed.
Lemma lem7668862 (_98790 : int) : (term82 _98790) = (term83 _98790).
Proof. exact (@lem1982792 (real_of_int _98790) term52). Qed.
Lemma lem7668864 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7668865 : term52 = term85.
Proof. exact (@lem7668864 (NUMERAL 0)). Qed.
Lemma lem7668867 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7668868 : term88 = term89.
Proof. exact (@lem7668867 term11). Qed.
Lemma lem7668869 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7668870 : term90 = term91.
Proof. exact (MK_COMB (@lem7668869) (@lem7668868)). Qed.
Lemma lem7668871 : term92 = term93.
Proof. exact (MK_COMB (@lem7668870) (@lem7668865)). Qed.
Lemma lem7668872 : term93 = term94.
Proof. exact (@lem1981613 term88 term52 term64 term64). Qed.
Lemma lem7668874 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7668875 : term97 = term98.
Proof. exact (@lem7668874 term11 term11). Qed.
Lemma lem7668876 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7668877 : term100 = term11.
Proof. exact (EQ_MP (@lem7668876) (@lem940073)). Qed.
Lemma lem7668878 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7668879 : term98 = term64.
Proof. exact (MK_COMB (@lem7668878) (@lem7668877)). Qed.
Lemma lem7668880 : term97 = term64.
Proof. exact (TRANS (@lem7668875) (@lem7668879)). Qed.
Lemma lem7668882 (x : nat) : (term101 x) = term52.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7668883 : term92 = term52.
Proof. exact (@lem7668882 term11). Qed.
Lemma lem7668884 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7668885 : term102 = term103.
Proof. exact (MK_COMB (@lem7668884) (@lem7668883)). Qed.
Lemma lem7668886 : term94 = term85.
Proof. exact (MK_COMB (@lem7668885) (@lem7668880)). Qed.
Lemma lem7668887 : term93 = term85.
Proof. exact (TRANS (@lem7668872) (@lem7668886)). Qed.
Lemma lem7668888 : term92 = term85.
Proof. exact (TRANS (@lem7668871) (@lem7668887)). Qed.
Lemma lem7668890 (x : real) : (term104 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7668891 : term85 = term52.
Proof. exact (@lem7668890 term52). Qed.
Lemma lem7668892 : term92 = term52.
Proof. exact (TRANS (@lem7668888) (@lem7668891)). Qed.
Lemma lem7668893 (_98790 : int) : (term65 _98790) = (term65 _98790).
Proof. exact (eq_refl (term65 _98790)). Qed.
Lemma lem7668894 (_98790 : int) : (term83 _98790) = (term105 _98790).
Proof. exact (MK_COMB (@lem7668893 _98790) (@lem7668892)). Qed.
Lemma lem7668895 (_98790 : int) : (term105 _98790) = (real_of_int _98790).
Proof. exact (@lem1982723 (real_of_int _98790)). Qed.
Lemma lem7668896 (_98790 : int) : (term83 _98790) = (real_of_int _98790).
Proof. exact (TRANS (@lem7668894 _98790) (@lem7668895 _98790)). Qed.
Lemma lem7668898 (_98790 : int) : (term82 _98790) = (real_of_int _98790).
Proof. exact (TRANS (@lem7668862 _98790) (@lem7668896 _98790)). Qed.
Lemma lem7668899 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7668900 (_98790 : int) : (term106 _98790) = (term107 _98790).
Proof. exact (MK_COMB (@lem7668899) (@lem7668898 _98790)). Qed.
Lemma lem7668901 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7668902 (_98790 : int) : (term81 _98790) = (term108 _98790).
Proof. exact (MK_COMB (@lem7668900 _98790) (@lem7668901)). Qed.
Lemma lem7668903 (_98790 : int) : (term55 _98790) = (term108 _98790).
Proof. exact (TRANS (@lem7668856 _98790) (@lem7668902 _98790)). Qed.
Lemma lem7668904 (_98788 : int) (_98787 : int) (_98789 : int) : ((real_of_int _98788) = (term59 _98787 _98789)) = ((term632 _98788 _98787 _98789) = term52).
Proof. exact (@lem1988293 (real_of_int _98788) (term59 _98787 _98789)). Qed.
Lemma lem7668916 (_98788 : int) (_98787 : int) (_98789 : int) : (term632 _98788 _98787 _98789) = (term633 _98788 _98787 _98789).
Proof. exact (@lem1982792 (real_of_int _98788) (term59 _98787 _98789)). Qed.
Lemma lem7668923 (_98787 : int) (_98789 : int) : (term634 _98787 _98789) = (term635 _98787 _98789).
Proof. exact (@lem1982781 (real_of_int _98787) term88 (real_of_int _98789)). Qed.
Lemma lem7668924 (_98788 : int) : (term65 _98788) = (term65 _98788).
Proof. exact (eq_refl (term65 _98788)). Qed.
Lemma lem7668925 (_98788 : int) (_98787 : int) (_98789 : int) : (term633 _98788 _98787 _98789) = (term636 _98788 _98787 _98789).
Proof. exact (MK_COMB (@lem7668924 _98788) (@lem7668923 _98787 _98789)). Qed.
Lemma lem7668930 (_98787 : int) (_98788 : int) (_98789 : int) : (term636 _98788 _98787 _98789) = (term637 _98787 _98788 _98789).
Proof. exact (@lem1982757 (term135 _98787) (real_of_int _98788) (term135 _98789)). Qed.
Lemma lem7668931 (_98787 : int) (_98788 : int) (_98789 : int) : (term633 _98788 _98787 _98789) = (term637 _98787 _98788 _98789).
Proof. exact (TRANS (@lem7668925 _98788 _98787 _98789) (@lem7668930 _98787 _98788 _98789)). Qed.
Lemma lem7668933 (_98787 : int) (_98788 : int) (_98789 : int) : (term632 _98788 _98787 _98789) = (term637 _98787 _98788 _98789).
Proof. exact (TRANS (@lem7668916 _98788 _98787 _98789) (@lem7668931 _98787 _98788 _98789)). Qed.
Lemma lem7668934 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7668935 (_98787 : int) (_98788 : int) (_98789 : int) : (term638 _98788 _98787 _98789) = (term639 _98787 _98788 _98789).
Proof. exact (MK_COMB (@lem7668934) (@lem7668933 _98787 _98788 _98789)). Qed.
Lemma lem7668936 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7668937 (_98787 : int) (_98788 : int) (_98789 : int) : ((term632 _98788 _98787 _98789) = term52) = ((term637 _98787 _98788 _98789) = term52).
Proof. exact (MK_COMB (@lem7668935 _98787 _98788 _98789) (@lem7668936)). Qed.
Lemma lem7668938 (_98787 : int) (_98788 : int) (_98789 : int) : ((real_of_int _98788) = (term59 _98787 _98789)) = ((term637 _98787 _98788 _98789) = term52).
Proof. exact (TRANS (@lem7668904 _98788 _98787 _98789) (@lem7668937 _98787 _98788 _98789)). Qed.
Lemma lem7668939 (_98789 : int) (_98788 : int) : (term69 _98788 _98789) = (term109 _98789 _98788).
Proof. exact (@lem1988287 (real_of_int _98789) (term66 _98788)). Qed.
Lemma lem7668951 (_98789 : int) (_98788 : int) : (term110 _98789 _98788) = (term111 _98789 _98788).
Proof. exact (@lem1982792 (real_of_int _98789) (term66 _98788)). Qed.
Lemma lem7668952 (_98788 : int) : (term112 _98788) = (term113 _98788).
Proof. exact (@lem1982781 (real_of_int _98788) term88 term64). Qed.
Lemma lem7668954 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7668955 : term64 = term114.
Proof. exact (@lem7668954 term11). Qed.
Lemma lem7668957 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7668958 : term88 = term89.
Proof. exact (@lem7668957 term11). Qed.
Lemma lem7668959 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7668960 : term90 = term91.
Proof. exact (MK_COMB (@lem7668959) (@lem7668958)). Qed.
Lemma lem7668961 : term115 = term116.
Proof. exact (MK_COMB (@lem7668960) (@lem7668955)). Qed.
Lemma lem7668962 : term116 = term117.
Proof. exact (@lem1981613 term88 term64 term64 term64). Qed.
Lemma lem7668964 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7668965 : term97 = term98.
Proof. exact (@lem7668964 term11 term11). Qed.
Lemma lem7668966 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7668967 : term100 = term11.
Proof. exact (EQ_MP (@lem7668966) (@lem940073)). Qed.
Lemma lem7668968 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7668969 : term98 = term64.
Proof. exact (MK_COMB (@lem7668968) (@lem7668967)). Qed.
Lemma lem7668970 : term97 = term64.
Proof. exact (TRANS (@lem7668965) (@lem7668969)). Qed.
Lemma lem7668972 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7668973 : term115 = term120.
Proof. exact (@lem7668972 term11 term11). Qed.
Lemma lem7668974 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7668975 : term100 = term11.
Proof. exact (EQ_MP (@lem7668974) (@lem940073)). Qed.
Lemma lem7668976 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7668977 : term98 = term64.
Proof. exact (MK_COMB (@lem7668976) (@lem7668975)). Qed.
Lemma lem7668978 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7668979 : term120 = term88.
Proof. exact (MK_COMB (@lem7668978) (@lem7668977)). Qed.
Lemma lem7668980 : term115 = term88.
Proof. exact (TRANS (@lem7668973) (@lem7668979)). Qed.
Lemma lem7668981 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7668982 : term121 = term122.
Proof. exact (MK_COMB (@lem7668981) (@lem7668980)). Qed.
Lemma lem7668983 : term117 = term89.
Proof. exact (MK_COMB (@lem7668982) (@lem7668970)). Qed.
Lemma lem7668984 : term116 = term89.
Proof. exact (TRANS (@lem7668962) (@lem7668983)). Qed.
Lemma lem7668985 : term115 = term89.
Proof. exact (TRANS (@lem7668961) (@lem7668984)). Qed.
Lemma lem7668987 (x : real) : (term104 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7668988 : term89 = term88.
Proof. exact (@lem7668987 term88). Qed.
Lemma lem7668989 : term115 = term88.
Proof. exact (TRANS (@lem7668985) (@lem7668988)). Qed.
Lemma lem7668992 (_98788 : int) : (term123 _98788) = (term123 _98788).
Proof. exact (eq_refl (term123 _98788)). Qed.
Lemma lem7668993 (_98788 : int) : (term113 _98788) = (term124 _98788).
Proof. exact (MK_COMB (@lem7668992 _98788) (@lem7668989)). Qed.
Lemma lem7668994 (_98788 : int) : (term112 _98788) = (term124 _98788).
Proof. exact (TRANS (@lem7668952 _98788) (@lem7668993 _98788)). Qed.
Lemma lem7668995 (_98789 : int) : (term65 _98789) = (term65 _98789).
Proof. exact (eq_refl (term65 _98789)). Qed.
Lemma lem7668996 (_98789 : int) (_98788 : int) : (term111 _98789 _98788) = (term125 _98789 _98788).
Proof. exact (MK_COMB (@lem7668995 _98789) (@lem7668994 _98788)). Qed.
Lemma lem7669001 (_98788 : int) (_98789 : int) : (term125 _98789 _98788) = (term640 _98788 _98789).
Proof. exact (@lem1982757 (term135 _98788) (real_of_int _98789) term88). Qed.
Lemma lem7669002 (_98788 : int) (_98789 : int) : (term111 _98789 _98788) = (term640 _98788 _98789).
Proof. exact (TRANS (@lem7668996 _98789 _98788) (@lem7669001 _98788 _98789)). Qed.
Lemma lem7669004 (_98788 : int) (_98789 : int) : (term110 _98789 _98788) = (term640 _98788 _98789).
Proof. exact (TRANS (@lem7668951 _98789 _98788) (@lem7669002 _98788 _98789)). Qed.
Lemma lem7669005 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7669006 (_98788 : int) (_98789 : int) : (term126 _98789 _98788) = (term641 _98788 _98789).
Proof. exact (MK_COMB (@lem7669005) (@lem7669004 _98788 _98789)). Qed.
Lemma lem7669007 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7669008 (_98788 : int) (_98789 : int) : (term109 _98789 _98788) = (term642 _98788 _98789).
Proof. exact (MK_COMB (@lem7669006 _98788 _98789) (@lem7669007)). Qed.
Lemma lem7669009 (_98788 : int) (_98789 : int) : (term69 _98788 _98789) = (term642 _98788 _98789).
Proof. exact (TRANS (@lem7668939 _98789 _98788) (@lem7669008 _98788 _98789)). Qed.
Lemma lem7669010 (_98787 : int) : ((real_of_int _98787) = term52) = ((term82 _98787) = term52).
Proof. exact (@lem1988293 (real_of_int _98787) term52). Qed.
Lemma lem7669016 (_98787 : int) : (term82 _98787) = (term83 _98787).
Proof. exact (@lem1982792 (real_of_int _98787) term52). Qed.
Lemma lem7669018 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7669019 : term52 = term85.
Proof. exact (@lem7669018 (NUMERAL 0)). Qed.
Lemma lem7669021 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7669022 : term88 = term89.
Proof. exact (@lem7669021 term11). Qed.
Lemma lem7669023 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7669024 : term90 = term91.
Proof. exact (MK_COMB (@lem7669023) (@lem7669022)). Qed.
Lemma lem7669025 : term92 = term93.
Proof. exact (MK_COMB (@lem7669024) (@lem7669019)). Qed.
Lemma lem7669026 : term93 = term94.
Proof. exact (@lem1981613 term88 term52 term64 term64). Qed.
Lemma lem7669028 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7669029 : term97 = term98.
Proof. exact (@lem7669028 term11 term11). Qed.
Lemma lem7669030 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7669031 : term100 = term11.
Proof. exact (EQ_MP (@lem7669030) (@lem940073)). Qed.
Lemma lem7669032 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7669033 : term98 = term64.
Proof. exact (MK_COMB (@lem7669032) (@lem7669031)). Qed.
Lemma lem7669034 : term97 = term64.
Proof. exact (TRANS (@lem7669029) (@lem7669033)). Qed.
Lemma lem7669036 (x : nat) : (term101 x) = term52.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7669037 : term92 = term52.
Proof. exact (@lem7669036 term11). Qed.
Lemma lem7669038 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7669039 : term102 = term103.
Proof. exact (MK_COMB (@lem7669038) (@lem7669037)). Qed.
Lemma lem7669040 : term94 = term85.
Proof. exact (MK_COMB (@lem7669039) (@lem7669034)). Qed.
Lemma lem7669041 : term93 = term85.
Proof. exact (TRANS (@lem7669026) (@lem7669040)). Qed.
Lemma lem7669042 : term92 = term85.
Proof. exact (TRANS (@lem7669025) (@lem7669041)). Qed.
Lemma lem7669044 (x : real) : (term104 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7669045 : term85 = term52.
Proof. exact (@lem7669044 term52). Qed.
Lemma lem7669046 : term92 = term52.
Proof. exact (TRANS (@lem7669042) (@lem7669045)). Qed.
Lemma lem7669047 (_98787 : int) : (term65 _98787) = (term65 _98787).
Proof. exact (eq_refl (term65 _98787)). Qed.
Lemma lem7669048 (_98787 : int) : (term83 _98787) = (term105 _98787).
Proof. exact (MK_COMB (@lem7669047 _98787) (@lem7669046)). Qed.
Lemma lem7669049 (_98787 : int) : (term105 _98787) = (real_of_int _98787).
Proof. exact (@lem1982723 (real_of_int _98787)). Qed.
Lemma lem7669050 (_98787 : int) : (term83 _98787) = (real_of_int _98787).
Proof. exact (TRANS (@lem7669048 _98787) (@lem7669049 _98787)). Qed.
Lemma lem7669052 (_98787 : int) : (term82 _98787) = (real_of_int _98787).
Proof. exact (TRANS (@lem7669016 _98787) (@lem7669050 _98787)). Qed.
Lemma lem7669053 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7669054 (_98787 : int) : (term643 _98787) = (term614 _98787).
Proof. exact (MK_COMB (@lem7669053) (@lem7669052 _98787)). Qed.
Lemma lem7669055 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7669056 (_98787 : int) : ((term82 _98787) = term52) = ((real_of_int _98787) = term52).
Proof. exact (MK_COMB (@lem7669054 _98787) (@lem7669055)). Qed.
Lemma lem7669057 (_98787 : int) : ((real_of_int _98787) = term52) = ((real_of_int _98787) = term52).
Proof. exact (TRANS (@lem7669010 _98787) (@lem7669056 _98787)). Qed.
Lemma lem7669058 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7669059 (_98788 : int) (_98789 : int) : (term74 _98788 _98789) = (term644 _98788 _98789).
Proof. exact (MK_COMB (@lem7669058) (@lem7669009 _98788 _98789)). Qed.
Lemma lem7669060 (_98788 : int) (_98789 : int) (_98787 : int) : (term615 _98788 _98789 _98787) = (term645 _98788 _98789 _98787).
Proof. exact (MK_COMB (@lem7669059 _98788 _98789) (@lem7669057 _98787)). Qed.
Lemma lem7669061 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7669062 (_98787 : int) (_98788 : int) (_98789 : int) : (term616 _98788 _98787 _98789) = (term646 _98787 _98788 _98789).
Proof. exact (MK_COMB (@lem7669061) (@lem7668938 _98787 _98788 _98789)). Qed.
Lemma lem7669063 (_98788 : int) (_98789 : int) (_98787 : int) : (term617 _98788 _98789 _98787) = (term647 _98788 _98789 _98787).
Proof. exact (MK_COMB (@lem7669062 _98787 _98788 _98789) (@lem7669060 _98788 _98789 _98787)). Qed.
Lemma lem7669064 (_98788 : int) (_98789 : int) : (term69 _98789 _98788) = (term109 _98788 _98789).
Proof. exact (@lem1988287 (real_of_int _98788) (term66 _98789)). Qed.
Lemma lem7669076 (_98788 : int) (_98789 : int) : (term110 _98788 _98789) = (term111 _98788 _98789).
Proof. exact (@lem1982792 (real_of_int _98788) (term66 _98789)). Qed.
Lemma lem7669077 (_98789 : int) : (term112 _98789) = (term113 _98789).
Proof. exact (@lem1982781 (real_of_int _98789) term88 term64). Qed.
Lemma lem7669079 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7669080 : term64 = term114.
Proof. exact (@lem7669079 term11). Qed.
Lemma lem7669082 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7669083 : term88 = term89.
Proof. exact (@lem7669082 term11). Qed.
Lemma lem7669084 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7669085 : term90 = term91.
Proof. exact (MK_COMB (@lem7669084) (@lem7669083)). Qed.
Lemma lem7669086 : term115 = term116.
Proof. exact (MK_COMB (@lem7669085) (@lem7669080)). Qed.
Lemma lem7669087 : term116 = term117.
Proof. exact (@lem1981613 term88 term64 term64 term64). Qed.
Lemma lem7669089 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7669090 : term97 = term98.
Proof. exact (@lem7669089 term11 term11). Qed.
Lemma lem7669091 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7669092 : term100 = term11.
Proof. exact (EQ_MP (@lem7669091) (@lem940073)). Qed.
Lemma lem7669093 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7669094 : term98 = term64.
Proof. exact (MK_COMB (@lem7669093) (@lem7669092)). Qed.
Lemma lem7669095 : term97 = term64.
Proof. exact (TRANS (@lem7669090) (@lem7669094)). Qed.
Lemma lem7669097 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7669098 : term115 = term120.
Proof. exact (@lem7669097 term11 term11). Qed.
Lemma lem7669099 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7669100 : term100 = term11.
Proof. exact (EQ_MP (@lem7669099) (@lem940073)). Qed.
Lemma lem7669101 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7669102 : term98 = term64.
Proof. exact (MK_COMB (@lem7669101) (@lem7669100)). Qed.
Lemma lem7669103 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7669104 : term120 = term88.
Proof. exact (MK_COMB (@lem7669103) (@lem7669102)). Qed.
Lemma lem7669105 : term115 = term88.
Proof. exact (TRANS (@lem7669098) (@lem7669104)). Qed.
Lemma lem7669106 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7669107 : term121 = term122.
Proof. exact (MK_COMB (@lem7669106) (@lem7669105)). Qed.
Lemma lem7669108 : term117 = term89.
Proof. exact (MK_COMB (@lem7669107) (@lem7669095)). Qed.
Lemma lem7669109 : term116 = term89.
Proof. exact (TRANS (@lem7669087) (@lem7669108)). Qed.
Lemma lem7669110 : term115 = term89.
Proof. exact (TRANS (@lem7669086) (@lem7669109)). Qed.
Lemma lem7669112 (x : real) : (term104 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7669113 : term89 = term88.
Proof. exact (@lem7669112 term88). Qed.
Lemma lem7669114 : term115 = term88.
Proof. exact (TRANS (@lem7669110) (@lem7669113)). Qed.
Lemma lem7669117 (_98789 : int) : (term123 _98789) = (term123 _98789).
Proof. exact (eq_refl (term123 _98789)). Qed.
Lemma lem7669118 (_98789 : int) : (term113 _98789) = (term124 _98789).
Proof. exact (MK_COMB (@lem7669117 _98789) (@lem7669114)). Qed.
Lemma lem7669119 (_98789 : int) : (term112 _98789) = (term124 _98789).
Proof. exact (TRANS (@lem7669077 _98789) (@lem7669118 _98789)). Qed.
Lemma lem7669120 (_98788 : int) : (term65 _98788) = (term65 _98788).
Proof. exact (eq_refl (term65 _98788)). Qed.
Lemma lem7669123 (_98788 : int) (_98789 : int) : (term111 _98788 _98789) = (term125 _98788 _98789).
Proof. exact (MK_COMB (@lem7669120 _98788) (@lem7669119 _98789)). Qed.
Lemma lem7669125 (_98788 : int) (_98789 : int) : (term110 _98788 _98789) = (term125 _98788 _98789).
Proof. exact (TRANS (@lem7669076 _98788 _98789) (@lem7669123 _98788 _98789)). Qed.
Lemma lem7669126 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7669127 (_98788 : int) (_98789 : int) : (term126 _98788 _98789) = (term127 _98788 _98789).
Proof. exact (MK_COMB (@lem7669126) (@lem7669125 _98788 _98789)). Qed.
Lemma lem7669128 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7669129 (_98788 : int) (_98789 : int) : (term109 _98788 _98789) = (term128 _98788 _98789).
Proof. exact (MK_COMB (@lem7669127 _98788 _98789) (@lem7669128)). Qed.
Lemma lem7669130 (_98788 : int) (_98789 : int) : (term69 _98789 _98788) = (term128 _98788 _98789).
Proof. exact (TRANS (@lem7669064 _98788 _98789) (@lem7669129 _98788 _98789)). Qed.
Lemma lem7669131 (_98789 : int) (_98790 : int) (_98788 : int) : (term620 _98788 _98789 _98790) = (term648 _98789 _98790 _98788).
Proof. exact (@lem1988287 (term59 _98789 _98790) (real_of_int _98788)). Qed.
Lemma lem7669143 (_98789 : int) (_98790 : int) (_98788 : int) : (term649 _98789 _98790 _98788) = (term650 _98789 _98790 _98788).
Proof. exact (@lem1982792 (term59 _98789 _98790) (real_of_int _98788)). Qed.
Lemma lem7669148 (_98788 : int) (_98789 : int) (_98790 : int) : (term650 _98789 _98790 _98788) = (term651 _98788 _98789 _98790).
Proof. exact (@lem1982761 (term135 _98788) (term59 _98789 _98790)). Qed.
Lemma lem7669150 (_98788 : int) (_98789 : int) (_98790 : int) : (term649 _98789 _98790 _98788) = (term651 _98788 _98789 _98790).
Proof. exact (TRANS (@lem7669143 _98789 _98790 _98788) (@lem7669148 _98788 _98789 _98790)). Qed.
Lemma lem7669151 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7669152 (_98788 : int) (_98789 : int) (_98790 : int) : (term652 _98789 _98790 _98788) = (term653 _98788 _98789 _98790).
Proof. exact (MK_COMB (@lem7669151) (@lem7669150 _98788 _98789 _98790)). Qed.
Lemma lem7669153 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7669154 (_98788 : int) (_98789 : int) (_98790 : int) : (term648 _98789 _98790 _98788) = (term654 _98788 _98789 _98790).
Proof. exact (MK_COMB (@lem7669152 _98788 _98789 _98790) (@lem7669153)). Qed.
Lemma lem7669155 (_98788 : int) (_98789 : int) (_98790 : int) : (term620 _98788 _98789 _98790) = (term654 _98788 _98789 _98790).
Proof. exact (TRANS (@lem7669131 _98789 _98790 _98788) (@lem7669154 _98788 _98789 _98790)). Qed.
Lemma lem7669156 (_98789 : int) (_98788 : int) : (term47 _98788 _98789) = (term414 _98789 _98788).
Proof. exact (@lem1988287 (real_of_int _98789) (real_of_int _98788)). Qed.
Lemma lem7669162 (_98789 : int) (_98788 : int) : (term415 _98789 _98788) = (term416 _98789 _98788).
Proof. exact (@lem1982792 (real_of_int _98789) (real_of_int _98788)). Qed.
Lemma lem7669167 (_98788 : int) (_98789 : int) : (term416 _98789 _98788) = (term417 _98788 _98789).
Proof. exact (@lem1982761 (term135 _98788) (real_of_int _98789)). Qed.
Lemma lem7669169 (_98788 : int) (_98789 : int) : (term415 _98789 _98788) = (term417 _98788 _98789).
Proof. exact (TRANS (@lem7669162 _98789 _98788) (@lem7669167 _98788 _98789)). Qed.
Lemma lem7669170 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7669171 (_98788 : int) (_98789 : int) : (term418 _98789 _98788) = (term419 _98788 _98789).
Proof. exact (MK_COMB (@lem7669170) (@lem7669169 _98788 _98789)). Qed.
Lemma lem7669172 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7669173 (_98788 : int) (_98789 : int) : (term414 _98789 _98788) = (term420 _98788 _98789).
Proof. exact (MK_COMB (@lem7669171 _98788 _98789) (@lem7669172)). Qed.
Lemma lem7669174 (_98788 : int) (_98789 : int) : (term47 _98788 _98789) = (term420 _98788 _98789).
Proof. exact (TRANS (@lem7669156 _98789 _98788) (@lem7669173 _98788 _98789)). Qed.
Lemma lem7669175 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term577 A M N u i v d) = (term577 A M N u i v d).
Proof. exact (eq_refl (term577 A M N u i v d)). Qed.
Lemma lem7669176 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7669177 (_98788 : int) (_98789 : int) : (term402 _98788 _98789) = (term434 _98788 _98789).
Proof. exact (MK_COMB (@lem7669176) (@lem7669174 _98788 _98789)). Qed.
Lemma lem7669178 {A M N : Type'} (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term621 A M N _98788 _98789 u i v d) = (term655 A M N _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7669177 _98788 _98789) (@lem7669175 A M N u i v d)). Qed.
Lemma lem7669179 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7669180 (_98788 : int) (_98789 : int) (_98790 : int) : (term622 _98788 _98789 _98790) = (term656 _98788 _98789 _98790).
Proof. exact (MK_COMB (@lem7669179) (@lem7669155 _98788 _98789 _98790)). Qed.
Lemma lem7669181 {A M N : Type'} (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term623 A M N _98790 _98788 _98789 u i v d) = (term657 A M N _98790 _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7669180 _98788 _98789 _98790) (@lem7669178 A M N _98788 _98789 u i v d)). Qed.
Lemma lem7669182 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7669183 (_98788 : int) (_98789 : int) : (term74 _98789 _98788) = (term160 _98788 _98789).
Proof. exact (MK_COMB (@lem7669182) (@lem7669130 _98788 _98789)). Qed.
Lemma lem7669184 {A M N : Type'} (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term624 A M N _98790 _98788 _98789 u i v d) = (term658 A M N _98790 _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7669183 _98788 _98789) (@lem7669181 A M N _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7669185 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7669186 (_98788 : int) (_98789 : int) (_98787 : int) : (term625 _98788 _98789 _98787) = (term659 _98788 _98789 _98787).
Proof. exact (MK_COMB (@lem7669185) (@lem7669063 _98788 _98789 _98787)). Qed.
Lemma lem7669187 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term626 A M N _98787 _98790 _98788 _98789 u i v d) = (term660 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7669186 _98788 _98789 _98787) (@lem7669184 A M N _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7669188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7669189 (_98790 : int) : (term76 _98790) = (term162 _98790).
Proof. exact (MK_COMB (@lem7669188) (@lem7668903 _98790)). Qed.
Lemma lem7669190 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term627 A M N _98787 _98790 _98788 _98789 u i v d) = (term661 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7669189 _98790) (@lem7669187 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7669191 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7669192 (_98789 : int) : (term76 _98789) = (term162 _98789).
Proof. exact (MK_COMB (@lem7669191) (@lem7668855 _98789)). Qed.
Lemma lem7669193 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term628 A M N _98787 _98790 _98788 _98789 u i v d) = (term662 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7669192 _98789) (@lem7669190 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7669194 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7669195 (_98788 : int) : (term76 _98788) = (term162 _98788).
Proof. exact (MK_COMB (@lem7669194) (@lem7668807 _98788)). Qed.
Lemma lem7669196 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term629 A M N _98787 _98790 _98788 _98789 u i v d) = (term663 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7669195 _98788) (@lem7669193 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7669197 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7669198 (_98787 : int) : (term76 _98787) = (term162 _98787).
Proof. exact (MK_COMB (@lem7669197) (@lem7668759 _98787)). Qed.
Lemma lem7669199 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term630 A M N _98787 _98790 _98788 _98789 u i v d) = (term664 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7669198 _98787) (@lem7669196 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7669206 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term631 A M N _98787 _98790 _98788 _98789 u i v d) = (term664 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (TRANS (@lem7668711 A M N _98787 _98790 _98788 _98789 u i v d) (@lem7669199 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7669247 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term660 A M N _98787 _98790 _98788 _98789 u i v d) = (term665 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (@lem19367 ((term637 _98787 _98788 _98789) = term52) (term645 _98788 _98789 _98787) (term658 A M N _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7669250 (_98790 : int) : (term162 _98790) = (term162 _98790).
Proof. exact (eq_refl (term162 _98790)). Qed.
Lemma lem7669251 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term661 A M N _98787 _98790 _98788 _98789 u i v d) = (term666 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7669250 _98790) (@lem7669247 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7669258 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term666 A M N _98787 _98790 _98788 _98789 u i v d) = (term667 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (@lem19158 (term668 A M N _98787 _98790 _98788 _98789 u i v d) (term108 _98790) (term669 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7669259 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term661 A M N _98787 _98790 _98788 _98789 u i v d) = (term667 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (TRANS (@lem7669251 A M N _98787 _98790 _98788 _98789 u i v d) (@lem7669258 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7669262 (_98789 : int) : (term162 _98789) = (term162 _98789).
Proof. exact (eq_refl (term162 _98789)). Qed.
Lemma lem7669263 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term662 A M N _98787 _98790 _98788 _98789 u i v d) = (term670 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7669262 _98789) (@lem7669259 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7669270 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term670 A M N _98787 _98790 _98788 _98789 u i v d) = (term671 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (@lem19158 (term672 A M N _98787 _98790 _98788 _98789 u i v d) (term108 _98789) (term673 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7669271 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term662 A M N _98787 _98790 _98788 _98789 u i v d) = (term671 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (TRANS (@lem7669263 A M N _98787 _98790 _98788 _98789 u i v d) (@lem7669270 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7669274 (_98788 : int) : (term162 _98788) = (term162 _98788).
Proof. exact (eq_refl (term162 _98788)). Qed.
Lemma lem7669275 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term663 A M N _98787 _98790 _98788 _98789 u i v d) = (term674 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7669274 _98788) (@lem7669271 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7669282 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term674 A M N _98787 _98790 _98788 _98789 u i v d) = (term675 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (@lem19158 (term676 A M N _98787 _98790 _98788 _98789 u i v d) (term108 _98788) (term677 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7669283 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term663 A M N _98787 _98790 _98788 _98789 u i v d) = (term675 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (TRANS (@lem7669275 A M N _98787 _98790 _98788 _98789 u i v d) (@lem7669282 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7669286 (_98787 : int) : (term162 _98787) = (term162 _98787).
Proof. exact (eq_refl (term162 _98787)). Qed.
Lemma lem7669287 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term664 A M N _98787 _98790 _98788 _98789 u i v d) = (term678 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7669286 _98787) (@lem7669283 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7669294 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term678 A M N _98787 _98790 _98788 _98789 u i v d) = (term679 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (@lem19158 (term680 A M N _98787 _98790 _98788 _98789 u i v d) (term108 _98787) (term681 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7669295 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term664 A M N _98787 _98790 _98788 _98789 u i v d) = (term679 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (TRANS (@lem7669287 A M N _98787 _98790 _98788 _98789 u i v d) (@lem7669294 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7669296 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term631 A M N _98787 _98790 _98788 _98789 u i v d) = (term679 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (TRANS (@lem7669206 A M N _98787 _98790 _98788 _98789 u i v d) (@lem7669295 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7669306 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term679 A M N _98787 _98790 _98788 _98789 u i v d) : term679 A M N _98787 _98790 _98788 _98789 u i v d.
Proof. exact (h1). Qed.
Lemma lem7669307 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term682 A M N _98787 _98790 _98788 _98789 u i v d) : term682 A M N _98787 _98790 _98788 _98789 u i v d.
Proof. exact (h1). Qed.
Lemma lem7669308 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term682 A M N _98787 _98790 _98788 _98789 u i v d) : term680 A M N _98787 _98790 _98788 _98789 u i v d.
Proof. exact (proj2 (@lem7669307 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669310 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term682 A M N _98787 _98790 _98788 _98789 u i v d) : term676 A M N _98787 _98790 _98788 _98789 u i v d.
Proof. exact (proj2 (@lem7669308 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669312 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term682 A M N _98787 _98790 _98788 _98789 u i v d) : term672 A M N _98787 _98790 _98788 _98789 u i v d.
Proof. exact (proj2 (@lem7669310 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669314 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term682 A M N _98787 _98790 _98788 _98789 u i v d) : term668 A M N _98787 _98790 _98788 _98789 u i v d.
Proof. exact (proj2 (@lem7669312 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669316 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term682 A M N _98787 _98790 _98788 _98789 u i v d) : term658 A M N _98790 _98788 _98789 u i v d.
Proof. exact (proj2 (@lem7669314 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669318 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term682 A M N _98787 _98790 _98788 _98789 u i v d) : term657 A M N _98790 _98788 _98789 u i v d.
Proof. exact (proj2 (@lem7669316 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669319 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term682 A M N _98787 _98790 _98788 _98789 u i v d) : term128 _98788 _98789.
Proof. exact (proj1 (@lem7669316 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669320 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term682 A M N _98787 _98790 _98788 _98789 u i v d) : term655 A M N _98788 _98789 u i v d.
Proof. exact (proj2 (@lem7669318 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669323 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term682 A M N _98787 _98790 _98788 _98789 u i v d) : term420 _98788 _98789.
Proof. exact (proj1 (@lem7669320 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669325 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7669326 : term165 = term141.
Proof. exact (@lem7669325 term52 term64). Qed.
Lemma lem7669328 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7669329 : term64 = term114.
Proof. exact (@lem7669328 term11). Qed.
Lemma lem7669331 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7669332 : term52 = term85.
Proof. exact (@lem7669331 (NUMERAL 0)). Qed.
Lemma lem7669333 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7669334 : term166 = term167.
Proof. exact (MK_COMB (@lem7669333) (@lem7669332)). Qed.
Lemma lem7669335 : term141 = term168.
Proof. exact (MK_COMB (@lem7669334) (@lem7669329)). Qed.
Lemma lem7669336 : term169.
Proof. exact (@lem1980255 term52 term64 term64 term64). Qed.
Lemma lem7669338 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7669339 : term141 = term142.
Proof. exact (@lem7669338 (NUMERAL 0) term11). Qed.
Lemma lem7669340 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7669341 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7669342 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7669341 h1) (fun h1 : term142 = True => @lem7669340)). Qed.
Lemma lem7669343 : term142 = True.
Proof. exact (EQ_MP (@lem7669342) (@lem7669340)). Qed.
Lemma lem7669344 : term141 = True.
Proof. exact (TRANS (@lem7669339) (@lem7669343)). Qed.
Lemma lem7669345 : True = term141.
Proof. exact (SYM (@lem7669344)). Qed.
Lemma lem7669346 : term141.
Proof. exact (EQ_MP (@lem7669345) (@lem0)). Qed.
Lemma lem7669347 : term170.
Proof. exact (@lem7669336 (@lem7669346)). Qed.
Lemma lem7669349 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7669350 : term141 = term142.
Proof. exact (@lem7669349 (NUMERAL 0) term11). Qed.
Lemma lem7669351 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7669352 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7669353 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7669352 h1) (fun h1 : term142 = True => @lem7669351)). Qed.
Lemma lem7669354 : term142 = True.
Proof. exact (EQ_MP (@lem7669353) (@lem7669351)). Qed.
Lemma lem7669355 : term141 = True.
Proof. exact (TRANS (@lem7669350) (@lem7669354)). Qed.
Lemma lem7669356 : True = term141.
Proof. exact (SYM (@lem7669355)). Qed.
Lemma lem7669357 : term141.
Proof. exact (EQ_MP (@lem7669356) (@lem0)). Qed.
Lemma lem7669358 : term168 = term171.
Proof. exact (@lem7669347 (@lem7669357)). Qed.
Lemma lem7669360 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7669361 : term97 = term98.
Proof. exact (@lem7669360 term11 term11). Qed.
Lemma lem7669362 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7669363 : term100 = term11.
Proof. exact (EQ_MP (@lem7669362) (@lem940073)). Qed.
Lemma lem7669364 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7669365 : term98 = term64.
Proof. exact (MK_COMB (@lem7669364) (@lem7669363)). Qed.
Lemma lem7669366 : term97 = term64.
Proof. exact (TRANS (@lem7669361) (@lem7669365)). Qed.
Lemma lem7669368 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7669369 : term153 = term52.
Proof. exact (@lem7669368 term11). Qed.
Lemma lem7669370 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7669371 : term172 = term166.
Proof. exact (MK_COMB (@lem7669370) (@lem7669369)). Qed.
Lemma lem7669372 : term171 = term141.
Proof. exact (MK_COMB (@lem7669371) (@lem7669366)). Qed.
Lemma lem7669374 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7669375 : term141 = term142.
Proof. exact (@lem7669374 (NUMERAL 0) term11). Qed.
Lemma lem7669376 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7669377 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7669378 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7669377 h1) (fun h1 : term142 = True => @lem7669376)). Qed.
Lemma lem7669379 : term142 = True.
Proof. exact (EQ_MP (@lem7669378) (@lem7669376)). Qed.
Lemma lem7669380 : term141 = True.
Proof. exact (TRANS (@lem7669375) (@lem7669379)). Qed.
Lemma lem7669381 : term171 = True.
Proof. exact (TRANS (@lem7669372) (@lem7669380)). Qed.
Lemma lem7669382 : term168 = True.
Proof. exact (TRANS (@lem7669358) (@lem7669381)). Qed.
Lemma lem7669383 : term141 = True.
Proof. exact (TRANS (@lem7669335) (@lem7669382)). Qed.
Lemma lem7669384 : term165 = True.
Proof. exact (TRANS (@lem7669326) (@lem7669383)). Qed.
Lemma lem7669385 : True = term165.
Proof. exact (SYM (@lem7669384)). Qed.
Lemma lem7669386 : term165.
Proof. exact (EQ_MP (@lem7669385) (@lem0)). Qed.
Lemma lem7669387 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term682 A M N _98787 _98790 _98788 _98789 u i v d) : term179 _98788 _98789.
Proof. exact (conj (@lem7669386) (@lem7669319 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669389 (x : real) (y : real) : term174 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7669390 (_98788 : int) (_98789 : int) : term180 _98788 _98789.
Proof. exact (@lem7669389 term64 (term125 _98788 _98789)). Qed.
Lemma lem7669391 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term682 A M N _98787 _98790 _98788 _98789 u i v d) : term181 _98788 _98789.
Proof. exact (@lem7669390 _98788 _98789 (@lem7669387 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669392 (_98788 : int) (_98789 : int) : (term182 _98788 _98789) = (term125 _98788 _98789).
Proof. exact (@lem1982733 (term125 _98788 _98789)). Qed.
Lemma lem7669393 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7669394 (_98788 : int) (_98789 : int) : (term183 _98788 _98789) = (term127 _98788 _98789).
Proof. exact (MK_COMB (@lem7669393) (@lem7669392 _98788 _98789)). Qed.
Lemma lem7669395 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7669396 (_98788 : int) (_98789 : int) : (term181 _98788 _98789) = (term128 _98788 _98789).
Proof. exact (MK_COMB (@lem7669394 _98788 _98789) (@lem7669395)). Qed.
Lemma lem7669397 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term682 A M N _98787 _98790 _98788 _98789 u i v d) : term128 _98788 _98789.
Proof. exact (EQ_MP (@lem7669396 _98788 _98789) (@lem7669391 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669399 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7669400 : term165 = term141.
Proof. exact (@lem7669399 term52 term64). Qed.
Lemma lem7669402 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7669403 : term64 = term114.
Proof. exact (@lem7669402 term11). Qed.
Lemma lem7669405 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7669406 : term52 = term85.
Proof. exact (@lem7669405 (NUMERAL 0)). Qed.
Lemma lem7669407 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7669408 : term166 = term167.
Proof. exact (MK_COMB (@lem7669407) (@lem7669406)). Qed.
Lemma lem7669409 : term141 = term168.
Proof. exact (MK_COMB (@lem7669408) (@lem7669403)). Qed.
Lemma lem7669410 : term169.
Proof. exact (@lem1980255 term52 term64 term64 term64). Qed.
Lemma lem7669412 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7669413 : term141 = term142.
Proof. exact (@lem7669412 (NUMERAL 0) term11). Qed.
Lemma lem7669414 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7669415 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7669416 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7669415 h1) (fun h1 : term142 = True => @lem7669414)). Qed.
Lemma lem7669417 : term142 = True.
Proof. exact (EQ_MP (@lem7669416) (@lem7669414)). Qed.
Lemma lem7669418 : term141 = True.
Proof. exact (TRANS (@lem7669413) (@lem7669417)). Qed.
Lemma lem7669419 : True = term141.
Proof. exact (SYM (@lem7669418)). Qed.
Lemma lem7669420 : term141.
Proof. exact (EQ_MP (@lem7669419) (@lem0)). Qed.
Lemma lem7669421 : term170.
Proof. exact (@lem7669410 (@lem7669420)). Qed.
Lemma lem7669423 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7669424 : term141 = term142.
Proof. exact (@lem7669423 (NUMERAL 0) term11). Qed.
Lemma lem7669425 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7669426 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7669427 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7669426 h1) (fun h1 : term142 = True => @lem7669425)). Qed.
Lemma lem7669428 : term142 = True.
Proof. exact (EQ_MP (@lem7669427) (@lem7669425)). Qed.
Lemma lem7669429 : term141 = True.
Proof. exact (TRANS (@lem7669424) (@lem7669428)). Qed.
Lemma lem7669430 : True = term141.
Proof. exact (SYM (@lem7669429)). Qed.
Lemma lem7669431 : term141.
Proof. exact (EQ_MP (@lem7669430) (@lem0)). Qed.
Lemma lem7669432 : term168 = term171.
Proof. exact (@lem7669421 (@lem7669431)). Qed.
Lemma lem7669434 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7669435 : term97 = term98.
Proof. exact (@lem7669434 term11 term11). Qed.
Lemma lem7669436 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7669437 : term100 = term11.
Proof. exact (EQ_MP (@lem7669436) (@lem940073)). Qed.
Lemma lem7669438 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7669439 : term98 = term64.
Proof. exact (MK_COMB (@lem7669438) (@lem7669437)). Qed.
Lemma lem7669440 : term97 = term64.
Proof. exact (TRANS (@lem7669435) (@lem7669439)). Qed.
Lemma lem7669442 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7669443 : term153 = term52.
Proof. exact (@lem7669442 term11). Qed.
Lemma lem7669444 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7669445 : term172 = term166.
Proof. exact (MK_COMB (@lem7669444) (@lem7669443)). Qed.
Lemma lem7669446 : term171 = term141.
Proof. exact (MK_COMB (@lem7669445) (@lem7669440)). Qed.
Lemma lem7669448 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7669449 : term141 = term142.
Proof. exact (@lem7669448 (NUMERAL 0) term11). Qed.
Lemma lem7669450 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7669451 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7669452 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7669451 h1) (fun h1 : term142 = True => @lem7669450)). Qed.
Lemma lem7669453 : term142 = True.
Proof. exact (EQ_MP (@lem7669452) (@lem7669450)). Qed.
Lemma lem7669454 : term141 = True.
Proof. exact (TRANS (@lem7669449) (@lem7669453)). Qed.
Lemma lem7669455 : term171 = True.
Proof. exact (TRANS (@lem7669446) (@lem7669454)). Qed.
Lemma lem7669456 : term168 = True.
Proof. exact (TRANS (@lem7669432) (@lem7669455)). Qed.
Lemma lem7669457 : term141 = True.
Proof. exact (TRANS (@lem7669409) (@lem7669456)). Qed.
Lemma lem7669458 : term165 = True.
Proof. exact (TRANS (@lem7669400) (@lem7669457)). Qed.
Lemma lem7669459 : True = term165.
Proof. exact (SYM (@lem7669458)). Qed.
Lemma lem7669460 : term165.
Proof. exact (EQ_MP (@lem7669459) (@lem0)). Qed.
Lemma lem7669461 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term682 A M N _98787 _98790 _98788 _98789 u i v d) : term441 _98788 _98789.
Proof. exact (conj (@lem7669460) (@lem7669323 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669463 (x : real) (y : real) : term174 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7669464 (_98788 : int) (_98789 : int) : term442 _98788 _98789.
Proof. exact (@lem7669463 term64 (term417 _98788 _98789)). Qed.
Lemma lem7669465 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term682 A M N _98787 _98790 _98788 _98789 u i v d) : term443 _98788 _98789.
Proof. exact (@lem7669464 _98788 _98789 (@lem7669461 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669466 (_98788 : int) (_98789 : int) : (term444 _98788 _98789) = (term417 _98788 _98789).
Proof. exact (@lem1982733 (term417 _98788 _98789)). Qed.
Lemma lem7669467 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7669468 (_98788 : int) (_98789 : int) : (term445 _98788 _98789) = (term419 _98788 _98789).
Proof. exact (MK_COMB (@lem7669467) (@lem7669466 _98788 _98789)). Qed.
Lemma lem7669469 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7669470 (_98788 : int) (_98789 : int) : (term443 _98788 _98789) = (term420 _98788 _98789).
Proof. exact (MK_COMB (@lem7669468 _98788 _98789) (@lem7669469)). Qed.
Lemma lem7669471 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term682 A M N _98787 _98790 _98788 _98789 u i v d) : term420 _98788 _98789.
Proof. exact (EQ_MP (@lem7669470 _98788 _98789) (@lem7669465 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669472 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term682 A M N _98787 _98790 _98788 _98789 u i v d) : term683 _98788 _98789.
Proof. exact (conj (@lem7669471 A M N _98787 _98790 _98788 _98789 u i v d h1) (@lem7669397 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669474 (x : real) (y : real) : term185 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7669475 (_98788 : int) (_98789 : int) : term684 _98788 _98789.
Proof. exact (@lem7669474 (term417 _98788 _98789) (term125 _98788 _98789)). Qed.
Lemma lem7669476 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term682 A M N _98787 _98790 _98788 _98789 u i v d) : term685 _98788 _98789.
Proof. exact (@lem7669475 _98788 _98789 (@lem7669472 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669477 (_98788 : int) (_98789 : int) : (term686 _98788 _98789) = (term687 _98788 _98789).
Proof. exact (@lem1982753 (term135 _98788) (real_of_int _98788) (real_of_int _98789) (term124 _98789)). Qed.
Lemma lem7669478 (_98788 : int) : (term192 _98788) = (term193 _98788).
Proof. exact (@lem1982713 term88 (real_of_int _98788)). Qed.
Lemma lem7669480 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7669481 : term64 = term114.
Proof. exact (@lem7669480 term11). Qed.
Lemma lem7669483 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7669484 : term88 = term89.
Proof. exact (@lem7669483 term11). Qed.
Lemma lem7669485 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7669486 : term194 = term195.
Proof. exact (MK_COMB (@lem7669485) (@lem7669484)). Qed.
Lemma lem7669487 : term196 = term197.
Proof. exact (MK_COMB (@lem7669486) (@lem7669481)). Qed.
Lemma lem7669488 : term198.
Proof. exact (@lem1981473 term88 term64 term64 term64 term52 term64). Qed.
Lemma lem7669490 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7669491 : term141 = term142.
Proof. exact (@lem7669490 (NUMERAL 0) term11). Qed.
Lemma lem7669492 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7669493 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7669494 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7669493 h1) (fun h1 : term142 = True => @lem7669492)). Qed.
Lemma lem7669495 : term142 = True.
Proof. exact (EQ_MP (@lem7669494) (@lem7669492)). Qed.
Lemma lem7669496 : term141 = True.
Proof. exact (TRANS (@lem7669491) (@lem7669495)). Qed.
Lemma lem7669497 : True = term141.
Proof. exact (SYM (@lem7669496)). Qed.
Lemma lem7669498 : term141.
Proof. exact (EQ_MP (@lem7669497) (@lem0)). Qed.
Lemma lem7669499 : term199.
Proof. exact (@lem7669488 (@lem7669498)). Qed.
Lemma lem7669501 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7669502 : term141 = term142.
Proof. exact (@lem7669501 (NUMERAL 0) term11). Qed.
Lemma lem7669503 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7669504 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7669505 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7669504 h1) (fun h1 : term142 = True => @lem7669503)). Qed.
Lemma lem7669506 : term142 = True.
Proof. exact (EQ_MP (@lem7669505) (@lem7669503)). Qed.
Lemma lem7669507 : term141 = True.
Proof. exact (TRANS (@lem7669502) (@lem7669506)). Qed.
Lemma lem7669508 : True = term141.
Proof. exact (SYM (@lem7669507)). Qed.
Lemma lem7669509 : term141.
Proof. exact (EQ_MP (@lem7669508) (@lem0)). Qed.
Lemma lem7669510 : term200.
Proof. exact (@lem7669499 (@lem7669509)). Qed.
Lemma lem7669512 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7669513 : term141 = term142.
Proof. exact (@lem7669512 (NUMERAL 0) term11). Qed.
Lemma lem7669514 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7669515 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7669516 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7669515 h1) (fun h1 : term142 = True => @lem7669514)). Qed.
Lemma lem7669517 : term142 = True.
Proof. exact (EQ_MP (@lem7669516) (@lem7669514)). Qed.
Lemma lem7669518 : term141 = True.
Proof. exact (TRANS (@lem7669513) (@lem7669517)). Qed.
Lemma lem7669519 : True = term141.
Proof. exact (SYM (@lem7669518)). Qed.
Lemma lem7669520 : term141.
Proof. exact (EQ_MP (@lem7669519) (@lem0)). Qed.
Lemma lem7669521 : term201.
Proof. exact (@lem7669510 (@lem7669520)). Qed.
Lemma lem7669523 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7669524 : term97 = term98.
Proof. exact (@lem7669523 term11 term11). Qed.
Lemma lem7669525 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7669526 : term100 = term11.
Proof. exact (EQ_MP (@lem7669525) (@lem940073)). Qed.
Lemma lem7669527 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7669528 : term98 = term64.
Proof. exact (MK_COMB (@lem7669527) (@lem7669526)). Qed.
Lemma lem7669529 : term97 = term64.
Proof. exact (TRANS (@lem7669524) (@lem7669528)). Qed.
Lemma lem7669531 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7669532 : term115 = term120.
Proof. exact (@lem7669531 term11 term11). Qed.
Lemma lem7669533 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7669534 : term100 = term11.
Proof. exact (EQ_MP (@lem7669533) (@lem940073)). Qed.
Lemma lem7669535 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7669536 : term98 = term64.
Proof. exact (MK_COMB (@lem7669535) (@lem7669534)). Qed.
Lemma lem7669537 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7669538 : term120 = term88.
Proof. exact (MK_COMB (@lem7669537) (@lem7669536)). Qed.
Lemma lem7669539 : term115 = term88.
Proof. exact (TRANS (@lem7669532) (@lem7669538)). Qed.
Lemma lem7669540 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7669541 : term202 = term194.
Proof. exact (MK_COMB (@lem7669540) (@lem7669539)). Qed.
Lemma lem7669542 : term203 = term196.
Proof. exact (MK_COMB (@lem7669541) (@lem7669529)). Qed.
Lemma lem7669544 (m : nat) : (term204 m) = term52.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7669545 : term196 = term52.
Proof. exact (@lem7669544 term11). Qed.
Lemma lem7669546 : term203 = term52.
Proof. exact (TRANS (@lem7669542) (@lem7669545)). Qed.
Lemma lem7669547 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7669548 : term205 = term151.
Proof. exact (MK_COMB (@lem7669547) (@lem7669546)). Qed.
Lemma lem7669549 : term64 = term64.
Proof. exact (eq_refl term64). Qed.
Lemma lem7669550 : term206 = term153.
Proof. exact (MK_COMB (@lem7669548) (@lem7669549)). Qed.
Lemma lem7669552 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7669553 : term153 = term52.
Proof. exact (@lem7669552 term11). Qed.
Lemma lem7669554 : term206 = term52.
Proof. exact (TRANS (@lem7669550) (@lem7669553)). Qed.
Lemma lem7669556 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7669557 : term97 = term98.
Proof. exact (@lem7669556 term11 term11). Qed.
Lemma lem7669558 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7669559 : term100 = term11.
Proof. exact (EQ_MP (@lem7669558) (@lem940073)). Qed.
Lemma lem7669560 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7669561 : term98 = term64.
Proof. exact (MK_COMB (@lem7669560) (@lem7669559)). Qed.
Lemma lem7669562 : term97 = term64.
Proof. exact (TRANS (@lem7669557) (@lem7669561)). Qed.
Lemma lem7669563 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem7669564 : term155 = term153.
Proof. exact (MK_COMB (@lem7669563) (@lem7669562)). Qed.
Lemma lem7669566 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7669567 : term153 = term52.
Proof. exact (@lem7669566 term11). Qed.
Lemma lem7669568 : term155 = term52.
Proof. exact (TRANS (@lem7669564) (@lem7669567)). Qed.
Lemma lem7669569 : term52 = term155.
Proof. exact (SYM (@lem7669568)). Qed.
Lemma lem7669570 : term206 = term155.
Proof. exact (TRANS (@lem7669554) (@lem7669569)). Qed.
Lemma lem7669571 : term197 = term85.
Proof. exact (@lem7669521 (@lem7669570)). Qed.
Lemma lem7669572 : term196 = term85.
Proof. exact (TRANS (@lem7669487) (@lem7669571)). Qed.
Lemma lem7669574 (x : real) : (term104 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7669575 : term85 = term52.
Proof. exact (@lem7669574 term52). Qed.
Lemma lem7669576 : term196 = term52.
Proof. exact (TRANS (@lem7669572) (@lem7669575)). Qed.
Lemma lem7669577 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7669578 : term207 = term151.
Proof. exact (MK_COMB (@lem7669577) (@lem7669576)). Qed.
Lemma lem7669579 (_98788 : int) : (real_of_int _98788) = (real_of_int _98788).
Proof. exact (eq_refl (real_of_int _98788)). Qed.
Lemma lem7669580 (_98788 : int) : (term193 _98788) = (term208 _98788).
Proof. exact (MK_COMB (@lem7669578) (@lem7669579 _98788)). Qed.
Lemma lem7669581 (_98788 : int) : (term192 _98788) = (term208 _98788).
Proof. exact (TRANS (@lem7669478 _98788) (@lem7669580 _98788)). Qed.
Lemma lem7669582 (_98788 : int) : (term208 _98788) = term52.
Proof. exact (@lem1982719 (real_of_int _98788)). Qed.
Lemma lem7669583 (_98788 : int) : (term192 _98788) = term52.
Proof. exact (TRANS (@lem7669581 _98788) (@lem7669582 _98788)). Qed.
Lemma lem7669584 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7669585 (_98788 : int) : (term209 _98788) = term210.
Proof. exact (MK_COMB (@lem7669584) (@lem7669583 _98788)). Qed.
Lemma lem7669586 (_98789 : int) : (term688 _98789) = (term689 _98789).
Proof. exact (@lem1982763 (real_of_int _98789) (term135 _98789) term88). Qed.
Lemma lem7669587 (_98789 : int) : (term464 _98789) = (term193 _98789).
Proof. exact (@lem1982715 term88 (real_of_int _98789)). Qed.
Lemma lem7669589 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7669590 : term64 = term114.
Proof. exact (@lem7669589 term11). Qed.
Lemma lem7669592 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7669593 : term88 = term89.
Proof. exact (@lem7669592 term11). Qed.
Lemma lem7669594 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7669595 : term194 = term195.
Proof. exact (MK_COMB (@lem7669594) (@lem7669593)). Qed.
Lemma lem7669596 : term196 = term197.
Proof. exact (MK_COMB (@lem7669595) (@lem7669590)). Qed.
Lemma lem7669597 : term198.
Proof. exact (@lem1981473 term88 term64 term64 term64 term52 term64). Qed.
Lemma lem7669599 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7669600 : term141 = term142.
Proof. exact (@lem7669599 (NUMERAL 0) term11). Qed.
Lemma lem7669601 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7669602 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7669603 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7669602 h1) (fun h1 : term142 = True => @lem7669601)). Qed.
Lemma lem7669604 : term142 = True.
Proof. exact (EQ_MP (@lem7669603) (@lem7669601)). Qed.
Lemma lem7669605 : term141 = True.
Proof. exact (TRANS (@lem7669600) (@lem7669604)). Qed.
Lemma lem7669606 : True = term141.
Proof. exact (SYM (@lem7669605)). Qed.
Lemma lem7669607 : term141.
Proof. exact (EQ_MP (@lem7669606) (@lem0)). Qed.
Lemma lem7669608 : term199.
Proof. exact (@lem7669597 (@lem7669607)). Qed.
Lemma lem7669610 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7669611 : term141 = term142.
Proof. exact (@lem7669610 (NUMERAL 0) term11). Qed.
Lemma lem7669612 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7669613 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7669614 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7669613 h1) (fun h1 : term142 = True => @lem7669612)). Qed.
Lemma lem7669615 : term142 = True.
Proof. exact (EQ_MP (@lem7669614) (@lem7669612)). Qed.
Lemma lem7669616 : term141 = True.
Proof. exact (TRANS (@lem7669611) (@lem7669615)). Qed.
Lemma lem7669617 : True = term141.
Proof. exact (SYM (@lem7669616)). Qed.
Lemma lem7669618 : term141.
Proof. exact (EQ_MP (@lem7669617) (@lem0)). Qed.
Lemma lem7669619 : term200.
Proof. exact (@lem7669608 (@lem7669618)). Qed.
Lemma lem7669621 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7669622 : term141 = term142.
Proof. exact (@lem7669621 (NUMERAL 0) term11). Qed.
Lemma lem7669623 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7669624 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7669625 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7669624 h1) (fun h1 : term142 = True => @lem7669623)). Qed.
Lemma lem7669626 : term142 = True.
Proof. exact (EQ_MP (@lem7669625) (@lem7669623)). Qed.
Lemma lem7669627 : term141 = True.
Proof. exact (TRANS (@lem7669622) (@lem7669626)). Qed.
Lemma lem7669628 : True = term141.
Proof. exact (SYM (@lem7669627)). Qed.
Lemma lem7669629 : term141.
Proof. exact (EQ_MP (@lem7669628) (@lem0)). Qed.
Lemma lem7669630 : term201.
Proof. exact (@lem7669619 (@lem7669629)). Qed.
Lemma lem7669632 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7669633 : term97 = term98.
Proof. exact (@lem7669632 term11 term11). Qed.
Lemma lem7669634 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7669635 : term100 = term11.
Proof. exact (EQ_MP (@lem7669634) (@lem940073)). Qed.
Lemma lem7669636 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7669637 : term98 = term64.
Proof. exact (MK_COMB (@lem7669636) (@lem7669635)). Qed.
Lemma lem7669638 : term97 = term64.
Proof. exact (TRANS (@lem7669633) (@lem7669637)). Qed.
Lemma lem7669640 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7669641 : term115 = term120.
Proof. exact (@lem7669640 term11 term11). Qed.
Lemma lem7669642 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7669643 : term100 = term11.
Proof. exact (EQ_MP (@lem7669642) (@lem940073)). Qed.
Lemma lem7669644 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7669645 : term98 = term64.
Proof. exact (MK_COMB (@lem7669644) (@lem7669643)). Qed.
Lemma lem7669646 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7669647 : term120 = term88.
Proof. exact (MK_COMB (@lem7669646) (@lem7669645)). Qed.
Lemma lem7669648 : term115 = term88.
Proof. exact (TRANS (@lem7669641) (@lem7669647)). Qed.
Lemma lem7669649 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7669650 : term202 = term194.
Proof. exact (MK_COMB (@lem7669649) (@lem7669648)). Qed.
Lemma lem7669651 : term203 = term196.
Proof. exact (MK_COMB (@lem7669650) (@lem7669638)). Qed.
Lemma lem7669653 (m : nat) : (term204 m) = term52.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7669654 : term196 = term52.
Proof. exact (@lem7669653 term11). Qed.
Lemma lem7669655 : term203 = term52.
Proof. exact (TRANS (@lem7669651) (@lem7669654)). Qed.
Lemma lem7669656 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7669657 : term205 = term151.
Proof. exact (MK_COMB (@lem7669656) (@lem7669655)). Qed.
Lemma lem7669658 : term64 = term64.
Proof. exact (eq_refl term64). Qed.
Lemma lem7669659 : term206 = term153.
Proof. exact (MK_COMB (@lem7669657) (@lem7669658)). Qed.
Lemma lem7669661 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7669662 : term153 = term52.
Proof. exact (@lem7669661 term11). Qed.
Lemma lem7669663 : term206 = term52.
Proof. exact (TRANS (@lem7669659) (@lem7669662)). Qed.
Lemma lem7669665 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7669666 : term97 = term98.
Proof. exact (@lem7669665 term11 term11). Qed.
Lemma lem7669667 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7669668 : term100 = term11.
Proof. exact (EQ_MP (@lem7669667) (@lem940073)). Qed.
Lemma lem7669669 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7669670 : term98 = term64.
Proof. exact (MK_COMB (@lem7669669) (@lem7669668)). Qed.
Lemma lem7669671 : term97 = term64.
Proof. exact (TRANS (@lem7669666) (@lem7669670)). Qed.
Lemma lem7669672 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem7669673 : term155 = term153.
Proof. exact (MK_COMB (@lem7669672) (@lem7669671)). Qed.
Lemma lem7669675 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7669676 : term153 = term52.
Proof. exact (@lem7669675 term11). Qed.
Lemma lem7669677 : term155 = term52.
Proof. exact (TRANS (@lem7669673) (@lem7669676)). Qed.
Lemma lem7669678 : term52 = term155.
Proof. exact (SYM (@lem7669677)). Qed.
Lemma lem7669679 : term206 = term155.
Proof. exact (TRANS (@lem7669663) (@lem7669678)). Qed.
Lemma lem7669680 : term197 = term85.
Proof. exact (@lem7669630 (@lem7669679)). Qed.
Lemma lem7669681 : term196 = term85.
Proof. exact (TRANS (@lem7669596) (@lem7669680)). Qed.
Lemma lem7669683 (x : real) : (term104 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7669684 : term85 = term52.
Proof. exact (@lem7669683 term52). Qed.
Lemma lem7669685 : term196 = term52.
Proof. exact (TRANS (@lem7669681) (@lem7669684)). Qed.
Lemma lem7669686 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7669687 : term207 = term151.
Proof. exact (MK_COMB (@lem7669686) (@lem7669685)). Qed.
Lemma lem7669688 (_98789 : int) : (real_of_int _98789) = (real_of_int _98789).
Proof. exact (eq_refl (real_of_int _98789)). Qed.
Lemma lem7669689 (_98789 : int) : (term193 _98789) = (term208 _98789).
Proof. exact (MK_COMB (@lem7669687) (@lem7669688 _98789)). Qed.
Lemma lem7669690 (_98789 : int) : (term464 _98789) = (term208 _98789).
Proof. exact (TRANS (@lem7669587 _98789) (@lem7669689 _98789)). Qed.
Lemma lem7669691 (_98789 : int) : (term208 _98789) = term52.
Proof. exact (@lem1982719 (real_of_int _98789)). Qed.
Lemma lem7669692 (_98789 : int) : (term464 _98789) = term52.
Proof. exact (TRANS (@lem7669690 _98789) (@lem7669691 _98789)). Qed.
Lemma lem7669693 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7669694 (_98789 : int) : (term465 _98789) = term210.
Proof. exact (MK_COMB (@lem7669693) (@lem7669692 _98789)). Qed.
Lemma lem7669695 : term88 = term88.
Proof. exact (eq_refl term88). Qed.
Lemma lem7669696 (_98789 : int) : (term689 _98789) = term211.
Proof. exact (MK_COMB (@lem7669694 _98789) (@lem7669695)). Qed.
Lemma lem7669697 (_98789 : int) : (term688 _98789) = term211.
Proof. exact (TRANS (@lem7669586 _98789) (@lem7669696 _98789)). Qed.
Lemma lem7669698 : term211 = term88.
Proof. exact (@lem1982721 term88). Qed.
Lemma lem7669699 (_98789 : int) : (term688 _98789) = term88.
Proof. exact (TRANS (@lem7669697 _98789) (@lem7669698)). Qed.
Lemma lem7669700 (_98788 : int) (_98789 : int) : (term687 _98788 _98789) = term211.
Proof. exact (MK_COMB (@lem7669585 _98788) (@lem7669699 _98789)). Qed.
Lemma lem7669701 (_98788 : int) (_98789 : int) : (term686 _98788 _98789) = term211.
Proof. exact (TRANS (@lem7669477 _98788 _98789) (@lem7669700 _98788 _98789)). Qed.
Lemma lem7669702 : term211 = term88.
Proof. exact (@lem1982721 term88). Qed.
Lemma lem7669703 (_98788 : int) (_98789 : int) : (term686 _98788 _98789) = term88.
Proof. exact (TRANS (@lem7669701 _98788 _98789) (@lem7669702)). Qed.
Lemma lem7669704 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7669705 (_98788 : int) (_98789 : int) : (term690 _98788 _98789) = term231.
Proof. exact (MK_COMB (@lem7669704) (@lem7669703 _98788 _98789)). Qed.
Lemma lem7669706 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7669707 (_98788 : int) (_98789 : int) : (term685 _98788 _98789) = term232.
Proof. exact (MK_COMB (@lem7669705 _98788 _98789) (@lem7669706)). Qed.
Lemma lem7669708 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term682 A M N _98787 _98790 _98788 _98789 u i v d) : term232.
Proof. exact (EQ_MP (@lem7669707 _98788 _98789) (@lem7669476 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669710 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7669711 : term232 = term233.
Proof. exact (@lem7669710 term52 term88). Qed.
Lemma lem7669713 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7669714 : term88 = term89.
Proof. exact (@lem7669713 term11). Qed.
Lemma lem7669716 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7669717 : term52 = term85.
Proof. exact (@lem7669716 (NUMERAL 0)). Qed.
Lemma lem7669718 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7669719 : term54 = term234.
Proof. exact (MK_COMB (@lem7669718) (@lem7669717)). Qed.
Lemma lem7669720 : term233 = term235.
Proof. exact (MK_COMB (@lem7669719) (@lem7669714)). Qed.
Lemma lem7669721 : term236.
Proof. exact (@lem1980026 term52 term64 term88 term64). Qed.
Lemma lem7669723 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7669724 : term141 = term142.
Proof. exact (@lem7669723 (NUMERAL 0) term11). Qed.
Lemma lem7669725 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7669726 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7669727 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7669726 h1) (fun h1 : term142 = True => @lem7669725)). Qed.
Lemma lem7669728 : term142 = True.
Proof. exact (EQ_MP (@lem7669727) (@lem7669725)). Qed.
Lemma lem7669729 : term141 = True.
Proof. exact (TRANS (@lem7669724) (@lem7669728)). Qed.
Lemma lem7669730 : True = term141.
Proof. exact (SYM (@lem7669729)). Qed.
Lemma lem7669731 : term141.
Proof. exact (EQ_MP (@lem7669730) (@lem0)). Qed.
Lemma lem7669732 : term237.
Proof. exact (@lem7669721 (@lem7669731)). Qed.
Lemma lem7669734 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7669735 : term141 = term142.
Proof. exact (@lem7669734 (NUMERAL 0) term11). Qed.
Lemma lem7669736 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7669737 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7669738 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7669737 h1) (fun h1 : term142 = True => @lem7669736)). Qed.
Lemma lem7669739 : term142 = True.
Proof. exact (EQ_MP (@lem7669738) (@lem7669736)). Qed.
Lemma lem7669740 : term141 = True.
Proof. exact (TRANS (@lem7669735) (@lem7669739)). Qed.
Lemma lem7669741 : True = term141.
Proof. exact (SYM (@lem7669740)). Qed.
Lemma lem7669742 : term141.
Proof. exact (EQ_MP (@lem7669741) (@lem0)). Qed.
Lemma lem7669743 : term235 = term238.
Proof. exact (@lem7669732 (@lem7669742)). Qed.
Lemma lem7669745 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7669746 : term115 = term120.
Proof. exact (@lem7669745 term11 term11). Qed.
Lemma lem7669747 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7669748 : term100 = term11.
Proof. exact (EQ_MP (@lem7669747) (@lem940073)). Qed.
Lemma lem7669749 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7669750 : term98 = term64.
Proof. exact (MK_COMB (@lem7669749) (@lem7669748)). Qed.
Lemma lem7669751 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7669752 : term120 = term88.
Proof. exact (MK_COMB (@lem7669751) (@lem7669750)). Qed.
Lemma lem7669753 : term115 = term88.
Proof. exact (TRANS (@lem7669746) (@lem7669752)). Qed.
Lemma lem7669755 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7669756 : term153 = term52.
Proof. exact (@lem7669755 term11). Qed.
Lemma lem7669757 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7669758 : term239 = term54.
Proof. exact (MK_COMB (@lem7669757) (@lem7669756)). Qed.
Lemma lem7669759 : term238 = term233.
Proof. exact (MK_COMB (@lem7669758) (@lem7669753)). Qed.
Lemma lem7669761 (m : nat) (n : nat) : (term240 m n) = (term241 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7669762 : term233 = term242.
Proof. exact (@lem7669761 (NUMERAL 0) term11). Qed.
Lemma lem7669763 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7669764 (h1 : term143 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7669765 : (term143 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7669764 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem7669763)). Qed.
Lemma lem7669766 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7669765) (@lem7669763)). Qed.
Lemma lem7669767 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7669768 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7669769 : term243 = (and True).
Proof. exact (MK_COMB (@lem7669768) (@lem7669767)). Qed.
Lemma lem7669770 : term242 = (True /\ False).
Proof. exact (MK_COMB (@lem7669769) (@lem7669766)). Qed.
Lemma lem7669772 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7669773 : term242 = False.
Proof. exact (TRANS (@lem7669770) (@lem7669772)). Qed.
Lemma lem7669774 : term233 = False.
Proof. exact (TRANS (@lem7669762) (@lem7669773)). Qed.
Lemma lem7669775 : term238 = False.
Proof. exact (TRANS (@lem7669759) (@lem7669774)). Qed.
Lemma lem7669776 : term235 = False.
Proof. exact (TRANS (@lem7669743) (@lem7669775)). Qed.
Lemma lem7669777 : term233 = False.
Proof. exact (TRANS (@lem7669720) (@lem7669776)). Qed.
Lemma lem7669778 : term232 = False.
Proof. exact (TRANS (@lem7669711) (@lem7669777)). Qed.
Lemma lem7669779 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term682 A M N _98787 _98790 _98788 _98789 u i v d) : False.
Proof. exact (EQ_MP (@lem7669778) (@lem7669708 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669780 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term691 A M N _98787 _98790 _98788 _98789 u i v d) : term691 A M N _98787 _98790 _98788 _98789 u i v d.
Proof. exact (h1). Qed.
Lemma lem7669781 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term691 A M N _98787 _98790 _98788 _98789 u i v d) : term681 A M N _98787 _98790 _98788 _98789 u i v d.
Proof. exact (proj2 (@lem7669780 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669783 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term691 A M N _98787 _98790 _98788 _98789 u i v d) : term677 A M N _98787 _98790 _98788 _98789 u i v d.
Proof. exact (proj2 (@lem7669781 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669785 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term691 A M N _98787 _98790 _98788 _98789 u i v d) : term673 A M N _98787 _98790 _98788 _98789 u i v d.
Proof. exact (proj2 (@lem7669783 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669787 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term691 A M N _98787 _98790 _98788 _98789 u i v d) : term669 A M N _98787 _98790 _98788 _98789 u i v d.
Proof. exact (proj2 (@lem7669785 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669789 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term691 A M N _98787 _98790 _98788 _98789 u i v d) : term658 A M N _98790 _98788 _98789 u i v d.
Proof. exact (proj2 (@lem7669787 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669793 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term691 A M N _98787 _98790 _98788 _98789 u i v d) : term657 A M N _98790 _98788 _98789 u i v d.
Proof. exact (proj2 (@lem7669789 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669794 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term691 A M N _98787 _98790 _98788 _98789 u i v d) : term128 _98788 _98789.
Proof. exact (proj1 (@lem7669789 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669795 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term691 A M N _98787 _98790 _98788 _98789 u i v d) : term655 A M N _98788 _98789 u i v d.
Proof. exact (proj2 (@lem7669793 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669798 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term691 A M N _98787 _98790 _98788 _98789 u i v d) : term420 _98788 _98789.
Proof. exact (proj1 (@lem7669795 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669800 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7669801 : term165 = term141.
Proof. exact (@lem7669800 term52 term64). Qed.
Lemma lem7669803 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7669804 : term64 = term114.
Proof. exact (@lem7669803 term11). Qed.
Lemma lem7669806 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7669807 : term52 = term85.
Proof. exact (@lem7669806 (NUMERAL 0)). Qed.
Lemma lem7669808 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7669809 : term166 = term167.
Proof. exact (MK_COMB (@lem7669808) (@lem7669807)). Qed.
Lemma lem7669810 : term141 = term168.
Proof. exact (MK_COMB (@lem7669809) (@lem7669804)). Qed.
Lemma lem7669811 : term169.
Proof. exact (@lem1980255 term52 term64 term64 term64). Qed.
Lemma lem7669813 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7669814 : term141 = term142.
Proof. exact (@lem7669813 (NUMERAL 0) term11). Qed.
Lemma lem7669815 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7669816 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7669817 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7669816 h1) (fun h1 : term142 = True => @lem7669815)). Qed.
Lemma lem7669818 : term142 = True.
Proof. exact (EQ_MP (@lem7669817) (@lem7669815)). Qed.
Lemma lem7669819 : term141 = True.
Proof. exact (TRANS (@lem7669814) (@lem7669818)). Qed.
Lemma lem7669820 : True = term141.
Proof. exact (SYM (@lem7669819)). Qed.
Lemma lem7669821 : term141.
Proof. exact (EQ_MP (@lem7669820) (@lem0)). Qed.
Lemma lem7669822 : term170.
Proof. exact (@lem7669811 (@lem7669821)). Qed.
Lemma lem7669824 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7669825 : term141 = term142.
Proof. exact (@lem7669824 (NUMERAL 0) term11). Qed.
Lemma lem7669826 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7669827 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7669828 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7669827 h1) (fun h1 : term142 = True => @lem7669826)). Qed.
Lemma lem7669829 : term142 = True.
Proof. exact (EQ_MP (@lem7669828) (@lem7669826)). Qed.
Lemma lem7669830 : term141 = True.
Proof. exact (TRANS (@lem7669825) (@lem7669829)). Qed.
Lemma lem7669831 : True = term141.
Proof. exact (SYM (@lem7669830)). Qed.
Lemma lem7669832 : term141.
Proof. exact (EQ_MP (@lem7669831) (@lem0)). Qed.
Lemma lem7669833 : term168 = term171.
Proof. exact (@lem7669822 (@lem7669832)). Qed.
Lemma lem7669835 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7669836 : term97 = term98.
Proof. exact (@lem7669835 term11 term11). Qed.
Lemma lem7669837 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7669838 : term100 = term11.
Proof. exact (EQ_MP (@lem7669837) (@lem940073)). Qed.
Lemma lem7669839 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7669840 : term98 = term64.
Proof. exact (MK_COMB (@lem7669839) (@lem7669838)). Qed.
Lemma lem7669841 : term97 = term64.
Proof. exact (TRANS (@lem7669836) (@lem7669840)). Qed.
Lemma lem7669843 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7669844 : term153 = term52.
Proof. exact (@lem7669843 term11). Qed.
Lemma lem7669845 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7669846 : term172 = term166.
Proof. exact (MK_COMB (@lem7669845) (@lem7669844)). Qed.
Lemma lem7669847 : term171 = term141.
Proof. exact (MK_COMB (@lem7669846) (@lem7669841)). Qed.
Lemma lem7669849 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7669850 : term141 = term142.
Proof. exact (@lem7669849 (NUMERAL 0) term11). Qed.
Lemma lem7669851 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7669852 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7669853 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7669852 h1) (fun h1 : term142 = True => @lem7669851)). Qed.
Lemma lem7669854 : term142 = True.
Proof. exact (EQ_MP (@lem7669853) (@lem7669851)). Qed.
Lemma lem7669855 : term141 = True.
Proof. exact (TRANS (@lem7669850) (@lem7669854)). Qed.
Lemma lem7669856 : term171 = True.
Proof. exact (TRANS (@lem7669847) (@lem7669855)). Qed.
Lemma lem7669857 : term168 = True.
Proof. exact (TRANS (@lem7669833) (@lem7669856)). Qed.
Lemma lem7669858 : term141 = True.
Proof. exact (TRANS (@lem7669810) (@lem7669857)). Qed.
Lemma lem7669859 : term165 = True.
Proof. exact (TRANS (@lem7669801) (@lem7669858)). Qed.
Lemma lem7669860 : True = term165.
Proof. exact (SYM (@lem7669859)). Qed.
Lemma lem7669861 : term165.
Proof. exact (EQ_MP (@lem7669860) (@lem0)). Qed.
Lemma lem7669862 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term691 A M N _98787 _98790 _98788 _98789 u i v d) : term441 _98788 _98789.
Proof. exact (conj (@lem7669861) (@lem7669798 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669864 (x : real) (y : real) : term174 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7669865 (_98788 : int) (_98789 : int) : term442 _98788 _98789.
Proof. exact (@lem7669864 term64 (term417 _98788 _98789)). Qed.
Lemma lem7669866 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term691 A M N _98787 _98790 _98788 _98789 u i v d) : term443 _98788 _98789.
Proof. exact (@lem7669865 _98788 _98789 (@lem7669862 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669867 (_98788 : int) (_98789 : int) : (term444 _98788 _98789) = (term417 _98788 _98789).
Proof. exact (@lem1982733 (term417 _98788 _98789)). Qed.
Lemma lem7669868 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7669869 (_98788 : int) (_98789 : int) : (term445 _98788 _98789) = (term419 _98788 _98789).
Proof. exact (MK_COMB (@lem7669868) (@lem7669867 _98788 _98789)). Qed.
Lemma lem7669870 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7669871 (_98788 : int) (_98789 : int) : (term443 _98788 _98789) = (term420 _98788 _98789).
Proof. exact (MK_COMB (@lem7669869 _98788 _98789) (@lem7669870)). Qed.
Lemma lem7669872 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term691 A M N _98787 _98790 _98788 _98789 u i v d) : term420 _98788 _98789.
Proof. exact (EQ_MP (@lem7669871 _98788 _98789) (@lem7669866 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669874 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7669875 : term165 = term141.
Proof. exact (@lem7669874 term52 term64). Qed.
Lemma lem7669877 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7669878 : term64 = term114.
Proof. exact (@lem7669877 term11). Qed.
Lemma lem7669880 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7669881 : term52 = term85.
Proof. exact (@lem7669880 (NUMERAL 0)). Qed.
Lemma lem7669882 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7669883 : term166 = term167.
Proof. exact (MK_COMB (@lem7669882) (@lem7669881)). Qed.
Lemma lem7669884 : term141 = term168.
Proof. exact (MK_COMB (@lem7669883) (@lem7669878)). Qed.
Lemma lem7669885 : term169.
Proof. exact (@lem1980255 term52 term64 term64 term64). Qed.
Lemma lem7669887 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7669888 : term141 = term142.
Proof. exact (@lem7669887 (NUMERAL 0) term11). Qed.
Lemma lem7669889 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7669890 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7669891 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7669890 h1) (fun h1 : term142 = True => @lem7669889)). Qed.
Lemma lem7669892 : term142 = True.
Proof. exact (EQ_MP (@lem7669891) (@lem7669889)). Qed.
Lemma lem7669893 : term141 = True.
Proof. exact (TRANS (@lem7669888) (@lem7669892)). Qed.
Lemma lem7669894 : True = term141.
Proof. exact (SYM (@lem7669893)). Qed.
Lemma lem7669895 : term141.
Proof. exact (EQ_MP (@lem7669894) (@lem0)). Qed.
Lemma lem7669896 : term170.
Proof. exact (@lem7669885 (@lem7669895)). Qed.
Lemma lem7669898 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7669899 : term141 = term142.
Proof. exact (@lem7669898 (NUMERAL 0) term11). Qed.
Lemma lem7669900 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7669901 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7669902 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7669901 h1) (fun h1 : term142 = True => @lem7669900)). Qed.
Lemma lem7669903 : term142 = True.
Proof. exact (EQ_MP (@lem7669902) (@lem7669900)). Qed.
Lemma lem7669904 : term141 = True.
Proof. exact (TRANS (@lem7669899) (@lem7669903)). Qed.
Lemma lem7669905 : True = term141.
Proof. exact (SYM (@lem7669904)). Qed.
Lemma lem7669906 : term141.
Proof. exact (EQ_MP (@lem7669905) (@lem0)). Qed.
Lemma lem7669907 : term168 = term171.
Proof. exact (@lem7669896 (@lem7669906)). Qed.
Lemma lem7669909 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7669910 : term97 = term98.
Proof. exact (@lem7669909 term11 term11). Qed.
Lemma lem7669911 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7669912 : term100 = term11.
Proof. exact (EQ_MP (@lem7669911) (@lem940073)). Qed.
Lemma lem7669913 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7669914 : term98 = term64.
Proof. exact (MK_COMB (@lem7669913) (@lem7669912)). Qed.
Lemma lem7669915 : term97 = term64.
Proof. exact (TRANS (@lem7669910) (@lem7669914)). Qed.
Lemma lem7669917 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7669918 : term153 = term52.
Proof. exact (@lem7669917 term11). Qed.
Lemma lem7669919 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7669920 : term172 = term166.
Proof. exact (MK_COMB (@lem7669919) (@lem7669918)). Qed.
Lemma lem7669921 : term171 = term141.
Proof. exact (MK_COMB (@lem7669920) (@lem7669915)). Qed.
Lemma lem7669923 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7669924 : term141 = term142.
Proof. exact (@lem7669923 (NUMERAL 0) term11). Qed.
Lemma lem7669925 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7669926 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7669927 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7669926 h1) (fun h1 : term142 = True => @lem7669925)). Qed.
Lemma lem7669928 : term142 = True.
Proof. exact (EQ_MP (@lem7669927) (@lem7669925)). Qed.
Lemma lem7669929 : term141 = True.
Proof. exact (TRANS (@lem7669924) (@lem7669928)). Qed.
Lemma lem7669930 : term171 = True.
Proof. exact (TRANS (@lem7669921) (@lem7669929)). Qed.
Lemma lem7669931 : term168 = True.
Proof. exact (TRANS (@lem7669907) (@lem7669930)). Qed.
Lemma lem7669932 : term141 = True.
Proof. exact (TRANS (@lem7669884) (@lem7669931)). Qed.
Lemma lem7669933 : term165 = True.
Proof. exact (TRANS (@lem7669875) (@lem7669932)). Qed.
Lemma lem7669934 : True = term165.
Proof. exact (SYM (@lem7669933)). Qed.
Lemma lem7669935 : term165.
Proof. exact (EQ_MP (@lem7669934) (@lem0)). Qed.
Lemma lem7669936 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term691 A M N _98787 _98790 _98788 _98789 u i v d) : term179 _98788 _98789.
Proof. exact (conj (@lem7669935) (@lem7669794 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669938 (x : real) (y : real) : term174 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7669939 (_98788 : int) (_98789 : int) : term180 _98788 _98789.
Proof. exact (@lem7669938 term64 (term125 _98788 _98789)). Qed.
Lemma lem7669940 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term691 A M N _98787 _98790 _98788 _98789 u i v d) : term181 _98788 _98789.
Proof. exact (@lem7669939 _98788 _98789 (@lem7669936 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669941 (_98788 : int) (_98789 : int) : (term182 _98788 _98789) = (term125 _98788 _98789).
Proof. exact (@lem1982733 (term125 _98788 _98789)). Qed.
Lemma lem7669942 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7669943 (_98788 : int) (_98789 : int) : (term183 _98788 _98789) = (term127 _98788 _98789).
Proof. exact (MK_COMB (@lem7669942) (@lem7669941 _98788 _98789)). Qed.
Lemma lem7669944 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7669945 (_98788 : int) (_98789 : int) : (term181 _98788 _98789) = (term128 _98788 _98789).
Proof. exact (MK_COMB (@lem7669943 _98788 _98789) (@lem7669944)). Qed.
Lemma lem7669946 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term691 A M N _98787 _98790 _98788 _98789 u i v d) : term128 _98788 _98789.
Proof. exact (EQ_MP (@lem7669945 _98788 _98789) (@lem7669940 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669947 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term691 A M N _98787 _98790 _98788 _98789 u i v d) : term459 _98788 _98789.
Proof. exact (conj (@lem7669946 A M N _98787 _98790 _98788 _98789 u i v d h1) (@lem7669872 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669949 (x : real) (y : real) : term185 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7669950 (_98788 : int) (_98789 : int) : term460 _98788 _98789.
Proof. exact (@lem7669949 (term125 _98788 _98789) (term417 _98788 _98789)). Qed.
Lemma lem7669951 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term691 A M N _98787 _98790 _98788 _98789 u i v d) : term461 _98788 _98789.
Proof. exact (@lem7669950 _98788 _98789 (@lem7669947 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7669952 (_98788 : int) (_98789 : int) : (term462 _98788 _98789) = (term463 _98788 _98789).
Proof. exact (@lem1982753 (real_of_int _98788) (term135 _98788) (term124 _98789) (real_of_int _98789)). Qed.
Lemma lem7669953 (_98788 : int) : (term464 _98788) = (term193 _98788).
Proof. exact (@lem1982715 term88 (real_of_int _98788)). Qed.
Lemma lem7669955 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7669956 : term64 = term114.
Proof. exact (@lem7669955 term11). Qed.
Lemma lem7669958 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7669959 : term88 = term89.
Proof. exact (@lem7669958 term11). Qed.
Lemma lem7669960 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7669961 : term194 = term195.
Proof. exact (MK_COMB (@lem7669960) (@lem7669959)). Qed.
Lemma lem7669962 : term196 = term197.
Proof. exact (MK_COMB (@lem7669961) (@lem7669956)). Qed.
Lemma lem7669963 : term198.
Proof. exact (@lem1981473 term88 term64 term64 term64 term52 term64). Qed.
Lemma lem7669965 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7669966 : term141 = term142.
Proof. exact (@lem7669965 (NUMERAL 0) term11). Qed.
Lemma lem7669967 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7669968 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7669969 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7669968 h1) (fun h1 : term142 = True => @lem7669967)). Qed.
Lemma lem7669970 : term142 = True.
Proof. exact (EQ_MP (@lem7669969) (@lem7669967)). Qed.
Lemma lem7669971 : term141 = True.
Proof. exact (TRANS (@lem7669966) (@lem7669970)). Qed.
Lemma lem7669972 : True = term141.
Proof. exact (SYM (@lem7669971)). Qed.
Lemma lem7669973 : term141.
Proof. exact (EQ_MP (@lem7669972) (@lem0)). Qed.
Lemma lem7669974 : term199.
Proof. exact (@lem7669963 (@lem7669973)). Qed.
Lemma lem7669976 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7669977 : term141 = term142.
Proof. exact (@lem7669976 (NUMERAL 0) term11). Qed.
Lemma lem7669978 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7669979 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7669980 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7669979 h1) (fun h1 : term142 = True => @lem7669978)). Qed.
Lemma lem7669981 : term142 = True.
Proof. exact (EQ_MP (@lem7669980) (@lem7669978)). Qed.
Lemma lem7669982 : term141 = True.
Proof. exact (TRANS (@lem7669977) (@lem7669981)). Qed.
Lemma lem7669983 : True = term141.
Proof. exact (SYM (@lem7669982)). Qed.
Lemma lem7669984 : term141.
Proof. exact (EQ_MP (@lem7669983) (@lem0)). Qed.
Lemma lem7669985 : term200.
Proof. exact (@lem7669974 (@lem7669984)). Qed.
Lemma lem7669987 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7669988 : term141 = term142.
Proof. exact (@lem7669987 (NUMERAL 0) term11). Qed.
Lemma lem7669989 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7669990 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7669991 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7669990 h1) (fun h1 : term142 = True => @lem7669989)). Qed.
Lemma lem7669992 : term142 = True.
Proof. exact (EQ_MP (@lem7669991) (@lem7669989)). Qed.
Lemma lem7669993 : term141 = True.
Proof. exact (TRANS (@lem7669988) (@lem7669992)). Qed.
Lemma lem7669994 : True = term141.
Proof. exact (SYM (@lem7669993)). Qed.
Lemma lem7669995 : term141.
Proof. exact (EQ_MP (@lem7669994) (@lem0)). Qed.
Lemma lem7669996 : term201.
Proof. exact (@lem7669985 (@lem7669995)). Qed.
Lemma lem7669998 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7669999 : term97 = term98.
Proof. exact (@lem7669998 term11 term11). Qed.
Lemma lem7670000 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7670001 : term100 = term11.
Proof. exact (EQ_MP (@lem7670000) (@lem940073)). Qed.
Lemma lem7670002 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7670003 : term98 = term64.
Proof. exact (MK_COMB (@lem7670002) (@lem7670001)). Qed.
Lemma lem7670004 : term97 = term64.
Proof. exact (TRANS (@lem7669999) (@lem7670003)). Qed.
Lemma lem7670006 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7670007 : term115 = term120.
Proof. exact (@lem7670006 term11 term11). Qed.
Lemma lem7670008 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7670009 : term100 = term11.
Proof. exact (EQ_MP (@lem7670008) (@lem940073)). Qed.
Lemma lem7670010 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7670011 : term98 = term64.
Proof. exact (MK_COMB (@lem7670010) (@lem7670009)). Qed.
Lemma lem7670012 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7670013 : term120 = term88.
Proof. exact (MK_COMB (@lem7670012) (@lem7670011)). Qed.
Lemma lem7670014 : term115 = term88.
Proof. exact (TRANS (@lem7670007) (@lem7670013)). Qed.
Lemma lem7670015 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7670016 : term202 = term194.
Proof. exact (MK_COMB (@lem7670015) (@lem7670014)). Qed.
Lemma lem7670017 : term203 = term196.
Proof. exact (MK_COMB (@lem7670016) (@lem7670004)). Qed.
Lemma lem7670019 (m : nat) : (term204 m) = term52.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7670020 : term196 = term52.
Proof. exact (@lem7670019 term11). Qed.
Lemma lem7670021 : term203 = term52.
Proof. exact (TRANS (@lem7670017) (@lem7670020)). Qed.
Lemma lem7670022 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7670023 : term205 = term151.
Proof. exact (MK_COMB (@lem7670022) (@lem7670021)). Qed.
Lemma lem7670024 : term64 = term64.
Proof. exact (eq_refl term64). Qed.
Lemma lem7670025 : term206 = term153.
Proof. exact (MK_COMB (@lem7670023) (@lem7670024)). Qed.
Lemma lem7670027 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7670028 : term153 = term52.
Proof. exact (@lem7670027 term11). Qed.
Lemma lem7670029 : term206 = term52.
Proof. exact (TRANS (@lem7670025) (@lem7670028)). Qed.
Lemma lem7670031 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7670032 : term97 = term98.
Proof. exact (@lem7670031 term11 term11). Qed.
Lemma lem7670033 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7670034 : term100 = term11.
Proof. exact (EQ_MP (@lem7670033) (@lem940073)). Qed.
Lemma lem7670035 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7670036 : term98 = term64.
Proof. exact (MK_COMB (@lem7670035) (@lem7670034)). Qed.
Lemma lem7670037 : term97 = term64.
Proof. exact (TRANS (@lem7670032) (@lem7670036)). Qed.
Lemma lem7670038 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem7670039 : term155 = term153.
Proof. exact (MK_COMB (@lem7670038) (@lem7670037)). Qed.
Lemma lem7670041 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7670042 : term153 = term52.
Proof. exact (@lem7670041 term11). Qed.
Lemma lem7670043 : term155 = term52.
Proof. exact (TRANS (@lem7670039) (@lem7670042)). Qed.
Lemma lem7670044 : term52 = term155.
Proof. exact (SYM (@lem7670043)). Qed.
Lemma lem7670045 : term206 = term155.
Proof. exact (TRANS (@lem7670029) (@lem7670044)). Qed.
Lemma lem7670046 : term197 = term85.
Proof. exact (@lem7669996 (@lem7670045)). Qed.
Lemma lem7670047 : term196 = term85.
Proof. exact (TRANS (@lem7669962) (@lem7670046)). Qed.
Lemma lem7670049 (x : real) : (term104 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7670050 : term85 = term52.
Proof. exact (@lem7670049 term52). Qed.
Lemma lem7670051 : term196 = term52.
Proof. exact (TRANS (@lem7670047) (@lem7670050)). Qed.
Lemma lem7670052 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7670053 : term207 = term151.
Proof. exact (MK_COMB (@lem7670052) (@lem7670051)). Qed.
Lemma lem7670054 (_98788 : int) : (real_of_int _98788) = (real_of_int _98788).
Proof. exact (eq_refl (real_of_int _98788)). Qed.
Lemma lem7670055 (_98788 : int) : (term193 _98788) = (term208 _98788).
Proof. exact (MK_COMB (@lem7670053) (@lem7670054 _98788)). Qed.
Lemma lem7670056 (_98788 : int) : (term464 _98788) = (term208 _98788).
Proof. exact (TRANS (@lem7669953 _98788) (@lem7670055 _98788)). Qed.
Lemma lem7670057 (_98788 : int) : (term208 _98788) = term52.
Proof. exact (@lem1982719 (real_of_int _98788)). Qed.
Lemma lem7670058 (_98788 : int) : (term464 _98788) = term52.
Proof. exact (TRANS (@lem7670056 _98788) (@lem7670057 _98788)). Qed.
Lemma lem7670059 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7670060 (_98788 : int) : (term465 _98788) = term210.
Proof. exact (MK_COMB (@lem7670059) (@lem7670058 _98788)). Qed.
Lemma lem7670061 (_98789 : int) : (term190 _98789) = (term191 _98789).
Proof. exact (@lem1982759 (term135 _98789) (real_of_int _98789) term88). Qed.
Lemma lem7670062 (_98789 : int) : (term192 _98789) = (term193 _98789).
Proof. exact (@lem1982713 term88 (real_of_int _98789)). Qed.
Lemma lem7670064 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7670065 : term64 = term114.
Proof. exact (@lem7670064 term11). Qed.
Lemma lem7670067 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7670068 : term88 = term89.
Proof. exact (@lem7670067 term11). Qed.
Lemma lem7670069 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7670070 : term194 = term195.
Proof. exact (MK_COMB (@lem7670069) (@lem7670068)). Qed.
Lemma lem7670071 : term196 = term197.
Proof. exact (MK_COMB (@lem7670070) (@lem7670065)). Qed.
Lemma lem7670072 : term198.
Proof. exact (@lem1981473 term88 term64 term64 term64 term52 term64). Qed.
Lemma lem7670074 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7670075 : term141 = term142.
Proof. exact (@lem7670074 (NUMERAL 0) term11). Qed.
Lemma lem7670076 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7670077 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7670078 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7670077 h1) (fun h1 : term142 = True => @lem7670076)). Qed.
Lemma lem7670079 : term142 = True.
Proof. exact (EQ_MP (@lem7670078) (@lem7670076)). Qed.
Lemma lem7670080 : term141 = True.
Proof. exact (TRANS (@lem7670075) (@lem7670079)). Qed.
Lemma lem7670081 : True = term141.
Proof. exact (SYM (@lem7670080)). Qed.
Lemma lem7670082 : term141.
Proof. exact (EQ_MP (@lem7670081) (@lem0)). Qed.
Lemma lem7670083 : term199.
Proof. exact (@lem7670072 (@lem7670082)). Qed.
Lemma lem7670085 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7670086 : term141 = term142.
Proof. exact (@lem7670085 (NUMERAL 0) term11). Qed.
Lemma lem7670087 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7670088 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7670089 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7670088 h1) (fun h1 : term142 = True => @lem7670087)). Qed.
Lemma lem7670090 : term142 = True.
Proof. exact (EQ_MP (@lem7670089) (@lem7670087)). Qed.
Lemma lem7670091 : term141 = True.
Proof. exact (TRANS (@lem7670086) (@lem7670090)). Qed.
Lemma lem7670092 : True = term141.
Proof. exact (SYM (@lem7670091)). Qed.
Lemma lem7670093 : term141.
Proof. exact (EQ_MP (@lem7670092) (@lem0)). Qed.
Lemma lem7670094 : term200.
Proof. exact (@lem7670083 (@lem7670093)). Qed.
Lemma lem7670096 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7670097 : term141 = term142.
Proof. exact (@lem7670096 (NUMERAL 0) term11). Qed.
Lemma lem7670098 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7670099 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7670100 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7670099 h1) (fun h1 : term142 = True => @lem7670098)). Qed.
Lemma lem7670101 : term142 = True.
Proof. exact (EQ_MP (@lem7670100) (@lem7670098)). Qed.
Lemma lem7670102 : term141 = True.
Proof. exact (TRANS (@lem7670097) (@lem7670101)). Qed.
Lemma lem7670103 : True = term141.
Proof. exact (SYM (@lem7670102)). Qed.
Lemma lem7670104 : term141.
Proof. exact (EQ_MP (@lem7670103) (@lem0)). Qed.
Lemma lem7670105 : term201.
Proof. exact (@lem7670094 (@lem7670104)). Qed.
Lemma lem7670107 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7670108 : term97 = term98.
Proof. exact (@lem7670107 term11 term11). Qed.
Lemma lem7670109 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7670110 : term100 = term11.
Proof. exact (EQ_MP (@lem7670109) (@lem940073)). Qed.
Lemma lem7670111 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7670112 : term98 = term64.
Proof. exact (MK_COMB (@lem7670111) (@lem7670110)). Qed.
Lemma lem7670113 : term97 = term64.
Proof. exact (TRANS (@lem7670108) (@lem7670112)). Qed.
Lemma lem7670115 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7670116 : term115 = term120.
Proof. exact (@lem7670115 term11 term11). Qed.
Lemma lem7670117 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7670118 : term100 = term11.
Proof. exact (EQ_MP (@lem7670117) (@lem940073)). Qed.
Lemma lem7670119 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7670120 : term98 = term64.
Proof. exact (MK_COMB (@lem7670119) (@lem7670118)). Qed.
Lemma lem7670121 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7670122 : term120 = term88.
Proof. exact (MK_COMB (@lem7670121) (@lem7670120)). Qed.
Lemma lem7670123 : term115 = term88.
Proof. exact (TRANS (@lem7670116) (@lem7670122)). Qed.
Lemma lem7670124 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7670125 : term202 = term194.
Proof. exact (MK_COMB (@lem7670124) (@lem7670123)). Qed.
Lemma lem7670126 : term203 = term196.
Proof. exact (MK_COMB (@lem7670125) (@lem7670113)). Qed.
Lemma lem7670128 (m : nat) : (term204 m) = term52.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7670129 : term196 = term52.
Proof. exact (@lem7670128 term11). Qed.
Lemma lem7670130 : term203 = term52.
Proof. exact (TRANS (@lem7670126) (@lem7670129)). Qed.
Lemma lem7670131 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7670132 : term205 = term151.
Proof. exact (MK_COMB (@lem7670131) (@lem7670130)). Qed.
Lemma lem7670133 : term64 = term64.
Proof. exact (eq_refl term64). Qed.
Lemma lem7670134 : term206 = term153.
Proof. exact (MK_COMB (@lem7670132) (@lem7670133)). Qed.
Lemma lem7670136 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7670137 : term153 = term52.
Proof. exact (@lem7670136 term11). Qed.
Lemma lem7670138 : term206 = term52.
Proof. exact (TRANS (@lem7670134) (@lem7670137)). Qed.
Lemma lem7670140 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7670141 : term97 = term98.
Proof. exact (@lem7670140 term11 term11). Qed.
Lemma lem7670142 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7670143 : term100 = term11.
Proof. exact (EQ_MP (@lem7670142) (@lem940073)). Qed.
Lemma lem7670144 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7670145 : term98 = term64.
Proof. exact (MK_COMB (@lem7670144) (@lem7670143)). Qed.
Lemma lem7670146 : term97 = term64.
Proof. exact (TRANS (@lem7670141) (@lem7670145)). Qed.
Lemma lem7670147 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem7670148 : term155 = term153.
Proof. exact (MK_COMB (@lem7670147) (@lem7670146)). Qed.
Lemma lem7670150 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7670151 : term153 = term52.
Proof. exact (@lem7670150 term11). Qed.
Lemma lem7670152 : term155 = term52.
Proof. exact (TRANS (@lem7670148) (@lem7670151)). Qed.
Lemma lem7670153 : term52 = term155.
Proof. exact (SYM (@lem7670152)). Qed.
Lemma lem7670154 : term206 = term155.
Proof. exact (TRANS (@lem7670138) (@lem7670153)). Qed.
Lemma lem7670155 : term197 = term85.
Proof. exact (@lem7670105 (@lem7670154)). Qed.
Lemma lem7670156 : term196 = term85.
Proof. exact (TRANS (@lem7670071) (@lem7670155)). Qed.
Lemma lem7670158 (x : real) : (term104 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7670159 : term85 = term52.
Proof. exact (@lem7670158 term52). Qed.
Lemma lem7670160 : term196 = term52.
Proof. exact (TRANS (@lem7670156) (@lem7670159)). Qed.
Lemma lem7670161 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7670162 : term207 = term151.
Proof. exact (MK_COMB (@lem7670161) (@lem7670160)). Qed.
Lemma lem7670163 (_98789 : int) : (real_of_int _98789) = (real_of_int _98789).
Proof. exact (eq_refl (real_of_int _98789)). Qed.
Lemma lem7670164 (_98789 : int) : (term193 _98789) = (term208 _98789).
Proof. exact (MK_COMB (@lem7670162) (@lem7670163 _98789)). Qed.
Lemma lem7670165 (_98789 : int) : (term192 _98789) = (term208 _98789).
Proof. exact (TRANS (@lem7670062 _98789) (@lem7670164 _98789)). Qed.
Lemma lem7670166 (_98789 : int) : (term208 _98789) = term52.
Proof. exact (@lem1982719 (real_of_int _98789)). Qed.
Lemma lem7670167 (_98789 : int) : (term192 _98789) = term52.
Proof. exact (TRANS (@lem7670165 _98789) (@lem7670166 _98789)). Qed.
Lemma lem7670168 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7670169 (_98789 : int) : (term209 _98789) = term210.
Proof. exact (MK_COMB (@lem7670168) (@lem7670167 _98789)). Qed.
Lemma lem7670170 : term88 = term88.
Proof. exact (eq_refl term88). Qed.
Lemma lem7670171 (_98789 : int) : (term191 _98789) = term211.
Proof. exact (MK_COMB (@lem7670169 _98789) (@lem7670170)). Qed.
Lemma lem7670172 (_98789 : int) : (term190 _98789) = term211.
Proof. exact (TRANS (@lem7670061 _98789) (@lem7670171 _98789)). Qed.
Lemma lem7670173 : term211 = term88.
Proof. exact (@lem1982721 term88). Qed.
Lemma lem7670174 (_98789 : int) : (term190 _98789) = term88.
Proof. exact (TRANS (@lem7670172 _98789) (@lem7670173)). Qed.
Lemma lem7670175 (_98788 : int) (_98789 : int) : (term463 _98788 _98789) = term211.
Proof. exact (MK_COMB (@lem7670060 _98788) (@lem7670174 _98789)). Qed.
Lemma lem7670176 (_98788 : int) (_98789 : int) : (term462 _98788 _98789) = term211.
Proof. exact (TRANS (@lem7669952 _98788 _98789) (@lem7670175 _98788 _98789)). Qed.
Lemma lem7670177 : term211 = term88.
Proof. exact (@lem1982721 term88). Qed.
Lemma lem7670178 (_98788 : int) (_98789 : int) : (term462 _98788 _98789) = term88.
Proof. exact (TRANS (@lem7670176 _98788 _98789) (@lem7670177)). Qed.
Lemma lem7670179 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7670180 (_98788 : int) (_98789 : int) : (term466 _98788 _98789) = term231.
Proof. exact (MK_COMB (@lem7670179) (@lem7670178 _98788 _98789)). Qed.
Lemma lem7670181 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7670182 (_98788 : int) (_98789 : int) : (term461 _98788 _98789) = term232.
Proof. exact (MK_COMB (@lem7670180 _98788 _98789) (@lem7670181)). Qed.
Lemma lem7670183 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term691 A M N _98787 _98790 _98788 _98789 u i v d) : term232.
Proof. exact (EQ_MP (@lem7670182 _98788 _98789) (@lem7669951 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7670185 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7670186 : term232 = term233.
Proof. exact (@lem7670185 term52 term88). Qed.
Lemma lem7670188 (x : nat) : (term86 x) = (term87 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7670189 : term88 = term89.
Proof. exact (@lem7670188 term11). Qed.
Lemma lem7670191 (x : nat) : (real_of_num x) = (term84 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7670192 : term52 = term85.
Proof. exact (@lem7670191 (NUMERAL 0)). Qed.
Lemma lem7670193 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7670194 : term54 = term234.
Proof. exact (MK_COMB (@lem7670193) (@lem7670192)). Qed.
Lemma lem7670195 : term233 = term235.
Proof. exact (MK_COMB (@lem7670194) (@lem7670189)). Qed.
Lemma lem7670196 : term236.
Proof. exact (@lem1980026 term52 term64 term88 term64). Qed.
Lemma lem7670198 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7670199 : term141 = term142.
Proof. exact (@lem7670198 (NUMERAL 0) term11). Qed.
Lemma lem7670200 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7670201 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7670202 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7670201 h1) (fun h1 : term142 = True => @lem7670200)). Qed.
Lemma lem7670203 : term142 = True.
Proof. exact (EQ_MP (@lem7670202) (@lem7670200)). Qed.
Lemma lem7670204 : term141 = True.
Proof. exact (TRANS (@lem7670199) (@lem7670203)). Qed.
Lemma lem7670205 : True = term141.
Proof. exact (SYM (@lem7670204)). Qed.
Lemma lem7670206 : term141.
Proof. exact (EQ_MP (@lem7670205) (@lem0)). Qed.
Lemma lem7670207 : term237.
Proof. exact (@lem7670196 (@lem7670206)). Qed.
Lemma lem7670209 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7670210 : term141 = term142.
Proof. exact (@lem7670209 (NUMERAL 0) term11). Qed.
Lemma lem7670211 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7670212 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7670213 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7670212 h1) (fun h1 : term142 = True => @lem7670211)). Qed.
Lemma lem7670214 : term142 = True.
Proof. exact (EQ_MP (@lem7670213) (@lem7670211)). Qed.
Lemma lem7670215 : term141 = True.
Proof. exact (TRANS (@lem7670210) (@lem7670214)). Qed.
Lemma lem7670216 : True = term141.
Proof. exact (SYM (@lem7670215)). Qed.
Lemma lem7670217 : term141.
Proof. exact (EQ_MP (@lem7670216) (@lem0)). Qed.
Lemma lem7670218 : term235 = term238.
Proof. exact (@lem7670207 (@lem7670217)). Qed.
Lemma lem7670220 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7670221 : term115 = term120.
Proof. exact (@lem7670220 term11 term11). Qed.
Lemma lem7670222 : (term99 = (BIT1 0)) = (term100 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7670223 : term100 = term11.
Proof. exact (EQ_MP (@lem7670222) (@lem940073)). Qed.
Lemma lem7670224 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7670225 : term98 = term64.
Proof. exact (MK_COMB (@lem7670224) (@lem7670223)). Qed.
Lemma lem7670226 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7670227 : term120 = term88.
Proof. exact (MK_COMB (@lem7670226) (@lem7670225)). Qed.
Lemma lem7670228 : term115 = term88.
Proof. exact (TRANS (@lem7670221) (@lem7670227)). Qed.
Lemma lem7670230 (x : nat) : (term154 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7670231 : term153 = term52.
Proof. exact (@lem7670230 term11). Qed.
Lemma lem7670232 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7670233 : term239 = term54.
Proof. exact (MK_COMB (@lem7670232) (@lem7670231)). Qed.
Lemma lem7670234 : term238 = term233.
Proof. exact (MK_COMB (@lem7670233) (@lem7670228)). Qed.
Lemma lem7670236 (m : nat) (n : nat) : (term240 m n) = (term241 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7670237 : term233 = term242.
Proof. exact (@lem7670236 (NUMERAL 0) term11). Qed.
Lemma lem7670238 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7670239 (h1 : term143 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7670240 : (term143 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem7670239 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem7670238)). Qed.
Lemma lem7670241 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7670240) (@lem7670238)). Qed.
Lemma lem7670242 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7670243 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7670244 : term243 = (and True).
Proof. exact (MK_COMB (@lem7670243) (@lem7670242)). Qed.
Lemma lem7670245 : term242 = (True /\ False).
Proof. exact (MK_COMB (@lem7670244) (@lem7670241)). Qed.
Lemma lem7670247 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7670248 : term242 = False.
Proof. exact (TRANS (@lem7670245) (@lem7670247)). Qed.
Lemma lem7670249 : term233 = False.
Proof. exact (TRANS (@lem7670237) (@lem7670248)). Qed.
Lemma lem7670250 : term238 = False.
Proof. exact (TRANS (@lem7670234) (@lem7670249)). Qed.
Lemma lem7670251 : term235 = False.
Proof. exact (TRANS (@lem7670218) (@lem7670250)). Qed.
Lemma lem7670252 : term233 = False.
Proof. exact (TRANS (@lem7670195) (@lem7670251)). Qed.
Lemma lem7670253 : term232 = False.
Proof. exact (TRANS (@lem7670186) (@lem7670252)). Qed.
Lemma lem7670254 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term691 A M N _98787 _98790 _98788 _98789 u i v d) : False.
Proof. exact (EQ_MP (@lem7670253) (@lem7670183 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7670255 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term679 A M N _98787 _98790 _98788 _98789 u i v d) : False.
Proof. exact (or_elim (@lem7669306 A M N _98787 _98790 _98788 _98789 u i v d h1) (fun h0 : term682 A M N _98787 _98790 _98788 _98789 u i v d => @lem7669779 A M N _98787 _98790 _98788 _98789 u i v d h0) (fun h0 : term691 A M N _98787 _98790 _98788 _98789 u i v d => @lem7670254 A M N _98787 _98790 _98788 _98789 u i v d h0)). Qed.
Lemma lem7670257 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term679 A M N _98787 _98790 _98788 _98789 u i v d) : term679 A M N _98787 _98790 _98788 _98789 u i v d.
Proof. exact (h1). Qed.
Lemma lem7670258 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term679 A M N _98787 _98790 _98788 _98789 u i v d) : (term679 A M N _98787 _98790 _98788 _98789 u i v d) = False.
Proof. exact (prop_ext (fun h2 : term679 A M N _98787 _98790 _98788 _98789 u i v d => @lem7670255 A M N _98787 _98790 _98788 _98789 u i v d h1) (fun h2 : False => @lem7670257 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7670259 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term679 A M N _98787 _98790 _98788 _98789 u i v d) : False.
Proof. exact (EQ_MP (@lem7670258 A M N _98787 _98790 _98788 _98789 u i v d h1) (@lem7670257 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7670260 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term631 A M N _98787 _98790 _98788 _98789 u i v d) : term631 A M N _98787 _98790 _98788 _98789 u i v d.
Proof. exact (h1). Qed.
Lemma lem7670261 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term631 A M N _98787 _98790 _98788 _98789 u i v d) : term679 A M N _98787 _98790 _98788 _98789 u i v d.
Proof. exact (EQ_MP (@lem7669296 A M N _98787 _98790 _98788 _98789 u i v d) (@lem7670260 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7670262 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term631 A M N _98787 _98790 _98788 _98789 u i v d) : (term679 A M N _98787 _98790 _98788 _98789 u i v d) = False.
Proof. exact (prop_ext (fun h2 : term679 A M N _98787 _98790 _98788 _98789 u i v d => @lem7670259 A M N _98787 _98790 _98788 _98789 u i v d h2) (fun h2 : False => @lem7670261 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7670263 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) (h1 : term631 A M N _98787 _98790 _98788 _98789 u i v d) : False.
Proof. exact (EQ_MP (@lem7670262 A M N _98787 _98790 _98788 _98789 u i v d h1) (@lem7670261 A M N _98787 _98790 _98788 _98789 u i v d h1)). Qed.
Lemma lem7670264 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : term692 A M N _98787 _98790 _98788 _98789 u i v d.
Proof. exact (fun h0 : term631 A M N _98787 _98790 _98788 _98789 u i v d => @lem7670263 A M N _98787 _98790 _98788 _98789 u i v d h0). Qed.
Lemma lem7670265 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : term693 A M N _98787 _98790 _98788 _98789 u i v d.
Proof. exact (@lem1386578 (term694 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7670268 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : term694 A M N _98787 _98790 _98788 _98789 u i v d.
Proof. exact (@lem7670265 A M N _98787 _98790 _98788 _98789 u i v d (@lem7670264 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7670269 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term630 A M N _98787 _98790 _98788 _98789 u i v d) = (term612 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (SYM (@lem7668599 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7670270 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7670271 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : (term694 A M N _98787 _98790 _98788 _98789 u i v d) = (term557 A M N _98787 _98790 _98788 _98789 u i v d).
Proof. exact (MK_COMB (@lem7670270) (@lem7670269 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7670272 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : term557 A M N _98787 _98790 _98788 _98789 u i v d.
Proof. exact (EQ_MP (@lem7670271 A M N _98787 _98790 _98788 _98789 u i v d) (@lem7670268 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7670273 {A M N : Type'} (_98787 : int) (_98790 : int) (_98788 : int) (_98789 : int) (u : cart A M) (i : nat) (v : cart A N) (d : nat) : term558 A M N _98787 _98790 _98788 _98789 u i v d.
Proof. exact (EQ_MP (@lem7668284 A M N _98787 _98790 _98788 _98789 u i v d) (@lem7670272 A M N _98787 _98790 _98788 _98789 u i v d)). Qed.
Lemma lem7670274 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) (d : nat) : term695 A M N u i v d.
Proof. exact (@lem7670273 A M N (int_of_num d) (term248 N) (int_of_num i) (term248 M) u i v d). Qed.
Lemma lem7670275 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) (d : nat) : term696 A M N u i v d.
Proof. exact (@lem7670274 A M N u i v d (@lem7668274 d)). Qed.
Lemma lem7670276 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) (d : nat) : term697 A M N u i v d.
Proof. exact (@lem7670275 A M N u i v d (@lem7668277 i)). Qed.
Lemma lem7670277 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) (d : nat) : term698 A M N u i v d.
Proof. exact (@lem7670276 A M N u i v d (@lem7668280 M)). Qed.
Lemma lem7670278 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) (d : nat) : term554 A M N u i v d.
Proof. exact (@lem7670277 A M N u i v d (@lem7668283 N)). Qed.
Lemma lem7670279 {A M N : Type'} (u : cart A M) (i : nat) (v : cart A N) : term556 A M N u i v.
Proof. exact (fun d : nat => @lem7670278 A M N u i v d). Qed.
Lemma lem7670280 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term556 A M N u i v) = (term502 A M N u v i).
Proof. exact (SYM (@lem7668271 A M N u i v)). Qed.
Lemma lem7670281 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : term502 A M N u v i.
Proof. exact (EQ_MP (@lem7670280 A M N u v i) (@lem7670279 A M N u i v)). Qed.
Lemma lem7670282 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term502 A M N u v i) = ((term502 A M N u v i) = True).
Proof. exact (@lem7 (term502 A M N u v i)). Qed.
Lemma lem7670283 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : (term502 A M N u v i) = True.
Proof. exact (EQ_MP (@lem7670282 A M N u v i) (@lem7670281 A M N u v i)). Qed.
Lemma lem7670284 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : True = (term502 A M N u v i).
Proof. exact (SYM (@lem7670283 A M N u v i)). Qed.
Lemma lem7670285 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : term502 A M N u v i.
Proof. exact (EQ_MP (@lem7670284 A M N u v i) (@lem0)). Qed.
Lemma lem7670286 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (h1 : term2 M i) : term499 A M N u v i.
Proof. exact (@lem7670285 A M N u v i (@lem7666144 M i h1)). Qed.
Lemma lem7670287 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (h1 : term298 M N i) (h2 : term2 M i) : term489 A M N u v i.
Proof. exact (@lem7670286 A M N u v i h2 (@lem7666143 M N i h1)). Qed.
Lemma lem7670290 {A M N : Type'} (v : cart A N) (i : nat) : (term277 A M N v i) = (term277 A M N v i).
Proof. exact (EQ_MP (@lem7668011 A M N v i) (@lem0)). Qed.
Lemma lem7670291 {A M N : Type'} (v : cart A N) (i : nat) : term485 A M N v i.
Proof. exact (fun h0 : term347 M i => @lem7670290 A M N v i). Qed.
Lemma lem7670292 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (h1 : term296 M i) (h2 : term298 M N i) (h3 : term2 M i) : (@dollar A M u i) = (term277 A M N v i).
Proof. exact (@lem7670287 A M N u v i h2 h3 (@lem7667969 M i h1)). Qed.
Lemma lem7670293 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (h1 : term296 M i) (h2 : term298 M N i) (h3 : term2 M i) : (term296 M i) = ((@dollar A M u i) = (term277 A M N v i)).
Proof. exact (prop_ext (fun h4 : term296 M i => @lem7670292 A M N u v i h1 h2 h3) (fun h4 : (@dollar A M u i) = (term277 A M N v i) => @lem7667969 M i h1)). Qed.
Lemma lem7670294 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (h1 : term296 M i) (h2 : term298 M N i) (h3 : term2 M i) : (@dollar A M u i) = (term277 A M N v i).
Proof. exact (EQ_MP (@lem7670293 A M N u v i h1 h2 h3) (@lem7667969 M i h1)). Qed.
Lemma lem7670295 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (h1 : term298 M N i) (h2 : term2 M i) : term489 A M N u v i.
Proof. exact (fun h0 : term296 M i => @lem7670294 A M N u v i h0 h1 h2). Qed.
Lemma lem7670296 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (h1 : term298 M N i) (h2 : term2 M i) : term492 A M N u v i.
Proof. exact (conj (@lem7670295 A M N u v i h1 h2) (@lem7670291 A M N v i)). Qed.
Lemma lem7670297 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (h1 : term298 M N i) (h2 : term2 M i) : (term312 A M N u v i) = (term277 A M N v i).
Proof. exact (EQ_MP (@lem7667968 A M N u v i) (@lem7670296 A M N u v i h1 h2)). Qed.
Lemma lem7670298 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (h1 : term298 M N i) (h2 : term2 M i) : (term257 A M N u v i) = (term277 A M N v i).
Proof. exact (EQ_MP (@lem7667950 A M N u v i h1 h2) (@lem7670297 A M N u v i h1 h2)). Qed.
Lemma lem7670299 {M N : Type'} (i : nat) (h1 : term297 M N i) : term298 M N i.
Proof. exact (proj2 (@lem7666142 M N i h1)). Qed.
Lemma lem7670300 {M N : Type'} (i : nat) (h1 : term297 M N i) : term2 M i.
Proof. exact (proj1 (@lem7666142 M N i h1)). Qed.
Lemma lem7670301 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (h1 : term298 M N i) (h2 : term2 M i) : (term298 M N i) = ((term257 A M N u v i) = (term277 A M N v i)).
Proof. exact (prop_ext (fun h3 : term298 M N i => @lem7670298 A M N u v i h1 h2) (fun h3 : (term257 A M N u v i) = (term277 A M N v i) => @lem7666143 M N i h1)). Qed.
Lemma lem7670302 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (h1 : term298 M N i) (h2 : term2 M i) : (term257 A M N u v i) = (term277 A M N v i).
Proof. exact (EQ_MP (@lem7670301 A M N u v i h1 h2) (@lem7666143 M N i h1)). Qed.
Lemma lem7670303 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (h1 : term298 M N i) (h2 : term2 M i) : (term2 M i) = ((term257 A M N u v i) = (term277 A M N v i)).
Proof. exact (prop_ext (fun h3 : term2 M i => @lem7670302 A M N u v i h1 h2) (fun h3 : (term257 A M N u v i) = (term277 A M N v i) => @lem7666144 M i h2)). Qed.
Lemma lem7670304 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (h1 : term298 M N i) (h2 : term2 M i) : (term257 A M N u v i) = (term277 A M N v i).
Proof. exact (EQ_MP (@lem7670303 A M N u v i h1 h2) (@lem7666144 M i h2)). Qed.
Lemma lem7670305 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (h1 : term297 M N i) (h2 : term2 M i) : (term298 M N i) = ((term257 A M N u v i) = (term277 A M N v i)).
Proof. exact (prop_ext (fun h3 : term298 M N i => @lem7670304 A M N u v i h3 h2) (fun h3 : (term257 A M N u v i) = (term277 A M N v i) => @lem7670299 M N i h1)). Qed.
Lemma lem7670306 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (h1 : term297 M N i) (h2 : term2 M i) : (term257 A M N u v i) = (term277 A M N v i).
Proof. exact (EQ_MP (@lem7670305 A M N u v i h1 h2) (@lem7670299 M N i h1)). Qed.
Lemma lem7670307 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (h1 : term297 M N i) : (term2 M i) = ((term257 A M N u v i) = (term277 A M N v i)).
Proof. exact (prop_ext (fun h2 : term2 M i => @lem7670306 A M N u v i h1 h2) (fun h2 : (term257 A M N u v i) = (term277 A M N v i) => @lem7670300 M N i h1)). Qed.
Lemma lem7670308 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) (h1 : term297 M N i) : (term257 A M N u v i) = (term277 A M N v i).
Proof. exact (EQ_MP (@lem7670307 A M N u v i h1) (@lem7670300 M N i h1)). Qed.
Lemma lem7670309 {A M N : Type'} (u : cart A M) (v : cart A N) (i : nat) : term280 A M N u v i.
Proof. exact (fun h0 : term297 M N i => @lem7670308 A M N u v i h0). Qed.
Lemma lem7670310 {M : Type'} (i : nat) (h1 : term295 M i) : term296 M i.
Proof. exact (proj2 (@lem7666139 M i h1)). Qed.
Lemma lem7670311 {M : Type'} (i : nat) (h1 : term295 M i) : term3 i.
Proof. exact (proj1 (@lem7666139 M i h1)). Qed.
Lemma lem7670312 {A M N : Type'} (v : cart A N) (u : cart A M) (i : nat) (h1 : term296 M i) (h2 : term3 i) : (term296 M i) = ((term257 A M N u v i) = (@dollar A M u i)).
Proof. exact (prop_ext (fun h3 : term296 M i => @lem7667743 A M N v u i h1 h2) (fun h3 : (term257 A M N u v i) = (@dollar A M u i) => @lem7666140 M i h1)). Qed.
Lemma lem7670313 {A M N : Type'} (v : cart A N) (u : cart A M) (i : nat) (h1 : term296 M i) (h2 : term3 i) : (term257 A M N u v i) = (@dollar A M u i).
Proof. exact (EQ_MP (@lem7670312 A M N v u i h1 h2) (@lem7666140 M i h1)). Qed.
Lemma lem7670314 {A M N : Type'} (v : cart A N) (u : cart A M) (i : nat) (h1 : term296 M i) (h2 : term3 i) : (term3 i) = ((term257 A M N u v i) = (@dollar A M u i)).
Proof. exact (prop_ext (fun h3 : term3 i => @lem7670313 A M N v u i h1 h2) (fun h3 : (term257 A M N u v i) = (@dollar A M u i) => @lem7666141 i h2)). Qed.
Lemma lem7670315 {A M N : Type'} (v : cart A N) (u : cart A M) (i : nat) (h1 : term296 M i) (h2 : term3 i) : (term257 A M N u v i) = (@dollar A M u i).
Proof. exact (EQ_MP (@lem7670314 A M N v u i h1 h2) (@lem7666141 i h2)). Qed.
Lemma lem7670316 {A M N : Type'} (v : cart A N) (u : cart A M) (i : nat) (h1 : term295 M i) (h2 : term3 i) : (term296 M i) = ((term257 A M N u v i) = (@dollar A M u i)).
Proof. exact (prop_ext (fun h3 : term296 M i => @lem7670315 A M N v u i h3 h2) (fun h3 : (term257 A M N u v i) = (@dollar A M u i) => @lem7670310 M i h1)). Qed.
Lemma lem7670317 {A M N : Type'} (v : cart A N) (u : cart A M) (i : nat) (h1 : term295 M i) (h2 : term3 i) : (term257 A M N u v i) = (@dollar A M u i).
Proof. exact (EQ_MP (@lem7670316 A M N v u i h1 h2) (@lem7670310 M i h1)). Qed.
Lemma lem7670318 {A M N : Type'} (v : cart A N) (u : cart A M) (i : nat) (h1 : term295 M i) : (term3 i) = ((term257 A M N u v i) = (@dollar A M u i)).
Proof. exact (prop_ext (fun h2 : term3 i => @lem7670317 A M N v u i h1 h2) (fun h2 : (term257 A M N u v i) = (@dollar A M u i) => @lem7670311 M i h1)). Qed.
Lemma lem7670319 {A M N : Type'} (v : cart A N) (u : cart A M) (i : nat) (h1 : term295 M i) : (term257 A M N u v i) = (@dollar A M u i).
Proof. exact (EQ_MP (@lem7670318 A M N v u i h1) (@lem7670311 M i h1)). Qed.
Lemma lem7670320 {A M N : Type'} (v : cart A N) (u : cart A M) (i : nat) : term262 A M N v u i.
Proof. exact (fun h0 : term295 M i => @lem7670319 A M N v u i h0). Qed.
Lemma lem7670325 {A M N : Type'} (u : cart A M) (v : cart A N) : term284 A M N u v.
Proof. exact (fun i : nat => @lem7670309 A M N u v i). Qed.
Lemma lem7670330 {A M N : Type'} (u : cart A M) : term288 A M N u.
Proof. exact (fun v : cart A N => @lem7670325 A M N u v). Qed.
Lemma lem7670335 {A M N : Type'} : term292 A M N.
Proof. exact (fun u : cart A M => @lem7670330 A M N u). Qed.
Lemma lem7670340 {A M N : Type'} (v : cart A N) (u : cart A M) : term266 A M N v u.
Proof. exact (fun i : nat => @lem7670320 A M N v u i). Qed.
Lemma lem7670345 {A M N : Type'} (u : cart A M) : term270 A M N u.
Proof. exact (fun v : cart A N => @lem7670340 A M N v u). Qed.
Lemma lem7670350 {A M N : Type'} : term274 A M N.
Proof. exact (fun u : cart A M => @lem7670345 A M N u). Qed.
Lemma lem7670351 {A M N : Type'} : term294 A M N.
Proof. exact (conj (@lem7670350 A M N) (@lem7670335 A M N)). Qed.
Lemma lem7670352 {A M N : Type'} : term293 A M N.
Proof. exact (EQ_MP (@lem7666138 A M N) (@lem7670351 A M N)). Qed.
