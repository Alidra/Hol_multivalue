Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_DIV_LT_EQ_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import DISJ_ACI_spec.
Require Import FORALL_INT_CASES_spec.
Require Import INT_DIVISION_spec.
Require Import INT_DIV_LNEG_spec.
Require Import INT_LE_DISCRETE_spec.
Require Import INT_LT_LMUL_EQ_spec.
Require Import INT_LT_SUB_RADD_spec.
Require Import INT_MUL_RNEG_spec.
Require Import INT_OF_NUM_DIV_spec.
Require Import INT_OF_NUM_EQ_spec.
Require Import INT_OF_NUM_LT_spec.
Require Import INT_OF_NUM_MUL_spec.
Require Import INT_REM_MUL_spec.
Require Import INT_SGN_spec.
Require Import LE_1_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import RDIV_LT_EQ_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm13473_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1396812_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17500_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1857_spec.
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
Require Import thm1982709_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982747_spec.
Require Import thm1982749_spec.
Require Import thm1982751_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988293_spec.
Require Import thm1988332_spec.
Require Import thm1988336_spec.
Require Import thm1988342_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm2318495_spec.
Require Import thm2318496_spec.
Require Import thm2318497_spec.
Require Import thm2318532_spec.
Require Import thm2318533_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318541_spec.
Require Import thm2318542_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318574_spec.
Require Import thm2318575_spec.
Require Import thm2318604_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Lemma lem2599948 (m : int) (n : int) (c : int) : (term0 m n c) = (((term1 m n c) = (term2 m n c)) = (term3 m n c)).
Proof. exact (@lem2318604 (((term1 m n c) = (term2 m n c)) = (term3 m n c))). Qed.
Lemma lem2599957 (m : int) (n : int) (c : int) : (term4 m n c) = (term5 m n c).
Proof. exact (@lem16933 (term5 m n c)). Qed.
Lemma lem2599958 (m : int) (n : int) (c : int) : (term6 m n c) = (term6 m n c).
Proof. exact (eq_refl (term6 m n c)). Qed.
Lemma lem2599959 (m : int) (n : int) (c : int) : (term2 m n c) = (term2 m n c).
Proof. exact (eq_refl (term2 m n c)). Qed.
Lemma lem2599960 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2599961 (m : int) (n : int) (c : int) : (term7 m n c) = (term8 m n c).
Proof. exact (MK_COMB (@lem2599960) (@lem2599957 m n c)). Qed.
Lemma lem2599962 (m : int) (n : int) (c : int) : (term9 m n c) = (term10 m n c).
Proof. exact (MK_COMB (@lem2599961 m n c) (@lem2599959 m n c)). Qed.
Lemma lem2599967 (m : int) (n : int) (c : int) : (term11 m n c) = (term11 m n c).
Proof. exact (eq_refl (term11 m n c)). Qed.
Lemma lem2599968 (m : int) (n : int) (c : int) : (term12 m n c) = (term13 m n c).
Proof. exact (MK_COMB (@lem2599967 m n c) (@lem2599962 m n c)). Qed.
Lemma lem2599969 (m : int) (n : int) (c : int) : (term14 m n c) = (term12 m n c).
Proof. exact (@lem17646 (term1 m n c) (term2 m n c)). Qed.
Lemma lem2599970 (m : int) (n : int) (c : int) : (term14 m n c) = (term13 m n c).
Proof. exact (TRANS (@lem2599969 m n c) (@lem2599968 m n c)). Qed.
Lemma lem2599971 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2599972 (m : int) (n : int) (c : int) : (term7 m n c) = (term8 m n c).
Proof. exact (MK_COMB (@lem2599971) (@lem2599957 m n c)). Qed.
Lemma lem2599973 (m : int) (n : int) (c : int) : (term15 m n c) = (term16 m n c).
Proof. exact (MK_COMB (@lem2599972 m n c) (@lem2599958 m n c)). Qed.
Lemma lem2599978 (m : int) (n : int) (c : int) : (term17 m n c) = (term17 m n c).
Proof. exact (eq_refl (term17 m n c)). Qed.
Lemma lem2599979 (m : int) (n : int) (c : int) : (term18 m n c) = (term19 m n c).
Proof. exact (MK_COMB (@lem2599978 m n c) (@lem2599973 m n c)). Qed.
Lemma lem2599980 (m : int) (n : int) (c : int) : ((term1 m n c) = (term2 m n c)) = (term18 m n c).
Proof. exact (@lem17500 (term1 m n c) (term2 m n c)). Qed.
Lemma lem2599981 (m : int) (n : int) (c : int) : ((term1 m n c) = (term2 m n c)) = (term19 m n c).
Proof. exact (TRANS (@lem2599980 m n c) (@lem2599979 m n c)). Qed.
Lemma lem2599982 (m : int) (n : int) (c : int) : (term3 m n c) = (term3 m n c).
Proof. exact (eq_refl (term3 m n c)). Qed.
Lemma lem2599985 (m : int) (n : int) (c : int) : (term20 m n c) = (m = (term21 n c)).
Proof. exact (@lem16933 (m = (term21 n c))). Qed.
Lemma lem2599986 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2599987 (m : int) (n : int) (c : int) : (term22 m n c) = (term23 m n c).
Proof. exact (MK_COMB (@lem2599986) (@lem2599970 m n c)). Qed.
Lemma lem2599988 (m : int) (n : int) (c : int) : (term24 m n c) = (term25 m n c).
Proof. exact (MK_COMB (@lem2599987 m n c) (@lem2599982 m n c)). Qed.
Lemma lem2599989 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2599990 (m : int) (n : int) (c : int) : (term26 m n c) = (term27 m n c).
Proof. exact (MK_COMB (@lem2599989) (@lem2599981 m n c)). Qed.
Lemma lem2599991 (m : int) (n : int) (c : int) : (term28 m n c) = (term29 m n c).
Proof. exact (MK_COMB (@lem2599990 m n c) (@lem2599985 m n c)). Qed.
Lemma lem2599992 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2599993 (m : int) (n : int) (c : int) : (term30 m n c) = (term31 m n c).
Proof. exact (MK_COMB (@lem2599992) (@lem2599991 m n c)). Qed.
Lemma lem2599994 (m : int) (n : int) (c : int) : (term32 m n c) = (term33 m n c).
Proof. exact (MK_COMB (@lem2599993 m n c) (@lem2599988 m n c)). Qed.
Lemma lem2599995 (m : int) (n : int) (c : int) : (term34 m n c) = (term32 m n c).
Proof. exact (@lem17646 ((term1 m n c) = (term2 m n c)) (term3 m n c)). Qed.
Lemma lem2600045 (m : int) (n : int) (c : int) : (term34 m n c) = (term33 m n c).
Proof. exact (TRANS (@lem2599995 m n c) (@lem2599994 m n c)). Qed.
Lemma lem2600047 (y : int) (x : int) : (term35 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem2600048 (n : int) (c : int) (m : int) : (term1 m n c) = (term36 n c m).
Proof. exact (@lem2600047 (term21 n c) m). Qed.
Lemma lem2600050 (x : int) (y : int) : (int_le x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2600051 (n : int) (c : int) (m : int) : (term36 n c m) = (term38 n c m).
Proof. exact (@lem2600050 (term21 n c) m). Qed.
Lemma lem2600053 (x : int) (y : int) : (term39 x y) = (term40 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2600054 (n : int) (c : int) : (term41 n c) = (term42 n c).
Proof. exact (@lem2600053 n (int_neg c)). Qed.
Lemma lem2600056 (x : int) : (term43 x) = (term44 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2600057 (c : int) : (term43 c) = (term44 c).
Proof. exact (@lem2600056 c). Qed.
Lemma lem2600058 (n : int) : (term45 n) = (term45 n).
Proof. exact (eq_refl (term45 n)). Qed.
Lemma lem2600059 (n : int) (c : int) : (term42 n c) = (term46 n c).
Proof. exact (MK_COMB (@lem2600058 n) (@lem2600057 c)). Qed.
Lemma lem2600060 (n : int) (c : int) : (term41 n c) = (term46 n c).
Proof. exact (TRANS (@lem2600054 n c) (@lem2600059 n c)). Qed.
Lemma lem2600061 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2600062 (n : int) (c : int) : (term47 n c) = (term48 n c).
Proof. exact (MK_COMB (@lem2600061) (@lem2600060 n c)). Qed.
Lemma lem2600063 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2600064 (n : int) (c : int) (m : int) : (term38 n c m) = (term49 n c m).
Proof. exact (MK_COMB (@lem2600062 n c) (@lem2600063 m)). Qed.
Lemma lem2600065 (n : int) (c : int) (m : int) : (term36 n c m) = (term49 n c m).
Proof. exact (TRANS (@lem2600051 n c m) (@lem2600064 n c m)). Qed.
Lemma lem2600066 (n : int) (c : int) (m : int) : (term1 m n c) = (term49 n c m).
Proof. exact (TRANS (@lem2600048 n c m) (@lem2600065 n c m)). Qed.
Lemma lem2600068 (x : int) (y : int) : (int_lt x y) = (term50 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem2600069 (m : int) (n : int) (c : int) : (term2 m n c) = (term51 m n c).
Proof. exact (@lem2600068 (int_neg m) (int_mul n c)). Qed.
Lemma lem2600071 (x : int) (y : int) : (int_le x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2600072 (m : int) (n : int) (c : int) : (term51 m n c) = (term52 m n c).
Proof. exact (@lem2600071 (term53 m) (int_mul n c)). Qed.
Lemma lem2600074 (x : int) (y : int) : (term54 x y) = (term55 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2600075 (m : int) : (term56 m) = (term57 m).
Proof. exact (@lem2600074 (int_neg m) term58). Qed.
Lemma lem2600077 (x : int) : (term43 x) = (term44 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2600078 (m : int) : (term43 m) = (term44 m).
Proof. exact (@lem2600077 m). Qed.
Lemma lem2600079 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2600080 (m : int) : (term59 m) = (term60 m).
Proof. exact (MK_COMB (@lem2600079) (@lem2600078 m)). Qed.
Lemma lem2600082 (n : nat) : (term61 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2600083 : term62 = term63.
Proof. exact (@lem2600082 term64). Qed.
Lemma lem2600084 (m : int) : (term57 m) = (term65 m).
Proof. exact (MK_COMB (@lem2600080 m) (@lem2600083)). Qed.
Lemma lem2600085 (m : int) : (term56 m) = (term65 m).
Proof. exact (TRANS (@lem2600075 m) (@lem2600084 m)). Qed.
Lemma lem2600086 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2600087 (m : int) : (term66 m) = (term67 m).
Proof. exact (MK_COMB (@lem2600086) (@lem2600085 m)). Qed.
Lemma lem2600089 (x : int) (y : int) : (term39 x y) = (term40 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2600090 (n : int) (c : int) : (term39 n c) = (term40 n c).
Proof. exact (@lem2600089 n c). Qed.
Lemma lem2600091 (m : int) (n : int) (c : int) : (term52 m n c) = (term68 m n c).
Proof. exact (MK_COMB (@lem2600087 m) (@lem2600090 n c)). Qed.
Lemma lem2600092 (m : int) (n : int) (c : int) : (term51 m n c) = (term68 m n c).
Proof. exact (TRANS (@lem2600072 m n c) (@lem2600091 m n c)). Qed.
Lemma lem2600093 (m : int) (n : int) (c : int) : (term2 m n c) = (term68 m n c).
Proof. exact (TRANS (@lem2600069 m n c) (@lem2600092 m n c)). Qed.
Lemma lem2600094 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2600095 (n : int) (c : int) (m : int) : (term69 m n c) = (term70 n c m).
Proof. exact (MK_COMB (@lem2600094) (@lem2600066 n c m)). Qed.
Lemma lem2600096 (m : int) (n : int) (c : int) : (term71 m n c) = (term72 m n c).
Proof. exact (MK_COMB (@lem2600095 n c m) (@lem2600093 m n c)). Qed.
Lemma lem2600098 (x : int) (y : int) : (int_lt x y) = (term50 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem2600099 (m : int) (n : int) (c : int) : (term5 m n c) = (term73 m n c).
Proof. exact (@lem2600098 m (term21 n c)). Qed.
Lemma lem2600101 (x : int) (y : int) : (int_le x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2600102 (m : int) (n : int) (c : int) : (term73 m n c) = (term74 m n c).
Proof. exact (@lem2600101 (term75 m) (term21 n c)). Qed.
Lemma lem2600104 (x : int) (y : int) : (term54 x y) = (term55 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2600105 (m : int) : (term76 m) = (term77 m).
Proof. exact (@lem2600104 m term58). Qed.
Lemma lem2600107 (n : nat) : (term61 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2600108 : term62 = term63.
Proof. exact (@lem2600107 term64). Qed.
Lemma lem2600109 (m : int) : (term78 m) = (term78 m).
Proof. exact (eq_refl (term78 m)). Qed.
Lemma lem2600110 (m : int) : (term77 m) = (term79 m).
Proof. exact (MK_COMB (@lem2600109 m) (@lem2600108)). Qed.
Lemma lem2600111 (m : int) : (term76 m) = (term79 m).
Proof. exact (TRANS (@lem2600105 m) (@lem2600110 m)). Qed.
Lemma lem2600112 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2600113 (m : int) : (term80 m) = (term81 m).
Proof. exact (MK_COMB (@lem2600112) (@lem2600111 m)). Qed.
Lemma lem2600115 (x : int) (y : int) : (term39 x y) = (term40 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2600116 (n : int) (c : int) : (term41 n c) = (term42 n c).
Proof. exact (@lem2600115 n (int_neg c)). Qed.
Lemma lem2600118 (x : int) : (term43 x) = (term44 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2600119 (c : int) : (term43 c) = (term44 c).
Proof. exact (@lem2600118 c). Qed.
Lemma lem2600120 (n : int) : (term45 n) = (term45 n).
Proof. exact (eq_refl (term45 n)). Qed.
Lemma lem2600121 (n : int) (c : int) : (term42 n c) = (term46 n c).
Proof. exact (MK_COMB (@lem2600120 n) (@lem2600119 c)). Qed.
Lemma lem2600122 (n : int) (c : int) : (term41 n c) = (term46 n c).
Proof. exact (TRANS (@lem2600116 n c) (@lem2600121 n c)). Qed.
Lemma lem2600123 (m : int) (n : int) (c : int) : (term74 m n c) = (term82 m n c).
Proof. exact (MK_COMB (@lem2600113 m) (@lem2600122 n c)). Qed.
Lemma lem2600124 (m : int) (n : int) (c : int) : (term73 m n c) = (term82 m n c).
Proof. exact (TRANS (@lem2600102 m n c) (@lem2600123 m n c)). Qed.
Lemma lem2600125 (m : int) (n : int) (c : int) : (term5 m n c) = (term82 m n c).
Proof. exact (TRANS (@lem2600099 m n c) (@lem2600124 m n c)). Qed.
Lemma lem2600127 (y : int) (x : int) : (term35 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem2600128 (n : int) (c : int) (m : int) : (term6 m n c) = (term83 n c m).
Proof. exact (@lem2600127 (int_mul n c) (int_neg m)). Qed.
Lemma lem2600130 (x : int) (y : int) : (int_le x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2600131 (n : int) (c : int) (m : int) : (term83 n c m) = (term84 n c m).
Proof. exact (@lem2600130 (int_mul n c) (int_neg m)). Qed.
Lemma lem2600133 (x : int) (y : int) : (term39 x y) = (term40 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2600134 (n : int) (c : int) : (term39 n c) = (term40 n c).
Proof. exact (@lem2600133 n c). Qed.
Lemma lem2600135 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2600136 (n : int) (c : int) : (term85 n c) = (term86 n c).
Proof. exact (MK_COMB (@lem2600135) (@lem2600134 n c)). Qed.
Lemma lem2600138 (x : int) : (term43 x) = (term44 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2600139 (m : int) : (term43 m) = (term44 m).
Proof. exact (@lem2600138 m). Qed.
Lemma lem2600140 (n : int) (c : int) (m : int) : (term84 n c m) = (term87 n c m).
Proof. exact (MK_COMB (@lem2600136 n c) (@lem2600139 m)). Qed.
Lemma lem2600141 (n : int) (c : int) (m : int) : (term83 n c m) = (term87 n c m).
Proof. exact (TRANS (@lem2600131 n c m) (@lem2600140 n c m)). Qed.
Lemma lem2600142 (n : int) (c : int) (m : int) : (term6 m n c) = (term87 n c m).
Proof. exact (TRANS (@lem2600128 n c m) (@lem2600141 n c m)). Qed.
Lemma lem2600143 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2600144 (m : int) (n : int) (c : int) : (term8 m n c) = (term88 m n c).
Proof. exact (MK_COMB (@lem2600143) (@lem2600125 m n c)). Qed.
Lemma lem2600145 (n : int) (c : int) (m : int) : (term16 m n c) = (term89 n c m).
Proof. exact (MK_COMB (@lem2600144 m n c) (@lem2600142 n c m)). Qed.
Lemma lem2600146 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2600147 (m : int) (n : int) (c : int) : (term17 m n c) = (term90 m n c).
Proof. exact (MK_COMB (@lem2600146) (@lem2600096 m n c)). Qed.
Lemma lem2600148 (n : int) (c : int) (m : int) : (term19 m n c) = (term91 n c m).
Proof. exact (MK_COMB (@lem2600147 m n c) (@lem2600145 n c m)). Qed.
Lemma lem2600151 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem2600152 (m : int) (n : int) (c : int) : (m = (term21 n c)) = ((real_of_int m) = (term41 n c)).
Proof. exact (@lem2600151 m (term21 n c)). Qed.
Lemma lem2600156 (x : int) (y : int) : (term39 x y) = (term40 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2600157 (n : int) (c : int) : (term41 n c) = (term42 n c).
Proof. exact (@lem2600156 n (int_neg c)). Qed.
Lemma lem2600159 (x : int) : (term43 x) = (term44 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2600160 (c : int) : (term43 c) = (term44 c).
Proof. exact (@lem2600159 c). Qed.
Lemma lem2600161 (n : int) : (term45 n) = (term45 n).
Proof. exact (eq_refl (term45 n)). Qed.
Lemma lem2600162 (n : int) (c : int) : (term42 n c) = (term46 n c).
Proof. exact (MK_COMB (@lem2600161 n) (@lem2600160 c)). Qed.
Lemma lem2600163 (n : int) (c : int) : (term41 n c) = (term46 n c).
Proof. exact (TRANS (@lem2600157 n c) (@lem2600162 n c)). Qed.
Lemma lem2600164 (m : int) : (term92 m) = (term92 m).
Proof. exact (eq_refl (term92 m)). Qed.
Lemma lem2600165 (m : int) (n : int) (c : int) : ((real_of_int m) = (term41 n c)) = ((real_of_int m) = (term46 n c)).
Proof. exact (MK_COMB (@lem2600164 m) (@lem2600163 n c)). Qed.
Lemma lem2600167 (m : int) (n : int) (c : int) : (m = (term21 n c)) = ((real_of_int m) = (term46 n c)).
Proof. exact (TRANS (@lem2600152 m n c) (@lem2600165 m n c)). Qed.
Lemma lem2600168 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2600169 (n : int) (c : int) (m : int) : (term27 m n c) = (term93 n c m).
Proof. exact (MK_COMB (@lem2600168) (@lem2600148 n c m)). Qed.
Lemma lem2600170 (m : int) (n : int) (c : int) : (term29 m n c) = (term94 m n c).
Proof. exact (MK_COMB (@lem2600169 n c m) (@lem2600167 m n c)). Qed.
Lemma lem2600172 (y : int) (x : int) : (term35 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem2600173 (n : int) (c : int) (m : int) : (term1 m n c) = (term36 n c m).
Proof. exact (@lem2600172 (term21 n c) m). Qed.
Lemma lem2600175 (x : int) (y : int) : (int_le x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2600176 (n : int) (c : int) (m : int) : (term36 n c m) = (term38 n c m).
Proof. exact (@lem2600175 (term21 n c) m). Qed.
Lemma lem2600178 (x : int) (y : int) : (term39 x y) = (term40 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2600179 (n : int) (c : int) : (term41 n c) = (term42 n c).
Proof. exact (@lem2600178 n (int_neg c)). Qed.
Lemma lem2600181 (x : int) : (term43 x) = (term44 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2600182 (c : int) : (term43 c) = (term44 c).
Proof. exact (@lem2600181 c). Qed.
Lemma lem2600183 (n : int) : (term45 n) = (term45 n).
Proof. exact (eq_refl (term45 n)). Qed.
Lemma lem2600184 (n : int) (c : int) : (term42 n c) = (term46 n c).
Proof. exact (MK_COMB (@lem2600183 n) (@lem2600182 c)). Qed.
Lemma lem2600185 (n : int) (c : int) : (term41 n c) = (term46 n c).
Proof. exact (TRANS (@lem2600179 n c) (@lem2600184 n c)). Qed.
Lemma lem2600186 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2600187 (n : int) (c : int) : (term47 n c) = (term48 n c).
Proof. exact (MK_COMB (@lem2600186) (@lem2600185 n c)). Qed.
Lemma lem2600188 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2600189 (n : int) (c : int) (m : int) : (term38 n c m) = (term49 n c m).
Proof. exact (MK_COMB (@lem2600187 n c) (@lem2600188 m)). Qed.
Lemma lem2600190 (n : int) (c : int) (m : int) : (term36 n c m) = (term49 n c m).
Proof. exact (TRANS (@lem2600176 n c m) (@lem2600189 n c m)). Qed.
Lemma lem2600191 (n : int) (c : int) (m : int) : (term1 m n c) = (term49 n c m).
Proof. exact (TRANS (@lem2600173 n c m) (@lem2600190 n c m)). Qed.
Lemma lem2600193 (y : int) (x : int) : (term35 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem2600194 (n : int) (c : int) (m : int) : (term6 m n c) = (term83 n c m).
Proof. exact (@lem2600193 (int_mul n c) (int_neg m)). Qed.
Lemma lem2600196 (x : int) (y : int) : (int_le x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2600197 (n : int) (c : int) (m : int) : (term83 n c m) = (term84 n c m).
Proof. exact (@lem2600196 (int_mul n c) (int_neg m)). Qed.
Lemma lem2600199 (x : int) (y : int) : (term39 x y) = (term40 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2600200 (n : int) (c : int) : (term39 n c) = (term40 n c).
Proof. exact (@lem2600199 n c). Qed.
Lemma lem2600201 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2600202 (n : int) (c : int) : (term85 n c) = (term86 n c).
Proof. exact (MK_COMB (@lem2600201) (@lem2600200 n c)). Qed.
Lemma lem2600204 (x : int) : (term43 x) = (term44 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2600205 (m : int) : (term43 m) = (term44 m).
Proof. exact (@lem2600204 m). Qed.
Lemma lem2600206 (n : int) (c : int) (m : int) : (term84 n c m) = (term87 n c m).
Proof. exact (MK_COMB (@lem2600202 n c) (@lem2600205 m)). Qed.
Lemma lem2600207 (n : int) (c : int) (m : int) : (term83 n c m) = (term87 n c m).
Proof. exact (TRANS (@lem2600197 n c m) (@lem2600206 n c m)). Qed.
Lemma lem2600208 (n : int) (c : int) (m : int) : (term6 m n c) = (term87 n c m).
Proof. exact (TRANS (@lem2600194 n c m) (@lem2600207 n c m)). Qed.
Lemma lem2600209 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2600210 (n : int) (c : int) (m : int) : (term69 m n c) = (term70 n c m).
Proof. exact (MK_COMB (@lem2600209) (@lem2600191 n c m)). Qed.
Lemma lem2600211 (n : int) (c : int) (m : int) : (term95 m n c) = (term96 n c m).
Proof. exact (MK_COMB (@lem2600210 n c m) (@lem2600208 n c m)). Qed.
Lemma lem2600213 (x : int) (y : int) : (int_lt x y) = (term50 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem2600214 (m : int) (n : int) (c : int) : (term5 m n c) = (term73 m n c).
Proof. exact (@lem2600213 m (term21 n c)). Qed.
Lemma lem2600216 (x : int) (y : int) : (int_le x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2600217 (m : int) (n : int) (c : int) : (term73 m n c) = (term74 m n c).
Proof. exact (@lem2600216 (term75 m) (term21 n c)). Qed.
Lemma lem2600219 (x : int) (y : int) : (term54 x y) = (term55 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2600220 (m : int) : (term76 m) = (term77 m).
Proof. exact (@lem2600219 m term58). Qed.
Lemma lem2600222 (n : nat) : (term61 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2600223 : term62 = term63.
Proof. exact (@lem2600222 term64). Qed.
Lemma lem2600224 (m : int) : (term78 m) = (term78 m).
Proof. exact (eq_refl (term78 m)). Qed.
Lemma lem2600225 (m : int) : (term77 m) = (term79 m).
Proof. exact (MK_COMB (@lem2600224 m) (@lem2600223)). Qed.
Lemma lem2600226 (m : int) : (term76 m) = (term79 m).
Proof. exact (TRANS (@lem2600220 m) (@lem2600225 m)). Qed.
Lemma lem2600227 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2600228 (m : int) : (term80 m) = (term81 m).
Proof. exact (MK_COMB (@lem2600227) (@lem2600226 m)). Qed.
Lemma lem2600230 (x : int) (y : int) : (term39 x y) = (term40 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2600231 (n : int) (c : int) : (term41 n c) = (term42 n c).
Proof. exact (@lem2600230 n (int_neg c)). Qed.
Lemma lem2600233 (x : int) : (term43 x) = (term44 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2600234 (c : int) : (term43 c) = (term44 c).
Proof. exact (@lem2600233 c). Qed.
Lemma lem2600235 (n : int) : (term45 n) = (term45 n).
Proof. exact (eq_refl (term45 n)). Qed.
Lemma lem2600236 (n : int) (c : int) : (term42 n c) = (term46 n c).
Proof. exact (MK_COMB (@lem2600235 n) (@lem2600234 c)). Qed.
Lemma lem2600237 (n : int) (c : int) : (term41 n c) = (term46 n c).
Proof. exact (TRANS (@lem2600231 n c) (@lem2600236 n c)). Qed.
Lemma lem2600238 (m : int) (n : int) (c : int) : (term74 m n c) = (term82 m n c).
Proof. exact (MK_COMB (@lem2600228 m) (@lem2600237 n c)). Qed.
Lemma lem2600239 (m : int) (n : int) (c : int) : (term73 m n c) = (term82 m n c).
Proof. exact (TRANS (@lem2600217 m n c) (@lem2600238 m n c)). Qed.
Lemma lem2600240 (m : int) (n : int) (c : int) : (term5 m n c) = (term82 m n c).
Proof. exact (TRANS (@lem2600214 m n c) (@lem2600239 m n c)). Qed.
Lemma lem2600242 (x : int) (y : int) : (int_lt x y) = (term50 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem2600243 (m : int) (n : int) (c : int) : (term2 m n c) = (term51 m n c).
Proof. exact (@lem2600242 (int_neg m) (int_mul n c)). Qed.
Lemma lem2600245 (x : int) (y : int) : (int_le x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2600246 (m : int) (n : int) (c : int) : (term51 m n c) = (term52 m n c).
Proof. exact (@lem2600245 (term53 m) (int_mul n c)). Qed.
Lemma lem2600248 (x : int) (y : int) : (term54 x y) = (term55 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2600249 (m : int) : (term56 m) = (term57 m).
Proof. exact (@lem2600248 (int_neg m) term58). Qed.
Lemma lem2600251 (x : int) : (term43 x) = (term44 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2600252 (m : int) : (term43 m) = (term44 m).
Proof. exact (@lem2600251 m). Qed.
Lemma lem2600253 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2600254 (m : int) : (term59 m) = (term60 m).
Proof. exact (MK_COMB (@lem2600253) (@lem2600252 m)). Qed.
Lemma lem2600256 (n : nat) : (term61 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2600257 : term62 = term63.
Proof. exact (@lem2600256 term64). Qed.
Lemma lem2600258 (m : int) : (term57 m) = (term65 m).
Proof. exact (MK_COMB (@lem2600254 m) (@lem2600257)). Qed.
Lemma lem2600259 (m : int) : (term56 m) = (term65 m).
Proof. exact (TRANS (@lem2600249 m) (@lem2600258 m)). Qed.
Lemma lem2600260 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2600261 (m : int) : (term66 m) = (term67 m).
Proof. exact (MK_COMB (@lem2600260) (@lem2600259 m)). Qed.
Lemma lem2600263 (x : int) (y : int) : (term39 x y) = (term40 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2600264 (n : int) (c : int) : (term39 n c) = (term40 n c).
Proof. exact (@lem2600263 n c). Qed.
Lemma lem2600265 (m : int) (n : int) (c : int) : (term52 m n c) = (term68 m n c).
Proof. exact (MK_COMB (@lem2600261 m) (@lem2600264 n c)). Qed.
Lemma lem2600266 (m : int) (n : int) (c : int) : (term51 m n c) = (term68 m n c).
Proof. exact (TRANS (@lem2600246 m n c) (@lem2600265 m n c)). Qed.
Lemma lem2600267 (m : int) (n : int) (c : int) : (term2 m n c) = (term68 m n c).
Proof. exact (TRANS (@lem2600243 m n c) (@lem2600266 m n c)). Qed.
Lemma lem2600268 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2600269 (m : int) (n : int) (c : int) : (term8 m n c) = (term88 m n c).
Proof. exact (MK_COMB (@lem2600268) (@lem2600240 m n c)). Qed.
Lemma lem2600270 (m : int) (n : int) (c : int) : (term10 m n c) = (term97 m n c).
Proof. exact (MK_COMB (@lem2600269 m n c) (@lem2600267 m n c)). Qed.
Lemma lem2600271 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2600272 (n : int) (c : int) (m : int) : (term11 m n c) = (term98 n c m).
Proof. exact (MK_COMB (@lem2600271) (@lem2600211 n c m)). Qed.
Lemma lem2600273 (m : int) (n : int) (c : int) : (term13 m n c) = (term99 m n c).
Proof. exact (MK_COMB (@lem2600272 n c m) (@lem2600270 m n c)). Qed.
Lemma lem2600275 (y : int) (x : int) : (term100 x y) = (term101 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2600276 (n : int) (c : int) (m : int) : (term3 m n c) = (term102 n c m).
Proof. exact (@lem2600275 (term21 n c) m). Qed.
Lemma lem2600278 (x : int) (y : int) : (int_le x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2600279 (m : int) (n : int) (c : int) : (term73 m n c) = (term74 m n c).
Proof. exact (@lem2600278 (term75 m) (term21 n c)). Qed.
Lemma lem2600281 (x : int) (y : int) : (term54 x y) = (term55 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2600282 (m : int) : (term76 m) = (term77 m).
Proof. exact (@lem2600281 m term58). Qed.
Lemma lem2600284 (n : nat) : (term61 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2600285 : term62 = term63.
Proof. exact (@lem2600284 term64). Qed.
Lemma lem2600286 (m : int) : (term78 m) = (term78 m).
Proof. exact (eq_refl (term78 m)). Qed.
Lemma lem2600287 (m : int) : (term77 m) = (term79 m).
Proof. exact (MK_COMB (@lem2600286 m) (@lem2600285)). Qed.
Lemma lem2600288 (m : int) : (term76 m) = (term79 m).
Proof. exact (TRANS (@lem2600282 m) (@lem2600287 m)). Qed.
Lemma lem2600289 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2600290 (m : int) : (term80 m) = (term81 m).
Proof. exact (MK_COMB (@lem2600289) (@lem2600288 m)). Qed.
Lemma lem2600292 (x : int) (y : int) : (term39 x y) = (term40 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2600293 (n : int) (c : int) : (term41 n c) = (term42 n c).
Proof. exact (@lem2600292 n (int_neg c)). Qed.
Lemma lem2600295 (x : int) : (term43 x) = (term44 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2600296 (c : int) : (term43 c) = (term44 c).
Proof. exact (@lem2600295 c). Qed.
Lemma lem2600297 (n : int) : (term45 n) = (term45 n).
Proof. exact (eq_refl (term45 n)). Qed.
Lemma lem2600298 (n : int) (c : int) : (term42 n c) = (term46 n c).
Proof. exact (MK_COMB (@lem2600297 n) (@lem2600296 c)). Qed.
Lemma lem2600299 (n : int) (c : int) : (term41 n c) = (term46 n c).
Proof. exact (TRANS (@lem2600293 n c) (@lem2600298 n c)). Qed.
Lemma lem2600300 (m : int) (n : int) (c : int) : (term74 m n c) = (term82 m n c).
Proof. exact (MK_COMB (@lem2600290 m) (@lem2600299 n c)). Qed.
Lemma lem2600301 (m : int) (n : int) (c : int) : (term73 m n c) = (term82 m n c).
Proof. exact (TRANS (@lem2600279 m n c) (@lem2600300 m n c)). Qed.
Lemma lem2600302 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2600303 (m : int) (n : int) (c : int) : (term103 m n c) = (term104 m n c).
Proof. exact (MK_COMB (@lem2600302) (@lem2600301 m n c)). Qed.
Lemma lem2600305 (x : int) (y : int) : (int_le x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2600306 (n : int) (c : int) (m : int) : (term105 n c m) = (term106 n c m).
Proof. exact (@lem2600305 (term107 n c) m). Qed.
Lemma lem2600308 (x : int) (y : int) : (term54 x y) = (term55 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2600309 (n : int) (c : int) : (term108 n c) = (term109 n c).
Proof. exact (@lem2600308 (term21 n c) term58). Qed.
Lemma lem2600311 (x : int) (y : int) : (term39 x y) = (term40 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2600312 (n : int) (c : int) : (term41 n c) = (term42 n c).
Proof. exact (@lem2600311 n (int_neg c)). Qed.
Lemma lem2600314 (x : int) : (term43 x) = (term44 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2600315 (c : int) : (term43 c) = (term44 c).
Proof. exact (@lem2600314 c). Qed.
Lemma lem2600316 (n : int) : (term45 n) = (term45 n).
Proof. exact (eq_refl (term45 n)). Qed.
Lemma lem2600317 (n : int) (c : int) : (term42 n c) = (term46 n c).
Proof. exact (MK_COMB (@lem2600316 n) (@lem2600315 c)). Qed.
Lemma lem2600318 (n : int) (c : int) : (term41 n c) = (term46 n c).
Proof. exact (TRANS (@lem2600312 n c) (@lem2600317 n c)). Qed.
Lemma lem2600319 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2600320 (n : int) (c : int) : (term110 n c) = (term111 n c).
Proof. exact (MK_COMB (@lem2600319) (@lem2600318 n c)). Qed.
Lemma lem2600322 (n : nat) : (term61 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2600323 : term62 = term63.
Proof. exact (@lem2600322 term64). Qed.
Lemma lem2600324 (n : int) (c : int) : (term109 n c) = (term112 n c).
Proof. exact (MK_COMB (@lem2600320 n c) (@lem2600323)). Qed.
Lemma lem2600325 (n : int) (c : int) : (term108 n c) = (term112 n c).
Proof. exact (TRANS (@lem2600309 n c) (@lem2600324 n c)). Qed.
Lemma lem2600326 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2600327 (n : int) (c : int) : (term113 n c) = (term114 n c).
Proof. exact (MK_COMB (@lem2600326) (@lem2600325 n c)). Qed.
Lemma lem2600328 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2600329 (n : int) (c : int) (m : int) : (term106 n c m) = (term115 n c m).
Proof. exact (MK_COMB (@lem2600327 n c) (@lem2600328 m)). Qed.
Lemma lem2600330 (n : int) (c : int) (m : int) : (term105 n c m) = (term115 n c m).
Proof. exact (TRANS (@lem2600306 n c m) (@lem2600329 n c m)). Qed.
Lemma lem2600331 (n : int) (c : int) (m : int) : (term102 n c m) = (term116 n c m).
Proof. exact (MK_COMB (@lem2600303 m n c) (@lem2600330 n c m)). Qed.
Lemma lem2600332 (n : int) (c : int) (m : int) : (term3 m n c) = (term116 n c m).
Proof. exact (TRANS (@lem2600276 n c m) (@lem2600331 n c m)). Qed.
Lemma lem2600333 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2600334 (m : int) (n : int) (c : int) : (term23 m n c) = (term117 m n c).
Proof. exact (MK_COMB (@lem2600333) (@lem2600273 m n c)). Qed.
Lemma lem2600335 (n : int) (c : int) (m : int) : (term25 m n c) = (term118 n c m).
Proof. exact (MK_COMB (@lem2600334 m n c) (@lem2600332 n c m)). Qed.
Lemma lem2600336 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2600337 (m : int) (n : int) (c : int) : (term31 m n c) = (term119 m n c).
Proof. exact (MK_COMB (@lem2600336) (@lem2600170 m n c)). Qed.
Lemma lem2600338 (n : int) (c : int) (m : int) : (term33 m n c) = (term120 n c m).
Proof. exact (MK_COMB (@lem2600337 m n c) (@lem2600335 n c m)). Qed.
Lemma lem2600339 (n : int) (c : int) (m : int) : (term34 m n c) = (term120 n c m).
Proof. exact (TRANS (@lem2600045 m n c) (@lem2600338 n c m)). Qed.
Lemma lem2600343 (t : Prop) : (term121 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2600449 (n : int) (c : int) (m : int) : (term122 n c m) = (term120 n c m).
Proof. exact (@lem2600343 (term120 n c m)). Qed.
Lemma lem2600450 (m : int) (n : int) (c : int) : (term49 n c m) = (term123 m n c).
Proof. exact (@lem1988287 (real_of_int m) (term46 n c)). Qed.
Lemma lem2600457 (c : int) : (term44 c) = (term124 c).
Proof. exact (@lem1982785 (real_of_int c)). Qed.
Lemma lem2600460 (n : int) : (term45 n) = (term45 n).
Proof. exact (eq_refl (term45 n)). Qed.
Lemma lem2600461 (n : int) (c : int) : (term46 n c) = (term125 n c).
Proof. exact (MK_COMB (@lem2600460 n) (@lem2600457 c)). Qed.
Lemma lem2600462 (n : int) (c : int) : (term125 n c) = (term126 n c).
Proof. exact (@lem1982751 term127 (real_of_int n) (real_of_int c)). Qed.
Lemma lem2600463 (c : int) (n : int) : (term40 n c) = (term40 c n).
Proof. exact (@lem1982747 (real_of_int c) (real_of_int n)). Qed.
Lemma lem2600464 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem2600465 (c : int) (n : int) : (term126 n c) = (term126 c n).
Proof. exact (MK_COMB (@lem2600464) (@lem2600463 c n)). Qed.
Lemma lem2600466 (c : int) (n : int) : (term125 n c) = (term126 c n).
Proof. exact (TRANS (@lem2600462 n c) (@lem2600465 c n)). Qed.
Lemma lem2600467 (c : int) (n : int) : (term46 n c) = (term126 c n).
Proof. exact (TRANS (@lem2600461 n c) (@lem2600466 c n)). Qed.
Lemma lem2600470 (m : int) : (term129 m) = (term129 m).
Proof. exact (eq_refl (term129 m)). Qed.
Lemma lem2600471 (m : int) (c : int) (n : int) : (term130 m n c) = (term131 m c n).
Proof. exact (MK_COMB (@lem2600470 m) (@lem2600467 c n)). Qed.
Lemma lem2600472 (m : int) (c : int) (n : int) : (term131 m c n) = (term132 m c n).
Proof. exact (@lem1982792 (real_of_int m) (term126 c n)). Qed.
Lemma lem2600473 (c : int) (n : int) : (term133 c n) = (term134 c n).
Proof. exact (@lem1982749 term127 term127 (term40 c n)). Qed.
Lemma lem2600475 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2600476 : term127 = term137.
Proof. exact (@lem2600475 term64). Qed.
Lemma lem2600478 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2600479 : term127 = term137.
Proof. exact (@lem2600478 term64). Qed.
Lemma lem2600480 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2600481 : term128 = term138.
Proof. exact (MK_COMB (@lem2600480) (@lem2600479)). Qed.
Lemma lem2600482 : term139 = term140.
Proof. exact (MK_COMB (@lem2600481) (@lem2600476)). Qed.
Lemma lem2600483 : term140 = term141.
Proof. exact (@lem1981613 term127 term127 term63 term63). Qed.
Lemma lem2600485 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2600486 : term144 = term145.
Proof. exact (@lem2600485 term64 term64). Qed.
Lemma lem2600487 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2600488 : term147 = term64.
Proof. exact (EQ_MP (@lem2600487) (@lem940073)). Qed.
Lemma lem2600489 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2600490 : term145 = term63.
Proof. exact (MK_COMB (@lem2600489) (@lem2600488)). Qed.
Lemma lem2600491 : term144 = term63.
Proof. exact (TRANS (@lem2600486) (@lem2600490)). Qed.
Lemma lem2600493 (m : nat) (n : nat) : (term148 m n) = (term143 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2600494 : term139 = term145.
Proof. exact (@lem2600493 term64 term64). Qed.
Lemma lem2600495 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2600496 : term147 = term64.
Proof. exact (EQ_MP (@lem2600495) (@lem940073)). Qed.
Lemma lem2600497 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2600498 : term145 = term63.
Proof. exact (MK_COMB (@lem2600497) (@lem2600496)). Qed.
Lemma lem2600499 : term139 = term63.
Proof. exact (TRANS (@lem2600494) (@lem2600498)). Qed.
Lemma lem2600500 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2600501 : term149 = term150.
Proof. exact (MK_COMB (@lem2600500) (@lem2600499)). Qed.
Lemma lem2600502 : term141 = term151.
Proof. exact (MK_COMB (@lem2600501) (@lem2600491)). Qed.
Lemma lem2600503 : term140 = term151.
Proof. exact (TRANS (@lem2600483) (@lem2600502)). Qed.
Lemma lem2600504 : term139 = term151.
Proof. exact (TRANS (@lem2600482) (@lem2600503)). Qed.
Lemma lem2600506 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2600507 : term151 = term63.
Proof. exact (@lem2600506 term63). Qed.
Lemma lem2600508 : term139 = term63.
Proof. exact (TRANS (@lem2600504) (@lem2600507)). Qed.
Lemma lem2600509 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2600510 : term153 = term154.
Proof. exact (MK_COMB (@lem2600509) (@lem2600508)). Qed.
Lemma lem2600511 (c : int) (n : int) : (term40 c n) = (term40 c n).
Proof. exact (eq_refl (term40 c n)). Qed.
Lemma lem2600512 (c : int) (n : int) : (term134 c n) = (term155 c n).
Proof. exact (MK_COMB (@lem2600510) (@lem2600511 c n)). Qed.
Lemma lem2600513 (c : int) (n : int) : (term133 c n) = (term155 c n).
Proof. exact (TRANS (@lem2600473 c n) (@lem2600512 c n)). Qed.
Lemma lem2600514 (c : int) (n : int) : (term155 c n) = (term40 c n).
Proof. exact (@lem1982709 (term40 c n)). Qed.
Lemma lem2600515 (c : int) (n : int) : (term133 c n) = (term40 c n).
Proof. exact (TRANS (@lem2600513 c n) (@lem2600514 c n)). Qed.
Lemma lem2600516 (m : int) : (term78 m) = (term78 m).
Proof. exact (eq_refl (term78 m)). Qed.
Lemma lem2600517 (m : int) (c : int) (n : int) : (term132 m c n) = (term156 m c n).
Proof. exact (MK_COMB (@lem2600516 m) (@lem2600515 c n)). Qed.
Lemma lem2600518 (c : int) (n : int) (m : int) : (term156 m c n) = (term157 c n m).
Proof. exact (@lem1982761 (term40 c n) (real_of_int m)). Qed.
Lemma lem2600519 (c : int) (n : int) (m : int) : (term132 m c n) = (term157 c n m).
Proof. exact (TRANS (@lem2600517 m c n) (@lem2600518 c n m)). Qed.
Lemma lem2600520 (c : int) (n : int) (m : int) : (term131 m c n) = (term157 c n m).
Proof. exact (TRANS (@lem2600472 m c n) (@lem2600519 c n m)). Qed.
Lemma lem2600521 (c : int) (n : int) (m : int) : (term130 m n c) = (term157 c n m).
Proof. exact (TRANS (@lem2600471 m c n) (@lem2600520 c n m)). Qed.
Lemma lem2600522 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2600523 (c : int) (n : int) (m : int) : (term158 m n c) = (term159 c n m).
Proof. exact (MK_COMB (@lem2600522) (@lem2600521 c n m)). Qed.
Lemma lem2600524 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2600525 (c : int) (n : int) (m : int) : (term123 m n c) = (term161 c n m).
Proof. exact (MK_COMB (@lem2600523 c n m) (@lem2600524)). Qed.
Lemma lem2600526 (c : int) (n : int) (m : int) : (term49 n c m) = (term161 c n m).
Proof. exact (TRANS (@lem2600450 m n c) (@lem2600525 c n m)). Qed.
Lemma lem2600527 (n : int) (c : int) (m : int) : (term68 m n c) = (term162 n c m).
Proof. exact (@lem1988287 (term40 n c) (term65 m)). Qed.
Lemma lem2600528 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2600535 (m : int) : (term44 m) = (term124 m).
Proof. exact (@lem1982785 (real_of_int m)). Qed.
Lemma lem2600536 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2600537 (m : int) : (term60 m) = (term163 m).
Proof. exact (MK_COMB (@lem2600536) (@lem2600535 m)). Qed.
Lemma lem2600540 (m : int) : (term65 m) = (term164 m).
Proof. exact (MK_COMB (@lem2600537 m) (@lem2600528)). Qed.
Lemma lem2600547 (c : int) (n : int) : (term40 n c) = (term40 c n).
Proof. exact (@lem1982747 (real_of_int c) (real_of_int n)). Qed.
Lemma lem2600548 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2600549 (c : int) (n : int) : (term165 n c) = (term165 c n).
Proof. exact (MK_COMB (@lem2600548) (@lem2600547 c n)). Qed.
Lemma lem2600550 (c : int) (n : int) (m : int) : (term166 n c m) = (term167 c n m).
Proof. exact (MK_COMB (@lem2600549 c n) (@lem2600540 m)). Qed.
Lemma lem2600551 (c : int) (n : int) (m : int) : (term167 c n m) = (term168 c n m).
Proof. exact (@lem1982792 (term40 c n) (term164 m)). Qed.
Lemma lem2600552 (m : int) : (term169 m) = (term170 m).
Proof. exact (@lem1982781 (term124 m) term127 term63). Qed.
Lemma lem2600554 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2600555 : term63 = term151.
Proof. exact (@lem2600554 term64). Qed.
Lemma lem2600557 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2600558 : term127 = term137.
Proof. exact (@lem2600557 term64). Qed.
Lemma lem2600559 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2600560 : term128 = term138.
Proof. exact (MK_COMB (@lem2600559) (@lem2600558)). Qed.
Lemma lem2600561 : term172 = term173.
Proof. exact (MK_COMB (@lem2600560) (@lem2600555)). Qed.
Lemma lem2600562 : term173 = term174.
Proof. exact (@lem1981613 term127 term63 term63 term63). Qed.
Lemma lem2600564 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2600565 : term144 = term145.
Proof. exact (@lem2600564 term64 term64). Qed.
Lemma lem2600566 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2600567 : term147 = term64.
Proof. exact (EQ_MP (@lem2600566) (@lem940073)). Qed.
Lemma lem2600568 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2600569 : term145 = term63.
Proof. exact (MK_COMB (@lem2600568) (@lem2600567)). Qed.
Lemma lem2600570 : term144 = term63.
Proof. exact (TRANS (@lem2600565) (@lem2600569)). Qed.
Lemma lem2600572 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2600573 : term172 = term177.
Proof. exact (@lem2600572 term64 term64). Qed.
Lemma lem2600574 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2600575 : term147 = term64.
Proof. exact (EQ_MP (@lem2600574) (@lem940073)). Qed.
Lemma lem2600576 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2600577 : term145 = term63.
Proof. exact (MK_COMB (@lem2600576) (@lem2600575)). Qed.
Lemma lem2600578 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2600579 : term177 = term127.
Proof. exact (MK_COMB (@lem2600578) (@lem2600577)). Qed.
Lemma lem2600580 : term172 = term127.
Proof. exact (TRANS (@lem2600573) (@lem2600579)). Qed.
Lemma lem2600581 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2600582 : term178 = term179.
Proof. exact (MK_COMB (@lem2600581) (@lem2600580)). Qed.
Lemma lem2600583 : term174 = term137.
Proof. exact (MK_COMB (@lem2600582) (@lem2600570)). Qed.
Lemma lem2600584 : term173 = term137.
Proof. exact (TRANS (@lem2600562) (@lem2600583)). Qed.
Lemma lem2600585 : term172 = term137.
Proof. exact (TRANS (@lem2600561) (@lem2600584)). Qed.
Lemma lem2600587 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2600588 : term137 = term127.
Proof. exact (@lem2600587 term127). Qed.
Lemma lem2600589 : term172 = term127.
Proof. exact (TRANS (@lem2600585) (@lem2600588)). Qed.
Lemma lem2600590 (m : int) : (term180 m) = (term181 m).
Proof. exact (@lem1982749 term127 term127 (real_of_int m)). Qed.
Lemma lem2600592 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2600593 : term127 = term137.
Proof. exact (@lem2600592 term64). Qed.
Lemma lem2600595 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2600596 : term127 = term137.
Proof. exact (@lem2600595 term64). Qed.
Lemma lem2600597 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2600598 : term128 = term138.
Proof. exact (MK_COMB (@lem2600597) (@lem2600596)). Qed.
Lemma lem2600599 : term139 = term140.
Proof. exact (MK_COMB (@lem2600598) (@lem2600593)). Qed.
Lemma lem2600600 : term140 = term141.
Proof. exact (@lem1981613 term127 term127 term63 term63). Qed.
Lemma lem2600602 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2600603 : term144 = term145.
Proof. exact (@lem2600602 term64 term64). Qed.
Lemma lem2600604 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2600605 : term147 = term64.
Proof. exact (EQ_MP (@lem2600604) (@lem940073)). Qed.
Lemma lem2600606 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2600607 : term145 = term63.
Proof. exact (MK_COMB (@lem2600606) (@lem2600605)). Qed.
Lemma lem2600608 : term144 = term63.
Proof. exact (TRANS (@lem2600603) (@lem2600607)). Qed.
Lemma lem2600610 (m : nat) (n : nat) : (term148 m n) = (term143 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2600611 : term139 = term145.
Proof. exact (@lem2600610 term64 term64). Qed.
Lemma lem2600612 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2600613 : term147 = term64.
Proof. exact (EQ_MP (@lem2600612) (@lem940073)). Qed.
Lemma lem2600614 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2600615 : term145 = term63.
Proof. exact (MK_COMB (@lem2600614) (@lem2600613)). Qed.
Lemma lem2600616 : term139 = term63.
Proof. exact (TRANS (@lem2600611) (@lem2600615)). Qed.
Lemma lem2600617 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2600618 : term149 = term150.
Proof. exact (MK_COMB (@lem2600617) (@lem2600616)). Qed.
Lemma lem2600619 : term141 = term151.
Proof. exact (MK_COMB (@lem2600618) (@lem2600608)). Qed.
Lemma lem2600620 : term140 = term151.
Proof. exact (TRANS (@lem2600600) (@lem2600619)). Qed.
Lemma lem2600621 : term139 = term151.
Proof. exact (TRANS (@lem2600599) (@lem2600620)). Qed.
Lemma lem2600623 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2600624 : term151 = term63.
Proof. exact (@lem2600623 term63). Qed.
Lemma lem2600625 : term139 = term63.
Proof. exact (TRANS (@lem2600621) (@lem2600624)). Qed.
Lemma lem2600626 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2600627 : term153 = term154.
Proof. exact (MK_COMB (@lem2600626) (@lem2600625)). Qed.
Lemma lem2600628 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2600629 (m : int) : (term181 m) = (term182 m).
Proof. exact (MK_COMB (@lem2600627) (@lem2600628 m)). Qed.
Lemma lem2600630 (m : int) : (term180 m) = (term182 m).
Proof. exact (TRANS (@lem2600590 m) (@lem2600629 m)). Qed.
Lemma lem2600631 (m : int) : (term182 m) = (real_of_int m).
Proof. exact (@lem1982709 (real_of_int m)). Qed.
Lemma lem2600632 (m : int) : (term180 m) = (real_of_int m).
Proof. exact (TRANS (@lem2600630 m) (@lem2600631 m)). Qed.
Lemma lem2600633 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2600634 (m : int) : (term183 m) = (term78 m).
Proof. exact (MK_COMB (@lem2600633) (@lem2600632 m)). Qed.
Lemma lem2600635 (m : int) : (term170 m) = (term184 m).
Proof. exact (MK_COMB (@lem2600634 m) (@lem2600589)). Qed.
Lemma lem2600636 (m : int) : (term169 m) = (term184 m).
Proof. exact (TRANS (@lem2600552 m) (@lem2600635 m)). Qed.
Lemma lem2600637 (c : int) (n : int) : (term185 c n) = (term185 c n).
Proof. exact (eq_refl (term185 c n)). Qed.
Lemma lem2600640 (c : int) (n : int) (m : int) : (term168 c n m) = (term186 c n m).
Proof. exact (MK_COMB (@lem2600637 c n) (@lem2600636 m)). Qed.
Lemma lem2600641 (c : int) (n : int) (m : int) : (term167 c n m) = (term186 c n m).
Proof. exact (TRANS (@lem2600551 c n m) (@lem2600640 c n m)). Qed.
Lemma lem2600642 (c : int) (n : int) (m : int) : (term166 n c m) = (term186 c n m).
Proof. exact (TRANS (@lem2600550 c n m) (@lem2600641 c n m)). Qed.
Lemma lem2600643 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2600644 (c : int) (n : int) (m : int) : (term187 n c m) = (term188 c n m).
Proof. exact (MK_COMB (@lem2600643) (@lem2600642 c n m)). Qed.
Lemma lem2600645 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2600646 (c : int) (n : int) (m : int) : (term162 n c m) = (term189 c n m).
Proof. exact (MK_COMB (@lem2600644 c n m) (@lem2600645)). Qed.
Lemma lem2600647 (c : int) (n : int) (m : int) : (term68 m n c) = (term189 c n m).
Proof. exact (TRANS (@lem2600527 n c m) (@lem2600646 c n m)). Qed.
Lemma lem2600648 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2600649 (c : int) (n : int) (m : int) : (term70 n c m) = (term190 c n m).
Proof. exact (MK_COMB (@lem2600648) (@lem2600526 c n m)). Qed.
Lemma lem2600650 (c : int) (n : int) (m : int) : (term72 m n c) = (term191 c n m).
Proof. exact (MK_COMB (@lem2600649 c n m) (@lem2600647 c n m)). Qed.
Lemma lem2600651 (n : int) (c : int) (m : int) : (term82 m n c) = (term192 n c m).
Proof. exact (@lem1988287 (term46 n c) (term79 m)). Qed.
Lemma lem2600658 (m : int) : (term79 m) = (term79 m).
Proof. exact (eq_refl (term79 m)). Qed.
Lemma lem2600665 (c : int) : (term44 c) = (term124 c).
Proof. exact (@lem1982785 (real_of_int c)). Qed.
Lemma lem2600668 (n : int) : (term45 n) = (term45 n).
Proof. exact (eq_refl (term45 n)). Qed.
Lemma lem2600669 (n : int) (c : int) : (term46 n c) = (term125 n c).
Proof. exact (MK_COMB (@lem2600668 n) (@lem2600665 c)). Qed.
Lemma lem2600670 (n : int) (c : int) : (term125 n c) = (term126 n c).
Proof. exact (@lem1982751 term127 (real_of_int n) (real_of_int c)). Qed.
Lemma lem2600671 (c : int) (n : int) : (term40 n c) = (term40 c n).
Proof. exact (@lem1982747 (real_of_int c) (real_of_int n)). Qed.
Lemma lem2600672 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem2600673 (c : int) (n : int) : (term126 n c) = (term126 c n).
Proof. exact (MK_COMB (@lem2600672) (@lem2600671 c n)). Qed.
Lemma lem2600674 (c : int) (n : int) : (term125 n c) = (term126 c n).
Proof. exact (TRANS (@lem2600670 n c) (@lem2600673 c n)). Qed.
Lemma lem2600675 (c : int) (n : int) : (term46 n c) = (term126 c n).
Proof. exact (TRANS (@lem2600669 n c) (@lem2600674 c n)). Qed.
Lemma lem2600676 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2600677 (c : int) (n : int) : (term193 n c) = (term194 c n).
Proof. exact (MK_COMB (@lem2600676) (@lem2600675 c n)). Qed.
Lemma lem2600678 (c : int) (n : int) (m : int) : (term195 n c m) = (term196 c n m).
Proof. exact (MK_COMB (@lem2600677 c n) (@lem2600658 m)). Qed.
Lemma lem2600679 (c : int) (n : int) (m : int) : (term196 c n m) = (term197 c n m).
Proof. exact (@lem1982792 (term126 c n) (term79 m)). Qed.
Lemma lem2600680 (m : int) : (term198 m) = (term199 m).
Proof. exact (@lem1982781 (real_of_int m) term127 term63). Qed.
Lemma lem2600682 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2600683 : term63 = term151.
Proof. exact (@lem2600682 term64). Qed.
Lemma lem2600685 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2600686 : term127 = term137.
Proof. exact (@lem2600685 term64). Qed.
Lemma lem2600687 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2600688 : term128 = term138.
Proof. exact (MK_COMB (@lem2600687) (@lem2600686)). Qed.
Lemma lem2600689 : term172 = term173.
Proof. exact (MK_COMB (@lem2600688) (@lem2600683)). Qed.
Lemma lem2600690 : term173 = term174.
Proof. exact (@lem1981613 term127 term63 term63 term63). Qed.
Lemma lem2600692 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2600693 : term144 = term145.
Proof. exact (@lem2600692 term64 term64). Qed.
Lemma lem2600694 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2600695 : term147 = term64.
Proof. exact (EQ_MP (@lem2600694) (@lem940073)). Qed.
Lemma lem2600696 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2600697 : term145 = term63.
Proof. exact (MK_COMB (@lem2600696) (@lem2600695)). Qed.
Lemma lem2600698 : term144 = term63.
Proof. exact (TRANS (@lem2600693) (@lem2600697)). Qed.
Lemma lem2600700 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2600701 : term172 = term177.
Proof. exact (@lem2600700 term64 term64). Qed.
Lemma lem2600702 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2600703 : term147 = term64.
Proof. exact (EQ_MP (@lem2600702) (@lem940073)). Qed.
Lemma lem2600704 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2600705 : term145 = term63.
Proof. exact (MK_COMB (@lem2600704) (@lem2600703)). Qed.
Lemma lem2600706 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2600707 : term177 = term127.
Proof. exact (MK_COMB (@lem2600706) (@lem2600705)). Qed.
Lemma lem2600708 : term172 = term127.
Proof. exact (TRANS (@lem2600701) (@lem2600707)). Qed.
Lemma lem2600709 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2600710 : term178 = term179.
Proof. exact (MK_COMB (@lem2600709) (@lem2600708)). Qed.
Lemma lem2600711 : term174 = term137.
Proof. exact (MK_COMB (@lem2600710) (@lem2600698)). Qed.
Lemma lem2600712 : term173 = term137.
Proof. exact (TRANS (@lem2600690) (@lem2600711)). Qed.
Lemma lem2600713 : term172 = term137.
Proof. exact (TRANS (@lem2600689) (@lem2600712)). Qed.
Lemma lem2600715 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2600716 : term137 = term127.
Proof. exact (@lem2600715 term127). Qed.
Lemma lem2600717 : term172 = term127.
Proof. exact (TRANS (@lem2600713) (@lem2600716)). Qed.
Lemma lem2600720 (m : int) : (term163 m) = (term163 m).
Proof. exact (eq_refl (term163 m)). Qed.
Lemma lem2600721 (m : int) : (term199 m) = (term200 m).
Proof. exact (MK_COMB (@lem2600720 m) (@lem2600717)). Qed.
Lemma lem2600722 (m : int) : (term198 m) = (term200 m).
Proof. exact (TRANS (@lem2600680 m) (@lem2600721 m)). Qed.
Lemma lem2600723 (c : int) (n : int) : (term201 c n) = (term201 c n).
Proof. exact (eq_refl (term201 c n)). Qed.
Lemma lem2600726 (c : int) (n : int) (m : int) : (term197 c n m) = (term202 c n m).
Proof. exact (MK_COMB (@lem2600723 c n) (@lem2600722 m)). Qed.
Lemma lem2600727 (c : int) (n : int) (m : int) : (term196 c n m) = (term202 c n m).
Proof. exact (TRANS (@lem2600679 c n m) (@lem2600726 c n m)). Qed.
Lemma lem2600728 (c : int) (n : int) (m : int) : (term195 n c m) = (term202 c n m).
Proof. exact (TRANS (@lem2600678 c n m) (@lem2600727 c n m)). Qed.
Lemma lem2600729 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2600730 (c : int) (n : int) (m : int) : (term203 n c m) = (term204 c n m).
Proof. exact (MK_COMB (@lem2600729) (@lem2600728 c n m)). Qed.
Lemma lem2600731 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2600732 (c : int) (n : int) (m : int) : (term192 n c m) = (term205 c n m).
Proof. exact (MK_COMB (@lem2600730 c n m) (@lem2600731)). Qed.
Lemma lem2600733 (c : int) (n : int) (m : int) : (term82 m n c) = (term205 c n m).
Proof. exact (TRANS (@lem2600651 n c m) (@lem2600732 c n m)). Qed.
Lemma lem2600734 (m : int) (n : int) (c : int) : (term87 n c m) = (term206 m n c).
Proof. exact (@lem1988287 (term44 m) (term40 n c)). Qed.
Lemma lem2600741 (c : int) (n : int) : (term40 n c) = (term40 c n).
Proof. exact (@lem1982747 (real_of_int c) (real_of_int n)). Qed.
Lemma lem2600748 (m : int) : (term44 m) = (term124 m).
Proof. exact (@lem1982785 (real_of_int m)). Qed.
Lemma lem2600749 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2600750 (m : int) : (term207 m) = (term208 m).
Proof. exact (MK_COMB (@lem2600749) (@lem2600748 m)). Qed.
Lemma lem2600751 (m : int) (c : int) (n : int) : (term209 m n c) = (term210 m c n).
Proof. exact (MK_COMB (@lem2600750 m) (@lem2600741 c n)). Qed.
Lemma lem2600752 (m : int) (c : int) (n : int) : (term210 m c n) = (term211 m c n).
Proof. exact (@lem1982792 (term124 m) (term40 c n)). Qed.
Lemma lem2600757 (c : int) (n : int) (m : int) : (term211 m c n) = (term212 c n m).
Proof. exact (@lem1982761 (term126 c n) (term124 m)). Qed.
Lemma lem2600758 (c : int) (n : int) (m : int) : (term210 m c n) = (term212 c n m).
Proof. exact (TRANS (@lem2600752 m c n) (@lem2600757 c n m)). Qed.
Lemma lem2600759 (c : int) (n : int) (m : int) : (term209 m n c) = (term212 c n m).
Proof. exact (TRANS (@lem2600751 m c n) (@lem2600758 c n m)). Qed.
Lemma lem2600760 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2600761 (c : int) (n : int) (m : int) : (term213 m n c) = (term214 c n m).
Proof. exact (MK_COMB (@lem2600760) (@lem2600759 c n m)). Qed.
Lemma lem2600762 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2600763 (c : int) (n : int) (m : int) : (term206 m n c) = (term215 c n m).
Proof. exact (MK_COMB (@lem2600761 c n m) (@lem2600762)). Qed.
Lemma lem2600764 (c : int) (n : int) (m : int) : (term87 n c m) = (term215 c n m).
Proof. exact (TRANS (@lem2600734 m n c) (@lem2600763 c n m)). Qed.
Lemma lem2600765 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2600766 (c : int) (n : int) (m : int) : (term88 m n c) = (term216 c n m).
Proof. exact (MK_COMB (@lem2600765) (@lem2600733 c n m)). Qed.
Lemma lem2600767 (c : int) (n : int) (m : int) : (term89 n c m) = (term217 c n m).
Proof. exact (MK_COMB (@lem2600766 c n m) (@lem2600764 c n m)). Qed.
Lemma lem2600768 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2600769 (c : int) (n : int) (m : int) : (term90 m n c) = (term218 c n m).
Proof. exact (MK_COMB (@lem2600768) (@lem2600650 c n m)). Qed.
Lemma lem2600770 (c : int) (n : int) (m : int) : (term91 n c m) = (term219 c n m).
Proof. exact (MK_COMB (@lem2600769 c n m) (@lem2600767 c n m)). Qed.
Lemma lem2600771 (m : int) (n : int) (c : int) : ((real_of_int m) = (term46 n c)) = ((term130 m n c) = term160).
Proof. exact (@lem1988293 (real_of_int m) (term46 n c)). Qed.
Lemma lem2600778 (c : int) : (term44 c) = (term124 c).
Proof. exact (@lem1982785 (real_of_int c)). Qed.
Lemma lem2600781 (n : int) : (term45 n) = (term45 n).
Proof. exact (eq_refl (term45 n)). Qed.
Lemma lem2600782 (n : int) (c : int) : (term46 n c) = (term125 n c).
Proof. exact (MK_COMB (@lem2600781 n) (@lem2600778 c)). Qed.
Lemma lem2600783 (n : int) (c : int) : (term125 n c) = (term126 n c).
Proof. exact (@lem1982751 term127 (real_of_int n) (real_of_int c)). Qed.
Lemma lem2600784 (c : int) (n : int) : (term40 n c) = (term40 c n).
Proof. exact (@lem1982747 (real_of_int c) (real_of_int n)). Qed.
Lemma lem2600785 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem2600786 (c : int) (n : int) : (term126 n c) = (term126 c n).
Proof. exact (MK_COMB (@lem2600785) (@lem2600784 c n)). Qed.
Lemma lem2600787 (c : int) (n : int) : (term125 n c) = (term126 c n).
Proof. exact (TRANS (@lem2600783 n c) (@lem2600786 c n)). Qed.
Lemma lem2600788 (c : int) (n : int) : (term46 n c) = (term126 c n).
Proof. exact (TRANS (@lem2600782 n c) (@lem2600787 c n)). Qed.
Lemma lem2600791 (m : int) : (term129 m) = (term129 m).
Proof. exact (eq_refl (term129 m)). Qed.
Lemma lem2600792 (m : int) (c : int) (n : int) : (term130 m n c) = (term131 m c n).
Proof. exact (MK_COMB (@lem2600791 m) (@lem2600788 c n)). Qed.
Lemma lem2600793 (m : int) (c : int) (n : int) : (term131 m c n) = (term132 m c n).
Proof. exact (@lem1982792 (real_of_int m) (term126 c n)). Qed.
Lemma lem2600794 (c : int) (n : int) : (term133 c n) = (term134 c n).
Proof. exact (@lem1982749 term127 term127 (term40 c n)). Qed.
Lemma lem2600796 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2600797 : term127 = term137.
Proof. exact (@lem2600796 term64). Qed.
Lemma lem2600799 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2600800 : term127 = term137.
Proof. exact (@lem2600799 term64). Qed.
Lemma lem2600801 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2600802 : term128 = term138.
Proof. exact (MK_COMB (@lem2600801) (@lem2600800)). Qed.
Lemma lem2600803 : term139 = term140.
Proof. exact (MK_COMB (@lem2600802) (@lem2600797)). Qed.
Lemma lem2600804 : term140 = term141.
Proof. exact (@lem1981613 term127 term127 term63 term63). Qed.
Lemma lem2600806 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2600807 : term144 = term145.
Proof. exact (@lem2600806 term64 term64). Qed.
Lemma lem2600808 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2600809 : term147 = term64.
Proof. exact (EQ_MP (@lem2600808) (@lem940073)). Qed.
Lemma lem2600810 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2600811 : term145 = term63.
Proof. exact (MK_COMB (@lem2600810) (@lem2600809)). Qed.
Lemma lem2600812 : term144 = term63.
Proof. exact (TRANS (@lem2600807) (@lem2600811)). Qed.
Lemma lem2600814 (m : nat) (n : nat) : (term148 m n) = (term143 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2600815 : term139 = term145.
Proof. exact (@lem2600814 term64 term64). Qed.
Lemma lem2600816 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2600817 : term147 = term64.
Proof. exact (EQ_MP (@lem2600816) (@lem940073)). Qed.
Lemma lem2600818 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2600819 : term145 = term63.
Proof. exact (MK_COMB (@lem2600818) (@lem2600817)). Qed.
Lemma lem2600820 : term139 = term63.
Proof. exact (TRANS (@lem2600815) (@lem2600819)). Qed.
Lemma lem2600821 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2600822 : term149 = term150.
Proof. exact (MK_COMB (@lem2600821) (@lem2600820)). Qed.
Lemma lem2600823 : term141 = term151.
Proof. exact (MK_COMB (@lem2600822) (@lem2600812)). Qed.
Lemma lem2600824 : term140 = term151.
Proof. exact (TRANS (@lem2600804) (@lem2600823)). Qed.
Lemma lem2600825 : term139 = term151.
Proof. exact (TRANS (@lem2600803) (@lem2600824)). Qed.
Lemma lem2600827 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2600828 : term151 = term63.
Proof. exact (@lem2600827 term63). Qed.
Lemma lem2600829 : term139 = term63.
Proof. exact (TRANS (@lem2600825) (@lem2600828)). Qed.
Lemma lem2600830 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2600831 : term153 = term154.
Proof. exact (MK_COMB (@lem2600830) (@lem2600829)). Qed.
Lemma lem2600832 (c : int) (n : int) : (term40 c n) = (term40 c n).
Proof. exact (eq_refl (term40 c n)). Qed.
Lemma lem2600833 (c : int) (n : int) : (term134 c n) = (term155 c n).
Proof. exact (MK_COMB (@lem2600831) (@lem2600832 c n)). Qed.
Lemma lem2600834 (c : int) (n : int) : (term133 c n) = (term155 c n).
Proof. exact (TRANS (@lem2600794 c n) (@lem2600833 c n)). Qed.
Lemma lem2600835 (c : int) (n : int) : (term155 c n) = (term40 c n).
Proof. exact (@lem1982709 (term40 c n)). Qed.
Lemma lem2600836 (c : int) (n : int) : (term133 c n) = (term40 c n).
Proof. exact (TRANS (@lem2600834 c n) (@lem2600835 c n)). Qed.
Lemma lem2600837 (m : int) : (term78 m) = (term78 m).
Proof. exact (eq_refl (term78 m)). Qed.
Lemma lem2600838 (m : int) (c : int) (n : int) : (term132 m c n) = (term156 m c n).
Proof. exact (MK_COMB (@lem2600837 m) (@lem2600836 c n)). Qed.
Lemma lem2600839 (c : int) (n : int) (m : int) : (term156 m c n) = (term157 c n m).
Proof. exact (@lem1982761 (term40 c n) (real_of_int m)). Qed.
Lemma lem2600840 (c : int) (n : int) (m : int) : (term132 m c n) = (term157 c n m).
Proof. exact (TRANS (@lem2600838 m c n) (@lem2600839 c n m)). Qed.
Lemma lem2600841 (c : int) (n : int) (m : int) : (term131 m c n) = (term157 c n m).
Proof. exact (TRANS (@lem2600793 m c n) (@lem2600840 c n m)). Qed.
Lemma lem2600842 (c : int) (n : int) (m : int) : (term130 m n c) = (term157 c n m).
Proof. exact (TRANS (@lem2600792 m c n) (@lem2600841 c n m)). Qed.
Lemma lem2600843 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2600844 (c : int) (n : int) (m : int) : (term220 m n c) = (term221 c n m).
Proof. exact (MK_COMB (@lem2600843) (@lem2600842 c n m)). Qed.
Lemma lem2600845 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2600846 (c : int) (n : int) (m : int) : ((term130 m n c) = term160) = ((term157 c n m) = term160).
Proof. exact (MK_COMB (@lem2600844 c n m) (@lem2600845)). Qed.
Lemma lem2600847 (c : int) (n : int) (m : int) : ((real_of_int m) = (term46 n c)) = ((term157 c n m) = term160).
Proof. exact (TRANS (@lem2600771 m n c) (@lem2600846 c n m)). Qed.
Lemma lem2600848 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2600849 (c : int) (n : int) (m : int) : (term93 n c m) = (term222 c n m).
Proof. exact (MK_COMB (@lem2600848) (@lem2600770 c n m)). Qed.
Lemma lem2600850 (c : int) (n : int) (m : int) : (term94 m n c) = (term223 c n m).
Proof. exact (MK_COMB (@lem2600849 c n m) (@lem2600847 c n m)). Qed.
Lemma lem2600851 (m : int) (n : int) (c : int) : (term49 n c m) = (term123 m n c).
Proof. exact (@lem1988287 (real_of_int m) (term46 n c)). Qed.
Lemma lem2600858 (c : int) : (term44 c) = (term124 c).
Proof. exact (@lem1982785 (real_of_int c)). Qed.
Lemma lem2600861 (n : int) : (term45 n) = (term45 n).
Proof. exact (eq_refl (term45 n)). Qed.
Lemma lem2600862 (n : int) (c : int) : (term46 n c) = (term125 n c).
Proof. exact (MK_COMB (@lem2600861 n) (@lem2600858 c)). Qed.
Lemma lem2600863 (n : int) (c : int) : (term125 n c) = (term126 n c).
Proof. exact (@lem1982751 term127 (real_of_int n) (real_of_int c)). Qed.
Lemma lem2600864 (c : int) (n : int) : (term40 n c) = (term40 c n).
Proof. exact (@lem1982747 (real_of_int c) (real_of_int n)). Qed.
Lemma lem2600865 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem2600866 (c : int) (n : int) : (term126 n c) = (term126 c n).
Proof. exact (MK_COMB (@lem2600865) (@lem2600864 c n)). Qed.
Lemma lem2600867 (c : int) (n : int) : (term125 n c) = (term126 c n).
Proof. exact (TRANS (@lem2600863 n c) (@lem2600866 c n)). Qed.
Lemma lem2600868 (c : int) (n : int) : (term46 n c) = (term126 c n).
Proof. exact (TRANS (@lem2600862 n c) (@lem2600867 c n)). Qed.
Lemma lem2600871 (m : int) : (term129 m) = (term129 m).
Proof. exact (eq_refl (term129 m)). Qed.
Lemma lem2600872 (m : int) (c : int) (n : int) : (term130 m n c) = (term131 m c n).
Proof. exact (MK_COMB (@lem2600871 m) (@lem2600868 c n)). Qed.
Lemma lem2600873 (m : int) (c : int) (n : int) : (term131 m c n) = (term132 m c n).
Proof. exact (@lem1982792 (real_of_int m) (term126 c n)). Qed.
Lemma lem2600874 (c : int) (n : int) : (term133 c n) = (term134 c n).
Proof. exact (@lem1982749 term127 term127 (term40 c n)). Qed.
Lemma lem2600876 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2600877 : term127 = term137.
Proof. exact (@lem2600876 term64). Qed.
Lemma lem2600879 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2600880 : term127 = term137.
Proof. exact (@lem2600879 term64). Qed.
Lemma lem2600881 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2600882 : term128 = term138.
Proof. exact (MK_COMB (@lem2600881) (@lem2600880)). Qed.
Lemma lem2600883 : term139 = term140.
Proof. exact (MK_COMB (@lem2600882) (@lem2600877)). Qed.
Lemma lem2600884 : term140 = term141.
Proof. exact (@lem1981613 term127 term127 term63 term63). Qed.
Lemma lem2600886 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2600887 : term144 = term145.
Proof. exact (@lem2600886 term64 term64). Qed.
Lemma lem2600888 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2600889 : term147 = term64.
Proof. exact (EQ_MP (@lem2600888) (@lem940073)). Qed.
Lemma lem2600890 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2600891 : term145 = term63.
Proof. exact (MK_COMB (@lem2600890) (@lem2600889)). Qed.
Lemma lem2600892 : term144 = term63.
Proof. exact (TRANS (@lem2600887) (@lem2600891)). Qed.
Lemma lem2600894 (m : nat) (n : nat) : (term148 m n) = (term143 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2600895 : term139 = term145.
Proof. exact (@lem2600894 term64 term64). Qed.
Lemma lem2600896 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2600897 : term147 = term64.
Proof. exact (EQ_MP (@lem2600896) (@lem940073)). Qed.
Lemma lem2600898 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2600899 : term145 = term63.
Proof. exact (MK_COMB (@lem2600898) (@lem2600897)). Qed.
Lemma lem2600900 : term139 = term63.
Proof. exact (TRANS (@lem2600895) (@lem2600899)). Qed.
Lemma lem2600901 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2600902 : term149 = term150.
Proof. exact (MK_COMB (@lem2600901) (@lem2600900)). Qed.
Lemma lem2600903 : term141 = term151.
Proof. exact (MK_COMB (@lem2600902) (@lem2600892)). Qed.
Lemma lem2600904 : term140 = term151.
Proof. exact (TRANS (@lem2600884) (@lem2600903)). Qed.
Lemma lem2600905 : term139 = term151.
Proof. exact (TRANS (@lem2600883) (@lem2600904)). Qed.
Lemma lem2600907 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2600908 : term151 = term63.
Proof. exact (@lem2600907 term63). Qed.
Lemma lem2600909 : term139 = term63.
Proof. exact (TRANS (@lem2600905) (@lem2600908)). Qed.
Lemma lem2600910 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2600911 : term153 = term154.
Proof. exact (MK_COMB (@lem2600910) (@lem2600909)). Qed.
Lemma lem2600912 (c : int) (n : int) : (term40 c n) = (term40 c n).
Proof. exact (eq_refl (term40 c n)). Qed.
Lemma lem2600913 (c : int) (n : int) : (term134 c n) = (term155 c n).
Proof. exact (MK_COMB (@lem2600911) (@lem2600912 c n)). Qed.
Lemma lem2600914 (c : int) (n : int) : (term133 c n) = (term155 c n).
Proof. exact (TRANS (@lem2600874 c n) (@lem2600913 c n)). Qed.
Lemma lem2600915 (c : int) (n : int) : (term155 c n) = (term40 c n).
Proof. exact (@lem1982709 (term40 c n)). Qed.
Lemma lem2600916 (c : int) (n : int) : (term133 c n) = (term40 c n).
Proof. exact (TRANS (@lem2600914 c n) (@lem2600915 c n)). Qed.
Lemma lem2600917 (m : int) : (term78 m) = (term78 m).
Proof. exact (eq_refl (term78 m)). Qed.
Lemma lem2600918 (m : int) (c : int) (n : int) : (term132 m c n) = (term156 m c n).
Proof. exact (MK_COMB (@lem2600917 m) (@lem2600916 c n)). Qed.
Lemma lem2600919 (c : int) (n : int) (m : int) : (term156 m c n) = (term157 c n m).
Proof. exact (@lem1982761 (term40 c n) (real_of_int m)). Qed.
Lemma lem2600920 (c : int) (n : int) (m : int) : (term132 m c n) = (term157 c n m).
Proof. exact (TRANS (@lem2600918 m c n) (@lem2600919 c n m)). Qed.
Lemma lem2600921 (c : int) (n : int) (m : int) : (term131 m c n) = (term157 c n m).
Proof. exact (TRANS (@lem2600873 m c n) (@lem2600920 c n m)). Qed.
Lemma lem2600922 (c : int) (n : int) (m : int) : (term130 m n c) = (term157 c n m).
Proof. exact (TRANS (@lem2600872 m c n) (@lem2600921 c n m)). Qed.
Lemma lem2600923 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2600924 (c : int) (n : int) (m : int) : (term158 m n c) = (term159 c n m).
Proof. exact (MK_COMB (@lem2600923) (@lem2600922 c n m)). Qed.
Lemma lem2600925 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2600926 (c : int) (n : int) (m : int) : (term123 m n c) = (term161 c n m).
Proof. exact (MK_COMB (@lem2600924 c n m) (@lem2600925)). Qed.
Lemma lem2600927 (c : int) (n : int) (m : int) : (term49 n c m) = (term161 c n m).
Proof. exact (TRANS (@lem2600851 m n c) (@lem2600926 c n m)). Qed.
Lemma lem2600928 (m : int) (n : int) (c : int) : (term87 n c m) = (term206 m n c).
Proof. exact (@lem1988287 (term44 m) (term40 n c)). Qed.
Lemma lem2600935 (c : int) (n : int) : (term40 n c) = (term40 c n).
Proof. exact (@lem1982747 (real_of_int c) (real_of_int n)). Qed.
Lemma lem2600942 (m : int) : (term44 m) = (term124 m).
Proof. exact (@lem1982785 (real_of_int m)). Qed.
Lemma lem2600943 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2600944 (m : int) : (term207 m) = (term208 m).
Proof. exact (MK_COMB (@lem2600943) (@lem2600942 m)). Qed.
Lemma lem2600945 (m : int) (c : int) (n : int) : (term209 m n c) = (term210 m c n).
Proof. exact (MK_COMB (@lem2600944 m) (@lem2600935 c n)). Qed.
Lemma lem2600946 (m : int) (c : int) (n : int) : (term210 m c n) = (term211 m c n).
Proof. exact (@lem1982792 (term124 m) (term40 c n)). Qed.
Lemma lem2600951 (c : int) (n : int) (m : int) : (term211 m c n) = (term212 c n m).
Proof. exact (@lem1982761 (term126 c n) (term124 m)). Qed.
Lemma lem2600952 (c : int) (n : int) (m : int) : (term210 m c n) = (term212 c n m).
Proof. exact (TRANS (@lem2600946 m c n) (@lem2600951 c n m)). Qed.
Lemma lem2600953 (c : int) (n : int) (m : int) : (term209 m n c) = (term212 c n m).
Proof. exact (TRANS (@lem2600945 m c n) (@lem2600952 c n m)). Qed.
Lemma lem2600954 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2600955 (c : int) (n : int) (m : int) : (term213 m n c) = (term214 c n m).
Proof. exact (MK_COMB (@lem2600954) (@lem2600953 c n m)). Qed.
Lemma lem2600956 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2600957 (c : int) (n : int) (m : int) : (term206 m n c) = (term215 c n m).
Proof. exact (MK_COMB (@lem2600955 c n m) (@lem2600956)). Qed.
Lemma lem2600958 (c : int) (n : int) (m : int) : (term87 n c m) = (term215 c n m).
Proof. exact (TRANS (@lem2600928 m n c) (@lem2600957 c n m)). Qed.
Lemma lem2600959 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2600960 (c : int) (n : int) (m : int) : (term70 n c m) = (term190 c n m).
Proof. exact (MK_COMB (@lem2600959) (@lem2600927 c n m)). Qed.
Lemma lem2600961 (c : int) (n : int) (m : int) : (term96 n c m) = (term224 c n m).
Proof. exact (MK_COMB (@lem2600960 c n m) (@lem2600958 c n m)). Qed.
Lemma lem2600962 (n : int) (c : int) (m : int) : (term82 m n c) = (term192 n c m).
Proof. exact (@lem1988287 (term46 n c) (term79 m)). Qed.
Lemma lem2600969 (m : int) : (term79 m) = (term79 m).
Proof. exact (eq_refl (term79 m)). Qed.
Lemma lem2600976 (c : int) : (term44 c) = (term124 c).
Proof. exact (@lem1982785 (real_of_int c)). Qed.
Lemma lem2600979 (n : int) : (term45 n) = (term45 n).
Proof. exact (eq_refl (term45 n)). Qed.
Lemma lem2600980 (n : int) (c : int) : (term46 n c) = (term125 n c).
Proof. exact (MK_COMB (@lem2600979 n) (@lem2600976 c)). Qed.
Lemma lem2600981 (n : int) (c : int) : (term125 n c) = (term126 n c).
Proof. exact (@lem1982751 term127 (real_of_int n) (real_of_int c)). Qed.
Lemma lem2600982 (c : int) (n : int) : (term40 n c) = (term40 c n).
Proof. exact (@lem1982747 (real_of_int c) (real_of_int n)). Qed.
Lemma lem2600983 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem2600984 (c : int) (n : int) : (term126 n c) = (term126 c n).
Proof. exact (MK_COMB (@lem2600983) (@lem2600982 c n)). Qed.
Lemma lem2600985 (c : int) (n : int) : (term125 n c) = (term126 c n).
Proof. exact (TRANS (@lem2600981 n c) (@lem2600984 c n)). Qed.
Lemma lem2600986 (c : int) (n : int) : (term46 n c) = (term126 c n).
Proof. exact (TRANS (@lem2600980 n c) (@lem2600985 c n)). Qed.
Lemma lem2600987 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2600988 (c : int) (n : int) : (term193 n c) = (term194 c n).
Proof. exact (MK_COMB (@lem2600987) (@lem2600986 c n)). Qed.
Lemma lem2600989 (c : int) (n : int) (m : int) : (term195 n c m) = (term196 c n m).
Proof. exact (MK_COMB (@lem2600988 c n) (@lem2600969 m)). Qed.
Lemma lem2600990 (c : int) (n : int) (m : int) : (term196 c n m) = (term197 c n m).
Proof. exact (@lem1982792 (term126 c n) (term79 m)). Qed.
Lemma lem2600991 (m : int) : (term198 m) = (term199 m).
Proof. exact (@lem1982781 (real_of_int m) term127 term63). Qed.
Lemma lem2600993 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2600994 : term63 = term151.
Proof. exact (@lem2600993 term64). Qed.
Lemma lem2600996 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2600997 : term127 = term137.
Proof. exact (@lem2600996 term64). Qed.
Lemma lem2600998 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2600999 : term128 = term138.
Proof. exact (MK_COMB (@lem2600998) (@lem2600997)). Qed.
Lemma lem2601000 : term172 = term173.
Proof. exact (MK_COMB (@lem2600999) (@lem2600994)). Qed.
Lemma lem2601001 : term173 = term174.
Proof. exact (@lem1981613 term127 term63 term63 term63). Qed.
Lemma lem2601003 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2601004 : term144 = term145.
Proof. exact (@lem2601003 term64 term64). Qed.
Lemma lem2601005 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2601006 : term147 = term64.
Proof. exact (EQ_MP (@lem2601005) (@lem940073)). Qed.
Lemma lem2601007 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2601008 : term145 = term63.
Proof. exact (MK_COMB (@lem2601007) (@lem2601006)). Qed.
Lemma lem2601009 : term144 = term63.
Proof. exact (TRANS (@lem2601004) (@lem2601008)). Qed.
Lemma lem2601011 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2601012 : term172 = term177.
Proof. exact (@lem2601011 term64 term64). Qed.
Lemma lem2601013 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2601014 : term147 = term64.
Proof. exact (EQ_MP (@lem2601013) (@lem940073)). Qed.
Lemma lem2601015 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2601016 : term145 = term63.
Proof. exact (MK_COMB (@lem2601015) (@lem2601014)). Qed.
Lemma lem2601017 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2601018 : term177 = term127.
Proof. exact (MK_COMB (@lem2601017) (@lem2601016)). Qed.
Lemma lem2601019 : term172 = term127.
Proof. exact (TRANS (@lem2601012) (@lem2601018)). Qed.
Lemma lem2601020 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2601021 : term178 = term179.
Proof. exact (MK_COMB (@lem2601020) (@lem2601019)). Qed.
Lemma lem2601022 : term174 = term137.
Proof. exact (MK_COMB (@lem2601021) (@lem2601009)). Qed.
Lemma lem2601023 : term173 = term137.
Proof. exact (TRANS (@lem2601001) (@lem2601022)). Qed.
Lemma lem2601024 : term172 = term137.
Proof. exact (TRANS (@lem2601000) (@lem2601023)). Qed.
Lemma lem2601026 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2601027 : term137 = term127.
Proof. exact (@lem2601026 term127). Qed.
Lemma lem2601028 : term172 = term127.
Proof. exact (TRANS (@lem2601024) (@lem2601027)). Qed.
Lemma lem2601031 (m : int) : (term163 m) = (term163 m).
Proof. exact (eq_refl (term163 m)). Qed.
Lemma lem2601032 (m : int) : (term199 m) = (term200 m).
Proof. exact (MK_COMB (@lem2601031 m) (@lem2601028)). Qed.
Lemma lem2601033 (m : int) : (term198 m) = (term200 m).
Proof. exact (TRANS (@lem2600991 m) (@lem2601032 m)). Qed.
Lemma lem2601034 (c : int) (n : int) : (term201 c n) = (term201 c n).
Proof. exact (eq_refl (term201 c n)). Qed.
Lemma lem2601037 (c : int) (n : int) (m : int) : (term197 c n m) = (term202 c n m).
Proof. exact (MK_COMB (@lem2601034 c n) (@lem2601033 m)). Qed.
Lemma lem2601038 (c : int) (n : int) (m : int) : (term196 c n m) = (term202 c n m).
Proof. exact (TRANS (@lem2600990 c n m) (@lem2601037 c n m)). Qed.
Lemma lem2601039 (c : int) (n : int) (m : int) : (term195 n c m) = (term202 c n m).
Proof. exact (TRANS (@lem2600989 c n m) (@lem2601038 c n m)). Qed.
Lemma lem2601040 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2601041 (c : int) (n : int) (m : int) : (term203 n c m) = (term204 c n m).
Proof. exact (MK_COMB (@lem2601040) (@lem2601039 c n m)). Qed.
Lemma lem2601042 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2601043 (c : int) (n : int) (m : int) : (term192 n c m) = (term205 c n m).
Proof. exact (MK_COMB (@lem2601041 c n m) (@lem2601042)). Qed.
Lemma lem2601044 (c : int) (n : int) (m : int) : (term82 m n c) = (term205 c n m).
Proof. exact (TRANS (@lem2600962 n c m) (@lem2601043 c n m)). Qed.
Lemma lem2601045 (n : int) (c : int) (m : int) : (term68 m n c) = (term162 n c m).
Proof. exact (@lem1988287 (term40 n c) (term65 m)). Qed.
Lemma lem2601046 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2601053 (m : int) : (term44 m) = (term124 m).
Proof. exact (@lem1982785 (real_of_int m)). Qed.
Lemma lem2601054 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2601055 (m : int) : (term60 m) = (term163 m).
Proof. exact (MK_COMB (@lem2601054) (@lem2601053 m)). Qed.
Lemma lem2601058 (m : int) : (term65 m) = (term164 m).
Proof. exact (MK_COMB (@lem2601055 m) (@lem2601046)). Qed.
Lemma lem2601065 (c : int) (n : int) : (term40 n c) = (term40 c n).
Proof. exact (@lem1982747 (real_of_int c) (real_of_int n)). Qed.
Lemma lem2601066 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2601067 (c : int) (n : int) : (term165 n c) = (term165 c n).
Proof. exact (MK_COMB (@lem2601066) (@lem2601065 c n)). Qed.
Lemma lem2601068 (c : int) (n : int) (m : int) : (term166 n c m) = (term167 c n m).
Proof. exact (MK_COMB (@lem2601067 c n) (@lem2601058 m)). Qed.
Lemma lem2601069 (c : int) (n : int) (m : int) : (term167 c n m) = (term168 c n m).
Proof. exact (@lem1982792 (term40 c n) (term164 m)). Qed.
Lemma lem2601070 (m : int) : (term169 m) = (term170 m).
Proof. exact (@lem1982781 (term124 m) term127 term63). Qed.
Lemma lem2601072 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2601073 : term63 = term151.
Proof. exact (@lem2601072 term64). Qed.
Lemma lem2601075 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2601076 : term127 = term137.
Proof. exact (@lem2601075 term64). Qed.
Lemma lem2601077 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2601078 : term128 = term138.
Proof. exact (MK_COMB (@lem2601077) (@lem2601076)). Qed.
Lemma lem2601079 : term172 = term173.
Proof. exact (MK_COMB (@lem2601078) (@lem2601073)). Qed.
Lemma lem2601080 : term173 = term174.
Proof. exact (@lem1981613 term127 term63 term63 term63). Qed.
Lemma lem2601082 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2601083 : term144 = term145.
Proof. exact (@lem2601082 term64 term64). Qed.
Lemma lem2601084 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2601085 : term147 = term64.
Proof. exact (EQ_MP (@lem2601084) (@lem940073)). Qed.
Lemma lem2601086 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2601087 : term145 = term63.
Proof. exact (MK_COMB (@lem2601086) (@lem2601085)). Qed.
Lemma lem2601088 : term144 = term63.
Proof. exact (TRANS (@lem2601083) (@lem2601087)). Qed.
Lemma lem2601090 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2601091 : term172 = term177.
Proof. exact (@lem2601090 term64 term64). Qed.
Lemma lem2601092 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2601093 : term147 = term64.
Proof. exact (EQ_MP (@lem2601092) (@lem940073)). Qed.
Lemma lem2601094 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2601095 : term145 = term63.
Proof. exact (MK_COMB (@lem2601094) (@lem2601093)). Qed.
Lemma lem2601096 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2601097 : term177 = term127.
Proof. exact (MK_COMB (@lem2601096) (@lem2601095)). Qed.
Lemma lem2601098 : term172 = term127.
Proof. exact (TRANS (@lem2601091) (@lem2601097)). Qed.
Lemma lem2601099 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2601100 : term178 = term179.
Proof. exact (MK_COMB (@lem2601099) (@lem2601098)). Qed.
Lemma lem2601101 : term174 = term137.
Proof. exact (MK_COMB (@lem2601100) (@lem2601088)). Qed.
Lemma lem2601102 : term173 = term137.
Proof. exact (TRANS (@lem2601080) (@lem2601101)). Qed.
Lemma lem2601103 : term172 = term137.
Proof. exact (TRANS (@lem2601079) (@lem2601102)). Qed.
Lemma lem2601105 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2601106 : term137 = term127.
Proof. exact (@lem2601105 term127). Qed.
Lemma lem2601107 : term172 = term127.
Proof. exact (TRANS (@lem2601103) (@lem2601106)). Qed.
Lemma lem2601108 (m : int) : (term180 m) = (term181 m).
Proof. exact (@lem1982749 term127 term127 (real_of_int m)). Qed.
Lemma lem2601110 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2601111 : term127 = term137.
Proof. exact (@lem2601110 term64). Qed.
Lemma lem2601113 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2601114 : term127 = term137.
Proof. exact (@lem2601113 term64). Qed.
Lemma lem2601115 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2601116 : term128 = term138.
Proof. exact (MK_COMB (@lem2601115) (@lem2601114)). Qed.
Lemma lem2601117 : term139 = term140.
Proof. exact (MK_COMB (@lem2601116) (@lem2601111)). Qed.
Lemma lem2601118 : term140 = term141.
Proof. exact (@lem1981613 term127 term127 term63 term63). Qed.
Lemma lem2601120 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2601121 : term144 = term145.
Proof. exact (@lem2601120 term64 term64). Qed.
Lemma lem2601122 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2601123 : term147 = term64.
Proof. exact (EQ_MP (@lem2601122) (@lem940073)). Qed.
Lemma lem2601124 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2601125 : term145 = term63.
Proof. exact (MK_COMB (@lem2601124) (@lem2601123)). Qed.
Lemma lem2601126 : term144 = term63.
Proof. exact (TRANS (@lem2601121) (@lem2601125)). Qed.
Lemma lem2601128 (m : nat) (n : nat) : (term148 m n) = (term143 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2601129 : term139 = term145.
Proof. exact (@lem2601128 term64 term64). Qed.
Lemma lem2601130 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2601131 : term147 = term64.
Proof. exact (EQ_MP (@lem2601130) (@lem940073)). Qed.
Lemma lem2601132 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2601133 : term145 = term63.
Proof. exact (MK_COMB (@lem2601132) (@lem2601131)). Qed.
Lemma lem2601134 : term139 = term63.
Proof. exact (TRANS (@lem2601129) (@lem2601133)). Qed.
Lemma lem2601135 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2601136 : term149 = term150.
Proof. exact (MK_COMB (@lem2601135) (@lem2601134)). Qed.
Lemma lem2601137 : term141 = term151.
Proof. exact (MK_COMB (@lem2601136) (@lem2601126)). Qed.
Lemma lem2601138 : term140 = term151.
Proof. exact (TRANS (@lem2601118) (@lem2601137)). Qed.
Lemma lem2601139 : term139 = term151.
Proof. exact (TRANS (@lem2601117) (@lem2601138)). Qed.
Lemma lem2601141 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2601142 : term151 = term63.
Proof. exact (@lem2601141 term63). Qed.
Lemma lem2601143 : term139 = term63.
Proof. exact (TRANS (@lem2601139) (@lem2601142)). Qed.
Lemma lem2601144 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2601145 : term153 = term154.
Proof. exact (MK_COMB (@lem2601144) (@lem2601143)). Qed.
Lemma lem2601146 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2601147 (m : int) : (term181 m) = (term182 m).
Proof. exact (MK_COMB (@lem2601145) (@lem2601146 m)). Qed.
Lemma lem2601148 (m : int) : (term180 m) = (term182 m).
Proof. exact (TRANS (@lem2601108 m) (@lem2601147 m)). Qed.
Lemma lem2601149 (m : int) : (term182 m) = (real_of_int m).
Proof. exact (@lem1982709 (real_of_int m)). Qed.
Lemma lem2601150 (m : int) : (term180 m) = (real_of_int m).
Proof. exact (TRANS (@lem2601148 m) (@lem2601149 m)). Qed.
Lemma lem2601151 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2601152 (m : int) : (term183 m) = (term78 m).
Proof. exact (MK_COMB (@lem2601151) (@lem2601150 m)). Qed.
Lemma lem2601153 (m : int) : (term170 m) = (term184 m).
Proof. exact (MK_COMB (@lem2601152 m) (@lem2601107)). Qed.
Lemma lem2601154 (m : int) : (term169 m) = (term184 m).
Proof. exact (TRANS (@lem2601070 m) (@lem2601153 m)). Qed.
Lemma lem2601155 (c : int) (n : int) : (term185 c n) = (term185 c n).
Proof. exact (eq_refl (term185 c n)). Qed.
Lemma lem2601158 (c : int) (n : int) (m : int) : (term168 c n m) = (term186 c n m).
Proof. exact (MK_COMB (@lem2601155 c n) (@lem2601154 m)). Qed.
Lemma lem2601159 (c : int) (n : int) (m : int) : (term167 c n m) = (term186 c n m).
Proof. exact (TRANS (@lem2601069 c n m) (@lem2601158 c n m)). Qed.
Lemma lem2601160 (c : int) (n : int) (m : int) : (term166 n c m) = (term186 c n m).
Proof. exact (TRANS (@lem2601068 c n m) (@lem2601159 c n m)). Qed.
Lemma lem2601161 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2601162 (c : int) (n : int) (m : int) : (term187 n c m) = (term188 c n m).
Proof. exact (MK_COMB (@lem2601161) (@lem2601160 c n m)). Qed.
Lemma lem2601163 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2601164 (c : int) (n : int) (m : int) : (term162 n c m) = (term189 c n m).
Proof. exact (MK_COMB (@lem2601162 c n m) (@lem2601163)). Qed.
Lemma lem2601165 (c : int) (n : int) (m : int) : (term68 m n c) = (term189 c n m).
Proof. exact (TRANS (@lem2601045 n c m) (@lem2601164 c n m)). Qed.
Lemma lem2601166 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2601167 (c : int) (n : int) (m : int) : (term88 m n c) = (term216 c n m).
Proof. exact (MK_COMB (@lem2601166) (@lem2601044 c n m)). Qed.
Lemma lem2601168 (c : int) (n : int) (m : int) : (term97 m n c) = (term225 c n m).
Proof. exact (MK_COMB (@lem2601167 c n m) (@lem2601165 c n m)). Qed.
Lemma lem2601169 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2601170 (c : int) (n : int) (m : int) : (term98 n c m) = (term226 c n m).
Proof. exact (MK_COMB (@lem2601169) (@lem2600961 c n m)). Qed.
Lemma lem2601171 (c : int) (n : int) (m : int) : (term99 m n c) = (term227 c n m).
Proof. exact (MK_COMB (@lem2601170 c n m) (@lem2601168 c n m)). Qed.
Lemma lem2601172 (n : int) (c : int) (m : int) : (term82 m n c) = (term192 n c m).
Proof. exact (@lem1988287 (term46 n c) (term79 m)). Qed.
Lemma lem2601179 (m : int) : (term79 m) = (term79 m).
Proof. exact (eq_refl (term79 m)). Qed.
Lemma lem2601186 (c : int) : (term44 c) = (term124 c).
Proof. exact (@lem1982785 (real_of_int c)). Qed.
Lemma lem2601189 (n : int) : (term45 n) = (term45 n).
Proof. exact (eq_refl (term45 n)). Qed.
Lemma lem2601190 (n : int) (c : int) : (term46 n c) = (term125 n c).
Proof. exact (MK_COMB (@lem2601189 n) (@lem2601186 c)). Qed.
Lemma lem2601191 (n : int) (c : int) : (term125 n c) = (term126 n c).
Proof. exact (@lem1982751 term127 (real_of_int n) (real_of_int c)). Qed.
Lemma lem2601192 (c : int) (n : int) : (term40 n c) = (term40 c n).
Proof. exact (@lem1982747 (real_of_int c) (real_of_int n)). Qed.
Lemma lem2601193 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem2601194 (c : int) (n : int) : (term126 n c) = (term126 c n).
Proof. exact (MK_COMB (@lem2601193) (@lem2601192 c n)). Qed.
Lemma lem2601195 (c : int) (n : int) : (term125 n c) = (term126 c n).
Proof. exact (TRANS (@lem2601191 n c) (@lem2601194 c n)). Qed.
Lemma lem2601196 (c : int) (n : int) : (term46 n c) = (term126 c n).
Proof. exact (TRANS (@lem2601190 n c) (@lem2601195 c n)). Qed.
Lemma lem2601197 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2601198 (c : int) (n : int) : (term193 n c) = (term194 c n).
Proof. exact (MK_COMB (@lem2601197) (@lem2601196 c n)). Qed.
Lemma lem2601199 (c : int) (n : int) (m : int) : (term195 n c m) = (term196 c n m).
Proof. exact (MK_COMB (@lem2601198 c n) (@lem2601179 m)). Qed.
Lemma lem2601200 (c : int) (n : int) (m : int) : (term196 c n m) = (term197 c n m).
Proof. exact (@lem1982792 (term126 c n) (term79 m)). Qed.
Lemma lem2601201 (m : int) : (term198 m) = (term199 m).
Proof. exact (@lem1982781 (real_of_int m) term127 term63). Qed.
Lemma lem2601203 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2601204 : term63 = term151.
Proof. exact (@lem2601203 term64). Qed.
Lemma lem2601206 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2601207 : term127 = term137.
Proof. exact (@lem2601206 term64). Qed.
Lemma lem2601208 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2601209 : term128 = term138.
Proof. exact (MK_COMB (@lem2601208) (@lem2601207)). Qed.
Lemma lem2601210 : term172 = term173.
Proof. exact (MK_COMB (@lem2601209) (@lem2601204)). Qed.
Lemma lem2601211 : term173 = term174.
Proof. exact (@lem1981613 term127 term63 term63 term63). Qed.
Lemma lem2601213 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2601214 : term144 = term145.
Proof. exact (@lem2601213 term64 term64). Qed.
Lemma lem2601215 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2601216 : term147 = term64.
Proof. exact (EQ_MP (@lem2601215) (@lem940073)). Qed.
Lemma lem2601217 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2601218 : term145 = term63.
Proof. exact (MK_COMB (@lem2601217) (@lem2601216)). Qed.
Lemma lem2601219 : term144 = term63.
Proof. exact (TRANS (@lem2601214) (@lem2601218)). Qed.
Lemma lem2601221 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2601222 : term172 = term177.
Proof. exact (@lem2601221 term64 term64). Qed.
Lemma lem2601223 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2601224 : term147 = term64.
Proof. exact (EQ_MP (@lem2601223) (@lem940073)). Qed.
Lemma lem2601225 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2601226 : term145 = term63.
Proof. exact (MK_COMB (@lem2601225) (@lem2601224)). Qed.
Lemma lem2601227 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2601228 : term177 = term127.
Proof. exact (MK_COMB (@lem2601227) (@lem2601226)). Qed.
Lemma lem2601229 : term172 = term127.
Proof. exact (TRANS (@lem2601222) (@lem2601228)). Qed.
Lemma lem2601230 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2601231 : term178 = term179.
Proof. exact (MK_COMB (@lem2601230) (@lem2601229)). Qed.
Lemma lem2601232 : term174 = term137.
Proof. exact (MK_COMB (@lem2601231) (@lem2601219)). Qed.
Lemma lem2601233 : term173 = term137.
Proof. exact (TRANS (@lem2601211) (@lem2601232)). Qed.
Lemma lem2601234 : term172 = term137.
Proof. exact (TRANS (@lem2601210) (@lem2601233)). Qed.
Lemma lem2601236 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2601237 : term137 = term127.
Proof. exact (@lem2601236 term127). Qed.
Lemma lem2601238 : term172 = term127.
Proof. exact (TRANS (@lem2601234) (@lem2601237)). Qed.
Lemma lem2601241 (m : int) : (term163 m) = (term163 m).
Proof. exact (eq_refl (term163 m)). Qed.
Lemma lem2601242 (m : int) : (term199 m) = (term200 m).
Proof. exact (MK_COMB (@lem2601241 m) (@lem2601238)). Qed.
Lemma lem2601243 (m : int) : (term198 m) = (term200 m).
Proof. exact (TRANS (@lem2601201 m) (@lem2601242 m)). Qed.
Lemma lem2601244 (c : int) (n : int) : (term201 c n) = (term201 c n).
Proof. exact (eq_refl (term201 c n)). Qed.
Lemma lem2601247 (c : int) (n : int) (m : int) : (term197 c n m) = (term202 c n m).
Proof. exact (MK_COMB (@lem2601244 c n) (@lem2601243 m)). Qed.
Lemma lem2601248 (c : int) (n : int) (m : int) : (term196 c n m) = (term202 c n m).
Proof. exact (TRANS (@lem2601200 c n m) (@lem2601247 c n m)). Qed.
Lemma lem2601249 (c : int) (n : int) (m : int) : (term195 n c m) = (term202 c n m).
Proof. exact (TRANS (@lem2601199 c n m) (@lem2601248 c n m)). Qed.
Lemma lem2601250 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2601251 (c : int) (n : int) (m : int) : (term203 n c m) = (term204 c n m).
Proof. exact (MK_COMB (@lem2601250) (@lem2601249 c n m)). Qed.
Lemma lem2601252 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2601253 (c : int) (n : int) (m : int) : (term192 n c m) = (term205 c n m).
Proof. exact (MK_COMB (@lem2601251 c n m) (@lem2601252)). Qed.
Lemma lem2601254 (c : int) (n : int) (m : int) : (term82 m n c) = (term205 c n m).
Proof. exact (TRANS (@lem2601172 n c m) (@lem2601253 c n m)). Qed.
Lemma lem2601255 (m : int) (n : int) (c : int) : (term115 n c m) = (term228 m n c).
Proof. exact (@lem1988287 (real_of_int m) (term112 n c)). Qed.
Lemma lem2601256 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2601263 (c : int) : (term44 c) = (term124 c).
Proof. exact (@lem1982785 (real_of_int c)). Qed.
Lemma lem2601266 (n : int) : (term45 n) = (term45 n).
Proof. exact (eq_refl (term45 n)). Qed.
Lemma lem2601267 (n : int) (c : int) : (term46 n c) = (term125 n c).
Proof. exact (MK_COMB (@lem2601266 n) (@lem2601263 c)). Qed.
Lemma lem2601268 (n : int) (c : int) : (term125 n c) = (term126 n c).
Proof. exact (@lem1982751 term127 (real_of_int n) (real_of_int c)). Qed.
Lemma lem2601269 (c : int) (n : int) : (term40 n c) = (term40 c n).
Proof. exact (@lem1982747 (real_of_int c) (real_of_int n)). Qed.
Lemma lem2601270 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem2601271 (c : int) (n : int) : (term126 n c) = (term126 c n).
Proof. exact (MK_COMB (@lem2601270) (@lem2601269 c n)). Qed.
Lemma lem2601272 (c : int) (n : int) : (term125 n c) = (term126 c n).
Proof. exact (TRANS (@lem2601268 n c) (@lem2601271 c n)). Qed.
Lemma lem2601273 (c : int) (n : int) : (term46 n c) = (term126 c n).
Proof. exact (TRANS (@lem2601267 n c) (@lem2601272 c n)). Qed.
Lemma lem2601274 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2601275 (c : int) (n : int) : (term111 n c) = (term201 c n).
Proof. exact (MK_COMB (@lem2601274) (@lem2601273 c n)). Qed.
Lemma lem2601278 (c : int) (n : int) : (term112 n c) = (term229 c n).
Proof. exact (MK_COMB (@lem2601275 c n) (@lem2601256)). Qed.
Lemma lem2601281 (m : int) : (term129 m) = (term129 m).
Proof. exact (eq_refl (term129 m)). Qed.
Lemma lem2601282 (m : int) (c : int) (n : int) : (term230 m n c) = (term231 m c n).
Proof. exact (MK_COMB (@lem2601281 m) (@lem2601278 c n)). Qed.
Lemma lem2601283 (m : int) (c : int) (n : int) : (term231 m c n) = (term232 m c n).
Proof. exact (@lem1982792 (real_of_int m) (term229 c n)). Qed.
Lemma lem2601284 (c : int) (n : int) : (term233 c n) = (term234 c n).
Proof. exact (@lem1982781 (term126 c n) term127 term63). Qed.
Lemma lem2601286 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2601287 : term63 = term151.
Proof. exact (@lem2601286 term64). Qed.
Lemma lem2601289 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2601290 : term127 = term137.
Proof. exact (@lem2601289 term64). Qed.
Lemma lem2601291 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2601292 : term128 = term138.
Proof. exact (MK_COMB (@lem2601291) (@lem2601290)). Qed.
Lemma lem2601293 : term172 = term173.
Proof. exact (MK_COMB (@lem2601292) (@lem2601287)). Qed.
Lemma lem2601294 : term173 = term174.
Proof. exact (@lem1981613 term127 term63 term63 term63). Qed.
Lemma lem2601296 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2601297 : term144 = term145.
Proof. exact (@lem2601296 term64 term64). Qed.
Lemma lem2601298 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2601299 : term147 = term64.
Proof. exact (EQ_MP (@lem2601298) (@lem940073)). Qed.
Lemma lem2601300 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2601301 : term145 = term63.
Proof. exact (MK_COMB (@lem2601300) (@lem2601299)). Qed.
Lemma lem2601302 : term144 = term63.
Proof. exact (TRANS (@lem2601297) (@lem2601301)). Qed.
Lemma lem2601304 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2601305 : term172 = term177.
Proof. exact (@lem2601304 term64 term64). Qed.
Lemma lem2601306 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2601307 : term147 = term64.
Proof. exact (EQ_MP (@lem2601306) (@lem940073)). Qed.
Lemma lem2601308 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2601309 : term145 = term63.
Proof. exact (MK_COMB (@lem2601308) (@lem2601307)). Qed.
Lemma lem2601310 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2601311 : term177 = term127.
Proof. exact (MK_COMB (@lem2601310) (@lem2601309)). Qed.
Lemma lem2601312 : term172 = term127.
Proof. exact (TRANS (@lem2601305) (@lem2601311)). Qed.
Lemma lem2601313 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2601314 : term178 = term179.
Proof. exact (MK_COMB (@lem2601313) (@lem2601312)). Qed.
Lemma lem2601315 : term174 = term137.
Proof. exact (MK_COMB (@lem2601314) (@lem2601302)). Qed.
Lemma lem2601316 : term173 = term137.
Proof. exact (TRANS (@lem2601294) (@lem2601315)). Qed.
Lemma lem2601317 : term172 = term137.
Proof. exact (TRANS (@lem2601293) (@lem2601316)). Qed.
Lemma lem2601319 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2601320 : term137 = term127.
Proof. exact (@lem2601319 term127). Qed.
Lemma lem2601321 : term172 = term127.
Proof. exact (TRANS (@lem2601317) (@lem2601320)). Qed.
Lemma lem2601322 (c : int) (n : int) : (term133 c n) = (term134 c n).
Proof. exact (@lem1982749 term127 term127 (term40 c n)). Qed.
Lemma lem2601324 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2601325 : term127 = term137.
Proof. exact (@lem2601324 term64). Qed.
Lemma lem2601327 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2601328 : term127 = term137.
Proof. exact (@lem2601327 term64). Qed.
Lemma lem2601329 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2601330 : term128 = term138.
Proof. exact (MK_COMB (@lem2601329) (@lem2601328)). Qed.
Lemma lem2601331 : term139 = term140.
Proof. exact (MK_COMB (@lem2601330) (@lem2601325)). Qed.
Lemma lem2601332 : term140 = term141.
Proof. exact (@lem1981613 term127 term127 term63 term63). Qed.
Lemma lem2601334 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2601335 : term144 = term145.
Proof. exact (@lem2601334 term64 term64). Qed.
Lemma lem2601336 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2601337 : term147 = term64.
Proof. exact (EQ_MP (@lem2601336) (@lem940073)). Qed.
Lemma lem2601338 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2601339 : term145 = term63.
Proof. exact (MK_COMB (@lem2601338) (@lem2601337)). Qed.
Lemma lem2601340 : term144 = term63.
Proof. exact (TRANS (@lem2601335) (@lem2601339)). Qed.
Lemma lem2601342 (m : nat) (n : nat) : (term148 m n) = (term143 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2601343 : term139 = term145.
Proof. exact (@lem2601342 term64 term64). Qed.
Lemma lem2601344 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2601345 : term147 = term64.
Proof. exact (EQ_MP (@lem2601344) (@lem940073)). Qed.
Lemma lem2601346 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2601347 : term145 = term63.
Proof. exact (MK_COMB (@lem2601346) (@lem2601345)). Qed.
Lemma lem2601348 : term139 = term63.
Proof. exact (TRANS (@lem2601343) (@lem2601347)). Qed.
Lemma lem2601349 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2601350 : term149 = term150.
Proof. exact (MK_COMB (@lem2601349) (@lem2601348)). Qed.
Lemma lem2601351 : term141 = term151.
Proof. exact (MK_COMB (@lem2601350) (@lem2601340)). Qed.
Lemma lem2601352 : term140 = term151.
Proof. exact (TRANS (@lem2601332) (@lem2601351)). Qed.
Lemma lem2601353 : term139 = term151.
Proof. exact (TRANS (@lem2601331) (@lem2601352)). Qed.
Lemma lem2601355 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2601356 : term151 = term63.
Proof. exact (@lem2601355 term63). Qed.
Lemma lem2601357 : term139 = term63.
Proof. exact (TRANS (@lem2601353) (@lem2601356)). Qed.
Lemma lem2601358 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2601359 : term153 = term154.
Proof. exact (MK_COMB (@lem2601358) (@lem2601357)). Qed.
Lemma lem2601360 (c : int) (n : int) : (term40 c n) = (term40 c n).
Proof. exact (eq_refl (term40 c n)). Qed.
Lemma lem2601361 (c : int) (n : int) : (term134 c n) = (term155 c n).
Proof. exact (MK_COMB (@lem2601359) (@lem2601360 c n)). Qed.
Lemma lem2601362 (c : int) (n : int) : (term133 c n) = (term155 c n).
Proof. exact (TRANS (@lem2601322 c n) (@lem2601361 c n)). Qed.
Lemma lem2601363 (c : int) (n : int) : (term155 c n) = (term40 c n).
Proof. exact (@lem1982709 (term40 c n)). Qed.
Lemma lem2601364 (c : int) (n : int) : (term133 c n) = (term40 c n).
Proof. exact (TRANS (@lem2601362 c n) (@lem2601363 c n)). Qed.
Lemma lem2601365 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2601366 (c : int) (n : int) : (term235 c n) = (term185 c n).
Proof. exact (MK_COMB (@lem2601365) (@lem2601364 c n)). Qed.
Lemma lem2601367 (c : int) (n : int) : (term234 c n) = (term236 c n).
Proof. exact (MK_COMB (@lem2601366 c n) (@lem2601321)). Qed.
Lemma lem2601368 (c : int) (n : int) : (term233 c n) = (term236 c n).
Proof. exact (TRANS (@lem2601284 c n) (@lem2601367 c n)). Qed.
Lemma lem2601369 (m : int) : (term78 m) = (term78 m).
Proof. exact (eq_refl (term78 m)). Qed.
Lemma lem2601370 (m : int) (c : int) (n : int) : (term232 m c n) = (term237 m c n).
Proof. exact (MK_COMB (@lem2601369 m) (@lem2601368 c n)). Qed.
Lemma lem2601375 (c : int) (n : int) (m : int) : (term237 m c n) = (term186 c n m).
Proof. exact (@lem1982757 (term40 c n) (real_of_int m) term127). Qed.
Lemma lem2601376 (c : int) (n : int) (m : int) : (term232 m c n) = (term186 c n m).
Proof. exact (TRANS (@lem2601370 m c n) (@lem2601375 c n m)). Qed.
Lemma lem2601377 (c : int) (n : int) (m : int) : (term231 m c n) = (term186 c n m).
Proof. exact (TRANS (@lem2601283 m c n) (@lem2601376 c n m)). Qed.
Lemma lem2601378 (c : int) (n : int) (m : int) : (term230 m n c) = (term186 c n m).
Proof. exact (TRANS (@lem2601282 m c n) (@lem2601377 c n m)). Qed.
Lemma lem2601379 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2601380 (c : int) (n : int) (m : int) : (term238 m n c) = (term188 c n m).
Proof. exact (MK_COMB (@lem2601379) (@lem2601378 c n m)). Qed.
Lemma lem2601381 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2601382 (c : int) (n : int) (m : int) : (term228 m n c) = (term189 c n m).
Proof. exact (MK_COMB (@lem2601380 c n m) (@lem2601381)). Qed.
Lemma lem2601383 (c : int) (n : int) (m : int) : (term115 n c m) = (term189 c n m).
Proof. exact (TRANS (@lem2601255 m n c) (@lem2601382 c n m)). Qed.
Lemma lem2601384 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2601385 (c : int) (n : int) (m : int) : (term104 m n c) = (term239 c n m).
Proof. exact (MK_COMB (@lem2601384) (@lem2601254 c n m)). Qed.
Lemma lem2601386 (c : int) (n : int) (m : int) : (term116 n c m) = (term240 c n m).
Proof. exact (MK_COMB (@lem2601385 c n m) (@lem2601383 c n m)). Qed.
Lemma lem2601387 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2601388 (c : int) (n : int) (m : int) : (term117 m n c) = (term241 c n m).
Proof. exact (MK_COMB (@lem2601387) (@lem2601171 c n m)). Qed.
Lemma lem2601389 (c : int) (n : int) (m : int) : (term118 n c m) = (term242 c n m).
Proof. exact (MK_COMB (@lem2601388 c n m) (@lem2601386 c n m)). Qed.
Lemma lem2601390 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2601391 (c : int) (n : int) (m : int) : (term119 m n c) = (term243 c n m).
Proof. exact (MK_COMB (@lem2601390) (@lem2600850 c n m)). Qed.
Lemma lem2601392 (c : int) (n : int) (m : int) : (term120 n c m) = (term244 c n m).
Proof. exact (MK_COMB (@lem2601391 c n m) (@lem2601389 c n m)). Qed.
Lemma lem2601399 (c : int) (n : int) (m : int) : (term122 n c m) = (term244 c n m).
Proof. exact (TRANS (@lem2600449 n c m) (@lem2601392 c n m)). Qed.
Lemma lem2601425 (c : int) (n : int) (m : int) : (term242 c n m) = (term245 c n m).
Proof. exact (@lem19158 (term205 c n m) (term227 c n m) (term189 c n m)). Qed.
Lemma lem2601432 (c : int) (n : int) (m : int) : (term246 c n m) = (term247 c n m).
Proof. exact (@lem19367 (term224 c n m) (term225 c n m) (term189 c n m)). Qed.
Lemma lem2601439 (c : int) (n : int) (m : int) : (term248 c n m) = (term249 c n m).
Proof. exact (@lem19367 (term224 c n m) (term225 c n m) (term205 c n m)). Qed.
Lemma lem2601440 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2601441 (c : int) (n : int) (m : int) : (term250 c n m) = (term251 c n m).
Proof. exact (MK_COMB (@lem2601440) (@lem2601439 c n m)). Qed.
Lemma lem2601442 (c : int) (n : int) (m : int) : (term245 c n m) = (term252 c n m).
Proof. exact (MK_COMB (@lem2601441 c n m) (@lem2601432 c n m)). Qed.
Lemma lem2601444 (c : int) (n : int) (m : int) : (term242 c n m) = (term252 c n m).
Proof. exact (TRANS (@lem2601425 c n m) (@lem2601442 c n m)). Qed.
Lemma lem2601473 (c : int) (n : int) (m : int) : (term223 c n m) = (term253 c n m).
Proof. exact (@lem19367 (term191 c n m) (term217 c n m) ((term157 c n m) = term160)). Qed.
Lemma lem2601474 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2601475 (c : int) (n : int) (m : int) : (term243 c n m) = (term254 c n m).
Proof. exact (MK_COMB (@lem2601474) (@lem2601473 c n m)). Qed.
Lemma lem2601476 (c : int) (n : int) (m : int) : (term244 c n m) = (term255 c n m).
Proof. exact (MK_COMB (@lem2601475 c n m) (@lem2601444 c n m)). Qed.
Lemma lem2601477 (c : int) (n : int) (m : int) : (term122 n c m) = (term255 c n m).
Proof. exact (TRANS (@lem2601399 c n m) (@lem2601476 c n m)). Qed.
Lemma lem2601511 (c : int) (n : int) (m : int) (h1 : term255 c n m) : term255 c n m.
Proof. exact (h1). Qed.
Lemma lem2601512 (c : int) (n : int) (m : int) (h1 : term253 c n m) : term253 c n m.
Proof. exact (h1). Qed.
Lemma lem2601513 (c : int) (n : int) (m : int) (h1 : term256 c n m) : term256 c n m.
Proof. exact (h1). Qed.
Lemma lem2601514 (c : int) (n : int) (m : int) (h1 : term256 c n m) : (term157 c n m) = term160.
Proof. exact (proj2 (@lem2601513 c n m h1)). Qed.
Lemma lem2601515 (c : int) (n : int) (m : int) (h1 : term256 c n m) : term191 c n m.
Proof. exact (proj1 (@lem2601513 c n m h1)). Qed.
Lemma lem2601516 (c : int) (n : int) (m : int) (h1 : term256 c n m) : term189 c n m.
Proof. exact (proj2 (@lem2601515 c n m h1)). Qed.
Lemma lem2601519 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2601520 : term257 = term258.
Proof. exact (@lem2601519 term160 term63). Qed.
Lemma lem2601522 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2601523 : term63 = term151.
Proof. exact (@lem2601522 term64). Qed.
Lemma lem2601525 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2601526 : term160 = term259.
Proof. exact (@lem2601525 (NUMERAL 0)). Qed.
Lemma lem2601527 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2601528 : term260 = term261.
Proof. exact (MK_COMB (@lem2601527) (@lem2601526)). Qed.
Lemma lem2601529 : term258 = term262.
Proof. exact (MK_COMB (@lem2601528) (@lem2601523)). Qed.
Lemma lem2601530 : term263.
Proof. exact (@lem1980255 term160 term63 term63 term63). Qed.
Lemma lem2601532 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2601533 : term258 = term265.
Proof. exact (@lem2601532 (NUMERAL 0) term64). Qed.
Lemma lem2601534 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2601535 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2601536 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2601535 h1) (fun h1 : term265 = True => @lem2601534)). Qed.
Lemma lem2601537 : term265 = True.
Proof. exact (EQ_MP (@lem2601536) (@lem2601534)). Qed.
Lemma lem2601538 : term258 = True.
Proof. exact (TRANS (@lem2601533) (@lem2601537)). Qed.
Lemma lem2601539 : True = term258.
Proof. exact (SYM (@lem2601538)). Qed.
Lemma lem2601540 : term258.
Proof. exact (EQ_MP (@lem2601539) (@lem0)). Qed.
Lemma lem2601541 : term267.
Proof. exact (@lem2601530 (@lem2601540)). Qed.
Lemma lem2601543 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2601544 : term258 = term265.
Proof. exact (@lem2601543 (NUMERAL 0) term64). Qed.
Lemma lem2601545 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2601546 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2601547 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2601546 h1) (fun h1 : term265 = True => @lem2601545)). Qed.
Lemma lem2601548 : term265 = True.
Proof. exact (EQ_MP (@lem2601547) (@lem2601545)). Qed.
Lemma lem2601549 : term258 = True.
Proof. exact (TRANS (@lem2601544) (@lem2601548)). Qed.
Lemma lem2601550 : True = term258.
Proof. exact (SYM (@lem2601549)). Qed.
Lemma lem2601551 : term258.
Proof. exact (EQ_MP (@lem2601550) (@lem0)). Qed.
Lemma lem2601552 : term262 = term268.
Proof. exact (@lem2601541 (@lem2601551)). Qed.
Lemma lem2601554 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2601555 : term144 = term145.
Proof. exact (@lem2601554 term64 term64). Qed.
Lemma lem2601556 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2601557 : term147 = term64.
Proof. exact (EQ_MP (@lem2601556) (@lem940073)). Qed.
Lemma lem2601558 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2601559 : term145 = term63.
Proof. exact (MK_COMB (@lem2601558) (@lem2601557)). Qed.
Lemma lem2601560 : term144 = term63.
Proof. exact (TRANS (@lem2601555) (@lem2601559)). Qed.
Lemma lem2601562 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2601563 : term270 = term160.
Proof. exact (@lem2601562 term64). Qed.
Lemma lem2601564 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2601565 : term271 = term260.
Proof. exact (MK_COMB (@lem2601564) (@lem2601563)). Qed.
Lemma lem2601566 : term268 = term258.
Proof. exact (MK_COMB (@lem2601565) (@lem2601560)). Qed.
Lemma lem2601568 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2601569 : term258 = term265.
Proof. exact (@lem2601568 (NUMERAL 0) term64). Qed.
Lemma lem2601570 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2601571 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2601572 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2601571 h1) (fun h1 : term265 = True => @lem2601570)). Qed.
Lemma lem2601573 : term265 = True.
Proof. exact (EQ_MP (@lem2601572) (@lem2601570)). Qed.
Lemma lem2601574 : term258 = True.
Proof. exact (TRANS (@lem2601569) (@lem2601573)). Qed.
Lemma lem2601575 : term268 = True.
Proof. exact (TRANS (@lem2601566) (@lem2601574)). Qed.
Lemma lem2601576 : term262 = True.
Proof. exact (TRANS (@lem2601552) (@lem2601575)). Qed.
Lemma lem2601577 : term258 = True.
Proof. exact (TRANS (@lem2601529) (@lem2601576)). Qed.
Lemma lem2601578 : term257 = True.
Proof. exact (TRANS (@lem2601520) (@lem2601577)). Qed.
Lemma lem2601579 : True = term257.
Proof. exact (SYM (@lem2601578)). Qed.
Lemma lem2601580 : term257.
Proof. exact (EQ_MP (@lem2601579) (@lem0)). Qed.
Lemma lem2601581 (c : int) (n : int) (m : int) (h1 : term256 c n m) : term272 c n m.
Proof. exact (conj (@lem2601580) (@lem2601516 c n m h1)). Qed.
Lemma lem2601583 (x : real) (y : real) : term273 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2601584 (c : int) (n : int) (m : int) : term274 c n m.
Proof. exact (@lem2601583 term63 (term186 c n m)). Qed.
Lemma lem2601585 (c : int) (n : int) (m : int) (h1 : term256 c n m) : term275 c n m.
Proof. exact (@lem2601584 c n m (@lem2601581 c n m h1)). Qed.
Lemma lem2601586 (c : int) (n : int) (m : int) : (term276 c n m) = (term186 c n m).
Proof. exact (@lem1982733 (term186 c n m)). Qed.
Lemma lem2601587 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2601588 (c : int) (n : int) (m : int) : (term277 c n m) = (term188 c n m).
Proof. exact (MK_COMB (@lem2601587) (@lem2601586 c n m)). Qed.
Lemma lem2601589 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2601590 (c : int) (n : int) (m : int) : (term275 c n m) = (term189 c n m).
Proof. exact (MK_COMB (@lem2601588 c n m) (@lem2601589)). Qed.
Lemma lem2601591 (c : int) (n : int) (m : int) (h1 : term256 c n m) : term189 c n m.
Proof. exact (EQ_MP (@lem2601590 c n m) (@lem2601585 c n m h1)). Qed.
Lemma lem2601593 (y : real) : term278 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2601594 (c : int) (n : int) (m : int) : term279 c n m.
Proof. exact (@lem2601593 (term157 c n m)). Qed.
Lemma lem2601595 (c : int) (n : int) (m : int) (h1 : term256 c n m) : term280 c n m.
Proof. exact (@lem2601594 c n m (@lem2601514 c n m h1)). Qed.
Lemma lem2601596 (c : int) (n : int) (m : int) (h1 : term256 c n m) : term281 c n m.
Proof. exact (@lem2601595 c n m h1 term127). Qed.
Lemma lem2601597 (c : int) (n : int) (m : int) : (term281 c n m) = ((term282 c n m) = term160).
Proof. exact (eq_refl (term281 c n m)). Qed.
Lemma lem2601598 (c : int) (n : int) (m : int) (h1 : term256 c n m) : (term282 c n m) = term160.
Proof. exact (EQ_MP (@lem2601597 c n m) (@lem2601596 c n m h1)). Qed.
Lemma lem2601605 (c : int) (n : int) (m : int) : (term282 c n m) = (term212 c n m).
Proof. exact (@lem1982781 (term40 c n) term127 (real_of_int m)). Qed.
Lemma lem2601606 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2601607 (c : int) (n : int) (m : int) : (term283 c n m) = (term284 c n m).
Proof. exact (MK_COMB (@lem2601606) (@lem2601605 c n m)). Qed.
Lemma lem2601608 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2601609 (c : int) (n : int) (m : int) : ((term282 c n m) = term160) = ((term212 c n m) = term160).
Proof. exact (MK_COMB (@lem2601607 c n m) (@lem2601608)). Qed.
Lemma lem2601610 (c : int) (n : int) (m : int) (h1 : term256 c n m) : (term212 c n m) = term160.
Proof. exact (EQ_MP (@lem2601609 c n m) (@lem2601598 c n m h1)). Qed.
Lemma lem2601611 (c : int) (n : int) (m : int) (h1 : term256 c n m) : term285 c n m.
Proof. exact (conj (@lem2601610 c n m h1) (@lem2601591 c n m h1)). Qed.
Lemma lem2601613 (x : real) (y : real) : term286 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2601614 (c : int) (n : int) (m : int) : term287 c n m.
Proof. exact (@lem2601613 (term212 c n m) (term186 c n m)). Qed.
Lemma lem2601615 (c : int) (n : int) (m : int) (h1 : term256 c n m) : term288 c n m.
Proof. exact (@lem2601614 c n m (@lem2601611 c n m h1)). Qed.
Lemma lem2601616 (c : int) (n : int) (m : int) : (term289 c n m) = (term290 c n m).
Proof. exact (@lem1982753 (term126 c n) (term40 c n) (term124 m) (term184 m)). Qed.
Lemma lem2601617 (c : int) (n : int) : (term291 c n) = (term292 c n).
Proof. exact (@lem1982713 term127 (term40 c n)). Qed.
Lemma lem2601619 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2601620 : term63 = term151.
Proof. exact (@lem2601619 term64). Qed.
Lemma lem2601622 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2601623 : term127 = term137.
Proof. exact (@lem2601622 term64). Qed.
Lemma lem2601624 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2601625 : term293 = term294.
Proof. exact (MK_COMB (@lem2601624) (@lem2601623)). Qed.
Lemma lem2601626 : term295 = term296.
Proof. exact (MK_COMB (@lem2601625) (@lem2601620)). Qed.
Lemma lem2601627 : term297.
Proof. exact (@lem1981473 term127 term63 term63 term63 term160 term63). Qed.
Lemma lem2601629 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2601630 : term258 = term265.
Proof. exact (@lem2601629 (NUMERAL 0) term64). Qed.
Lemma lem2601631 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2601632 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2601633 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2601632 h1) (fun h1 : term265 = True => @lem2601631)). Qed.
Lemma lem2601634 : term265 = True.
Proof. exact (EQ_MP (@lem2601633) (@lem2601631)). Qed.
Lemma lem2601635 : term258 = True.
Proof. exact (TRANS (@lem2601630) (@lem2601634)). Qed.
Lemma lem2601636 : True = term258.
Proof. exact (SYM (@lem2601635)). Qed.
Lemma lem2601637 : term258.
Proof. exact (EQ_MP (@lem2601636) (@lem0)). Qed.
Lemma lem2601638 : term298.
Proof. exact (@lem2601627 (@lem2601637)). Qed.
Lemma lem2601640 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2601641 : term258 = term265.
Proof. exact (@lem2601640 (NUMERAL 0) term64). Qed.
Lemma lem2601642 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2601643 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2601644 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2601643 h1) (fun h1 : term265 = True => @lem2601642)). Qed.
Lemma lem2601645 : term265 = True.
Proof. exact (EQ_MP (@lem2601644) (@lem2601642)). Qed.
Lemma lem2601646 : term258 = True.
Proof. exact (TRANS (@lem2601641) (@lem2601645)). Qed.
Lemma lem2601647 : True = term258.
Proof. exact (SYM (@lem2601646)). Qed.
Lemma lem2601648 : term258.
Proof. exact (EQ_MP (@lem2601647) (@lem0)). Qed.
Lemma lem2601649 : term299.
Proof. exact (@lem2601638 (@lem2601648)). Qed.
Lemma lem2601651 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2601652 : term258 = term265.
Proof. exact (@lem2601651 (NUMERAL 0) term64). Qed.
Lemma lem2601653 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2601654 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2601655 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2601654 h1) (fun h1 : term265 = True => @lem2601653)). Qed.
Lemma lem2601656 : term265 = True.
Proof. exact (EQ_MP (@lem2601655) (@lem2601653)). Qed.
Lemma lem2601657 : term258 = True.
Proof. exact (TRANS (@lem2601652) (@lem2601656)). Qed.
Lemma lem2601658 : True = term258.
Proof. exact (SYM (@lem2601657)). Qed.
Lemma lem2601659 : term258.
Proof. exact (EQ_MP (@lem2601658) (@lem0)). Qed.
Lemma lem2601660 : term300.
Proof. exact (@lem2601649 (@lem2601659)). Qed.
Lemma lem2601662 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2601663 : term144 = term145.
Proof. exact (@lem2601662 term64 term64). Qed.
Lemma lem2601664 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2601665 : term147 = term64.
Proof. exact (EQ_MP (@lem2601664) (@lem940073)). Qed.
Lemma lem2601666 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2601667 : term145 = term63.
Proof. exact (MK_COMB (@lem2601666) (@lem2601665)). Qed.
Lemma lem2601668 : term144 = term63.
Proof. exact (TRANS (@lem2601663) (@lem2601667)). Qed.
Lemma lem2601670 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2601671 : term172 = term177.
Proof. exact (@lem2601670 term64 term64). Qed.
Lemma lem2601672 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2601673 : term147 = term64.
Proof. exact (EQ_MP (@lem2601672) (@lem940073)). Qed.
Lemma lem2601674 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2601675 : term145 = term63.
Proof. exact (MK_COMB (@lem2601674) (@lem2601673)). Qed.
Lemma lem2601676 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2601677 : term177 = term127.
Proof. exact (MK_COMB (@lem2601676) (@lem2601675)). Qed.
Lemma lem2601678 : term172 = term127.
Proof. exact (TRANS (@lem2601671) (@lem2601677)). Qed.
Lemma lem2601679 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2601680 : term301 = term293.
Proof. exact (MK_COMB (@lem2601679) (@lem2601678)). Qed.
Lemma lem2601681 : term302 = term295.
Proof. exact (MK_COMB (@lem2601680) (@lem2601668)). Qed.
Lemma lem2601683 (m : nat) : (term303 m) = term160.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2601684 : term295 = term160.
Proof. exact (@lem2601683 term64). Qed.
Lemma lem2601685 : term302 = term160.
Proof. exact (TRANS (@lem2601681) (@lem2601684)). Qed.
Lemma lem2601686 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2601687 : term304 = term305.
Proof. exact (MK_COMB (@lem2601686) (@lem2601685)). Qed.
Lemma lem2601688 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2601689 : term306 = term270.
Proof. exact (MK_COMB (@lem2601687) (@lem2601688)). Qed.
Lemma lem2601691 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2601692 : term270 = term160.
Proof. exact (@lem2601691 term64). Qed.
Lemma lem2601693 : term306 = term160.
Proof. exact (TRANS (@lem2601689) (@lem2601692)). Qed.
Lemma lem2601695 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2601696 : term144 = term145.
Proof. exact (@lem2601695 term64 term64). Qed.
Lemma lem2601697 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2601698 : term147 = term64.
Proof. exact (EQ_MP (@lem2601697) (@lem940073)). Qed.
Lemma lem2601699 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2601700 : term145 = term63.
Proof. exact (MK_COMB (@lem2601699) (@lem2601698)). Qed.
Lemma lem2601701 : term144 = term63.
Proof. exact (TRANS (@lem2601696) (@lem2601700)). Qed.
Lemma lem2601702 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem2601703 : term307 = term270.
Proof. exact (MK_COMB (@lem2601702) (@lem2601701)). Qed.
Lemma lem2601705 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2601706 : term270 = term160.
Proof. exact (@lem2601705 term64). Qed.
Lemma lem2601707 : term307 = term160.
Proof. exact (TRANS (@lem2601703) (@lem2601706)). Qed.
Lemma lem2601708 : term160 = term307.
Proof. exact (SYM (@lem2601707)). Qed.
Lemma lem2601709 : term306 = term307.
Proof. exact (TRANS (@lem2601693) (@lem2601708)). Qed.
Lemma lem2601710 : term296 = term259.
Proof. exact (@lem2601660 (@lem2601709)). Qed.
Lemma lem2601711 : term295 = term259.
Proof. exact (TRANS (@lem2601626) (@lem2601710)). Qed.
Lemma lem2601713 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2601714 : term259 = term160.
Proof. exact (@lem2601713 term160). Qed.
Lemma lem2601715 : term295 = term160.
Proof. exact (TRANS (@lem2601711) (@lem2601714)). Qed.
Lemma lem2601716 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2601717 : term308 = term305.
Proof. exact (MK_COMB (@lem2601716) (@lem2601715)). Qed.
Lemma lem2601718 (c : int) (n : int) : (term40 c n) = (term40 c n).
Proof. exact (eq_refl (term40 c n)). Qed.
Lemma lem2601719 (c : int) (n : int) : (term292 c n) = (term309 c n).
Proof. exact (MK_COMB (@lem2601717) (@lem2601718 c n)). Qed.
Lemma lem2601720 (c : int) (n : int) : (term291 c n) = (term309 c n).
Proof. exact (TRANS (@lem2601617 c n) (@lem2601719 c n)). Qed.
Lemma lem2601721 (c : int) (n : int) : (term309 c n) = term160.
Proof. exact (@lem1982719 (term40 c n)). Qed.
Lemma lem2601722 (c : int) (n : int) : (term291 c n) = term160.
Proof. exact (TRANS (@lem2601720 c n) (@lem2601721 c n)). Qed.
Lemma lem2601723 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2601724 (c : int) (n : int) : (term310 c n) = term311.
Proof. exact (MK_COMB (@lem2601723) (@lem2601722 c n)). Qed.
Lemma lem2601725 (m : int) : (term312 m) = (term313 m).
Proof. exact (@lem1982763 (term124 m) (real_of_int m) term127). Qed.
Lemma lem2601726 (m : int) : (term314 m) = (term315 m).
Proof. exact (@lem1982713 term127 (real_of_int m)). Qed.
Lemma lem2601728 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2601729 : term63 = term151.
Proof. exact (@lem2601728 term64). Qed.
Lemma lem2601731 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2601732 : term127 = term137.
Proof. exact (@lem2601731 term64). Qed.
Lemma lem2601733 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2601734 : term293 = term294.
Proof. exact (MK_COMB (@lem2601733) (@lem2601732)). Qed.
Lemma lem2601735 : term295 = term296.
Proof. exact (MK_COMB (@lem2601734) (@lem2601729)). Qed.
Lemma lem2601736 : term297.
Proof. exact (@lem1981473 term127 term63 term63 term63 term160 term63). Qed.
Lemma lem2601738 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2601739 : term258 = term265.
Proof. exact (@lem2601738 (NUMERAL 0) term64). Qed.
Lemma lem2601740 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2601741 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2601742 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2601741 h1) (fun h1 : term265 = True => @lem2601740)). Qed.
Lemma lem2601743 : term265 = True.
Proof. exact (EQ_MP (@lem2601742) (@lem2601740)). Qed.
Lemma lem2601744 : term258 = True.
Proof. exact (TRANS (@lem2601739) (@lem2601743)). Qed.
Lemma lem2601745 : True = term258.
Proof. exact (SYM (@lem2601744)). Qed.
Lemma lem2601746 : term258.
Proof. exact (EQ_MP (@lem2601745) (@lem0)). Qed.
Lemma lem2601747 : term298.
Proof. exact (@lem2601736 (@lem2601746)). Qed.
Lemma lem2601749 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2601750 : term258 = term265.
Proof. exact (@lem2601749 (NUMERAL 0) term64). Qed.
Lemma lem2601751 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2601752 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2601753 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2601752 h1) (fun h1 : term265 = True => @lem2601751)). Qed.
Lemma lem2601754 : term265 = True.
Proof. exact (EQ_MP (@lem2601753) (@lem2601751)). Qed.
Lemma lem2601755 : term258 = True.
Proof. exact (TRANS (@lem2601750) (@lem2601754)). Qed.
Lemma lem2601756 : True = term258.
Proof. exact (SYM (@lem2601755)). Qed.
Lemma lem2601757 : term258.
Proof. exact (EQ_MP (@lem2601756) (@lem0)). Qed.
Lemma lem2601758 : term299.
Proof. exact (@lem2601747 (@lem2601757)). Qed.
Lemma lem2601760 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2601761 : term258 = term265.
Proof. exact (@lem2601760 (NUMERAL 0) term64). Qed.
Lemma lem2601762 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2601763 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2601764 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2601763 h1) (fun h1 : term265 = True => @lem2601762)). Qed.
Lemma lem2601765 : term265 = True.
Proof. exact (EQ_MP (@lem2601764) (@lem2601762)). Qed.
Lemma lem2601766 : term258 = True.
Proof. exact (TRANS (@lem2601761) (@lem2601765)). Qed.
Lemma lem2601767 : True = term258.
Proof. exact (SYM (@lem2601766)). Qed.
Lemma lem2601768 : term258.
Proof. exact (EQ_MP (@lem2601767) (@lem0)). Qed.
Lemma lem2601769 : term300.
Proof. exact (@lem2601758 (@lem2601768)). Qed.
Lemma lem2601771 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2601772 : term144 = term145.
Proof. exact (@lem2601771 term64 term64). Qed.
Lemma lem2601773 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2601774 : term147 = term64.
Proof. exact (EQ_MP (@lem2601773) (@lem940073)). Qed.
Lemma lem2601775 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2601776 : term145 = term63.
Proof. exact (MK_COMB (@lem2601775) (@lem2601774)). Qed.
Lemma lem2601777 : term144 = term63.
Proof. exact (TRANS (@lem2601772) (@lem2601776)). Qed.
Lemma lem2601779 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2601780 : term172 = term177.
Proof. exact (@lem2601779 term64 term64). Qed.
Lemma lem2601781 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2601782 : term147 = term64.
Proof. exact (EQ_MP (@lem2601781) (@lem940073)). Qed.
Lemma lem2601783 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2601784 : term145 = term63.
Proof. exact (MK_COMB (@lem2601783) (@lem2601782)). Qed.
Lemma lem2601785 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2601786 : term177 = term127.
Proof. exact (MK_COMB (@lem2601785) (@lem2601784)). Qed.
Lemma lem2601787 : term172 = term127.
Proof. exact (TRANS (@lem2601780) (@lem2601786)). Qed.
Lemma lem2601788 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2601789 : term301 = term293.
Proof. exact (MK_COMB (@lem2601788) (@lem2601787)). Qed.
Lemma lem2601790 : term302 = term295.
Proof. exact (MK_COMB (@lem2601789) (@lem2601777)). Qed.
Lemma lem2601792 (m : nat) : (term303 m) = term160.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2601793 : term295 = term160.
Proof. exact (@lem2601792 term64). Qed.
Lemma lem2601794 : term302 = term160.
Proof. exact (TRANS (@lem2601790) (@lem2601793)). Qed.
Lemma lem2601795 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2601796 : term304 = term305.
Proof. exact (MK_COMB (@lem2601795) (@lem2601794)). Qed.
Lemma lem2601797 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2601798 : term306 = term270.
Proof. exact (MK_COMB (@lem2601796) (@lem2601797)). Qed.
Lemma lem2601800 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2601801 : term270 = term160.
Proof. exact (@lem2601800 term64). Qed.
Lemma lem2601802 : term306 = term160.
Proof. exact (TRANS (@lem2601798) (@lem2601801)). Qed.
Lemma lem2601804 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2601805 : term144 = term145.
Proof. exact (@lem2601804 term64 term64). Qed.
Lemma lem2601806 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2601807 : term147 = term64.
Proof. exact (EQ_MP (@lem2601806) (@lem940073)). Qed.
Lemma lem2601808 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2601809 : term145 = term63.
Proof. exact (MK_COMB (@lem2601808) (@lem2601807)). Qed.
Lemma lem2601810 : term144 = term63.
Proof. exact (TRANS (@lem2601805) (@lem2601809)). Qed.
Lemma lem2601811 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem2601812 : term307 = term270.
Proof. exact (MK_COMB (@lem2601811) (@lem2601810)). Qed.
Lemma lem2601814 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2601815 : term270 = term160.
Proof. exact (@lem2601814 term64). Qed.
Lemma lem2601816 : term307 = term160.
Proof. exact (TRANS (@lem2601812) (@lem2601815)). Qed.
Lemma lem2601817 : term160 = term307.
Proof. exact (SYM (@lem2601816)). Qed.
Lemma lem2601818 : term306 = term307.
Proof. exact (TRANS (@lem2601802) (@lem2601817)). Qed.
Lemma lem2601819 : term296 = term259.
Proof. exact (@lem2601769 (@lem2601818)). Qed.
Lemma lem2601820 : term295 = term259.
Proof. exact (TRANS (@lem2601735) (@lem2601819)). Qed.
Lemma lem2601822 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2601823 : term259 = term160.
Proof. exact (@lem2601822 term160). Qed.
Lemma lem2601824 : term295 = term160.
Proof. exact (TRANS (@lem2601820) (@lem2601823)). Qed.
Lemma lem2601825 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2601826 : term308 = term305.
Proof. exact (MK_COMB (@lem2601825) (@lem2601824)). Qed.
Lemma lem2601827 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2601828 (m : int) : (term315 m) = (term316 m).
Proof. exact (MK_COMB (@lem2601826) (@lem2601827 m)). Qed.
Lemma lem2601829 (m : int) : (term314 m) = (term316 m).
Proof. exact (TRANS (@lem2601726 m) (@lem2601828 m)). Qed.
Lemma lem2601830 (m : int) : (term316 m) = term160.
Proof. exact (@lem1982719 (real_of_int m)). Qed.
Lemma lem2601831 (m : int) : (term314 m) = term160.
Proof. exact (TRANS (@lem2601829 m) (@lem2601830 m)). Qed.
Lemma lem2601832 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2601833 (m : int) : (term317 m) = term311.
Proof. exact (MK_COMB (@lem2601832) (@lem2601831 m)). Qed.
Lemma lem2601834 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem2601835 (m : int) : (term313 m) = term318.
Proof. exact (MK_COMB (@lem2601833 m) (@lem2601834)). Qed.
Lemma lem2601836 (m : int) : (term312 m) = term318.
Proof. exact (TRANS (@lem2601725 m) (@lem2601835 m)). Qed.
Lemma lem2601837 : term318 = term127.
Proof. exact (@lem1982721 term127). Qed.
Lemma lem2601838 (m : int) : (term312 m) = term127.
Proof. exact (TRANS (@lem2601836 m) (@lem2601837)). Qed.
Lemma lem2601839 (c : int) (n : int) (m : int) : (term290 c n m) = term318.
Proof. exact (MK_COMB (@lem2601724 c n) (@lem2601838 m)). Qed.
Lemma lem2601840 (c : int) (n : int) (m : int) : (term289 c n m) = term318.
Proof. exact (TRANS (@lem2601616 c n m) (@lem2601839 c n m)). Qed.
Lemma lem2601841 : term318 = term127.
Proof. exact (@lem1982721 term127). Qed.
Lemma lem2601842 (c : int) (n : int) (m : int) : (term289 c n m) = term127.
Proof. exact (TRANS (@lem2601840 c n m) (@lem2601841)). Qed.
Lemma lem2601843 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2601844 (c : int) (n : int) (m : int) : (term319 c n m) = term320.
Proof. exact (MK_COMB (@lem2601843) (@lem2601842 c n m)). Qed.
Lemma lem2601845 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2601846 (c : int) (n : int) (m : int) : (term288 c n m) = term321.
Proof. exact (MK_COMB (@lem2601844 c n m) (@lem2601845)). Qed.
Lemma lem2601847 (c : int) (n : int) (m : int) (h1 : term256 c n m) : term321.
Proof. exact (EQ_MP (@lem2601846 c n m) (@lem2601615 c n m h1)). Qed.
Lemma lem2601849 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2601850 : term321 = term322.
Proof. exact (@lem2601849 term160 term127). Qed.
Lemma lem2601852 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2601853 : term127 = term137.
Proof. exact (@lem2601852 term64). Qed.
Lemma lem2601855 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2601856 : term160 = term259.
Proof. exact (@lem2601855 (NUMERAL 0)). Qed.
Lemma lem2601857 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2601858 : term323 = term324.
Proof. exact (MK_COMB (@lem2601857) (@lem2601856)). Qed.
Lemma lem2601859 : term322 = term325.
Proof. exact (MK_COMB (@lem2601858) (@lem2601853)). Qed.
Lemma lem2601860 : term326.
Proof. exact (@lem1980026 term160 term63 term127 term63). Qed.
Lemma lem2601862 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2601863 : term258 = term265.
Proof. exact (@lem2601862 (NUMERAL 0) term64). Qed.
Lemma lem2601864 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2601865 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2601866 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2601865 h1) (fun h1 : term265 = True => @lem2601864)). Qed.
Lemma lem2601867 : term265 = True.
Proof. exact (EQ_MP (@lem2601866) (@lem2601864)). Qed.
Lemma lem2601868 : term258 = True.
Proof. exact (TRANS (@lem2601863) (@lem2601867)). Qed.
Lemma lem2601869 : True = term258.
Proof. exact (SYM (@lem2601868)). Qed.
Lemma lem2601870 : term258.
Proof. exact (EQ_MP (@lem2601869) (@lem0)). Qed.
Lemma lem2601871 : term327.
Proof. exact (@lem2601860 (@lem2601870)). Qed.
Lemma lem2601873 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2601874 : term258 = term265.
Proof. exact (@lem2601873 (NUMERAL 0) term64). Qed.
Lemma lem2601875 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2601876 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2601877 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2601876 h1) (fun h1 : term265 = True => @lem2601875)). Qed.
Lemma lem2601878 : term265 = True.
Proof. exact (EQ_MP (@lem2601877) (@lem2601875)). Qed.
Lemma lem2601879 : term258 = True.
Proof. exact (TRANS (@lem2601874) (@lem2601878)). Qed.
Lemma lem2601880 : True = term258.
Proof. exact (SYM (@lem2601879)). Qed.
Lemma lem2601881 : term258.
Proof. exact (EQ_MP (@lem2601880) (@lem0)). Qed.
Lemma lem2601882 : term325 = term328.
Proof. exact (@lem2601871 (@lem2601881)). Qed.
Lemma lem2601884 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2601885 : term172 = term177.
Proof. exact (@lem2601884 term64 term64). Qed.
Lemma lem2601886 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2601887 : term147 = term64.
Proof. exact (EQ_MP (@lem2601886) (@lem940073)). Qed.
Lemma lem2601888 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2601889 : term145 = term63.
Proof. exact (MK_COMB (@lem2601888) (@lem2601887)). Qed.
Lemma lem2601890 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2601891 : term177 = term127.
Proof. exact (MK_COMB (@lem2601890) (@lem2601889)). Qed.
Lemma lem2601892 : term172 = term127.
Proof. exact (TRANS (@lem2601885) (@lem2601891)). Qed.
Lemma lem2601894 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2601895 : term270 = term160.
Proof. exact (@lem2601894 term64). Qed.
Lemma lem2601896 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2601897 : term329 = term323.
Proof. exact (MK_COMB (@lem2601896) (@lem2601895)). Qed.
Lemma lem2601898 : term328 = term322.
Proof. exact (MK_COMB (@lem2601897) (@lem2601892)). Qed.
Lemma lem2601900 (m : nat) (n : nat) : (term330 m n) = (term331 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2601901 : term322 = term332.
Proof. exact (@lem2601900 (NUMERAL 0) term64). Qed.
Lemma lem2601902 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2601903 (h1 : term266 = (BIT1 0)) : (term64 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2601904 : (term266 = (BIT1 0)) = ((term64 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2601903 h1) (fun h1 : (term64 = (NUMERAL 0)) = False => @lem2601902)). Qed.
Lemma lem2601905 : (term64 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2601904) (@lem2601902)). Qed.
Lemma lem2601906 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2601907 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2601908 : term333 = (and True).
Proof. exact (MK_COMB (@lem2601907) (@lem2601906)). Qed.
Lemma lem2601909 : term332 = (True /\ False).
Proof. exact (MK_COMB (@lem2601908) (@lem2601905)). Qed.
Lemma lem2601911 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2601912 : term332 = False.
Proof. exact (TRANS (@lem2601909) (@lem2601911)). Qed.
Lemma lem2601913 : term322 = False.
Proof. exact (TRANS (@lem2601901) (@lem2601912)). Qed.
Lemma lem2601914 : term328 = False.
Proof. exact (TRANS (@lem2601898) (@lem2601913)). Qed.
Lemma lem2601915 : term325 = False.
Proof. exact (TRANS (@lem2601882) (@lem2601914)). Qed.
Lemma lem2601916 : term322 = False.
Proof. exact (TRANS (@lem2601859) (@lem2601915)). Qed.
Lemma lem2601917 : term321 = False.
Proof. exact (TRANS (@lem2601850) (@lem2601916)). Qed.
Lemma lem2601918 (c : int) (n : int) (m : int) (h1 : term256 c n m) : False.
Proof. exact (EQ_MP (@lem2601917) (@lem2601847 c n m h1)). Qed.
Lemma lem2601919 (c : int) (n : int) (m : int) (h1 : term334 c n m) : term334 c n m.
Proof. exact (h1). Qed.
Lemma lem2601920 (c : int) (n : int) (m : int) (h1 : term334 c n m) : (term157 c n m) = term160.
Proof. exact (proj2 (@lem2601919 c n m h1)). Qed.
Lemma lem2601921 (c : int) (n : int) (m : int) (h1 : term334 c n m) : term217 c n m.
Proof. exact (proj1 (@lem2601919 c n m h1)). Qed.
Lemma lem2601923 (c : int) (n : int) (m : int) (h1 : term334 c n m) : term205 c n m.
Proof. exact (proj1 (@lem2601921 c n m h1)). Qed.
Lemma lem2601925 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2601926 : term257 = term258.
Proof. exact (@lem2601925 term160 term63). Qed.
Lemma lem2601928 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2601929 : term63 = term151.
Proof. exact (@lem2601928 term64). Qed.
Lemma lem2601931 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2601932 : term160 = term259.
Proof. exact (@lem2601931 (NUMERAL 0)). Qed.
Lemma lem2601933 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2601934 : term260 = term261.
Proof. exact (MK_COMB (@lem2601933) (@lem2601932)). Qed.
Lemma lem2601935 : term258 = term262.
Proof. exact (MK_COMB (@lem2601934) (@lem2601929)). Qed.
Lemma lem2601936 : term263.
Proof. exact (@lem1980255 term160 term63 term63 term63). Qed.
Lemma lem2601938 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2601939 : term258 = term265.
Proof. exact (@lem2601938 (NUMERAL 0) term64). Qed.
Lemma lem2601940 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2601941 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2601942 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2601941 h1) (fun h1 : term265 = True => @lem2601940)). Qed.
Lemma lem2601943 : term265 = True.
Proof. exact (EQ_MP (@lem2601942) (@lem2601940)). Qed.
Lemma lem2601944 : term258 = True.
Proof. exact (TRANS (@lem2601939) (@lem2601943)). Qed.
Lemma lem2601945 : True = term258.
Proof. exact (SYM (@lem2601944)). Qed.
Lemma lem2601946 : term258.
Proof. exact (EQ_MP (@lem2601945) (@lem0)). Qed.
Lemma lem2601947 : term267.
Proof. exact (@lem2601936 (@lem2601946)). Qed.
Lemma lem2601949 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2601950 : term258 = term265.
Proof. exact (@lem2601949 (NUMERAL 0) term64). Qed.
Lemma lem2601951 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2601952 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2601953 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2601952 h1) (fun h1 : term265 = True => @lem2601951)). Qed.
Lemma lem2601954 : term265 = True.
Proof. exact (EQ_MP (@lem2601953) (@lem2601951)). Qed.
Lemma lem2601955 : term258 = True.
Proof. exact (TRANS (@lem2601950) (@lem2601954)). Qed.
Lemma lem2601956 : True = term258.
Proof. exact (SYM (@lem2601955)). Qed.
Lemma lem2601957 : term258.
Proof. exact (EQ_MP (@lem2601956) (@lem0)). Qed.
Lemma lem2601958 : term262 = term268.
Proof. exact (@lem2601947 (@lem2601957)). Qed.
Lemma lem2601960 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2601961 : term144 = term145.
Proof. exact (@lem2601960 term64 term64). Qed.
Lemma lem2601962 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2601963 : term147 = term64.
Proof. exact (EQ_MP (@lem2601962) (@lem940073)). Qed.
Lemma lem2601964 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2601965 : term145 = term63.
Proof. exact (MK_COMB (@lem2601964) (@lem2601963)). Qed.
Lemma lem2601966 : term144 = term63.
Proof. exact (TRANS (@lem2601961) (@lem2601965)). Qed.
Lemma lem2601968 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2601969 : term270 = term160.
Proof. exact (@lem2601968 term64). Qed.
Lemma lem2601970 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2601971 : term271 = term260.
Proof. exact (MK_COMB (@lem2601970) (@lem2601969)). Qed.
Lemma lem2601972 : term268 = term258.
Proof. exact (MK_COMB (@lem2601971) (@lem2601966)). Qed.
Lemma lem2601974 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2601975 : term258 = term265.
Proof. exact (@lem2601974 (NUMERAL 0) term64). Qed.
Lemma lem2601976 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2601977 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2601978 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2601977 h1) (fun h1 : term265 = True => @lem2601976)). Qed.
Lemma lem2601979 : term265 = True.
Proof. exact (EQ_MP (@lem2601978) (@lem2601976)). Qed.
Lemma lem2601980 : term258 = True.
Proof. exact (TRANS (@lem2601975) (@lem2601979)). Qed.
Lemma lem2601981 : term268 = True.
Proof. exact (TRANS (@lem2601972) (@lem2601980)). Qed.
Lemma lem2601982 : term262 = True.
Proof. exact (TRANS (@lem2601958) (@lem2601981)). Qed.
Lemma lem2601983 : term258 = True.
Proof. exact (TRANS (@lem2601935) (@lem2601982)). Qed.
Lemma lem2601984 : term257 = True.
Proof. exact (TRANS (@lem2601926) (@lem2601983)). Qed.
Lemma lem2601985 : True = term257.
Proof. exact (SYM (@lem2601984)). Qed.
Lemma lem2601986 : term257.
Proof. exact (EQ_MP (@lem2601985) (@lem0)). Qed.
Lemma lem2601987 (c : int) (n : int) (m : int) (h1 : term334 c n m) : term335 c n m.
Proof. exact (conj (@lem2601986) (@lem2601923 c n m h1)). Qed.
Lemma lem2601989 (x : real) (y : real) : term273 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2601990 (c : int) (n : int) (m : int) : term336 c n m.
Proof. exact (@lem2601989 term63 (term202 c n m)). Qed.
Lemma lem2601991 (c : int) (n : int) (m : int) (h1 : term334 c n m) : term337 c n m.
Proof. exact (@lem2601990 c n m (@lem2601987 c n m h1)). Qed.
Lemma lem2601992 (c : int) (n : int) (m : int) : (term338 c n m) = (term202 c n m).
Proof. exact (@lem1982733 (term202 c n m)). Qed.
Lemma lem2601993 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2601994 (c : int) (n : int) (m : int) : (term339 c n m) = (term204 c n m).
Proof. exact (MK_COMB (@lem2601993) (@lem2601992 c n m)). Qed.
Lemma lem2601995 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2601996 (c : int) (n : int) (m : int) : (term337 c n m) = (term205 c n m).
Proof. exact (MK_COMB (@lem2601994 c n m) (@lem2601995)). Qed.
Lemma lem2601997 (c : int) (n : int) (m : int) (h1 : term334 c n m) : term205 c n m.
Proof. exact (EQ_MP (@lem2601996 c n m) (@lem2601991 c n m h1)). Qed.
Lemma lem2601999 (y : real) : term278 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2602000 (c : int) (n : int) (m : int) : term279 c n m.
Proof. exact (@lem2601999 (term157 c n m)). Qed.
Lemma lem2602001 (c : int) (n : int) (m : int) (h1 : term334 c n m) : term280 c n m.
Proof. exact (@lem2602000 c n m (@lem2601920 c n m h1)). Qed.
Lemma lem2602002 (c : int) (n : int) (m : int) (h1 : term334 c n m) : term340 c n m.
Proof. exact (@lem2602001 c n m h1 term63). Qed.
Lemma lem2602003 (c : int) (n : int) (m : int) : (term340 c n m) = ((term341 c n m) = term160).
Proof. exact (eq_refl (term340 c n m)). Qed.
Lemma lem2602004 (c : int) (n : int) (m : int) (h1 : term334 c n m) : (term341 c n m) = term160.
Proof. exact (EQ_MP (@lem2602003 c n m) (@lem2602002 c n m h1)). Qed.
Lemma lem2602005 (c : int) (n : int) (m : int) : (term341 c n m) = (term157 c n m).
Proof. exact (@lem1982733 (term157 c n m)). Qed.
Lemma lem2602006 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2602007 (c : int) (n : int) (m : int) : (term342 c n m) = (term221 c n m).
Proof. exact (MK_COMB (@lem2602006) (@lem2602005 c n m)). Qed.
Lemma lem2602008 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2602009 (c : int) (n : int) (m : int) : ((term341 c n m) = term160) = ((term157 c n m) = term160).
Proof. exact (MK_COMB (@lem2602007 c n m) (@lem2602008)). Qed.
Lemma lem2602010 (c : int) (n : int) (m : int) (h1 : term334 c n m) : (term157 c n m) = term160.
Proof. exact (EQ_MP (@lem2602009 c n m) (@lem2602004 c n m h1)). Qed.
Lemma lem2602011 (c : int) (n : int) (m : int) (h1 : term334 c n m) : term343 c n m.
Proof. exact (conj (@lem2602010 c n m h1) (@lem2601997 c n m h1)). Qed.
Lemma lem2602013 (x : real) (y : real) : term286 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2602014 (c : int) (n : int) (m : int) : term344 c n m.
Proof. exact (@lem2602013 (term157 c n m) (term202 c n m)). Qed.
Lemma lem2602015 (c : int) (n : int) (m : int) (h1 : term334 c n m) : term345 c n m.
Proof. exact (@lem2602014 c n m (@lem2602011 c n m h1)). Qed.
Lemma lem2602016 (c : int) (n : int) (m : int) : (term346 c n m) = (term347 c n m).
Proof. exact (@lem1982753 (term40 c n) (term126 c n) (real_of_int m) (term200 m)). Qed.
Lemma lem2602017 (c : int) (n : int) : (term348 c n) = (term292 c n).
Proof. exact (@lem1982715 term127 (term40 c n)). Qed.
Lemma lem2602019 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2602020 : term63 = term151.
Proof. exact (@lem2602019 term64). Qed.
Lemma lem2602022 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2602023 : term127 = term137.
Proof. exact (@lem2602022 term64). Qed.
Lemma lem2602024 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2602025 : term293 = term294.
Proof. exact (MK_COMB (@lem2602024) (@lem2602023)). Qed.
Lemma lem2602026 : term295 = term296.
Proof. exact (MK_COMB (@lem2602025) (@lem2602020)). Qed.
Lemma lem2602027 : term297.
Proof. exact (@lem1981473 term127 term63 term63 term63 term160 term63). Qed.
Lemma lem2602029 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602030 : term258 = term265.
Proof. exact (@lem2602029 (NUMERAL 0) term64). Qed.
Lemma lem2602031 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602032 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602033 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602032 h1) (fun h1 : term265 = True => @lem2602031)). Qed.
Lemma lem2602034 : term265 = True.
Proof. exact (EQ_MP (@lem2602033) (@lem2602031)). Qed.
Lemma lem2602035 : term258 = True.
Proof. exact (TRANS (@lem2602030) (@lem2602034)). Qed.
Lemma lem2602036 : True = term258.
Proof. exact (SYM (@lem2602035)). Qed.
Lemma lem2602037 : term258.
Proof. exact (EQ_MP (@lem2602036) (@lem0)). Qed.
Lemma lem2602038 : term298.
Proof. exact (@lem2602027 (@lem2602037)). Qed.
Lemma lem2602040 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602041 : term258 = term265.
Proof. exact (@lem2602040 (NUMERAL 0) term64). Qed.
Lemma lem2602042 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602043 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602044 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602043 h1) (fun h1 : term265 = True => @lem2602042)). Qed.
Lemma lem2602045 : term265 = True.
Proof. exact (EQ_MP (@lem2602044) (@lem2602042)). Qed.
Lemma lem2602046 : term258 = True.
Proof. exact (TRANS (@lem2602041) (@lem2602045)). Qed.
Lemma lem2602047 : True = term258.
Proof. exact (SYM (@lem2602046)). Qed.
Lemma lem2602048 : term258.
Proof. exact (EQ_MP (@lem2602047) (@lem0)). Qed.
Lemma lem2602049 : term299.
Proof. exact (@lem2602038 (@lem2602048)). Qed.
Lemma lem2602051 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602052 : term258 = term265.
Proof. exact (@lem2602051 (NUMERAL 0) term64). Qed.
Lemma lem2602053 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602054 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602055 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602054 h1) (fun h1 : term265 = True => @lem2602053)). Qed.
Lemma lem2602056 : term265 = True.
Proof. exact (EQ_MP (@lem2602055) (@lem2602053)). Qed.
Lemma lem2602057 : term258 = True.
Proof. exact (TRANS (@lem2602052) (@lem2602056)). Qed.
Lemma lem2602058 : True = term258.
Proof. exact (SYM (@lem2602057)). Qed.
Lemma lem2602059 : term258.
Proof. exact (EQ_MP (@lem2602058) (@lem0)). Qed.
Lemma lem2602060 : term300.
Proof. exact (@lem2602049 (@lem2602059)). Qed.
Lemma lem2602062 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2602063 : term144 = term145.
Proof. exact (@lem2602062 term64 term64). Qed.
Lemma lem2602064 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2602065 : term147 = term64.
Proof. exact (EQ_MP (@lem2602064) (@lem940073)). Qed.
Lemma lem2602066 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2602067 : term145 = term63.
Proof. exact (MK_COMB (@lem2602066) (@lem2602065)). Qed.
Lemma lem2602068 : term144 = term63.
Proof. exact (TRANS (@lem2602063) (@lem2602067)). Qed.
Lemma lem2602070 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2602071 : term172 = term177.
Proof. exact (@lem2602070 term64 term64). Qed.
Lemma lem2602072 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2602073 : term147 = term64.
Proof. exact (EQ_MP (@lem2602072) (@lem940073)). Qed.
Lemma lem2602074 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2602075 : term145 = term63.
Proof. exact (MK_COMB (@lem2602074) (@lem2602073)). Qed.
Lemma lem2602076 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2602077 : term177 = term127.
Proof. exact (MK_COMB (@lem2602076) (@lem2602075)). Qed.
Lemma lem2602078 : term172 = term127.
Proof. exact (TRANS (@lem2602071) (@lem2602077)). Qed.
Lemma lem2602079 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2602080 : term301 = term293.
Proof. exact (MK_COMB (@lem2602079) (@lem2602078)). Qed.
Lemma lem2602081 : term302 = term295.
Proof. exact (MK_COMB (@lem2602080) (@lem2602068)). Qed.
Lemma lem2602083 (m : nat) : (term303 m) = term160.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2602084 : term295 = term160.
Proof. exact (@lem2602083 term64). Qed.
Lemma lem2602085 : term302 = term160.
Proof. exact (TRANS (@lem2602081) (@lem2602084)). Qed.
Lemma lem2602086 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2602087 : term304 = term305.
Proof. exact (MK_COMB (@lem2602086) (@lem2602085)). Qed.
Lemma lem2602088 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2602089 : term306 = term270.
Proof. exact (MK_COMB (@lem2602087) (@lem2602088)). Qed.
Lemma lem2602091 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2602092 : term270 = term160.
Proof. exact (@lem2602091 term64). Qed.
Lemma lem2602093 : term306 = term160.
Proof. exact (TRANS (@lem2602089) (@lem2602092)). Qed.
Lemma lem2602095 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2602096 : term144 = term145.
Proof. exact (@lem2602095 term64 term64). Qed.
Lemma lem2602097 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2602098 : term147 = term64.
Proof. exact (EQ_MP (@lem2602097) (@lem940073)). Qed.
Lemma lem2602099 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2602100 : term145 = term63.
Proof. exact (MK_COMB (@lem2602099) (@lem2602098)). Qed.
Lemma lem2602101 : term144 = term63.
Proof. exact (TRANS (@lem2602096) (@lem2602100)). Qed.
Lemma lem2602102 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem2602103 : term307 = term270.
Proof. exact (MK_COMB (@lem2602102) (@lem2602101)). Qed.
Lemma lem2602105 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2602106 : term270 = term160.
Proof. exact (@lem2602105 term64). Qed.
Lemma lem2602107 : term307 = term160.
Proof. exact (TRANS (@lem2602103) (@lem2602106)). Qed.
Lemma lem2602108 : term160 = term307.
Proof. exact (SYM (@lem2602107)). Qed.
Lemma lem2602109 : term306 = term307.
Proof. exact (TRANS (@lem2602093) (@lem2602108)). Qed.
Lemma lem2602110 : term296 = term259.
Proof. exact (@lem2602060 (@lem2602109)). Qed.
Lemma lem2602111 : term295 = term259.
Proof. exact (TRANS (@lem2602026) (@lem2602110)). Qed.
Lemma lem2602113 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2602114 : term259 = term160.
Proof. exact (@lem2602113 term160). Qed.
Lemma lem2602115 : term295 = term160.
Proof. exact (TRANS (@lem2602111) (@lem2602114)). Qed.
Lemma lem2602116 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2602117 : term308 = term305.
Proof. exact (MK_COMB (@lem2602116) (@lem2602115)). Qed.
Lemma lem2602118 (c : int) (n : int) : (term40 c n) = (term40 c n).
Proof. exact (eq_refl (term40 c n)). Qed.
Lemma lem2602119 (c : int) (n : int) : (term292 c n) = (term309 c n).
Proof. exact (MK_COMB (@lem2602117) (@lem2602118 c n)). Qed.
Lemma lem2602120 (c : int) (n : int) : (term348 c n) = (term309 c n).
Proof. exact (TRANS (@lem2602017 c n) (@lem2602119 c n)). Qed.
Lemma lem2602121 (c : int) (n : int) : (term309 c n) = term160.
Proof. exact (@lem1982719 (term40 c n)). Qed.
Lemma lem2602122 (c : int) (n : int) : (term348 c n) = term160.
Proof. exact (TRANS (@lem2602120 c n) (@lem2602121 c n)). Qed.
Lemma lem2602123 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2602124 (c : int) (n : int) : (term349 c n) = term311.
Proof. exact (MK_COMB (@lem2602123) (@lem2602122 c n)). Qed.
Lemma lem2602125 (m : int) : (term350 m) = (term351 m).
Proof. exact (@lem1982763 (real_of_int m) (term124 m) term127). Qed.
Lemma lem2602126 (m : int) : (term352 m) = (term315 m).
Proof. exact (@lem1982715 term127 (real_of_int m)). Qed.
Lemma lem2602128 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2602129 : term63 = term151.
Proof. exact (@lem2602128 term64). Qed.
Lemma lem2602131 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2602132 : term127 = term137.
Proof. exact (@lem2602131 term64). Qed.
Lemma lem2602133 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2602134 : term293 = term294.
Proof. exact (MK_COMB (@lem2602133) (@lem2602132)). Qed.
Lemma lem2602135 : term295 = term296.
Proof. exact (MK_COMB (@lem2602134) (@lem2602129)). Qed.
Lemma lem2602136 : term297.
Proof. exact (@lem1981473 term127 term63 term63 term63 term160 term63). Qed.
Lemma lem2602138 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602139 : term258 = term265.
Proof. exact (@lem2602138 (NUMERAL 0) term64). Qed.
Lemma lem2602140 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602141 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602142 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602141 h1) (fun h1 : term265 = True => @lem2602140)). Qed.
Lemma lem2602143 : term265 = True.
Proof. exact (EQ_MP (@lem2602142) (@lem2602140)). Qed.
Lemma lem2602144 : term258 = True.
Proof. exact (TRANS (@lem2602139) (@lem2602143)). Qed.
Lemma lem2602145 : True = term258.
Proof. exact (SYM (@lem2602144)). Qed.
Lemma lem2602146 : term258.
Proof. exact (EQ_MP (@lem2602145) (@lem0)). Qed.
Lemma lem2602147 : term298.
Proof. exact (@lem2602136 (@lem2602146)). Qed.
Lemma lem2602149 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602150 : term258 = term265.
Proof. exact (@lem2602149 (NUMERAL 0) term64). Qed.
Lemma lem2602151 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602152 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602153 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602152 h1) (fun h1 : term265 = True => @lem2602151)). Qed.
Lemma lem2602154 : term265 = True.
Proof. exact (EQ_MP (@lem2602153) (@lem2602151)). Qed.
Lemma lem2602155 : term258 = True.
Proof. exact (TRANS (@lem2602150) (@lem2602154)). Qed.
Lemma lem2602156 : True = term258.
Proof. exact (SYM (@lem2602155)). Qed.
Lemma lem2602157 : term258.
Proof. exact (EQ_MP (@lem2602156) (@lem0)). Qed.
Lemma lem2602158 : term299.
Proof. exact (@lem2602147 (@lem2602157)). Qed.
Lemma lem2602160 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602161 : term258 = term265.
Proof. exact (@lem2602160 (NUMERAL 0) term64). Qed.
Lemma lem2602162 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602163 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602164 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602163 h1) (fun h1 : term265 = True => @lem2602162)). Qed.
Lemma lem2602165 : term265 = True.
Proof. exact (EQ_MP (@lem2602164) (@lem2602162)). Qed.
Lemma lem2602166 : term258 = True.
Proof. exact (TRANS (@lem2602161) (@lem2602165)). Qed.
Lemma lem2602167 : True = term258.
Proof. exact (SYM (@lem2602166)). Qed.
Lemma lem2602168 : term258.
Proof. exact (EQ_MP (@lem2602167) (@lem0)). Qed.
Lemma lem2602169 : term300.
Proof. exact (@lem2602158 (@lem2602168)). Qed.
Lemma lem2602171 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2602172 : term144 = term145.
Proof. exact (@lem2602171 term64 term64). Qed.
Lemma lem2602173 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2602174 : term147 = term64.
Proof. exact (EQ_MP (@lem2602173) (@lem940073)). Qed.
Lemma lem2602175 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2602176 : term145 = term63.
Proof. exact (MK_COMB (@lem2602175) (@lem2602174)). Qed.
Lemma lem2602177 : term144 = term63.
Proof. exact (TRANS (@lem2602172) (@lem2602176)). Qed.
Lemma lem2602179 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2602180 : term172 = term177.
Proof. exact (@lem2602179 term64 term64). Qed.
Lemma lem2602181 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2602182 : term147 = term64.
Proof. exact (EQ_MP (@lem2602181) (@lem940073)). Qed.
Lemma lem2602183 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2602184 : term145 = term63.
Proof. exact (MK_COMB (@lem2602183) (@lem2602182)). Qed.
Lemma lem2602185 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2602186 : term177 = term127.
Proof. exact (MK_COMB (@lem2602185) (@lem2602184)). Qed.
Lemma lem2602187 : term172 = term127.
Proof. exact (TRANS (@lem2602180) (@lem2602186)). Qed.
Lemma lem2602188 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2602189 : term301 = term293.
Proof. exact (MK_COMB (@lem2602188) (@lem2602187)). Qed.
Lemma lem2602190 : term302 = term295.
Proof. exact (MK_COMB (@lem2602189) (@lem2602177)). Qed.
Lemma lem2602192 (m : nat) : (term303 m) = term160.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2602193 : term295 = term160.
Proof. exact (@lem2602192 term64). Qed.
Lemma lem2602194 : term302 = term160.
Proof. exact (TRANS (@lem2602190) (@lem2602193)). Qed.
Lemma lem2602195 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2602196 : term304 = term305.
Proof. exact (MK_COMB (@lem2602195) (@lem2602194)). Qed.
Lemma lem2602197 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2602198 : term306 = term270.
Proof. exact (MK_COMB (@lem2602196) (@lem2602197)). Qed.
Lemma lem2602200 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2602201 : term270 = term160.
Proof. exact (@lem2602200 term64). Qed.
Lemma lem2602202 : term306 = term160.
Proof. exact (TRANS (@lem2602198) (@lem2602201)). Qed.
Lemma lem2602204 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2602205 : term144 = term145.
Proof. exact (@lem2602204 term64 term64). Qed.
Lemma lem2602206 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2602207 : term147 = term64.
Proof. exact (EQ_MP (@lem2602206) (@lem940073)). Qed.
Lemma lem2602208 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2602209 : term145 = term63.
Proof. exact (MK_COMB (@lem2602208) (@lem2602207)). Qed.
Lemma lem2602210 : term144 = term63.
Proof. exact (TRANS (@lem2602205) (@lem2602209)). Qed.
Lemma lem2602211 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem2602212 : term307 = term270.
Proof. exact (MK_COMB (@lem2602211) (@lem2602210)). Qed.
Lemma lem2602214 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2602215 : term270 = term160.
Proof. exact (@lem2602214 term64). Qed.
Lemma lem2602216 : term307 = term160.
Proof. exact (TRANS (@lem2602212) (@lem2602215)). Qed.
Lemma lem2602217 : term160 = term307.
Proof. exact (SYM (@lem2602216)). Qed.
Lemma lem2602218 : term306 = term307.
Proof. exact (TRANS (@lem2602202) (@lem2602217)). Qed.
Lemma lem2602219 : term296 = term259.
Proof. exact (@lem2602169 (@lem2602218)). Qed.
Lemma lem2602220 : term295 = term259.
Proof. exact (TRANS (@lem2602135) (@lem2602219)). Qed.
Lemma lem2602222 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2602223 : term259 = term160.
Proof. exact (@lem2602222 term160). Qed.
Lemma lem2602224 : term295 = term160.
Proof. exact (TRANS (@lem2602220) (@lem2602223)). Qed.
Lemma lem2602225 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2602226 : term308 = term305.
Proof. exact (MK_COMB (@lem2602225) (@lem2602224)). Qed.
Lemma lem2602227 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2602228 (m : int) : (term315 m) = (term316 m).
Proof. exact (MK_COMB (@lem2602226) (@lem2602227 m)). Qed.
Lemma lem2602229 (m : int) : (term352 m) = (term316 m).
Proof. exact (TRANS (@lem2602126 m) (@lem2602228 m)). Qed.
Lemma lem2602230 (m : int) : (term316 m) = term160.
Proof. exact (@lem1982719 (real_of_int m)). Qed.
Lemma lem2602231 (m : int) : (term352 m) = term160.
Proof. exact (TRANS (@lem2602229 m) (@lem2602230 m)). Qed.
Lemma lem2602232 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2602233 (m : int) : (term353 m) = term311.
Proof. exact (MK_COMB (@lem2602232) (@lem2602231 m)). Qed.
Lemma lem2602234 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem2602235 (m : int) : (term351 m) = term318.
Proof. exact (MK_COMB (@lem2602233 m) (@lem2602234)). Qed.
Lemma lem2602236 (m : int) : (term350 m) = term318.
Proof. exact (TRANS (@lem2602125 m) (@lem2602235 m)). Qed.
Lemma lem2602237 : term318 = term127.
Proof. exact (@lem1982721 term127). Qed.
Lemma lem2602238 (m : int) : (term350 m) = term127.
Proof. exact (TRANS (@lem2602236 m) (@lem2602237)). Qed.
Lemma lem2602239 (c : int) (n : int) (m : int) : (term347 c n m) = term318.
Proof. exact (MK_COMB (@lem2602124 c n) (@lem2602238 m)). Qed.
Lemma lem2602240 (c : int) (n : int) (m : int) : (term346 c n m) = term318.
Proof. exact (TRANS (@lem2602016 c n m) (@lem2602239 c n m)). Qed.
Lemma lem2602241 : term318 = term127.
Proof. exact (@lem1982721 term127). Qed.
Lemma lem2602242 (c : int) (n : int) (m : int) : (term346 c n m) = term127.
Proof. exact (TRANS (@lem2602240 c n m) (@lem2602241)). Qed.
Lemma lem2602243 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2602244 (c : int) (n : int) (m : int) : (term354 c n m) = term320.
Proof. exact (MK_COMB (@lem2602243) (@lem2602242 c n m)). Qed.
Lemma lem2602245 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2602246 (c : int) (n : int) (m : int) : (term345 c n m) = term321.
Proof. exact (MK_COMB (@lem2602244 c n m) (@lem2602245)). Qed.
Lemma lem2602247 (c : int) (n : int) (m : int) (h1 : term334 c n m) : term321.
Proof. exact (EQ_MP (@lem2602246 c n m) (@lem2602015 c n m h1)). Qed.
Lemma lem2602249 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2602250 : term321 = term322.
Proof. exact (@lem2602249 term160 term127). Qed.
Lemma lem2602252 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2602253 : term127 = term137.
Proof. exact (@lem2602252 term64). Qed.
Lemma lem2602255 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2602256 : term160 = term259.
Proof. exact (@lem2602255 (NUMERAL 0)). Qed.
Lemma lem2602257 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2602258 : term323 = term324.
Proof. exact (MK_COMB (@lem2602257) (@lem2602256)). Qed.
Lemma lem2602259 : term322 = term325.
Proof. exact (MK_COMB (@lem2602258) (@lem2602253)). Qed.
Lemma lem2602260 : term326.
Proof. exact (@lem1980026 term160 term63 term127 term63). Qed.
Lemma lem2602262 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602263 : term258 = term265.
Proof. exact (@lem2602262 (NUMERAL 0) term64). Qed.
Lemma lem2602264 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602265 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602266 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602265 h1) (fun h1 : term265 = True => @lem2602264)). Qed.
Lemma lem2602267 : term265 = True.
Proof. exact (EQ_MP (@lem2602266) (@lem2602264)). Qed.
Lemma lem2602268 : term258 = True.
Proof. exact (TRANS (@lem2602263) (@lem2602267)). Qed.
Lemma lem2602269 : True = term258.
Proof. exact (SYM (@lem2602268)). Qed.
Lemma lem2602270 : term258.
Proof. exact (EQ_MP (@lem2602269) (@lem0)). Qed.
Lemma lem2602271 : term327.
Proof. exact (@lem2602260 (@lem2602270)). Qed.
Lemma lem2602273 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602274 : term258 = term265.
Proof. exact (@lem2602273 (NUMERAL 0) term64). Qed.
Lemma lem2602275 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602276 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602277 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602276 h1) (fun h1 : term265 = True => @lem2602275)). Qed.
Lemma lem2602278 : term265 = True.
Proof. exact (EQ_MP (@lem2602277) (@lem2602275)). Qed.
Lemma lem2602279 : term258 = True.
Proof. exact (TRANS (@lem2602274) (@lem2602278)). Qed.
Lemma lem2602280 : True = term258.
Proof. exact (SYM (@lem2602279)). Qed.
Lemma lem2602281 : term258.
Proof. exact (EQ_MP (@lem2602280) (@lem0)). Qed.
Lemma lem2602282 : term325 = term328.
Proof. exact (@lem2602271 (@lem2602281)). Qed.
Lemma lem2602284 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2602285 : term172 = term177.
Proof. exact (@lem2602284 term64 term64). Qed.
Lemma lem2602286 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2602287 : term147 = term64.
Proof. exact (EQ_MP (@lem2602286) (@lem940073)). Qed.
Lemma lem2602288 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2602289 : term145 = term63.
Proof. exact (MK_COMB (@lem2602288) (@lem2602287)). Qed.
Lemma lem2602290 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2602291 : term177 = term127.
Proof. exact (MK_COMB (@lem2602290) (@lem2602289)). Qed.
Lemma lem2602292 : term172 = term127.
Proof. exact (TRANS (@lem2602285) (@lem2602291)). Qed.
Lemma lem2602294 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2602295 : term270 = term160.
Proof. exact (@lem2602294 term64). Qed.
Lemma lem2602296 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2602297 : term329 = term323.
Proof. exact (MK_COMB (@lem2602296) (@lem2602295)). Qed.
Lemma lem2602298 : term328 = term322.
Proof. exact (MK_COMB (@lem2602297) (@lem2602292)). Qed.
Lemma lem2602300 (m : nat) (n : nat) : (term330 m n) = (term331 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2602301 : term322 = term332.
Proof. exact (@lem2602300 (NUMERAL 0) term64). Qed.
Lemma lem2602302 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602303 (h1 : term266 = (BIT1 0)) : (term64 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2602304 : (term266 = (BIT1 0)) = ((term64 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602303 h1) (fun h1 : (term64 = (NUMERAL 0)) = False => @lem2602302)). Qed.
Lemma lem2602305 : (term64 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2602304) (@lem2602302)). Qed.
Lemma lem2602306 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2602307 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2602308 : term333 = (and True).
Proof. exact (MK_COMB (@lem2602307) (@lem2602306)). Qed.
Lemma lem2602309 : term332 = (True /\ False).
Proof. exact (MK_COMB (@lem2602308) (@lem2602305)). Qed.
Lemma lem2602311 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2602312 : term332 = False.
Proof. exact (TRANS (@lem2602309) (@lem2602311)). Qed.
Lemma lem2602313 : term322 = False.
Proof. exact (TRANS (@lem2602301) (@lem2602312)). Qed.
Lemma lem2602314 : term328 = False.
Proof. exact (TRANS (@lem2602298) (@lem2602313)). Qed.
Lemma lem2602315 : term325 = False.
Proof. exact (TRANS (@lem2602282) (@lem2602314)). Qed.
Lemma lem2602316 : term322 = False.
Proof. exact (TRANS (@lem2602259) (@lem2602315)). Qed.
Lemma lem2602317 : term321 = False.
Proof. exact (TRANS (@lem2602250) (@lem2602316)). Qed.
Lemma lem2602318 (c : int) (n : int) (m : int) (h1 : term334 c n m) : False.
Proof. exact (EQ_MP (@lem2602317) (@lem2602247 c n m h1)). Qed.
Lemma lem2602319 (c : int) (n : int) (m : int) (h1 : term253 c n m) : False.
Proof. exact (or_elim (@lem2601512 c n m h1) (fun h0 : term256 c n m => @lem2601918 c n m h0) (fun h0 : term334 c n m => @lem2602318 c n m h0)). Qed.
Lemma lem2602320 (c : int) (n : int) (m : int) (h1 : term252 c n m) : term252 c n m.
Proof. exact (h1). Qed.
Lemma lem2602321 (c : int) (n : int) (m : int) (h1 : term249 c n m) : term249 c n m.
Proof. exact (h1). Qed.
Lemma lem2602322 (c : int) (n : int) (m : int) (h1 : term355 c n m) : term355 c n m.
Proof. exact (h1). Qed.
Lemma lem2602323 (c : int) (n : int) (m : int) (h1 : term355 c n m) : term205 c n m.
Proof. exact (proj2 (@lem2602322 c n m h1)). Qed.
Lemma lem2602324 (c : int) (n : int) (m : int) (h1 : term355 c n m) : term224 c n m.
Proof. exact (proj1 (@lem2602322 c n m h1)). Qed.
Lemma lem2602326 (c : int) (n : int) (m : int) (h1 : term355 c n m) : term161 c n m.
Proof. exact (proj1 (@lem2602324 c n m h1)). Qed.
Lemma lem2602328 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2602329 : term257 = term258.
Proof. exact (@lem2602328 term160 term63). Qed.
Lemma lem2602331 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2602332 : term63 = term151.
Proof. exact (@lem2602331 term64). Qed.
Lemma lem2602334 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2602335 : term160 = term259.
Proof. exact (@lem2602334 (NUMERAL 0)). Qed.
Lemma lem2602336 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2602337 : term260 = term261.
Proof. exact (MK_COMB (@lem2602336) (@lem2602335)). Qed.
Lemma lem2602338 : term258 = term262.
Proof. exact (MK_COMB (@lem2602337) (@lem2602332)). Qed.
Lemma lem2602339 : term263.
Proof. exact (@lem1980255 term160 term63 term63 term63). Qed.
Lemma lem2602341 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602342 : term258 = term265.
Proof. exact (@lem2602341 (NUMERAL 0) term64). Qed.
Lemma lem2602343 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602344 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602345 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602344 h1) (fun h1 : term265 = True => @lem2602343)). Qed.
Lemma lem2602346 : term265 = True.
Proof. exact (EQ_MP (@lem2602345) (@lem2602343)). Qed.
Lemma lem2602347 : term258 = True.
Proof. exact (TRANS (@lem2602342) (@lem2602346)). Qed.
Lemma lem2602348 : True = term258.
Proof. exact (SYM (@lem2602347)). Qed.
Lemma lem2602349 : term258.
Proof. exact (EQ_MP (@lem2602348) (@lem0)). Qed.
Lemma lem2602350 : term267.
Proof. exact (@lem2602339 (@lem2602349)). Qed.
Lemma lem2602352 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602353 : term258 = term265.
Proof. exact (@lem2602352 (NUMERAL 0) term64). Qed.
Lemma lem2602354 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602355 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602356 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602355 h1) (fun h1 : term265 = True => @lem2602354)). Qed.
Lemma lem2602357 : term265 = True.
Proof. exact (EQ_MP (@lem2602356) (@lem2602354)). Qed.
Lemma lem2602358 : term258 = True.
Proof. exact (TRANS (@lem2602353) (@lem2602357)). Qed.
Lemma lem2602359 : True = term258.
Proof. exact (SYM (@lem2602358)). Qed.
Lemma lem2602360 : term258.
Proof. exact (EQ_MP (@lem2602359) (@lem0)). Qed.
Lemma lem2602361 : term262 = term268.
Proof. exact (@lem2602350 (@lem2602360)). Qed.
Lemma lem2602363 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2602364 : term144 = term145.
Proof. exact (@lem2602363 term64 term64). Qed.
Lemma lem2602365 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2602366 : term147 = term64.
Proof. exact (EQ_MP (@lem2602365) (@lem940073)). Qed.
Lemma lem2602367 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2602368 : term145 = term63.
Proof. exact (MK_COMB (@lem2602367) (@lem2602366)). Qed.
Lemma lem2602369 : term144 = term63.
Proof. exact (TRANS (@lem2602364) (@lem2602368)). Qed.
Lemma lem2602371 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2602372 : term270 = term160.
Proof. exact (@lem2602371 term64). Qed.
Lemma lem2602373 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2602374 : term271 = term260.
Proof. exact (MK_COMB (@lem2602373) (@lem2602372)). Qed.
Lemma lem2602375 : term268 = term258.
Proof. exact (MK_COMB (@lem2602374) (@lem2602369)). Qed.
Lemma lem2602377 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602378 : term258 = term265.
Proof. exact (@lem2602377 (NUMERAL 0) term64). Qed.
Lemma lem2602379 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602380 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602381 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602380 h1) (fun h1 : term265 = True => @lem2602379)). Qed.
Lemma lem2602382 : term265 = True.
Proof. exact (EQ_MP (@lem2602381) (@lem2602379)). Qed.
Lemma lem2602383 : term258 = True.
Proof. exact (TRANS (@lem2602378) (@lem2602382)). Qed.
Lemma lem2602384 : term268 = True.
Proof. exact (TRANS (@lem2602375) (@lem2602383)). Qed.
Lemma lem2602385 : term262 = True.
Proof. exact (TRANS (@lem2602361) (@lem2602384)). Qed.
Lemma lem2602386 : term258 = True.
Proof. exact (TRANS (@lem2602338) (@lem2602385)). Qed.
Lemma lem2602387 : term257 = True.
Proof. exact (TRANS (@lem2602329) (@lem2602386)). Qed.
Lemma lem2602388 : True = term257.
Proof. exact (SYM (@lem2602387)). Qed.
Lemma lem2602389 : term257.
Proof. exact (EQ_MP (@lem2602388) (@lem0)). Qed.
Lemma lem2602390 (c : int) (n : int) (m : int) (h1 : term355 c n m) : term356 c n m.
Proof. exact (conj (@lem2602389) (@lem2602326 c n m h1)). Qed.
Lemma lem2602392 (x : real) (y : real) : term273 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2602393 (c : int) (n : int) (m : int) : term357 c n m.
Proof. exact (@lem2602392 term63 (term157 c n m)). Qed.
Lemma lem2602394 (c : int) (n : int) (m : int) (h1 : term355 c n m) : term358 c n m.
Proof. exact (@lem2602393 c n m (@lem2602390 c n m h1)). Qed.
Lemma lem2602395 (c : int) (n : int) (m : int) : (term341 c n m) = (term157 c n m).
Proof. exact (@lem1982733 (term157 c n m)). Qed.
Lemma lem2602396 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2602397 (c : int) (n : int) (m : int) : (term359 c n m) = (term159 c n m).
Proof. exact (MK_COMB (@lem2602396) (@lem2602395 c n m)). Qed.
Lemma lem2602398 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2602399 (c : int) (n : int) (m : int) : (term358 c n m) = (term161 c n m).
Proof. exact (MK_COMB (@lem2602397 c n m) (@lem2602398)). Qed.
Lemma lem2602400 (c : int) (n : int) (m : int) (h1 : term355 c n m) : term161 c n m.
Proof. exact (EQ_MP (@lem2602399 c n m) (@lem2602394 c n m h1)). Qed.
Lemma lem2602402 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2602403 : term257 = term258.
Proof. exact (@lem2602402 term160 term63). Qed.
Lemma lem2602405 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2602406 : term63 = term151.
Proof. exact (@lem2602405 term64). Qed.
Lemma lem2602408 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2602409 : term160 = term259.
Proof. exact (@lem2602408 (NUMERAL 0)). Qed.
Lemma lem2602410 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2602411 : term260 = term261.
Proof. exact (MK_COMB (@lem2602410) (@lem2602409)). Qed.
Lemma lem2602412 : term258 = term262.
Proof. exact (MK_COMB (@lem2602411) (@lem2602406)). Qed.
Lemma lem2602413 : term263.
Proof. exact (@lem1980255 term160 term63 term63 term63). Qed.
Lemma lem2602415 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602416 : term258 = term265.
Proof. exact (@lem2602415 (NUMERAL 0) term64). Qed.
Lemma lem2602417 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602418 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602419 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602418 h1) (fun h1 : term265 = True => @lem2602417)). Qed.
Lemma lem2602420 : term265 = True.
Proof. exact (EQ_MP (@lem2602419) (@lem2602417)). Qed.
Lemma lem2602421 : term258 = True.
Proof. exact (TRANS (@lem2602416) (@lem2602420)). Qed.
Lemma lem2602422 : True = term258.
Proof. exact (SYM (@lem2602421)). Qed.
Lemma lem2602423 : term258.
Proof. exact (EQ_MP (@lem2602422) (@lem0)). Qed.
Lemma lem2602424 : term267.
Proof. exact (@lem2602413 (@lem2602423)). Qed.
Lemma lem2602426 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602427 : term258 = term265.
Proof. exact (@lem2602426 (NUMERAL 0) term64). Qed.
Lemma lem2602428 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602429 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602430 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602429 h1) (fun h1 : term265 = True => @lem2602428)). Qed.
Lemma lem2602431 : term265 = True.
Proof. exact (EQ_MP (@lem2602430) (@lem2602428)). Qed.
Lemma lem2602432 : term258 = True.
Proof. exact (TRANS (@lem2602427) (@lem2602431)). Qed.
Lemma lem2602433 : True = term258.
Proof. exact (SYM (@lem2602432)). Qed.
Lemma lem2602434 : term258.
Proof. exact (EQ_MP (@lem2602433) (@lem0)). Qed.
Lemma lem2602435 : term262 = term268.
Proof. exact (@lem2602424 (@lem2602434)). Qed.
Lemma lem2602437 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2602438 : term144 = term145.
Proof. exact (@lem2602437 term64 term64). Qed.
Lemma lem2602439 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2602440 : term147 = term64.
Proof. exact (EQ_MP (@lem2602439) (@lem940073)). Qed.
Lemma lem2602441 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2602442 : term145 = term63.
Proof. exact (MK_COMB (@lem2602441) (@lem2602440)). Qed.
Lemma lem2602443 : term144 = term63.
Proof. exact (TRANS (@lem2602438) (@lem2602442)). Qed.
Lemma lem2602445 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2602446 : term270 = term160.
Proof. exact (@lem2602445 term64). Qed.
Lemma lem2602447 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2602448 : term271 = term260.
Proof. exact (MK_COMB (@lem2602447) (@lem2602446)). Qed.
Lemma lem2602449 : term268 = term258.
Proof. exact (MK_COMB (@lem2602448) (@lem2602443)). Qed.
Lemma lem2602451 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602452 : term258 = term265.
Proof. exact (@lem2602451 (NUMERAL 0) term64). Qed.
Lemma lem2602453 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602454 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602455 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602454 h1) (fun h1 : term265 = True => @lem2602453)). Qed.
Lemma lem2602456 : term265 = True.
Proof. exact (EQ_MP (@lem2602455) (@lem2602453)). Qed.
Lemma lem2602457 : term258 = True.
Proof. exact (TRANS (@lem2602452) (@lem2602456)). Qed.
Lemma lem2602458 : term268 = True.
Proof. exact (TRANS (@lem2602449) (@lem2602457)). Qed.
Lemma lem2602459 : term262 = True.
Proof. exact (TRANS (@lem2602435) (@lem2602458)). Qed.
Lemma lem2602460 : term258 = True.
Proof. exact (TRANS (@lem2602412) (@lem2602459)). Qed.
Lemma lem2602461 : term257 = True.
Proof. exact (TRANS (@lem2602403) (@lem2602460)). Qed.
Lemma lem2602462 : True = term257.
Proof. exact (SYM (@lem2602461)). Qed.
Lemma lem2602463 : term257.
Proof. exact (EQ_MP (@lem2602462) (@lem0)). Qed.
Lemma lem2602464 (c : int) (n : int) (m : int) (h1 : term355 c n m) : term335 c n m.
Proof. exact (conj (@lem2602463) (@lem2602323 c n m h1)). Qed.
Lemma lem2602466 (x : real) (y : real) : term273 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2602467 (c : int) (n : int) (m : int) : term336 c n m.
Proof. exact (@lem2602466 term63 (term202 c n m)). Qed.
Lemma lem2602468 (c : int) (n : int) (m : int) (h1 : term355 c n m) : term337 c n m.
Proof. exact (@lem2602467 c n m (@lem2602464 c n m h1)). Qed.
Lemma lem2602469 (c : int) (n : int) (m : int) : (term338 c n m) = (term202 c n m).
Proof. exact (@lem1982733 (term202 c n m)). Qed.
Lemma lem2602470 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2602471 (c : int) (n : int) (m : int) : (term339 c n m) = (term204 c n m).
Proof. exact (MK_COMB (@lem2602470) (@lem2602469 c n m)). Qed.
Lemma lem2602472 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2602473 (c : int) (n : int) (m : int) : (term337 c n m) = (term205 c n m).
Proof. exact (MK_COMB (@lem2602471 c n m) (@lem2602472)). Qed.
Lemma lem2602474 (c : int) (n : int) (m : int) (h1 : term355 c n m) : term205 c n m.
Proof. exact (EQ_MP (@lem2602473 c n m) (@lem2602468 c n m h1)). Qed.
Lemma lem2602475 (c : int) (n : int) (m : int) (h1 : term355 c n m) : term360 c n m.
Proof. exact (conj (@lem2602474 c n m h1) (@lem2602400 c n m h1)). Qed.
Lemma lem2602477 (x : real) (y : real) : term361 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2602478 (c : int) (n : int) (m : int) : term362 c n m.
Proof. exact (@lem2602477 (term202 c n m) (term157 c n m)). Qed.
Lemma lem2602479 (c : int) (n : int) (m : int) (h1 : term355 c n m) : term363 c n m.
Proof. exact (@lem2602478 c n m (@lem2602475 c n m h1)). Qed.
Lemma lem2602480 (c : int) (n : int) (m : int) : (term364 c n m) = (term365 c n m).
Proof. exact (@lem1982753 (term126 c n) (term40 c n) (term200 m) (real_of_int m)). Qed.
Lemma lem2602481 (c : int) (n : int) : (term291 c n) = (term292 c n).
Proof. exact (@lem1982713 term127 (term40 c n)). Qed.
Lemma lem2602483 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2602484 : term63 = term151.
Proof. exact (@lem2602483 term64). Qed.
Lemma lem2602486 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2602487 : term127 = term137.
Proof. exact (@lem2602486 term64). Qed.
Lemma lem2602488 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2602489 : term293 = term294.
Proof. exact (MK_COMB (@lem2602488) (@lem2602487)). Qed.
Lemma lem2602490 : term295 = term296.
Proof. exact (MK_COMB (@lem2602489) (@lem2602484)). Qed.
Lemma lem2602491 : term297.
Proof. exact (@lem1981473 term127 term63 term63 term63 term160 term63). Qed.
Lemma lem2602493 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602494 : term258 = term265.
Proof. exact (@lem2602493 (NUMERAL 0) term64). Qed.
Lemma lem2602495 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602496 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602497 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602496 h1) (fun h1 : term265 = True => @lem2602495)). Qed.
Lemma lem2602498 : term265 = True.
Proof. exact (EQ_MP (@lem2602497) (@lem2602495)). Qed.
Lemma lem2602499 : term258 = True.
Proof. exact (TRANS (@lem2602494) (@lem2602498)). Qed.
Lemma lem2602500 : True = term258.
Proof. exact (SYM (@lem2602499)). Qed.
Lemma lem2602501 : term258.
Proof. exact (EQ_MP (@lem2602500) (@lem0)). Qed.
Lemma lem2602502 : term298.
Proof. exact (@lem2602491 (@lem2602501)). Qed.
Lemma lem2602504 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602505 : term258 = term265.
Proof. exact (@lem2602504 (NUMERAL 0) term64). Qed.
Lemma lem2602506 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602507 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602508 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602507 h1) (fun h1 : term265 = True => @lem2602506)). Qed.
Lemma lem2602509 : term265 = True.
Proof. exact (EQ_MP (@lem2602508) (@lem2602506)). Qed.
Lemma lem2602510 : term258 = True.
Proof. exact (TRANS (@lem2602505) (@lem2602509)). Qed.
Lemma lem2602511 : True = term258.
Proof. exact (SYM (@lem2602510)). Qed.
Lemma lem2602512 : term258.
Proof. exact (EQ_MP (@lem2602511) (@lem0)). Qed.
Lemma lem2602513 : term299.
Proof. exact (@lem2602502 (@lem2602512)). Qed.
Lemma lem2602515 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602516 : term258 = term265.
Proof. exact (@lem2602515 (NUMERAL 0) term64). Qed.
Lemma lem2602517 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602518 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602519 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602518 h1) (fun h1 : term265 = True => @lem2602517)). Qed.
Lemma lem2602520 : term265 = True.
Proof. exact (EQ_MP (@lem2602519) (@lem2602517)). Qed.
Lemma lem2602521 : term258 = True.
Proof. exact (TRANS (@lem2602516) (@lem2602520)). Qed.
Lemma lem2602522 : True = term258.
Proof. exact (SYM (@lem2602521)). Qed.
Lemma lem2602523 : term258.
Proof. exact (EQ_MP (@lem2602522) (@lem0)). Qed.
Lemma lem2602524 : term300.
Proof. exact (@lem2602513 (@lem2602523)). Qed.
Lemma lem2602526 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2602527 : term144 = term145.
Proof. exact (@lem2602526 term64 term64). Qed.
Lemma lem2602528 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2602529 : term147 = term64.
Proof. exact (EQ_MP (@lem2602528) (@lem940073)). Qed.
Lemma lem2602530 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2602531 : term145 = term63.
Proof. exact (MK_COMB (@lem2602530) (@lem2602529)). Qed.
Lemma lem2602532 : term144 = term63.
Proof. exact (TRANS (@lem2602527) (@lem2602531)). Qed.
Lemma lem2602534 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2602535 : term172 = term177.
Proof. exact (@lem2602534 term64 term64). Qed.
Lemma lem2602536 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2602537 : term147 = term64.
Proof. exact (EQ_MP (@lem2602536) (@lem940073)). Qed.
Lemma lem2602538 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2602539 : term145 = term63.
Proof. exact (MK_COMB (@lem2602538) (@lem2602537)). Qed.
Lemma lem2602540 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2602541 : term177 = term127.
Proof. exact (MK_COMB (@lem2602540) (@lem2602539)). Qed.
Lemma lem2602542 : term172 = term127.
Proof. exact (TRANS (@lem2602535) (@lem2602541)). Qed.
Lemma lem2602543 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2602544 : term301 = term293.
Proof. exact (MK_COMB (@lem2602543) (@lem2602542)). Qed.
Lemma lem2602545 : term302 = term295.
Proof. exact (MK_COMB (@lem2602544) (@lem2602532)). Qed.
Lemma lem2602547 (m : nat) : (term303 m) = term160.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2602548 : term295 = term160.
Proof. exact (@lem2602547 term64). Qed.
Lemma lem2602549 : term302 = term160.
Proof. exact (TRANS (@lem2602545) (@lem2602548)). Qed.
Lemma lem2602550 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2602551 : term304 = term305.
Proof. exact (MK_COMB (@lem2602550) (@lem2602549)). Qed.
Lemma lem2602552 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2602553 : term306 = term270.
Proof. exact (MK_COMB (@lem2602551) (@lem2602552)). Qed.
Lemma lem2602555 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2602556 : term270 = term160.
Proof. exact (@lem2602555 term64). Qed.
Lemma lem2602557 : term306 = term160.
Proof. exact (TRANS (@lem2602553) (@lem2602556)). Qed.
Lemma lem2602559 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2602560 : term144 = term145.
Proof. exact (@lem2602559 term64 term64). Qed.
Lemma lem2602561 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2602562 : term147 = term64.
Proof. exact (EQ_MP (@lem2602561) (@lem940073)). Qed.
Lemma lem2602563 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2602564 : term145 = term63.
Proof. exact (MK_COMB (@lem2602563) (@lem2602562)). Qed.
Lemma lem2602565 : term144 = term63.
Proof. exact (TRANS (@lem2602560) (@lem2602564)). Qed.
Lemma lem2602566 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem2602567 : term307 = term270.
Proof. exact (MK_COMB (@lem2602566) (@lem2602565)). Qed.
Lemma lem2602569 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2602570 : term270 = term160.
Proof. exact (@lem2602569 term64). Qed.
Lemma lem2602571 : term307 = term160.
Proof. exact (TRANS (@lem2602567) (@lem2602570)). Qed.
Lemma lem2602572 : term160 = term307.
Proof. exact (SYM (@lem2602571)). Qed.
Lemma lem2602573 : term306 = term307.
Proof. exact (TRANS (@lem2602557) (@lem2602572)). Qed.
Lemma lem2602574 : term296 = term259.
Proof. exact (@lem2602524 (@lem2602573)). Qed.
Lemma lem2602575 : term295 = term259.
Proof. exact (TRANS (@lem2602490) (@lem2602574)). Qed.
Lemma lem2602577 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2602578 : term259 = term160.
Proof. exact (@lem2602577 term160). Qed.
Lemma lem2602579 : term295 = term160.
Proof. exact (TRANS (@lem2602575) (@lem2602578)). Qed.
Lemma lem2602580 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2602581 : term308 = term305.
Proof. exact (MK_COMB (@lem2602580) (@lem2602579)). Qed.
Lemma lem2602582 (c : int) (n : int) : (term40 c n) = (term40 c n).
Proof. exact (eq_refl (term40 c n)). Qed.
Lemma lem2602583 (c : int) (n : int) : (term292 c n) = (term309 c n).
Proof. exact (MK_COMB (@lem2602581) (@lem2602582 c n)). Qed.
Lemma lem2602584 (c : int) (n : int) : (term291 c n) = (term309 c n).
Proof. exact (TRANS (@lem2602481 c n) (@lem2602583 c n)). Qed.
Lemma lem2602585 (c : int) (n : int) : (term309 c n) = term160.
Proof. exact (@lem1982719 (term40 c n)). Qed.
Lemma lem2602586 (c : int) (n : int) : (term291 c n) = term160.
Proof. exact (TRANS (@lem2602584 c n) (@lem2602585 c n)). Qed.
Lemma lem2602587 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2602588 (c : int) (n : int) : (term310 c n) = term311.
Proof. exact (MK_COMB (@lem2602587) (@lem2602586 c n)). Qed.
Lemma lem2602589 (m : int) : (term366 m) = (term313 m).
Proof. exact (@lem1982759 (term124 m) (real_of_int m) term127). Qed.
Lemma lem2602590 (m : int) : (term314 m) = (term315 m).
Proof. exact (@lem1982713 term127 (real_of_int m)). Qed.
Lemma lem2602592 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2602593 : term63 = term151.
Proof. exact (@lem2602592 term64). Qed.
Lemma lem2602595 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2602596 : term127 = term137.
Proof. exact (@lem2602595 term64). Qed.
Lemma lem2602597 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2602598 : term293 = term294.
Proof. exact (MK_COMB (@lem2602597) (@lem2602596)). Qed.
Lemma lem2602599 : term295 = term296.
Proof. exact (MK_COMB (@lem2602598) (@lem2602593)). Qed.
Lemma lem2602600 : term297.
Proof. exact (@lem1981473 term127 term63 term63 term63 term160 term63). Qed.
Lemma lem2602602 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602603 : term258 = term265.
Proof. exact (@lem2602602 (NUMERAL 0) term64). Qed.
Lemma lem2602604 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602605 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602606 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602605 h1) (fun h1 : term265 = True => @lem2602604)). Qed.
Lemma lem2602607 : term265 = True.
Proof. exact (EQ_MP (@lem2602606) (@lem2602604)). Qed.
Lemma lem2602608 : term258 = True.
Proof. exact (TRANS (@lem2602603) (@lem2602607)). Qed.
Lemma lem2602609 : True = term258.
Proof. exact (SYM (@lem2602608)). Qed.
Lemma lem2602610 : term258.
Proof. exact (EQ_MP (@lem2602609) (@lem0)). Qed.
Lemma lem2602611 : term298.
Proof. exact (@lem2602600 (@lem2602610)). Qed.
Lemma lem2602613 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602614 : term258 = term265.
Proof. exact (@lem2602613 (NUMERAL 0) term64). Qed.
Lemma lem2602615 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602616 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602617 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602616 h1) (fun h1 : term265 = True => @lem2602615)). Qed.
Lemma lem2602618 : term265 = True.
Proof. exact (EQ_MP (@lem2602617) (@lem2602615)). Qed.
Lemma lem2602619 : term258 = True.
Proof. exact (TRANS (@lem2602614) (@lem2602618)). Qed.
Lemma lem2602620 : True = term258.
Proof. exact (SYM (@lem2602619)). Qed.
Lemma lem2602621 : term258.
Proof. exact (EQ_MP (@lem2602620) (@lem0)). Qed.
Lemma lem2602622 : term299.
Proof. exact (@lem2602611 (@lem2602621)). Qed.
Lemma lem2602624 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602625 : term258 = term265.
Proof. exact (@lem2602624 (NUMERAL 0) term64). Qed.
Lemma lem2602626 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602627 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602628 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602627 h1) (fun h1 : term265 = True => @lem2602626)). Qed.
Lemma lem2602629 : term265 = True.
Proof. exact (EQ_MP (@lem2602628) (@lem2602626)). Qed.
Lemma lem2602630 : term258 = True.
Proof. exact (TRANS (@lem2602625) (@lem2602629)). Qed.
Lemma lem2602631 : True = term258.
Proof. exact (SYM (@lem2602630)). Qed.
Lemma lem2602632 : term258.
Proof. exact (EQ_MP (@lem2602631) (@lem0)). Qed.
Lemma lem2602633 : term300.
Proof. exact (@lem2602622 (@lem2602632)). Qed.
Lemma lem2602635 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2602636 : term144 = term145.
Proof. exact (@lem2602635 term64 term64). Qed.
Lemma lem2602637 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2602638 : term147 = term64.
Proof. exact (EQ_MP (@lem2602637) (@lem940073)). Qed.
Lemma lem2602639 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2602640 : term145 = term63.
Proof. exact (MK_COMB (@lem2602639) (@lem2602638)). Qed.
Lemma lem2602641 : term144 = term63.
Proof. exact (TRANS (@lem2602636) (@lem2602640)). Qed.
Lemma lem2602643 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2602644 : term172 = term177.
Proof. exact (@lem2602643 term64 term64). Qed.
Lemma lem2602645 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2602646 : term147 = term64.
Proof. exact (EQ_MP (@lem2602645) (@lem940073)). Qed.
Lemma lem2602647 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2602648 : term145 = term63.
Proof. exact (MK_COMB (@lem2602647) (@lem2602646)). Qed.
Lemma lem2602649 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2602650 : term177 = term127.
Proof. exact (MK_COMB (@lem2602649) (@lem2602648)). Qed.
Lemma lem2602651 : term172 = term127.
Proof. exact (TRANS (@lem2602644) (@lem2602650)). Qed.
Lemma lem2602652 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2602653 : term301 = term293.
Proof. exact (MK_COMB (@lem2602652) (@lem2602651)). Qed.
Lemma lem2602654 : term302 = term295.
Proof. exact (MK_COMB (@lem2602653) (@lem2602641)). Qed.
Lemma lem2602656 (m : nat) : (term303 m) = term160.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2602657 : term295 = term160.
Proof. exact (@lem2602656 term64). Qed.
Lemma lem2602658 : term302 = term160.
Proof. exact (TRANS (@lem2602654) (@lem2602657)). Qed.
Lemma lem2602659 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2602660 : term304 = term305.
Proof. exact (MK_COMB (@lem2602659) (@lem2602658)). Qed.
Lemma lem2602661 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2602662 : term306 = term270.
Proof. exact (MK_COMB (@lem2602660) (@lem2602661)). Qed.
Lemma lem2602664 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2602665 : term270 = term160.
Proof. exact (@lem2602664 term64). Qed.
Lemma lem2602666 : term306 = term160.
Proof. exact (TRANS (@lem2602662) (@lem2602665)). Qed.
Lemma lem2602668 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2602669 : term144 = term145.
Proof. exact (@lem2602668 term64 term64). Qed.
Lemma lem2602670 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2602671 : term147 = term64.
Proof. exact (EQ_MP (@lem2602670) (@lem940073)). Qed.
Lemma lem2602672 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2602673 : term145 = term63.
Proof. exact (MK_COMB (@lem2602672) (@lem2602671)). Qed.
Lemma lem2602674 : term144 = term63.
Proof. exact (TRANS (@lem2602669) (@lem2602673)). Qed.
Lemma lem2602675 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem2602676 : term307 = term270.
Proof. exact (MK_COMB (@lem2602675) (@lem2602674)). Qed.
Lemma lem2602678 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2602679 : term270 = term160.
Proof. exact (@lem2602678 term64). Qed.
Lemma lem2602680 : term307 = term160.
Proof. exact (TRANS (@lem2602676) (@lem2602679)). Qed.
Lemma lem2602681 : term160 = term307.
Proof. exact (SYM (@lem2602680)). Qed.
Lemma lem2602682 : term306 = term307.
Proof. exact (TRANS (@lem2602666) (@lem2602681)). Qed.
Lemma lem2602683 : term296 = term259.
Proof. exact (@lem2602633 (@lem2602682)). Qed.
Lemma lem2602684 : term295 = term259.
Proof. exact (TRANS (@lem2602599) (@lem2602683)). Qed.
Lemma lem2602686 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2602687 : term259 = term160.
Proof. exact (@lem2602686 term160). Qed.
Lemma lem2602688 : term295 = term160.
Proof. exact (TRANS (@lem2602684) (@lem2602687)). Qed.
Lemma lem2602689 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2602690 : term308 = term305.
Proof. exact (MK_COMB (@lem2602689) (@lem2602688)). Qed.
Lemma lem2602691 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2602692 (m : int) : (term315 m) = (term316 m).
Proof. exact (MK_COMB (@lem2602690) (@lem2602691 m)). Qed.
Lemma lem2602693 (m : int) : (term314 m) = (term316 m).
Proof. exact (TRANS (@lem2602590 m) (@lem2602692 m)). Qed.
Lemma lem2602694 (m : int) : (term316 m) = term160.
Proof. exact (@lem1982719 (real_of_int m)). Qed.
Lemma lem2602695 (m : int) : (term314 m) = term160.
Proof. exact (TRANS (@lem2602693 m) (@lem2602694 m)). Qed.
Lemma lem2602696 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2602697 (m : int) : (term317 m) = term311.
Proof. exact (MK_COMB (@lem2602696) (@lem2602695 m)). Qed.
Lemma lem2602698 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem2602699 (m : int) : (term313 m) = term318.
Proof. exact (MK_COMB (@lem2602697 m) (@lem2602698)). Qed.
Lemma lem2602700 (m : int) : (term366 m) = term318.
Proof. exact (TRANS (@lem2602589 m) (@lem2602699 m)). Qed.
Lemma lem2602701 : term318 = term127.
Proof. exact (@lem1982721 term127). Qed.
Lemma lem2602702 (m : int) : (term366 m) = term127.
Proof. exact (TRANS (@lem2602700 m) (@lem2602701)). Qed.
Lemma lem2602703 (c : int) (n : int) (m : int) : (term365 c n m) = term318.
Proof. exact (MK_COMB (@lem2602588 c n) (@lem2602702 m)). Qed.
Lemma lem2602704 (c : int) (n : int) (m : int) : (term364 c n m) = term318.
Proof. exact (TRANS (@lem2602480 c n m) (@lem2602703 c n m)). Qed.
Lemma lem2602705 : term318 = term127.
Proof. exact (@lem1982721 term127). Qed.
Lemma lem2602706 (c : int) (n : int) (m : int) : (term364 c n m) = term127.
Proof. exact (TRANS (@lem2602704 c n m) (@lem2602705)). Qed.
Lemma lem2602707 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2602708 (c : int) (n : int) (m : int) : (term367 c n m) = term320.
Proof. exact (MK_COMB (@lem2602707) (@lem2602706 c n m)). Qed.
Lemma lem2602709 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2602710 (c : int) (n : int) (m : int) : (term363 c n m) = term321.
Proof. exact (MK_COMB (@lem2602708 c n m) (@lem2602709)). Qed.
Lemma lem2602711 (c : int) (n : int) (m : int) (h1 : term355 c n m) : term321.
Proof. exact (EQ_MP (@lem2602710 c n m) (@lem2602479 c n m h1)). Qed.
Lemma lem2602713 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2602714 : term321 = term322.
Proof. exact (@lem2602713 term160 term127). Qed.
Lemma lem2602716 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2602717 : term127 = term137.
Proof. exact (@lem2602716 term64). Qed.
Lemma lem2602719 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2602720 : term160 = term259.
Proof. exact (@lem2602719 (NUMERAL 0)). Qed.
Lemma lem2602721 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2602722 : term323 = term324.
Proof. exact (MK_COMB (@lem2602721) (@lem2602720)). Qed.
Lemma lem2602723 : term322 = term325.
Proof. exact (MK_COMB (@lem2602722) (@lem2602717)). Qed.
Lemma lem2602724 : term326.
Proof. exact (@lem1980026 term160 term63 term127 term63). Qed.
Lemma lem2602726 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602727 : term258 = term265.
Proof. exact (@lem2602726 (NUMERAL 0) term64). Qed.
Lemma lem2602728 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602729 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602730 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602729 h1) (fun h1 : term265 = True => @lem2602728)). Qed.
Lemma lem2602731 : term265 = True.
Proof. exact (EQ_MP (@lem2602730) (@lem2602728)). Qed.
Lemma lem2602732 : term258 = True.
Proof. exact (TRANS (@lem2602727) (@lem2602731)). Qed.
Lemma lem2602733 : True = term258.
Proof. exact (SYM (@lem2602732)). Qed.
Lemma lem2602734 : term258.
Proof. exact (EQ_MP (@lem2602733) (@lem0)). Qed.
Lemma lem2602735 : term327.
Proof. exact (@lem2602724 (@lem2602734)). Qed.
Lemma lem2602737 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602738 : term258 = term265.
Proof. exact (@lem2602737 (NUMERAL 0) term64). Qed.
Lemma lem2602739 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602740 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602741 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602740 h1) (fun h1 : term265 = True => @lem2602739)). Qed.
Lemma lem2602742 : term265 = True.
Proof. exact (EQ_MP (@lem2602741) (@lem2602739)). Qed.
Lemma lem2602743 : term258 = True.
Proof. exact (TRANS (@lem2602738) (@lem2602742)). Qed.
Lemma lem2602744 : True = term258.
Proof. exact (SYM (@lem2602743)). Qed.
Lemma lem2602745 : term258.
Proof. exact (EQ_MP (@lem2602744) (@lem0)). Qed.
Lemma lem2602746 : term325 = term328.
Proof. exact (@lem2602735 (@lem2602745)). Qed.
Lemma lem2602748 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2602749 : term172 = term177.
Proof. exact (@lem2602748 term64 term64). Qed.
Lemma lem2602750 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2602751 : term147 = term64.
Proof. exact (EQ_MP (@lem2602750) (@lem940073)). Qed.
Lemma lem2602752 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2602753 : term145 = term63.
Proof. exact (MK_COMB (@lem2602752) (@lem2602751)). Qed.
Lemma lem2602754 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2602755 : term177 = term127.
Proof. exact (MK_COMB (@lem2602754) (@lem2602753)). Qed.
Lemma lem2602756 : term172 = term127.
Proof. exact (TRANS (@lem2602749) (@lem2602755)). Qed.
Lemma lem2602758 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2602759 : term270 = term160.
Proof. exact (@lem2602758 term64). Qed.
Lemma lem2602760 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2602761 : term329 = term323.
Proof. exact (MK_COMB (@lem2602760) (@lem2602759)). Qed.
Lemma lem2602762 : term328 = term322.
Proof. exact (MK_COMB (@lem2602761) (@lem2602756)). Qed.
Lemma lem2602764 (m : nat) (n : nat) : (term330 m n) = (term331 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2602765 : term322 = term332.
Proof. exact (@lem2602764 (NUMERAL 0) term64). Qed.
Lemma lem2602766 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602767 (h1 : term266 = (BIT1 0)) : (term64 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2602768 : (term266 = (BIT1 0)) = ((term64 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602767 h1) (fun h1 : (term64 = (NUMERAL 0)) = False => @lem2602766)). Qed.
Lemma lem2602769 : (term64 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2602768) (@lem2602766)). Qed.
Lemma lem2602770 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2602771 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2602772 : term333 = (and True).
Proof. exact (MK_COMB (@lem2602771) (@lem2602770)). Qed.
Lemma lem2602773 : term332 = (True /\ False).
Proof. exact (MK_COMB (@lem2602772) (@lem2602769)). Qed.
Lemma lem2602775 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2602776 : term332 = False.
Proof. exact (TRANS (@lem2602773) (@lem2602775)). Qed.
Lemma lem2602777 : term322 = False.
Proof. exact (TRANS (@lem2602765) (@lem2602776)). Qed.
Lemma lem2602778 : term328 = False.
Proof. exact (TRANS (@lem2602762) (@lem2602777)). Qed.
Lemma lem2602779 : term325 = False.
Proof. exact (TRANS (@lem2602746) (@lem2602778)). Qed.
Lemma lem2602780 : term322 = False.
Proof. exact (TRANS (@lem2602723) (@lem2602779)). Qed.
Lemma lem2602781 : term321 = False.
Proof. exact (TRANS (@lem2602714) (@lem2602780)). Qed.
Lemma lem2602782 (c : int) (n : int) (m : int) (h1 : term355 c n m) : False.
Proof. exact (EQ_MP (@lem2602781) (@lem2602711 c n m h1)). Qed.
Lemma lem2602783 (c : int) (n : int) (m : int) (h1 : term368 c n m) : term368 c n m.
Proof. exact (h1). Qed.
Lemma lem2602784 (c : int) (n : int) (m : int) (h1 : term368 c n m) : term205 c n m.
Proof. exact (proj2 (@lem2602783 c n m h1)). Qed.
Lemma lem2602785 (c : int) (n : int) (m : int) (h1 : term368 c n m) : term225 c n m.
Proof. exact (proj1 (@lem2602783 c n m h1)). Qed.
Lemma lem2602786 (c : int) (n : int) (m : int) (h1 : term368 c n m) : term189 c n m.
Proof. exact (proj2 (@lem2602785 c n m h1)). Qed.
Lemma lem2602789 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2602790 : term257 = term258.
Proof. exact (@lem2602789 term160 term63). Qed.
Lemma lem2602792 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2602793 : term63 = term151.
Proof. exact (@lem2602792 term64). Qed.
Lemma lem2602795 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2602796 : term160 = term259.
Proof. exact (@lem2602795 (NUMERAL 0)). Qed.
Lemma lem2602797 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2602798 : term260 = term261.
Proof. exact (MK_COMB (@lem2602797) (@lem2602796)). Qed.
Lemma lem2602799 : term258 = term262.
Proof. exact (MK_COMB (@lem2602798) (@lem2602793)). Qed.
Lemma lem2602800 : term263.
Proof. exact (@lem1980255 term160 term63 term63 term63). Qed.
Lemma lem2602802 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602803 : term258 = term265.
Proof. exact (@lem2602802 (NUMERAL 0) term64). Qed.
Lemma lem2602804 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602805 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602806 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602805 h1) (fun h1 : term265 = True => @lem2602804)). Qed.
Lemma lem2602807 : term265 = True.
Proof. exact (EQ_MP (@lem2602806) (@lem2602804)). Qed.
Lemma lem2602808 : term258 = True.
Proof. exact (TRANS (@lem2602803) (@lem2602807)). Qed.
Lemma lem2602809 : True = term258.
Proof. exact (SYM (@lem2602808)). Qed.
Lemma lem2602810 : term258.
Proof. exact (EQ_MP (@lem2602809) (@lem0)). Qed.
Lemma lem2602811 : term267.
Proof. exact (@lem2602800 (@lem2602810)). Qed.
Lemma lem2602813 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602814 : term258 = term265.
Proof. exact (@lem2602813 (NUMERAL 0) term64). Qed.
Lemma lem2602815 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602816 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602817 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602816 h1) (fun h1 : term265 = True => @lem2602815)). Qed.
Lemma lem2602818 : term265 = True.
Proof. exact (EQ_MP (@lem2602817) (@lem2602815)). Qed.
Lemma lem2602819 : term258 = True.
Proof. exact (TRANS (@lem2602814) (@lem2602818)). Qed.
Lemma lem2602820 : True = term258.
Proof. exact (SYM (@lem2602819)). Qed.
Lemma lem2602821 : term258.
Proof. exact (EQ_MP (@lem2602820) (@lem0)). Qed.
Lemma lem2602822 : term262 = term268.
Proof. exact (@lem2602811 (@lem2602821)). Qed.
Lemma lem2602824 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2602825 : term144 = term145.
Proof. exact (@lem2602824 term64 term64). Qed.
Lemma lem2602826 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2602827 : term147 = term64.
Proof. exact (EQ_MP (@lem2602826) (@lem940073)). Qed.
Lemma lem2602828 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2602829 : term145 = term63.
Proof. exact (MK_COMB (@lem2602828) (@lem2602827)). Qed.
Lemma lem2602830 : term144 = term63.
Proof. exact (TRANS (@lem2602825) (@lem2602829)). Qed.
Lemma lem2602832 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2602833 : term270 = term160.
Proof. exact (@lem2602832 term64). Qed.
Lemma lem2602834 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2602835 : term271 = term260.
Proof. exact (MK_COMB (@lem2602834) (@lem2602833)). Qed.
Lemma lem2602836 : term268 = term258.
Proof. exact (MK_COMB (@lem2602835) (@lem2602830)). Qed.
Lemma lem2602838 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602839 : term258 = term265.
Proof. exact (@lem2602838 (NUMERAL 0) term64). Qed.
Lemma lem2602840 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602841 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602842 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602841 h1) (fun h1 : term265 = True => @lem2602840)). Qed.
Lemma lem2602843 : term265 = True.
Proof. exact (EQ_MP (@lem2602842) (@lem2602840)). Qed.
Lemma lem2602844 : term258 = True.
Proof. exact (TRANS (@lem2602839) (@lem2602843)). Qed.
Lemma lem2602845 : term268 = True.
Proof. exact (TRANS (@lem2602836) (@lem2602844)). Qed.
Lemma lem2602846 : term262 = True.
Proof. exact (TRANS (@lem2602822) (@lem2602845)). Qed.
Lemma lem2602847 : term258 = True.
Proof. exact (TRANS (@lem2602799) (@lem2602846)). Qed.
Lemma lem2602848 : term257 = True.
Proof. exact (TRANS (@lem2602790) (@lem2602847)). Qed.
Lemma lem2602849 : True = term257.
Proof. exact (SYM (@lem2602848)). Qed.
Lemma lem2602850 : term257.
Proof. exact (EQ_MP (@lem2602849) (@lem0)). Qed.
Lemma lem2602851 (c : int) (n : int) (m : int) (h1 : term368 c n m) : term272 c n m.
Proof. exact (conj (@lem2602850) (@lem2602786 c n m h1)). Qed.
Lemma lem2602853 (x : real) (y : real) : term273 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2602854 (c : int) (n : int) (m : int) : term274 c n m.
Proof. exact (@lem2602853 term63 (term186 c n m)). Qed.
Lemma lem2602855 (c : int) (n : int) (m : int) (h1 : term368 c n m) : term275 c n m.
Proof. exact (@lem2602854 c n m (@lem2602851 c n m h1)). Qed.
Lemma lem2602856 (c : int) (n : int) (m : int) : (term276 c n m) = (term186 c n m).
Proof. exact (@lem1982733 (term186 c n m)). Qed.
Lemma lem2602857 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2602858 (c : int) (n : int) (m : int) : (term277 c n m) = (term188 c n m).
Proof. exact (MK_COMB (@lem2602857) (@lem2602856 c n m)). Qed.
Lemma lem2602859 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2602860 (c : int) (n : int) (m : int) : (term275 c n m) = (term189 c n m).
Proof. exact (MK_COMB (@lem2602858 c n m) (@lem2602859)). Qed.
Lemma lem2602861 (c : int) (n : int) (m : int) (h1 : term368 c n m) : term189 c n m.
Proof. exact (EQ_MP (@lem2602860 c n m) (@lem2602855 c n m h1)). Qed.
Lemma lem2602863 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2602864 : term257 = term258.
Proof. exact (@lem2602863 term160 term63). Qed.
Lemma lem2602866 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2602867 : term63 = term151.
Proof. exact (@lem2602866 term64). Qed.
Lemma lem2602869 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2602870 : term160 = term259.
Proof. exact (@lem2602869 (NUMERAL 0)). Qed.
Lemma lem2602871 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2602872 : term260 = term261.
Proof. exact (MK_COMB (@lem2602871) (@lem2602870)). Qed.
Lemma lem2602873 : term258 = term262.
Proof. exact (MK_COMB (@lem2602872) (@lem2602867)). Qed.
Lemma lem2602874 : term263.
Proof. exact (@lem1980255 term160 term63 term63 term63). Qed.
Lemma lem2602876 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602877 : term258 = term265.
Proof. exact (@lem2602876 (NUMERAL 0) term64). Qed.
Lemma lem2602878 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602879 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602880 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602879 h1) (fun h1 : term265 = True => @lem2602878)). Qed.
Lemma lem2602881 : term265 = True.
Proof. exact (EQ_MP (@lem2602880) (@lem2602878)). Qed.
Lemma lem2602882 : term258 = True.
Proof. exact (TRANS (@lem2602877) (@lem2602881)). Qed.
Lemma lem2602883 : True = term258.
Proof. exact (SYM (@lem2602882)). Qed.
Lemma lem2602884 : term258.
Proof. exact (EQ_MP (@lem2602883) (@lem0)). Qed.
Lemma lem2602885 : term267.
Proof. exact (@lem2602874 (@lem2602884)). Qed.
Lemma lem2602887 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602888 : term258 = term265.
Proof. exact (@lem2602887 (NUMERAL 0) term64). Qed.
Lemma lem2602889 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602890 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602891 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602890 h1) (fun h1 : term265 = True => @lem2602889)). Qed.
Lemma lem2602892 : term265 = True.
Proof. exact (EQ_MP (@lem2602891) (@lem2602889)). Qed.
Lemma lem2602893 : term258 = True.
Proof. exact (TRANS (@lem2602888) (@lem2602892)). Qed.
Lemma lem2602894 : True = term258.
Proof. exact (SYM (@lem2602893)). Qed.
Lemma lem2602895 : term258.
Proof. exact (EQ_MP (@lem2602894) (@lem0)). Qed.
Lemma lem2602896 : term262 = term268.
Proof. exact (@lem2602885 (@lem2602895)). Qed.
Lemma lem2602898 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2602899 : term144 = term145.
Proof. exact (@lem2602898 term64 term64). Qed.
Lemma lem2602900 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2602901 : term147 = term64.
Proof. exact (EQ_MP (@lem2602900) (@lem940073)). Qed.
Lemma lem2602902 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2602903 : term145 = term63.
Proof. exact (MK_COMB (@lem2602902) (@lem2602901)). Qed.
Lemma lem2602904 : term144 = term63.
Proof. exact (TRANS (@lem2602899) (@lem2602903)). Qed.
Lemma lem2602906 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2602907 : term270 = term160.
Proof. exact (@lem2602906 term64). Qed.
Lemma lem2602908 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2602909 : term271 = term260.
Proof. exact (MK_COMB (@lem2602908) (@lem2602907)). Qed.
Lemma lem2602910 : term268 = term258.
Proof. exact (MK_COMB (@lem2602909) (@lem2602904)). Qed.
Lemma lem2602912 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602913 : term258 = term265.
Proof. exact (@lem2602912 (NUMERAL 0) term64). Qed.
Lemma lem2602914 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602915 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602916 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602915 h1) (fun h1 : term265 = True => @lem2602914)). Qed.
Lemma lem2602917 : term265 = True.
Proof. exact (EQ_MP (@lem2602916) (@lem2602914)). Qed.
Lemma lem2602918 : term258 = True.
Proof. exact (TRANS (@lem2602913) (@lem2602917)). Qed.
Lemma lem2602919 : term268 = True.
Proof. exact (TRANS (@lem2602910) (@lem2602918)). Qed.
Lemma lem2602920 : term262 = True.
Proof. exact (TRANS (@lem2602896) (@lem2602919)). Qed.
Lemma lem2602921 : term258 = True.
Proof. exact (TRANS (@lem2602873) (@lem2602920)). Qed.
Lemma lem2602922 : term257 = True.
Proof. exact (TRANS (@lem2602864) (@lem2602921)). Qed.
Lemma lem2602923 : True = term257.
Proof. exact (SYM (@lem2602922)). Qed.
Lemma lem2602924 : term257.
Proof. exact (EQ_MP (@lem2602923) (@lem0)). Qed.
Lemma lem2602925 (c : int) (n : int) (m : int) (h1 : term368 c n m) : term335 c n m.
Proof. exact (conj (@lem2602924) (@lem2602784 c n m h1)). Qed.
Lemma lem2602927 (x : real) (y : real) : term273 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2602928 (c : int) (n : int) (m : int) : term336 c n m.
Proof. exact (@lem2602927 term63 (term202 c n m)). Qed.
Lemma lem2602929 (c : int) (n : int) (m : int) (h1 : term368 c n m) : term337 c n m.
Proof. exact (@lem2602928 c n m (@lem2602925 c n m h1)). Qed.
Lemma lem2602930 (c : int) (n : int) (m : int) : (term338 c n m) = (term202 c n m).
Proof. exact (@lem1982733 (term202 c n m)). Qed.
Lemma lem2602931 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2602932 (c : int) (n : int) (m : int) : (term339 c n m) = (term204 c n m).
Proof. exact (MK_COMB (@lem2602931) (@lem2602930 c n m)). Qed.
Lemma lem2602933 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2602934 (c : int) (n : int) (m : int) : (term337 c n m) = (term205 c n m).
Proof. exact (MK_COMB (@lem2602932 c n m) (@lem2602933)). Qed.
Lemma lem2602935 (c : int) (n : int) (m : int) (h1 : term368 c n m) : term205 c n m.
Proof. exact (EQ_MP (@lem2602934 c n m) (@lem2602929 c n m h1)). Qed.
Lemma lem2602936 (c : int) (n : int) (m : int) (h1 : term368 c n m) : term225 c n m.
Proof. exact (conj (@lem2602935 c n m h1) (@lem2602861 c n m h1)). Qed.
Lemma lem2602938 (x : real) (y : real) : term361 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2602939 (c : int) (n : int) (m : int) : term369 c n m.
Proof. exact (@lem2602938 (term202 c n m) (term186 c n m)). Qed.
Lemma lem2602940 (c : int) (n : int) (m : int) (h1 : term368 c n m) : term370 c n m.
Proof. exact (@lem2602939 c n m (@lem2602936 c n m h1)). Qed.
Lemma lem2602941 (c : int) (n : int) (m : int) : (term371 c n m) = (term372 c n m).
Proof. exact (@lem1982753 (term126 c n) (term40 c n) (term200 m) (term184 m)). Qed.
Lemma lem2602942 (c : int) (n : int) : (term291 c n) = (term292 c n).
Proof. exact (@lem1982713 term127 (term40 c n)). Qed.
Lemma lem2602944 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2602945 : term63 = term151.
Proof. exact (@lem2602944 term64). Qed.
Lemma lem2602947 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2602948 : term127 = term137.
Proof. exact (@lem2602947 term64). Qed.
Lemma lem2602949 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2602950 : term293 = term294.
Proof. exact (MK_COMB (@lem2602949) (@lem2602948)). Qed.
Lemma lem2602951 : term295 = term296.
Proof. exact (MK_COMB (@lem2602950) (@lem2602945)). Qed.
Lemma lem2602952 : term297.
Proof. exact (@lem1981473 term127 term63 term63 term63 term160 term63). Qed.
Lemma lem2602954 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602955 : term258 = term265.
Proof. exact (@lem2602954 (NUMERAL 0) term64). Qed.
Lemma lem2602956 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602957 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602958 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602957 h1) (fun h1 : term265 = True => @lem2602956)). Qed.
Lemma lem2602959 : term265 = True.
Proof. exact (EQ_MP (@lem2602958) (@lem2602956)). Qed.
Lemma lem2602960 : term258 = True.
Proof. exact (TRANS (@lem2602955) (@lem2602959)). Qed.
Lemma lem2602961 : True = term258.
Proof. exact (SYM (@lem2602960)). Qed.
Lemma lem2602962 : term258.
Proof. exact (EQ_MP (@lem2602961) (@lem0)). Qed.
Lemma lem2602963 : term298.
Proof. exact (@lem2602952 (@lem2602962)). Qed.
Lemma lem2602965 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602966 : term258 = term265.
Proof. exact (@lem2602965 (NUMERAL 0) term64). Qed.
Lemma lem2602967 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602968 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602969 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602968 h1) (fun h1 : term265 = True => @lem2602967)). Qed.
Lemma lem2602970 : term265 = True.
Proof. exact (EQ_MP (@lem2602969) (@lem2602967)). Qed.
Lemma lem2602971 : term258 = True.
Proof. exact (TRANS (@lem2602966) (@lem2602970)). Qed.
Lemma lem2602972 : True = term258.
Proof. exact (SYM (@lem2602971)). Qed.
Lemma lem2602973 : term258.
Proof. exact (EQ_MP (@lem2602972) (@lem0)). Qed.
Lemma lem2602974 : term299.
Proof. exact (@lem2602963 (@lem2602973)). Qed.
Lemma lem2602976 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2602977 : term258 = term265.
Proof. exact (@lem2602976 (NUMERAL 0) term64). Qed.
Lemma lem2602978 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2602979 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2602980 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2602979 h1) (fun h1 : term265 = True => @lem2602978)). Qed.
Lemma lem2602981 : term265 = True.
Proof. exact (EQ_MP (@lem2602980) (@lem2602978)). Qed.
Lemma lem2602982 : term258 = True.
Proof. exact (TRANS (@lem2602977) (@lem2602981)). Qed.
Lemma lem2602983 : True = term258.
Proof. exact (SYM (@lem2602982)). Qed.
Lemma lem2602984 : term258.
Proof. exact (EQ_MP (@lem2602983) (@lem0)). Qed.
Lemma lem2602985 : term300.
Proof. exact (@lem2602974 (@lem2602984)). Qed.
Lemma lem2602987 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2602988 : term144 = term145.
Proof. exact (@lem2602987 term64 term64). Qed.
Lemma lem2602989 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2602990 : term147 = term64.
Proof. exact (EQ_MP (@lem2602989) (@lem940073)). Qed.
Lemma lem2602991 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2602992 : term145 = term63.
Proof. exact (MK_COMB (@lem2602991) (@lem2602990)). Qed.
Lemma lem2602993 : term144 = term63.
Proof. exact (TRANS (@lem2602988) (@lem2602992)). Qed.
Lemma lem2602995 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2602996 : term172 = term177.
Proof. exact (@lem2602995 term64 term64). Qed.
Lemma lem2602997 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2602998 : term147 = term64.
Proof. exact (EQ_MP (@lem2602997) (@lem940073)). Qed.
Lemma lem2602999 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2603000 : term145 = term63.
Proof. exact (MK_COMB (@lem2602999) (@lem2602998)). Qed.
Lemma lem2603001 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2603002 : term177 = term127.
Proof. exact (MK_COMB (@lem2603001) (@lem2603000)). Qed.
Lemma lem2603003 : term172 = term127.
Proof. exact (TRANS (@lem2602996) (@lem2603002)). Qed.
Lemma lem2603004 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2603005 : term301 = term293.
Proof. exact (MK_COMB (@lem2603004) (@lem2603003)). Qed.
Lemma lem2603006 : term302 = term295.
Proof. exact (MK_COMB (@lem2603005) (@lem2602993)). Qed.
Lemma lem2603008 (m : nat) : (term303 m) = term160.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2603009 : term295 = term160.
Proof. exact (@lem2603008 term64). Qed.
Lemma lem2603010 : term302 = term160.
Proof. exact (TRANS (@lem2603006) (@lem2603009)). Qed.
Lemma lem2603011 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2603012 : term304 = term305.
Proof. exact (MK_COMB (@lem2603011) (@lem2603010)). Qed.
Lemma lem2603013 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2603014 : term306 = term270.
Proof. exact (MK_COMB (@lem2603012) (@lem2603013)). Qed.
Lemma lem2603016 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2603017 : term270 = term160.
Proof. exact (@lem2603016 term64). Qed.
Lemma lem2603018 : term306 = term160.
Proof. exact (TRANS (@lem2603014) (@lem2603017)). Qed.
Lemma lem2603020 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2603021 : term144 = term145.
Proof. exact (@lem2603020 term64 term64). Qed.
Lemma lem2603022 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2603023 : term147 = term64.
Proof. exact (EQ_MP (@lem2603022) (@lem940073)). Qed.
Lemma lem2603024 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2603025 : term145 = term63.
Proof. exact (MK_COMB (@lem2603024) (@lem2603023)). Qed.
Lemma lem2603026 : term144 = term63.
Proof. exact (TRANS (@lem2603021) (@lem2603025)). Qed.
Lemma lem2603027 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem2603028 : term307 = term270.
Proof. exact (MK_COMB (@lem2603027) (@lem2603026)). Qed.
Lemma lem2603030 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2603031 : term270 = term160.
Proof. exact (@lem2603030 term64). Qed.
Lemma lem2603032 : term307 = term160.
Proof. exact (TRANS (@lem2603028) (@lem2603031)). Qed.
Lemma lem2603033 : term160 = term307.
Proof. exact (SYM (@lem2603032)). Qed.
Lemma lem2603034 : term306 = term307.
Proof. exact (TRANS (@lem2603018) (@lem2603033)). Qed.
Lemma lem2603035 : term296 = term259.
Proof. exact (@lem2602985 (@lem2603034)). Qed.
Lemma lem2603036 : term295 = term259.
Proof. exact (TRANS (@lem2602951) (@lem2603035)). Qed.
Lemma lem2603038 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2603039 : term259 = term160.
Proof. exact (@lem2603038 term160). Qed.
Lemma lem2603040 : term295 = term160.
Proof. exact (TRANS (@lem2603036) (@lem2603039)). Qed.
Lemma lem2603041 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2603042 : term308 = term305.
Proof. exact (MK_COMB (@lem2603041) (@lem2603040)). Qed.
Lemma lem2603043 (c : int) (n : int) : (term40 c n) = (term40 c n).
Proof. exact (eq_refl (term40 c n)). Qed.
Lemma lem2603044 (c : int) (n : int) : (term292 c n) = (term309 c n).
Proof. exact (MK_COMB (@lem2603042) (@lem2603043 c n)). Qed.
Lemma lem2603045 (c : int) (n : int) : (term291 c n) = (term309 c n).
Proof. exact (TRANS (@lem2602942 c n) (@lem2603044 c n)). Qed.
Lemma lem2603046 (c : int) (n : int) : (term309 c n) = term160.
Proof. exact (@lem1982719 (term40 c n)). Qed.
Lemma lem2603047 (c : int) (n : int) : (term291 c n) = term160.
Proof. exact (TRANS (@lem2603045 c n) (@lem2603046 c n)). Qed.
Lemma lem2603048 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2603049 (c : int) (n : int) : (term310 c n) = term311.
Proof. exact (MK_COMB (@lem2603048) (@lem2603047 c n)). Qed.
Lemma lem2603050 (m : int) : (term373 m) = (term374 m).
Proof. exact (@lem1982753 (term124 m) (real_of_int m) term127 term127). Qed.
Lemma lem2603051 (m : int) : (term314 m) = (term315 m).
Proof. exact (@lem1982713 term127 (real_of_int m)). Qed.
Lemma lem2603053 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2603054 : term63 = term151.
Proof. exact (@lem2603053 term64). Qed.
Lemma lem2603056 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2603057 : term127 = term137.
Proof. exact (@lem2603056 term64). Qed.
Lemma lem2603058 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2603059 : term293 = term294.
Proof. exact (MK_COMB (@lem2603058) (@lem2603057)). Qed.
Lemma lem2603060 : term295 = term296.
Proof. exact (MK_COMB (@lem2603059) (@lem2603054)). Qed.
Lemma lem2603061 : term297.
Proof. exact (@lem1981473 term127 term63 term63 term63 term160 term63). Qed.
Lemma lem2603063 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603064 : term258 = term265.
Proof. exact (@lem2603063 (NUMERAL 0) term64). Qed.
Lemma lem2603065 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603066 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603067 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603066 h1) (fun h1 : term265 = True => @lem2603065)). Qed.
Lemma lem2603068 : term265 = True.
Proof. exact (EQ_MP (@lem2603067) (@lem2603065)). Qed.
Lemma lem2603069 : term258 = True.
Proof. exact (TRANS (@lem2603064) (@lem2603068)). Qed.
Lemma lem2603070 : True = term258.
Proof. exact (SYM (@lem2603069)). Qed.
Lemma lem2603071 : term258.
Proof. exact (EQ_MP (@lem2603070) (@lem0)). Qed.
Lemma lem2603072 : term298.
Proof. exact (@lem2603061 (@lem2603071)). Qed.
Lemma lem2603074 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603075 : term258 = term265.
Proof. exact (@lem2603074 (NUMERAL 0) term64). Qed.
Lemma lem2603076 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603077 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603078 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603077 h1) (fun h1 : term265 = True => @lem2603076)). Qed.
Lemma lem2603079 : term265 = True.
Proof. exact (EQ_MP (@lem2603078) (@lem2603076)). Qed.
Lemma lem2603080 : term258 = True.
Proof. exact (TRANS (@lem2603075) (@lem2603079)). Qed.
Lemma lem2603081 : True = term258.
Proof. exact (SYM (@lem2603080)). Qed.
Lemma lem2603082 : term258.
Proof. exact (EQ_MP (@lem2603081) (@lem0)). Qed.
Lemma lem2603083 : term299.
Proof. exact (@lem2603072 (@lem2603082)). Qed.
Lemma lem2603085 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603086 : term258 = term265.
Proof. exact (@lem2603085 (NUMERAL 0) term64). Qed.
Lemma lem2603087 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603088 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603089 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603088 h1) (fun h1 : term265 = True => @lem2603087)). Qed.
Lemma lem2603090 : term265 = True.
Proof. exact (EQ_MP (@lem2603089) (@lem2603087)). Qed.
Lemma lem2603091 : term258 = True.
Proof. exact (TRANS (@lem2603086) (@lem2603090)). Qed.
Lemma lem2603092 : True = term258.
Proof. exact (SYM (@lem2603091)). Qed.
Lemma lem2603093 : term258.
Proof. exact (EQ_MP (@lem2603092) (@lem0)). Qed.
Lemma lem2603094 : term300.
Proof. exact (@lem2603083 (@lem2603093)). Qed.
Lemma lem2603096 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2603097 : term144 = term145.
Proof. exact (@lem2603096 term64 term64). Qed.
Lemma lem2603098 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2603099 : term147 = term64.
Proof. exact (EQ_MP (@lem2603098) (@lem940073)). Qed.
Lemma lem2603100 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2603101 : term145 = term63.
Proof. exact (MK_COMB (@lem2603100) (@lem2603099)). Qed.
Lemma lem2603102 : term144 = term63.
Proof. exact (TRANS (@lem2603097) (@lem2603101)). Qed.
Lemma lem2603104 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2603105 : term172 = term177.
Proof. exact (@lem2603104 term64 term64). Qed.
Lemma lem2603106 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2603107 : term147 = term64.
Proof. exact (EQ_MP (@lem2603106) (@lem940073)). Qed.
Lemma lem2603108 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2603109 : term145 = term63.
Proof. exact (MK_COMB (@lem2603108) (@lem2603107)). Qed.
Lemma lem2603110 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2603111 : term177 = term127.
Proof. exact (MK_COMB (@lem2603110) (@lem2603109)). Qed.
Lemma lem2603112 : term172 = term127.
Proof. exact (TRANS (@lem2603105) (@lem2603111)). Qed.
Lemma lem2603113 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2603114 : term301 = term293.
Proof. exact (MK_COMB (@lem2603113) (@lem2603112)). Qed.
Lemma lem2603115 : term302 = term295.
Proof. exact (MK_COMB (@lem2603114) (@lem2603102)). Qed.
Lemma lem2603117 (m : nat) : (term303 m) = term160.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2603118 : term295 = term160.
Proof. exact (@lem2603117 term64). Qed.
Lemma lem2603119 : term302 = term160.
Proof. exact (TRANS (@lem2603115) (@lem2603118)). Qed.
Lemma lem2603120 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2603121 : term304 = term305.
Proof. exact (MK_COMB (@lem2603120) (@lem2603119)). Qed.
Lemma lem2603122 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2603123 : term306 = term270.
Proof. exact (MK_COMB (@lem2603121) (@lem2603122)). Qed.
Lemma lem2603125 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2603126 : term270 = term160.
Proof. exact (@lem2603125 term64). Qed.
Lemma lem2603127 : term306 = term160.
Proof. exact (TRANS (@lem2603123) (@lem2603126)). Qed.
Lemma lem2603129 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2603130 : term144 = term145.
Proof. exact (@lem2603129 term64 term64). Qed.
Lemma lem2603131 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2603132 : term147 = term64.
Proof. exact (EQ_MP (@lem2603131) (@lem940073)). Qed.
Lemma lem2603133 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2603134 : term145 = term63.
Proof. exact (MK_COMB (@lem2603133) (@lem2603132)). Qed.
Lemma lem2603135 : term144 = term63.
Proof. exact (TRANS (@lem2603130) (@lem2603134)). Qed.
Lemma lem2603136 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem2603137 : term307 = term270.
Proof. exact (MK_COMB (@lem2603136) (@lem2603135)). Qed.
Lemma lem2603139 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2603140 : term270 = term160.
Proof. exact (@lem2603139 term64). Qed.
Lemma lem2603141 : term307 = term160.
Proof. exact (TRANS (@lem2603137) (@lem2603140)). Qed.
Lemma lem2603142 : term160 = term307.
Proof. exact (SYM (@lem2603141)). Qed.
Lemma lem2603143 : term306 = term307.
Proof. exact (TRANS (@lem2603127) (@lem2603142)). Qed.
Lemma lem2603144 : term296 = term259.
Proof. exact (@lem2603094 (@lem2603143)). Qed.
Lemma lem2603145 : term295 = term259.
Proof. exact (TRANS (@lem2603060) (@lem2603144)). Qed.
Lemma lem2603147 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2603148 : term259 = term160.
Proof. exact (@lem2603147 term160). Qed.
Lemma lem2603149 : term295 = term160.
Proof. exact (TRANS (@lem2603145) (@lem2603148)). Qed.
Lemma lem2603150 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2603151 : term308 = term305.
Proof. exact (MK_COMB (@lem2603150) (@lem2603149)). Qed.
Lemma lem2603152 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2603153 (m : int) : (term315 m) = (term316 m).
Proof. exact (MK_COMB (@lem2603151) (@lem2603152 m)). Qed.
Lemma lem2603154 (m : int) : (term314 m) = (term316 m).
Proof. exact (TRANS (@lem2603051 m) (@lem2603153 m)). Qed.
Lemma lem2603155 (m : int) : (term316 m) = term160.
Proof. exact (@lem1982719 (real_of_int m)). Qed.
Lemma lem2603156 (m : int) : (term314 m) = term160.
Proof. exact (TRANS (@lem2603154 m) (@lem2603155 m)). Qed.
Lemma lem2603157 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2603158 (m : int) : (term317 m) = term311.
Proof. exact (MK_COMB (@lem2603157) (@lem2603156 m)). Qed.
Lemma lem2603160 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2603161 : term127 = term137.
Proof. exact (@lem2603160 term64). Qed.
Lemma lem2603163 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2603164 : term127 = term137.
Proof. exact (@lem2603163 term64). Qed.
Lemma lem2603165 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2603166 : term293 = term294.
Proof. exact (MK_COMB (@lem2603165) (@lem2603164)). Qed.
Lemma lem2603167 : term375 = term376.
Proof. exact (MK_COMB (@lem2603166) (@lem2603161)). Qed.
Lemma lem2603168 : term377.
Proof. exact (@lem1981473 term127 term63 term127 term63 term378 term63). Qed.
Lemma lem2603170 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603171 : term258 = term265.
Proof. exact (@lem2603170 (NUMERAL 0) term64). Qed.
Lemma lem2603172 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603173 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603174 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603173 h1) (fun h1 : term265 = True => @lem2603172)). Qed.
Lemma lem2603175 : term265 = True.
Proof. exact (EQ_MP (@lem2603174) (@lem2603172)). Qed.
Lemma lem2603176 : term258 = True.
Proof. exact (TRANS (@lem2603171) (@lem2603175)). Qed.
Lemma lem2603177 : True = term258.
Proof. exact (SYM (@lem2603176)). Qed.
Lemma lem2603178 : term258.
Proof. exact (EQ_MP (@lem2603177) (@lem0)). Qed.
Lemma lem2603179 : term379.
Proof. exact (@lem2603168 (@lem2603178)). Qed.
Lemma lem2603181 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603182 : term258 = term265.
Proof. exact (@lem2603181 (NUMERAL 0) term64). Qed.
Lemma lem2603183 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603184 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603185 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603184 h1) (fun h1 : term265 = True => @lem2603183)). Qed.
Lemma lem2603186 : term265 = True.
Proof. exact (EQ_MP (@lem2603185) (@lem2603183)). Qed.
Lemma lem2603187 : term258 = True.
Proof. exact (TRANS (@lem2603182) (@lem2603186)). Qed.
Lemma lem2603188 : True = term258.
Proof. exact (SYM (@lem2603187)). Qed.
Lemma lem2603189 : term258.
Proof. exact (EQ_MP (@lem2603188) (@lem0)). Qed.
Lemma lem2603190 : term380.
Proof. exact (@lem2603179 (@lem2603189)). Qed.
Lemma lem2603192 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603193 : term258 = term265.
Proof. exact (@lem2603192 (NUMERAL 0) term64). Qed.
Lemma lem2603194 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603195 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603196 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603195 h1) (fun h1 : term265 = True => @lem2603194)). Qed.
Lemma lem2603197 : term265 = True.
Proof. exact (EQ_MP (@lem2603196) (@lem2603194)). Qed.
Lemma lem2603198 : term258 = True.
Proof. exact (TRANS (@lem2603193) (@lem2603197)). Qed.
Lemma lem2603199 : True = term258.
Proof. exact (SYM (@lem2603198)). Qed.
Lemma lem2603200 : term258.
Proof. exact (EQ_MP (@lem2603199) (@lem0)). Qed.
Lemma lem2603201 : term381.
Proof. exact (@lem2603190 (@lem2603200)). Qed.
Lemma lem2603203 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2603204 : term172 = term177.
Proof. exact (@lem2603203 term64 term64). Qed.
Lemma lem2603205 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2603206 : term147 = term64.
Proof. exact (EQ_MP (@lem2603205) (@lem940073)). Qed.
Lemma lem2603207 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2603208 : term145 = term63.
Proof. exact (MK_COMB (@lem2603207) (@lem2603206)). Qed.
Lemma lem2603209 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2603210 : term177 = term127.
Proof. exact (MK_COMB (@lem2603209) (@lem2603208)). Qed.
Lemma lem2603211 : term172 = term127.
Proof. exact (TRANS (@lem2603204) (@lem2603210)). Qed.
Lemma lem2603213 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2603214 : term172 = term177.
Proof. exact (@lem2603213 term64 term64). Qed.
Lemma lem2603215 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2603216 : term147 = term64.
Proof. exact (EQ_MP (@lem2603215) (@lem940073)). Qed.
Lemma lem2603217 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2603218 : term145 = term63.
Proof. exact (MK_COMB (@lem2603217) (@lem2603216)). Qed.
Lemma lem2603219 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2603220 : term177 = term127.
Proof. exact (MK_COMB (@lem2603219) (@lem2603218)). Qed.
Lemma lem2603221 : term172 = term127.
Proof. exact (TRANS (@lem2603214) (@lem2603220)). Qed.
Lemma lem2603222 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2603223 : term301 = term293.
Proof. exact (MK_COMB (@lem2603222) (@lem2603221)). Qed.
Lemma lem2603224 : term382 = term375.
Proof. exact (MK_COMB (@lem2603223) (@lem2603211)). Qed.
Lemma lem2603225 : term375 = term383.
Proof. exact (@lem1367763 term64 term64). Qed.
Lemma lem2603226 : term384 = term385.
Proof. exact (@lem706885). Qed.
Lemma lem2603227 : (term384 = term385) = (term386 = term387).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term385). Qed.
Lemma lem2603228 : term386 = term387.
Proof. exact (EQ_MP (@lem2603227) (@lem2603226)). Qed.
Lemma lem2603229 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2603230 : term388 = term389.
Proof. exact (MK_COMB (@lem2603229) (@lem2603228)). Qed.
Lemma lem2603231 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2603232 : term383 = term378.
Proof. exact (MK_COMB (@lem2603231) (@lem2603230)). Qed.
Lemma lem2603233 : term375 = term378.
Proof. exact (TRANS (@lem2603225) (@lem2603232)). Qed.
Lemma lem2603234 : term382 = term378.
Proof. exact (TRANS (@lem2603224) (@lem2603233)). Qed.
Lemma lem2603235 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2603236 : term390 = term391.
Proof. exact (MK_COMB (@lem2603235) (@lem2603234)). Qed.
Lemma lem2603237 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2603238 : term392 = term393.
Proof. exact (MK_COMB (@lem2603236) (@lem2603237)). Qed.
Lemma lem2603240 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2603241 : term393 = term394.
Proof. exact (@lem2603240 term387 term64). Qed.
Lemma lem2603242 : term395 = term385.
Proof. exact (@lem996237 term385). Qed.
Lemma lem2603243 : (term395 = term385) = (term396 = term387).
Proof. exact (@lem1007663 term385 (BIT1 0) term385). Qed.
Lemma lem2603244 : term396 = term387.
Proof. exact (EQ_MP (@lem2603243) (@lem2603242)). Qed.
Lemma lem2603245 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2603246 : term397 = term389.
Proof. exact (MK_COMB (@lem2603245) (@lem2603244)). Qed.
Lemma lem2603247 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2603248 : term394 = term378.
Proof. exact (MK_COMB (@lem2603247) (@lem2603246)). Qed.
Lemma lem2603249 : term393 = term378.
Proof. exact (TRANS (@lem2603241) (@lem2603248)). Qed.
Lemma lem2603250 : term392 = term378.
Proof. exact (TRANS (@lem2603238) (@lem2603249)). Qed.
Lemma lem2603252 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2603253 : term144 = term145.
Proof. exact (@lem2603252 term64 term64). Qed.
Lemma lem2603254 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2603255 : term147 = term64.
Proof. exact (EQ_MP (@lem2603254) (@lem940073)). Qed.
Lemma lem2603256 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2603257 : term145 = term63.
Proof. exact (MK_COMB (@lem2603256) (@lem2603255)). Qed.
Lemma lem2603258 : term144 = term63.
Proof. exact (TRANS (@lem2603253) (@lem2603257)). Qed.
Lemma lem2603259 : term391 = term391.
Proof. exact (eq_refl term391). Qed.
Lemma lem2603260 : term398 = term393.
Proof. exact (MK_COMB (@lem2603259) (@lem2603258)). Qed.
Lemma lem2603262 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2603263 : term393 = term394.
Proof. exact (@lem2603262 term387 term64). Qed.
Lemma lem2603264 : term395 = term385.
Proof. exact (@lem996237 term385). Qed.
Lemma lem2603265 : (term395 = term385) = (term396 = term387).
Proof. exact (@lem1007663 term385 (BIT1 0) term385). Qed.
Lemma lem2603266 : term396 = term387.
Proof. exact (EQ_MP (@lem2603265) (@lem2603264)). Qed.
Lemma lem2603267 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2603268 : term397 = term389.
Proof. exact (MK_COMB (@lem2603267) (@lem2603266)). Qed.
Lemma lem2603269 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2603270 : term394 = term378.
Proof. exact (MK_COMB (@lem2603269) (@lem2603268)). Qed.
Lemma lem2603271 : term393 = term378.
Proof. exact (TRANS (@lem2603263) (@lem2603270)). Qed.
Lemma lem2603272 : term398 = term378.
Proof. exact (TRANS (@lem2603260) (@lem2603271)). Qed.
Lemma lem2603273 : term378 = term398.
Proof. exact (SYM (@lem2603272)). Qed.
Lemma lem2603274 : term392 = term398.
Proof. exact (TRANS (@lem2603250) (@lem2603273)). Qed.
Lemma lem2603275 : term376 = term399.
Proof. exact (@lem2603201 (@lem2603274)). Qed.
Lemma lem2603276 : term375 = term399.
Proof. exact (TRANS (@lem2603167) (@lem2603275)). Qed.
Lemma lem2603278 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2603279 : term399 = term378.
Proof. exact (@lem2603278 term378). Qed.
Lemma lem2603280 : term375 = term378.
Proof. exact (TRANS (@lem2603276) (@lem2603279)). Qed.
Lemma lem2603281 (m : int) : (term374 m) = term400.
Proof. exact (MK_COMB (@lem2603158 m) (@lem2603280)). Qed.
Lemma lem2603282 (m : int) : (term373 m) = term400.
Proof. exact (TRANS (@lem2603050 m) (@lem2603281 m)). Qed.
Lemma lem2603283 : term400 = term378.
Proof. exact (@lem1982721 term378). Qed.
Lemma lem2603284 (m : int) : (term373 m) = term378.
Proof. exact (TRANS (@lem2603282 m) (@lem2603283)). Qed.
Lemma lem2603285 (c : int) (n : int) (m : int) : (term372 c n m) = term400.
Proof. exact (MK_COMB (@lem2603049 c n) (@lem2603284 m)). Qed.
Lemma lem2603286 (c : int) (n : int) (m : int) : (term371 c n m) = term400.
Proof. exact (TRANS (@lem2602941 c n m) (@lem2603285 c n m)). Qed.
Lemma lem2603287 : term400 = term378.
Proof. exact (@lem1982721 term378). Qed.
Lemma lem2603288 (c : int) (n : int) (m : int) : (term371 c n m) = term378.
Proof. exact (TRANS (@lem2603286 c n m) (@lem2603287)). Qed.
Lemma lem2603289 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2603290 (c : int) (n : int) (m : int) : (term401 c n m) = term402.
Proof. exact (MK_COMB (@lem2603289) (@lem2603288 c n m)). Qed.
Lemma lem2603291 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2603292 (c : int) (n : int) (m : int) : (term370 c n m) = term403.
Proof. exact (MK_COMB (@lem2603290 c n m) (@lem2603291)). Qed.
Lemma lem2603293 (c : int) (n : int) (m : int) (h1 : term368 c n m) : term403.
Proof. exact (EQ_MP (@lem2603292 c n m) (@lem2602940 c n m h1)). Qed.
Lemma lem2603295 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2603296 : term403 = term404.
Proof. exact (@lem2603295 term160 term378). Qed.
Lemma lem2603298 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2603299 : term378 = term399.
Proof. exact (@lem2603298 term387). Qed.
Lemma lem2603301 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2603302 : term160 = term259.
Proof. exact (@lem2603301 (NUMERAL 0)). Qed.
Lemma lem2603303 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2603304 : term323 = term324.
Proof. exact (MK_COMB (@lem2603303) (@lem2603302)). Qed.
Lemma lem2603305 : term404 = term405.
Proof. exact (MK_COMB (@lem2603304) (@lem2603299)). Qed.
Lemma lem2603306 : term406.
Proof. exact (@lem1980026 term160 term63 term378 term63). Qed.
Lemma lem2603308 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603309 : term258 = term265.
Proof. exact (@lem2603308 (NUMERAL 0) term64). Qed.
Lemma lem2603310 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603311 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603312 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603311 h1) (fun h1 : term265 = True => @lem2603310)). Qed.
Lemma lem2603313 : term265 = True.
Proof. exact (EQ_MP (@lem2603312) (@lem2603310)). Qed.
Lemma lem2603314 : term258 = True.
Proof. exact (TRANS (@lem2603309) (@lem2603313)). Qed.
Lemma lem2603315 : True = term258.
Proof. exact (SYM (@lem2603314)). Qed.
Lemma lem2603316 : term258.
Proof. exact (EQ_MP (@lem2603315) (@lem0)). Qed.
Lemma lem2603317 : term407.
Proof. exact (@lem2603306 (@lem2603316)). Qed.
Lemma lem2603319 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603320 : term258 = term265.
Proof. exact (@lem2603319 (NUMERAL 0) term64). Qed.
Lemma lem2603321 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603322 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603323 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603322 h1) (fun h1 : term265 = True => @lem2603321)). Qed.
Lemma lem2603324 : term265 = True.
Proof. exact (EQ_MP (@lem2603323) (@lem2603321)). Qed.
Lemma lem2603325 : term258 = True.
Proof. exact (TRANS (@lem2603320) (@lem2603324)). Qed.
Lemma lem2603326 : True = term258.
Proof. exact (SYM (@lem2603325)). Qed.
Lemma lem2603327 : term258.
Proof. exact (EQ_MP (@lem2603326) (@lem0)). Qed.
Lemma lem2603328 : term405 = term408.
Proof. exact (@lem2603317 (@lem2603327)). Qed.
Lemma lem2603330 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2603331 : term393 = term394.
Proof. exact (@lem2603330 term387 term64). Qed.
Lemma lem2603332 : term395 = term385.
Proof. exact (@lem996237 term385). Qed.
Lemma lem2603333 : (term395 = term385) = (term396 = term387).
Proof. exact (@lem1007663 term385 (BIT1 0) term385). Qed.
Lemma lem2603334 : term396 = term387.
Proof. exact (EQ_MP (@lem2603333) (@lem2603332)). Qed.
Lemma lem2603335 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2603336 : term397 = term389.
Proof. exact (MK_COMB (@lem2603335) (@lem2603334)). Qed.
Lemma lem2603337 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2603338 : term394 = term378.
Proof. exact (MK_COMB (@lem2603337) (@lem2603336)). Qed.
Lemma lem2603339 : term393 = term378.
Proof. exact (TRANS (@lem2603331) (@lem2603338)). Qed.
Lemma lem2603341 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2603342 : term270 = term160.
Proof. exact (@lem2603341 term64). Qed.
Lemma lem2603343 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2603344 : term329 = term323.
Proof. exact (MK_COMB (@lem2603343) (@lem2603342)). Qed.
Lemma lem2603345 : term408 = term404.
Proof. exact (MK_COMB (@lem2603344) (@lem2603339)). Qed.
Lemma lem2603347 (m : nat) (n : nat) : (term330 m n) = (term331 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2603348 : term404 = term409.
Proof. exact (@lem2603347 (NUMERAL 0) term387). Qed.
Lemma lem2603349 : term410 = term385.
Proof. exact (@lem912803). Qed.
Lemma lem2603350 (h1 : term410 = term385) : (term387 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term385 h1). Qed.
Lemma lem2603351 : (term410 = term385) = ((term387 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term410 = term385 => @lem2603350 h1) (fun h1 : (term387 = (NUMERAL 0)) = False => @lem2603349)). Qed.
Lemma lem2603352 : (term387 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2603351) (@lem2603349)). Qed.
Lemma lem2603353 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2603354 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2603355 : term333 = (and True).
Proof. exact (MK_COMB (@lem2603354) (@lem2603353)). Qed.
Lemma lem2603356 : term409 = (True /\ False).
Proof. exact (MK_COMB (@lem2603355) (@lem2603352)). Qed.
Lemma lem2603358 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2603359 : term409 = False.
Proof. exact (TRANS (@lem2603356) (@lem2603358)). Qed.
Lemma lem2603360 : term404 = False.
Proof. exact (TRANS (@lem2603348) (@lem2603359)). Qed.
Lemma lem2603361 : term408 = False.
Proof. exact (TRANS (@lem2603345) (@lem2603360)). Qed.
Lemma lem2603362 : term405 = False.
Proof. exact (TRANS (@lem2603328) (@lem2603361)). Qed.
Lemma lem2603363 : term404 = False.
Proof. exact (TRANS (@lem2603305) (@lem2603362)). Qed.
Lemma lem2603364 : term403 = False.
Proof. exact (TRANS (@lem2603296) (@lem2603363)). Qed.
Lemma lem2603365 (c : int) (n : int) (m : int) (h1 : term368 c n m) : False.
Proof. exact (EQ_MP (@lem2603364) (@lem2603293 c n m h1)). Qed.
Lemma lem2603366 (c : int) (n : int) (m : int) (h1 : term249 c n m) : False.
Proof. exact (or_elim (@lem2602321 c n m h1) (fun h0 : term355 c n m => @lem2602782 c n m h0) (fun h0 : term368 c n m => @lem2603365 c n m h0)). Qed.
Lemma lem2603367 (c : int) (n : int) (m : int) (h1 : term247 c n m) : term247 c n m.
Proof. exact (h1). Qed.
Lemma lem2603368 (c : int) (n : int) (m : int) (h1 : term411 c n m) : term411 c n m.
Proof. exact (h1). Qed.
Lemma lem2603369 (c : int) (n : int) (m : int) (h1 : term411 c n m) : term189 c n m.
Proof. exact (proj2 (@lem2603368 c n m h1)). Qed.
Lemma lem2603370 (c : int) (n : int) (m : int) (h1 : term411 c n m) : term224 c n m.
Proof. exact (proj1 (@lem2603368 c n m h1)). Qed.
Lemma lem2603371 (c : int) (n : int) (m : int) (h1 : term411 c n m) : term215 c n m.
Proof. exact (proj2 (@lem2603370 c n m h1)). Qed.
Lemma lem2603374 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2603375 : term257 = term258.
Proof. exact (@lem2603374 term160 term63). Qed.
Lemma lem2603377 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2603378 : term63 = term151.
Proof. exact (@lem2603377 term64). Qed.
Lemma lem2603380 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2603381 : term160 = term259.
Proof. exact (@lem2603380 (NUMERAL 0)). Qed.
Lemma lem2603382 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2603383 : term260 = term261.
Proof. exact (MK_COMB (@lem2603382) (@lem2603381)). Qed.
Lemma lem2603384 : term258 = term262.
Proof. exact (MK_COMB (@lem2603383) (@lem2603378)). Qed.
Lemma lem2603385 : term263.
Proof. exact (@lem1980255 term160 term63 term63 term63). Qed.
Lemma lem2603387 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603388 : term258 = term265.
Proof. exact (@lem2603387 (NUMERAL 0) term64). Qed.
Lemma lem2603389 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603390 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603391 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603390 h1) (fun h1 : term265 = True => @lem2603389)). Qed.
Lemma lem2603392 : term265 = True.
Proof. exact (EQ_MP (@lem2603391) (@lem2603389)). Qed.
Lemma lem2603393 : term258 = True.
Proof. exact (TRANS (@lem2603388) (@lem2603392)). Qed.
Lemma lem2603394 : True = term258.
Proof. exact (SYM (@lem2603393)). Qed.
Lemma lem2603395 : term258.
Proof. exact (EQ_MP (@lem2603394) (@lem0)). Qed.
Lemma lem2603396 : term267.
Proof. exact (@lem2603385 (@lem2603395)). Qed.
Lemma lem2603398 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603399 : term258 = term265.
Proof. exact (@lem2603398 (NUMERAL 0) term64). Qed.
Lemma lem2603400 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603401 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603402 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603401 h1) (fun h1 : term265 = True => @lem2603400)). Qed.
Lemma lem2603403 : term265 = True.
Proof. exact (EQ_MP (@lem2603402) (@lem2603400)). Qed.
Lemma lem2603404 : term258 = True.
Proof. exact (TRANS (@lem2603399) (@lem2603403)). Qed.
Lemma lem2603405 : True = term258.
Proof. exact (SYM (@lem2603404)). Qed.
Lemma lem2603406 : term258.
Proof. exact (EQ_MP (@lem2603405) (@lem0)). Qed.
Lemma lem2603407 : term262 = term268.
Proof. exact (@lem2603396 (@lem2603406)). Qed.
Lemma lem2603409 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2603410 : term144 = term145.
Proof. exact (@lem2603409 term64 term64). Qed.
Lemma lem2603411 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2603412 : term147 = term64.
Proof. exact (EQ_MP (@lem2603411) (@lem940073)). Qed.
Lemma lem2603413 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2603414 : term145 = term63.
Proof. exact (MK_COMB (@lem2603413) (@lem2603412)). Qed.
Lemma lem2603415 : term144 = term63.
Proof. exact (TRANS (@lem2603410) (@lem2603414)). Qed.
Lemma lem2603417 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2603418 : term270 = term160.
Proof. exact (@lem2603417 term64). Qed.
Lemma lem2603419 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2603420 : term271 = term260.
Proof. exact (MK_COMB (@lem2603419) (@lem2603418)). Qed.
Lemma lem2603421 : term268 = term258.
Proof. exact (MK_COMB (@lem2603420) (@lem2603415)). Qed.
Lemma lem2603423 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603424 : term258 = term265.
Proof. exact (@lem2603423 (NUMERAL 0) term64). Qed.
Lemma lem2603425 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603426 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603427 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603426 h1) (fun h1 : term265 = True => @lem2603425)). Qed.
Lemma lem2603428 : term265 = True.
Proof. exact (EQ_MP (@lem2603427) (@lem2603425)). Qed.
Lemma lem2603429 : term258 = True.
Proof. exact (TRANS (@lem2603424) (@lem2603428)). Qed.
Lemma lem2603430 : term268 = True.
Proof. exact (TRANS (@lem2603421) (@lem2603429)). Qed.
Lemma lem2603431 : term262 = True.
Proof. exact (TRANS (@lem2603407) (@lem2603430)). Qed.
Lemma lem2603432 : term258 = True.
Proof. exact (TRANS (@lem2603384) (@lem2603431)). Qed.
Lemma lem2603433 : term257 = True.
Proof. exact (TRANS (@lem2603375) (@lem2603432)). Qed.
Lemma lem2603434 : True = term257.
Proof. exact (SYM (@lem2603433)). Qed.
Lemma lem2603435 : term257.
Proof. exact (EQ_MP (@lem2603434) (@lem0)). Qed.
Lemma lem2603436 (c : int) (n : int) (m : int) (h1 : term411 c n m) : term272 c n m.
Proof. exact (conj (@lem2603435) (@lem2603369 c n m h1)). Qed.
Lemma lem2603438 (x : real) (y : real) : term273 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2603439 (c : int) (n : int) (m : int) : term274 c n m.
Proof. exact (@lem2603438 term63 (term186 c n m)). Qed.
Lemma lem2603440 (c : int) (n : int) (m : int) (h1 : term411 c n m) : term275 c n m.
Proof. exact (@lem2603439 c n m (@lem2603436 c n m h1)). Qed.
Lemma lem2603441 (c : int) (n : int) (m : int) : (term276 c n m) = (term186 c n m).
Proof. exact (@lem1982733 (term186 c n m)). Qed.
Lemma lem2603442 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2603443 (c : int) (n : int) (m : int) : (term277 c n m) = (term188 c n m).
Proof. exact (MK_COMB (@lem2603442) (@lem2603441 c n m)). Qed.
Lemma lem2603444 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2603445 (c : int) (n : int) (m : int) : (term275 c n m) = (term189 c n m).
Proof. exact (MK_COMB (@lem2603443 c n m) (@lem2603444)). Qed.
Lemma lem2603446 (c : int) (n : int) (m : int) (h1 : term411 c n m) : term189 c n m.
Proof. exact (EQ_MP (@lem2603445 c n m) (@lem2603440 c n m h1)). Qed.
Lemma lem2603448 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2603449 : term257 = term258.
Proof. exact (@lem2603448 term160 term63). Qed.
Lemma lem2603451 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2603452 : term63 = term151.
Proof. exact (@lem2603451 term64). Qed.
Lemma lem2603454 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2603455 : term160 = term259.
Proof. exact (@lem2603454 (NUMERAL 0)). Qed.
Lemma lem2603456 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2603457 : term260 = term261.
Proof. exact (MK_COMB (@lem2603456) (@lem2603455)). Qed.
Lemma lem2603458 : term258 = term262.
Proof. exact (MK_COMB (@lem2603457) (@lem2603452)). Qed.
Lemma lem2603459 : term263.
Proof. exact (@lem1980255 term160 term63 term63 term63). Qed.
Lemma lem2603461 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603462 : term258 = term265.
Proof. exact (@lem2603461 (NUMERAL 0) term64). Qed.
Lemma lem2603463 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603464 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603465 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603464 h1) (fun h1 : term265 = True => @lem2603463)). Qed.
Lemma lem2603466 : term265 = True.
Proof. exact (EQ_MP (@lem2603465) (@lem2603463)). Qed.
Lemma lem2603467 : term258 = True.
Proof. exact (TRANS (@lem2603462) (@lem2603466)). Qed.
Lemma lem2603468 : True = term258.
Proof. exact (SYM (@lem2603467)). Qed.
Lemma lem2603469 : term258.
Proof. exact (EQ_MP (@lem2603468) (@lem0)). Qed.
Lemma lem2603470 : term267.
Proof. exact (@lem2603459 (@lem2603469)). Qed.
Lemma lem2603472 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603473 : term258 = term265.
Proof. exact (@lem2603472 (NUMERAL 0) term64). Qed.
Lemma lem2603474 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603475 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603476 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603475 h1) (fun h1 : term265 = True => @lem2603474)). Qed.
Lemma lem2603477 : term265 = True.
Proof. exact (EQ_MP (@lem2603476) (@lem2603474)). Qed.
Lemma lem2603478 : term258 = True.
Proof. exact (TRANS (@lem2603473) (@lem2603477)). Qed.
Lemma lem2603479 : True = term258.
Proof. exact (SYM (@lem2603478)). Qed.
Lemma lem2603480 : term258.
Proof. exact (EQ_MP (@lem2603479) (@lem0)). Qed.
Lemma lem2603481 : term262 = term268.
Proof. exact (@lem2603470 (@lem2603480)). Qed.
Lemma lem2603483 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2603484 : term144 = term145.
Proof. exact (@lem2603483 term64 term64). Qed.
Lemma lem2603485 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2603486 : term147 = term64.
Proof. exact (EQ_MP (@lem2603485) (@lem940073)). Qed.
Lemma lem2603487 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2603488 : term145 = term63.
Proof. exact (MK_COMB (@lem2603487) (@lem2603486)). Qed.
Lemma lem2603489 : term144 = term63.
Proof. exact (TRANS (@lem2603484) (@lem2603488)). Qed.
Lemma lem2603491 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2603492 : term270 = term160.
Proof. exact (@lem2603491 term64). Qed.
Lemma lem2603493 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2603494 : term271 = term260.
Proof. exact (MK_COMB (@lem2603493) (@lem2603492)). Qed.
Lemma lem2603495 : term268 = term258.
Proof. exact (MK_COMB (@lem2603494) (@lem2603489)). Qed.
Lemma lem2603497 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603498 : term258 = term265.
Proof. exact (@lem2603497 (NUMERAL 0) term64). Qed.
Lemma lem2603499 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603500 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603501 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603500 h1) (fun h1 : term265 = True => @lem2603499)). Qed.
Lemma lem2603502 : term265 = True.
Proof. exact (EQ_MP (@lem2603501) (@lem2603499)). Qed.
Lemma lem2603503 : term258 = True.
Proof. exact (TRANS (@lem2603498) (@lem2603502)). Qed.
Lemma lem2603504 : term268 = True.
Proof. exact (TRANS (@lem2603495) (@lem2603503)). Qed.
Lemma lem2603505 : term262 = True.
Proof. exact (TRANS (@lem2603481) (@lem2603504)). Qed.
Lemma lem2603506 : term258 = True.
Proof. exact (TRANS (@lem2603458) (@lem2603505)). Qed.
Lemma lem2603507 : term257 = True.
Proof. exact (TRANS (@lem2603449) (@lem2603506)). Qed.
Lemma lem2603508 : True = term257.
Proof. exact (SYM (@lem2603507)). Qed.
Lemma lem2603509 : term257.
Proof. exact (EQ_MP (@lem2603508) (@lem0)). Qed.
Lemma lem2603510 (c : int) (n : int) (m : int) (h1 : term411 c n m) : term412 c n m.
Proof. exact (conj (@lem2603509) (@lem2603371 c n m h1)). Qed.
Lemma lem2603512 (x : real) (y : real) : term273 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2603513 (c : int) (n : int) (m : int) : term413 c n m.
Proof. exact (@lem2603512 term63 (term212 c n m)). Qed.
Lemma lem2603514 (c : int) (n : int) (m : int) (h1 : term411 c n m) : term414 c n m.
Proof. exact (@lem2603513 c n m (@lem2603510 c n m h1)). Qed.
Lemma lem2603515 (c : int) (n : int) (m : int) : (term415 c n m) = (term212 c n m).
Proof. exact (@lem1982733 (term212 c n m)). Qed.
Lemma lem2603516 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2603517 (c : int) (n : int) (m : int) : (term416 c n m) = (term214 c n m).
Proof. exact (MK_COMB (@lem2603516) (@lem2603515 c n m)). Qed.
Lemma lem2603518 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2603519 (c : int) (n : int) (m : int) : (term414 c n m) = (term215 c n m).
Proof. exact (MK_COMB (@lem2603517 c n m) (@lem2603518)). Qed.
Lemma lem2603520 (c : int) (n : int) (m : int) (h1 : term411 c n m) : term215 c n m.
Proof. exact (EQ_MP (@lem2603519 c n m) (@lem2603514 c n m h1)). Qed.
Lemma lem2603521 (c : int) (n : int) (m : int) (h1 : term411 c n m) : term417 c n m.
Proof. exact (conj (@lem2603520 c n m h1) (@lem2603446 c n m h1)). Qed.
Lemma lem2603523 (x : real) (y : real) : term361 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2603524 (c : int) (n : int) (m : int) : term418 c n m.
Proof. exact (@lem2603523 (term212 c n m) (term186 c n m)). Qed.
Lemma lem2603525 (c : int) (n : int) (m : int) (h1 : term411 c n m) : term288 c n m.
Proof. exact (@lem2603524 c n m (@lem2603521 c n m h1)). Qed.
Lemma lem2603526 (c : int) (n : int) (m : int) : (term289 c n m) = (term290 c n m).
Proof. exact (@lem1982753 (term126 c n) (term40 c n) (term124 m) (term184 m)). Qed.
Lemma lem2603527 (c : int) (n : int) : (term291 c n) = (term292 c n).
Proof. exact (@lem1982713 term127 (term40 c n)). Qed.
Lemma lem2603529 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2603530 : term63 = term151.
Proof. exact (@lem2603529 term64). Qed.
Lemma lem2603532 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2603533 : term127 = term137.
Proof. exact (@lem2603532 term64). Qed.
Lemma lem2603534 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2603535 : term293 = term294.
Proof. exact (MK_COMB (@lem2603534) (@lem2603533)). Qed.
Lemma lem2603536 : term295 = term296.
Proof. exact (MK_COMB (@lem2603535) (@lem2603530)). Qed.
Lemma lem2603537 : term297.
Proof. exact (@lem1981473 term127 term63 term63 term63 term160 term63). Qed.
Lemma lem2603539 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603540 : term258 = term265.
Proof. exact (@lem2603539 (NUMERAL 0) term64). Qed.
Lemma lem2603541 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603542 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603543 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603542 h1) (fun h1 : term265 = True => @lem2603541)). Qed.
Lemma lem2603544 : term265 = True.
Proof. exact (EQ_MP (@lem2603543) (@lem2603541)). Qed.
Lemma lem2603545 : term258 = True.
Proof. exact (TRANS (@lem2603540) (@lem2603544)). Qed.
Lemma lem2603546 : True = term258.
Proof. exact (SYM (@lem2603545)). Qed.
Lemma lem2603547 : term258.
Proof. exact (EQ_MP (@lem2603546) (@lem0)). Qed.
Lemma lem2603548 : term298.
Proof. exact (@lem2603537 (@lem2603547)). Qed.
Lemma lem2603550 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603551 : term258 = term265.
Proof. exact (@lem2603550 (NUMERAL 0) term64). Qed.
Lemma lem2603552 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603553 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603554 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603553 h1) (fun h1 : term265 = True => @lem2603552)). Qed.
Lemma lem2603555 : term265 = True.
Proof. exact (EQ_MP (@lem2603554) (@lem2603552)). Qed.
Lemma lem2603556 : term258 = True.
Proof. exact (TRANS (@lem2603551) (@lem2603555)). Qed.
Lemma lem2603557 : True = term258.
Proof. exact (SYM (@lem2603556)). Qed.
Lemma lem2603558 : term258.
Proof. exact (EQ_MP (@lem2603557) (@lem0)). Qed.
Lemma lem2603559 : term299.
Proof. exact (@lem2603548 (@lem2603558)). Qed.
Lemma lem2603561 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603562 : term258 = term265.
Proof. exact (@lem2603561 (NUMERAL 0) term64). Qed.
Lemma lem2603563 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603564 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603565 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603564 h1) (fun h1 : term265 = True => @lem2603563)). Qed.
Lemma lem2603566 : term265 = True.
Proof. exact (EQ_MP (@lem2603565) (@lem2603563)). Qed.
Lemma lem2603567 : term258 = True.
Proof. exact (TRANS (@lem2603562) (@lem2603566)). Qed.
Lemma lem2603568 : True = term258.
Proof. exact (SYM (@lem2603567)). Qed.
Lemma lem2603569 : term258.
Proof. exact (EQ_MP (@lem2603568) (@lem0)). Qed.
Lemma lem2603570 : term300.
Proof. exact (@lem2603559 (@lem2603569)). Qed.
Lemma lem2603572 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2603573 : term144 = term145.
Proof. exact (@lem2603572 term64 term64). Qed.
Lemma lem2603574 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2603575 : term147 = term64.
Proof. exact (EQ_MP (@lem2603574) (@lem940073)). Qed.
Lemma lem2603576 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2603577 : term145 = term63.
Proof. exact (MK_COMB (@lem2603576) (@lem2603575)). Qed.
Lemma lem2603578 : term144 = term63.
Proof. exact (TRANS (@lem2603573) (@lem2603577)). Qed.
Lemma lem2603580 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2603581 : term172 = term177.
Proof. exact (@lem2603580 term64 term64). Qed.
Lemma lem2603582 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2603583 : term147 = term64.
Proof. exact (EQ_MP (@lem2603582) (@lem940073)). Qed.
Lemma lem2603584 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2603585 : term145 = term63.
Proof. exact (MK_COMB (@lem2603584) (@lem2603583)). Qed.
Lemma lem2603586 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2603587 : term177 = term127.
Proof. exact (MK_COMB (@lem2603586) (@lem2603585)). Qed.
Lemma lem2603588 : term172 = term127.
Proof. exact (TRANS (@lem2603581) (@lem2603587)). Qed.
Lemma lem2603589 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2603590 : term301 = term293.
Proof. exact (MK_COMB (@lem2603589) (@lem2603588)). Qed.
Lemma lem2603591 : term302 = term295.
Proof. exact (MK_COMB (@lem2603590) (@lem2603578)). Qed.
Lemma lem2603593 (m : nat) : (term303 m) = term160.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2603594 : term295 = term160.
Proof. exact (@lem2603593 term64). Qed.
Lemma lem2603595 : term302 = term160.
Proof. exact (TRANS (@lem2603591) (@lem2603594)). Qed.
Lemma lem2603596 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2603597 : term304 = term305.
Proof. exact (MK_COMB (@lem2603596) (@lem2603595)). Qed.
Lemma lem2603598 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2603599 : term306 = term270.
Proof. exact (MK_COMB (@lem2603597) (@lem2603598)). Qed.
Lemma lem2603601 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2603602 : term270 = term160.
Proof. exact (@lem2603601 term64). Qed.
Lemma lem2603603 : term306 = term160.
Proof. exact (TRANS (@lem2603599) (@lem2603602)). Qed.
Lemma lem2603605 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2603606 : term144 = term145.
Proof. exact (@lem2603605 term64 term64). Qed.
Lemma lem2603607 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2603608 : term147 = term64.
Proof. exact (EQ_MP (@lem2603607) (@lem940073)). Qed.
Lemma lem2603609 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2603610 : term145 = term63.
Proof. exact (MK_COMB (@lem2603609) (@lem2603608)). Qed.
Lemma lem2603611 : term144 = term63.
Proof. exact (TRANS (@lem2603606) (@lem2603610)). Qed.
Lemma lem2603612 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem2603613 : term307 = term270.
Proof. exact (MK_COMB (@lem2603612) (@lem2603611)). Qed.
Lemma lem2603615 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2603616 : term270 = term160.
Proof. exact (@lem2603615 term64). Qed.
Lemma lem2603617 : term307 = term160.
Proof. exact (TRANS (@lem2603613) (@lem2603616)). Qed.
Lemma lem2603618 : term160 = term307.
Proof. exact (SYM (@lem2603617)). Qed.
Lemma lem2603619 : term306 = term307.
Proof. exact (TRANS (@lem2603603) (@lem2603618)). Qed.
Lemma lem2603620 : term296 = term259.
Proof. exact (@lem2603570 (@lem2603619)). Qed.
Lemma lem2603621 : term295 = term259.
Proof. exact (TRANS (@lem2603536) (@lem2603620)). Qed.
Lemma lem2603623 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2603624 : term259 = term160.
Proof. exact (@lem2603623 term160). Qed.
Lemma lem2603625 : term295 = term160.
Proof. exact (TRANS (@lem2603621) (@lem2603624)). Qed.
Lemma lem2603626 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2603627 : term308 = term305.
Proof. exact (MK_COMB (@lem2603626) (@lem2603625)). Qed.
Lemma lem2603628 (c : int) (n : int) : (term40 c n) = (term40 c n).
Proof. exact (eq_refl (term40 c n)). Qed.
Lemma lem2603629 (c : int) (n : int) : (term292 c n) = (term309 c n).
Proof. exact (MK_COMB (@lem2603627) (@lem2603628 c n)). Qed.
Lemma lem2603630 (c : int) (n : int) : (term291 c n) = (term309 c n).
Proof. exact (TRANS (@lem2603527 c n) (@lem2603629 c n)). Qed.
Lemma lem2603631 (c : int) (n : int) : (term309 c n) = term160.
Proof. exact (@lem1982719 (term40 c n)). Qed.
Lemma lem2603632 (c : int) (n : int) : (term291 c n) = term160.
Proof. exact (TRANS (@lem2603630 c n) (@lem2603631 c n)). Qed.
Lemma lem2603633 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2603634 (c : int) (n : int) : (term310 c n) = term311.
Proof. exact (MK_COMB (@lem2603633) (@lem2603632 c n)). Qed.
Lemma lem2603635 (m : int) : (term312 m) = (term313 m).
Proof. exact (@lem1982763 (term124 m) (real_of_int m) term127). Qed.
Lemma lem2603636 (m : int) : (term314 m) = (term315 m).
Proof. exact (@lem1982713 term127 (real_of_int m)). Qed.
Lemma lem2603638 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2603639 : term63 = term151.
Proof. exact (@lem2603638 term64). Qed.
Lemma lem2603641 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2603642 : term127 = term137.
Proof. exact (@lem2603641 term64). Qed.
Lemma lem2603643 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2603644 : term293 = term294.
Proof. exact (MK_COMB (@lem2603643) (@lem2603642)). Qed.
Lemma lem2603645 : term295 = term296.
Proof. exact (MK_COMB (@lem2603644) (@lem2603639)). Qed.
Lemma lem2603646 : term297.
Proof. exact (@lem1981473 term127 term63 term63 term63 term160 term63). Qed.
Lemma lem2603648 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603649 : term258 = term265.
Proof. exact (@lem2603648 (NUMERAL 0) term64). Qed.
Lemma lem2603650 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603651 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603652 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603651 h1) (fun h1 : term265 = True => @lem2603650)). Qed.
Lemma lem2603653 : term265 = True.
Proof. exact (EQ_MP (@lem2603652) (@lem2603650)). Qed.
Lemma lem2603654 : term258 = True.
Proof. exact (TRANS (@lem2603649) (@lem2603653)). Qed.
Lemma lem2603655 : True = term258.
Proof. exact (SYM (@lem2603654)). Qed.
Lemma lem2603656 : term258.
Proof. exact (EQ_MP (@lem2603655) (@lem0)). Qed.
Lemma lem2603657 : term298.
Proof. exact (@lem2603646 (@lem2603656)). Qed.
Lemma lem2603659 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603660 : term258 = term265.
Proof. exact (@lem2603659 (NUMERAL 0) term64). Qed.
Lemma lem2603661 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603662 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603663 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603662 h1) (fun h1 : term265 = True => @lem2603661)). Qed.
Lemma lem2603664 : term265 = True.
Proof. exact (EQ_MP (@lem2603663) (@lem2603661)). Qed.
Lemma lem2603665 : term258 = True.
Proof. exact (TRANS (@lem2603660) (@lem2603664)). Qed.
Lemma lem2603666 : True = term258.
Proof. exact (SYM (@lem2603665)). Qed.
Lemma lem2603667 : term258.
Proof. exact (EQ_MP (@lem2603666) (@lem0)). Qed.
Lemma lem2603668 : term299.
Proof. exact (@lem2603657 (@lem2603667)). Qed.
Lemma lem2603670 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603671 : term258 = term265.
Proof. exact (@lem2603670 (NUMERAL 0) term64). Qed.
Lemma lem2603672 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603673 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603674 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603673 h1) (fun h1 : term265 = True => @lem2603672)). Qed.
Lemma lem2603675 : term265 = True.
Proof. exact (EQ_MP (@lem2603674) (@lem2603672)). Qed.
Lemma lem2603676 : term258 = True.
Proof. exact (TRANS (@lem2603671) (@lem2603675)). Qed.
Lemma lem2603677 : True = term258.
Proof. exact (SYM (@lem2603676)). Qed.
Lemma lem2603678 : term258.
Proof. exact (EQ_MP (@lem2603677) (@lem0)). Qed.
Lemma lem2603679 : term300.
Proof. exact (@lem2603668 (@lem2603678)). Qed.
Lemma lem2603681 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2603682 : term144 = term145.
Proof. exact (@lem2603681 term64 term64). Qed.
Lemma lem2603683 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2603684 : term147 = term64.
Proof. exact (EQ_MP (@lem2603683) (@lem940073)). Qed.
Lemma lem2603685 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2603686 : term145 = term63.
Proof. exact (MK_COMB (@lem2603685) (@lem2603684)). Qed.
Lemma lem2603687 : term144 = term63.
Proof. exact (TRANS (@lem2603682) (@lem2603686)). Qed.
Lemma lem2603689 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2603690 : term172 = term177.
Proof. exact (@lem2603689 term64 term64). Qed.
Lemma lem2603691 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2603692 : term147 = term64.
Proof. exact (EQ_MP (@lem2603691) (@lem940073)). Qed.
Lemma lem2603693 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2603694 : term145 = term63.
Proof. exact (MK_COMB (@lem2603693) (@lem2603692)). Qed.
Lemma lem2603695 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2603696 : term177 = term127.
Proof. exact (MK_COMB (@lem2603695) (@lem2603694)). Qed.
Lemma lem2603697 : term172 = term127.
Proof. exact (TRANS (@lem2603690) (@lem2603696)). Qed.
Lemma lem2603698 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2603699 : term301 = term293.
Proof. exact (MK_COMB (@lem2603698) (@lem2603697)). Qed.
Lemma lem2603700 : term302 = term295.
Proof. exact (MK_COMB (@lem2603699) (@lem2603687)). Qed.
Lemma lem2603702 (m : nat) : (term303 m) = term160.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2603703 : term295 = term160.
Proof. exact (@lem2603702 term64). Qed.
Lemma lem2603704 : term302 = term160.
Proof. exact (TRANS (@lem2603700) (@lem2603703)). Qed.
Lemma lem2603705 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2603706 : term304 = term305.
Proof. exact (MK_COMB (@lem2603705) (@lem2603704)). Qed.
Lemma lem2603707 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2603708 : term306 = term270.
Proof. exact (MK_COMB (@lem2603706) (@lem2603707)). Qed.
Lemma lem2603710 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2603711 : term270 = term160.
Proof. exact (@lem2603710 term64). Qed.
Lemma lem2603712 : term306 = term160.
Proof. exact (TRANS (@lem2603708) (@lem2603711)). Qed.
Lemma lem2603714 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2603715 : term144 = term145.
Proof. exact (@lem2603714 term64 term64). Qed.
Lemma lem2603716 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2603717 : term147 = term64.
Proof. exact (EQ_MP (@lem2603716) (@lem940073)). Qed.
Lemma lem2603718 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2603719 : term145 = term63.
Proof. exact (MK_COMB (@lem2603718) (@lem2603717)). Qed.
Lemma lem2603720 : term144 = term63.
Proof. exact (TRANS (@lem2603715) (@lem2603719)). Qed.
Lemma lem2603721 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem2603722 : term307 = term270.
Proof. exact (MK_COMB (@lem2603721) (@lem2603720)). Qed.
Lemma lem2603724 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2603725 : term270 = term160.
Proof. exact (@lem2603724 term64). Qed.
Lemma lem2603726 : term307 = term160.
Proof. exact (TRANS (@lem2603722) (@lem2603725)). Qed.
Lemma lem2603727 : term160 = term307.
Proof. exact (SYM (@lem2603726)). Qed.
Lemma lem2603728 : term306 = term307.
Proof. exact (TRANS (@lem2603712) (@lem2603727)). Qed.
Lemma lem2603729 : term296 = term259.
Proof. exact (@lem2603679 (@lem2603728)). Qed.
Lemma lem2603730 : term295 = term259.
Proof. exact (TRANS (@lem2603645) (@lem2603729)). Qed.
Lemma lem2603732 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2603733 : term259 = term160.
Proof. exact (@lem2603732 term160). Qed.
Lemma lem2603734 : term295 = term160.
Proof. exact (TRANS (@lem2603730) (@lem2603733)). Qed.
Lemma lem2603735 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2603736 : term308 = term305.
Proof. exact (MK_COMB (@lem2603735) (@lem2603734)). Qed.
Lemma lem2603737 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2603738 (m : int) : (term315 m) = (term316 m).
Proof. exact (MK_COMB (@lem2603736) (@lem2603737 m)). Qed.
Lemma lem2603739 (m : int) : (term314 m) = (term316 m).
Proof. exact (TRANS (@lem2603636 m) (@lem2603738 m)). Qed.
Lemma lem2603740 (m : int) : (term316 m) = term160.
Proof. exact (@lem1982719 (real_of_int m)). Qed.
Lemma lem2603741 (m : int) : (term314 m) = term160.
Proof. exact (TRANS (@lem2603739 m) (@lem2603740 m)). Qed.
Lemma lem2603742 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2603743 (m : int) : (term317 m) = term311.
Proof. exact (MK_COMB (@lem2603742) (@lem2603741 m)). Qed.
Lemma lem2603744 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem2603745 (m : int) : (term313 m) = term318.
Proof. exact (MK_COMB (@lem2603743 m) (@lem2603744)). Qed.
Lemma lem2603746 (m : int) : (term312 m) = term318.
Proof. exact (TRANS (@lem2603635 m) (@lem2603745 m)). Qed.
Lemma lem2603747 : term318 = term127.
Proof. exact (@lem1982721 term127). Qed.
Lemma lem2603748 (m : int) : (term312 m) = term127.
Proof. exact (TRANS (@lem2603746 m) (@lem2603747)). Qed.
Lemma lem2603749 (c : int) (n : int) (m : int) : (term290 c n m) = term318.
Proof. exact (MK_COMB (@lem2603634 c n) (@lem2603748 m)). Qed.
Lemma lem2603750 (c : int) (n : int) (m : int) : (term289 c n m) = term318.
Proof. exact (TRANS (@lem2603526 c n m) (@lem2603749 c n m)). Qed.
Lemma lem2603751 : term318 = term127.
Proof. exact (@lem1982721 term127). Qed.
Lemma lem2603752 (c : int) (n : int) (m : int) : (term289 c n m) = term127.
Proof. exact (TRANS (@lem2603750 c n m) (@lem2603751)). Qed.
Lemma lem2603753 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2603754 (c : int) (n : int) (m : int) : (term319 c n m) = term320.
Proof. exact (MK_COMB (@lem2603753) (@lem2603752 c n m)). Qed.
Lemma lem2603755 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2603756 (c : int) (n : int) (m : int) : (term288 c n m) = term321.
Proof. exact (MK_COMB (@lem2603754 c n m) (@lem2603755)). Qed.
Lemma lem2603757 (c : int) (n : int) (m : int) (h1 : term411 c n m) : term321.
Proof. exact (EQ_MP (@lem2603756 c n m) (@lem2603525 c n m h1)). Qed.
Lemma lem2603759 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2603760 : term321 = term322.
Proof. exact (@lem2603759 term160 term127). Qed.
Lemma lem2603762 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2603763 : term127 = term137.
Proof. exact (@lem2603762 term64). Qed.
Lemma lem2603765 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2603766 : term160 = term259.
Proof. exact (@lem2603765 (NUMERAL 0)). Qed.
Lemma lem2603767 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2603768 : term323 = term324.
Proof. exact (MK_COMB (@lem2603767) (@lem2603766)). Qed.
Lemma lem2603769 : term322 = term325.
Proof. exact (MK_COMB (@lem2603768) (@lem2603763)). Qed.
Lemma lem2603770 : term326.
Proof. exact (@lem1980026 term160 term63 term127 term63). Qed.
Lemma lem2603772 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603773 : term258 = term265.
Proof. exact (@lem2603772 (NUMERAL 0) term64). Qed.
Lemma lem2603774 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603775 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603776 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603775 h1) (fun h1 : term265 = True => @lem2603774)). Qed.
Lemma lem2603777 : term265 = True.
Proof. exact (EQ_MP (@lem2603776) (@lem2603774)). Qed.
Lemma lem2603778 : term258 = True.
Proof. exact (TRANS (@lem2603773) (@lem2603777)). Qed.
Lemma lem2603779 : True = term258.
Proof. exact (SYM (@lem2603778)). Qed.
Lemma lem2603780 : term258.
Proof. exact (EQ_MP (@lem2603779) (@lem0)). Qed.
Lemma lem2603781 : term327.
Proof. exact (@lem2603770 (@lem2603780)). Qed.
Lemma lem2603783 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603784 : term258 = term265.
Proof. exact (@lem2603783 (NUMERAL 0) term64). Qed.
Lemma lem2603785 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603786 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603787 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603786 h1) (fun h1 : term265 = True => @lem2603785)). Qed.
Lemma lem2603788 : term265 = True.
Proof. exact (EQ_MP (@lem2603787) (@lem2603785)). Qed.
Lemma lem2603789 : term258 = True.
Proof. exact (TRANS (@lem2603784) (@lem2603788)). Qed.
Lemma lem2603790 : True = term258.
Proof. exact (SYM (@lem2603789)). Qed.
Lemma lem2603791 : term258.
Proof. exact (EQ_MP (@lem2603790) (@lem0)). Qed.
Lemma lem2603792 : term325 = term328.
Proof. exact (@lem2603781 (@lem2603791)). Qed.
Lemma lem2603794 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2603795 : term172 = term177.
Proof. exact (@lem2603794 term64 term64). Qed.
Lemma lem2603796 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2603797 : term147 = term64.
Proof. exact (EQ_MP (@lem2603796) (@lem940073)). Qed.
Lemma lem2603798 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2603799 : term145 = term63.
Proof. exact (MK_COMB (@lem2603798) (@lem2603797)). Qed.
Lemma lem2603800 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2603801 : term177 = term127.
Proof. exact (MK_COMB (@lem2603800) (@lem2603799)). Qed.
Lemma lem2603802 : term172 = term127.
Proof. exact (TRANS (@lem2603795) (@lem2603801)). Qed.
Lemma lem2603804 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2603805 : term270 = term160.
Proof. exact (@lem2603804 term64). Qed.
Lemma lem2603806 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2603807 : term329 = term323.
Proof. exact (MK_COMB (@lem2603806) (@lem2603805)). Qed.
Lemma lem2603808 : term328 = term322.
Proof. exact (MK_COMB (@lem2603807) (@lem2603802)). Qed.
Lemma lem2603810 (m : nat) (n : nat) : (term330 m n) = (term331 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2603811 : term322 = term332.
Proof. exact (@lem2603810 (NUMERAL 0) term64). Qed.
Lemma lem2603812 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603813 (h1 : term266 = (BIT1 0)) : (term64 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2603814 : (term266 = (BIT1 0)) = ((term64 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603813 h1) (fun h1 : (term64 = (NUMERAL 0)) = False => @lem2603812)). Qed.
Lemma lem2603815 : (term64 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2603814) (@lem2603812)). Qed.
Lemma lem2603816 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2603817 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2603818 : term333 = (and True).
Proof. exact (MK_COMB (@lem2603817) (@lem2603816)). Qed.
Lemma lem2603819 : term332 = (True /\ False).
Proof. exact (MK_COMB (@lem2603818) (@lem2603815)). Qed.
Lemma lem2603821 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2603822 : term332 = False.
Proof. exact (TRANS (@lem2603819) (@lem2603821)). Qed.
Lemma lem2603823 : term322 = False.
Proof. exact (TRANS (@lem2603811) (@lem2603822)). Qed.
Lemma lem2603824 : term328 = False.
Proof. exact (TRANS (@lem2603808) (@lem2603823)). Qed.
Lemma lem2603825 : term325 = False.
Proof. exact (TRANS (@lem2603792) (@lem2603824)). Qed.
Lemma lem2603826 : term322 = False.
Proof. exact (TRANS (@lem2603769) (@lem2603825)). Qed.
Lemma lem2603827 : term321 = False.
Proof. exact (TRANS (@lem2603760) (@lem2603826)). Qed.
Lemma lem2603828 (c : int) (n : int) (m : int) (h1 : term411 c n m) : False.
Proof. exact (EQ_MP (@lem2603827) (@lem2603757 c n m h1)). Qed.
Lemma lem2603829 (c : int) (n : int) (m : int) (h1 : term419 c n m) : term419 c n m.
Proof. exact (h1). Qed.
Lemma lem2603830 (c : int) (n : int) (m : int) (h1 : term419 c n m) : term189 c n m.
Proof. exact (proj2 (@lem2603829 c n m h1)). Qed.
Lemma lem2603831 (c : int) (n : int) (m : int) (h1 : term419 c n m) : term225 c n m.
Proof. exact (proj1 (@lem2603829 c n m h1)). Qed.
Lemma lem2603833 (c : int) (n : int) (m : int) (h1 : term419 c n m) : term205 c n m.
Proof. exact (proj1 (@lem2603831 c n m h1)). Qed.
Lemma lem2603835 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2603836 : term257 = term258.
Proof. exact (@lem2603835 term160 term63). Qed.
Lemma lem2603838 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2603839 : term63 = term151.
Proof. exact (@lem2603838 term64). Qed.
Lemma lem2603841 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2603842 : term160 = term259.
Proof. exact (@lem2603841 (NUMERAL 0)). Qed.
Lemma lem2603843 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2603844 : term260 = term261.
Proof. exact (MK_COMB (@lem2603843) (@lem2603842)). Qed.
Lemma lem2603845 : term258 = term262.
Proof. exact (MK_COMB (@lem2603844) (@lem2603839)). Qed.
Lemma lem2603846 : term263.
Proof. exact (@lem1980255 term160 term63 term63 term63). Qed.
Lemma lem2603848 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603849 : term258 = term265.
Proof. exact (@lem2603848 (NUMERAL 0) term64). Qed.
Lemma lem2603850 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603851 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603852 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603851 h1) (fun h1 : term265 = True => @lem2603850)). Qed.
Lemma lem2603853 : term265 = True.
Proof. exact (EQ_MP (@lem2603852) (@lem2603850)). Qed.
Lemma lem2603854 : term258 = True.
Proof. exact (TRANS (@lem2603849) (@lem2603853)). Qed.
Lemma lem2603855 : True = term258.
Proof. exact (SYM (@lem2603854)). Qed.
Lemma lem2603856 : term258.
Proof. exact (EQ_MP (@lem2603855) (@lem0)). Qed.
Lemma lem2603857 : term267.
Proof. exact (@lem2603846 (@lem2603856)). Qed.
Lemma lem2603859 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603860 : term258 = term265.
Proof. exact (@lem2603859 (NUMERAL 0) term64). Qed.
Lemma lem2603861 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603862 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603863 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603862 h1) (fun h1 : term265 = True => @lem2603861)). Qed.
Lemma lem2603864 : term265 = True.
Proof. exact (EQ_MP (@lem2603863) (@lem2603861)). Qed.
Lemma lem2603865 : term258 = True.
Proof. exact (TRANS (@lem2603860) (@lem2603864)). Qed.
Lemma lem2603866 : True = term258.
Proof. exact (SYM (@lem2603865)). Qed.
Lemma lem2603867 : term258.
Proof. exact (EQ_MP (@lem2603866) (@lem0)). Qed.
Lemma lem2603868 : term262 = term268.
Proof. exact (@lem2603857 (@lem2603867)). Qed.
Lemma lem2603870 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2603871 : term144 = term145.
Proof. exact (@lem2603870 term64 term64). Qed.
Lemma lem2603872 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2603873 : term147 = term64.
Proof. exact (EQ_MP (@lem2603872) (@lem940073)). Qed.
Lemma lem2603874 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2603875 : term145 = term63.
Proof. exact (MK_COMB (@lem2603874) (@lem2603873)). Qed.
Lemma lem2603876 : term144 = term63.
Proof. exact (TRANS (@lem2603871) (@lem2603875)). Qed.
Lemma lem2603878 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2603879 : term270 = term160.
Proof. exact (@lem2603878 term64). Qed.
Lemma lem2603880 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2603881 : term271 = term260.
Proof. exact (MK_COMB (@lem2603880) (@lem2603879)). Qed.
Lemma lem2603882 : term268 = term258.
Proof. exact (MK_COMB (@lem2603881) (@lem2603876)). Qed.
Lemma lem2603884 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603885 : term258 = term265.
Proof. exact (@lem2603884 (NUMERAL 0) term64). Qed.
Lemma lem2603886 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603887 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603888 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603887 h1) (fun h1 : term265 = True => @lem2603886)). Qed.
Lemma lem2603889 : term265 = True.
Proof. exact (EQ_MP (@lem2603888) (@lem2603886)). Qed.
Lemma lem2603890 : term258 = True.
Proof. exact (TRANS (@lem2603885) (@lem2603889)). Qed.
Lemma lem2603891 : term268 = True.
Proof. exact (TRANS (@lem2603882) (@lem2603890)). Qed.
Lemma lem2603892 : term262 = True.
Proof. exact (TRANS (@lem2603868) (@lem2603891)). Qed.
Lemma lem2603893 : term258 = True.
Proof. exact (TRANS (@lem2603845) (@lem2603892)). Qed.
Lemma lem2603894 : term257 = True.
Proof. exact (TRANS (@lem2603836) (@lem2603893)). Qed.
Lemma lem2603895 : True = term257.
Proof. exact (SYM (@lem2603894)). Qed.
Lemma lem2603896 : term257.
Proof. exact (EQ_MP (@lem2603895) (@lem0)). Qed.
Lemma lem2603897 (c : int) (n : int) (m : int) (h1 : term419 c n m) : term272 c n m.
Proof. exact (conj (@lem2603896) (@lem2603830 c n m h1)). Qed.
Lemma lem2603899 (x : real) (y : real) : term273 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2603900 (c : int) (n : int) (m : int) : term274 c n m.
Proof. exact (@lem2603899 term63 (term186 c n m)). Qed.
Lemma lem2603901 (c : int) (n : int) (m : int) (h1 : term419 c n m) : term275 c n m.
Proof. exact (@lem2603900 c n m (@lem2603897 c n m h1)). Qed.
Lemma lem2603902 (c : int) (n : int) (m : int) : (term276 c n m) = (term186 c n m).
Proof. exact (@lem1982733 (term186 c n m)). Qed.
Lemma lem2603903 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2603904 (c : int) (n : int) (m : int) : (term277 c n m) = (term188 c n m).
Proof. exact (MK_COMB (@lem2603903) (@lem2603902 c n m)). Qed.
Lemma lem2603905 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2603906 (c : int) (n : int) (m : int) : (term275 c n m) = (term189 c n m).
Proof. exact (MK_COMB (@lem2603904 c n m) (@lem2603905)). Qed.
Lemma lem2603907 (c : int) (n : int) (m : int) (h1 : term419 c n m) : term189 c n m.
Proof. exact (EQ_MP (@lem2603906 c n m) (@lem2603901 c n m h1)). Qed.
Lemma lem2603909 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2603910 : term257 = term258.
Proof. exact (@lem2603909 term160 term63). Qed.
Lemma lem2603912 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2603913 : term63 = term151.
Proof. exact (@lem2603912 term64). Qed.
Lemma lem2603915 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2603916 : term160 = term259.
Proof. exact (@lem2603915 (NUMERAL 0)). Qed.
Lemma lem2603917 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2603918 : term260 = term261.
Proof. exact (MK_COMB (@lem2603917) (@lem2603916)). Qed.
Lemma lem2603919 : term258 = term262.
Proof. exact (MK_COMB (@lem2603918) (@lem2603913)). Qed.
Lemma lem2603920 : term263.
Proof. exact (@lem1980255 term160 term63 term63 term63). Qed.
Lemma lem2603922 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603923 : term258 = term265.
Proof. exact (@lem2603922 (NUMERAL 0) term64). Qed.
Lemma lem2603924 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603925 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603926 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603925 h1) (fun h1 : term265 = True => @lem2603924)). Qed.
Lemma lem2603927 : term265 = True.
Proof. exact (EQ_MP (@lem2603926) (@lem2603924)). Qed.
Lemma lem2603928 : term258 = True.
Proof. exact (TRANS (@lem2603923) (@lem2603927)). Qed.
Lemma lem2603929 : True = term258.
Proof. exact (SYM (@lem2603928)). Qed.
Lemma lem2603930 : term258.
Proof. exact (EQ_MP (@lem2603929) (@lem0)). Qed.
Lemma lem2603931 : term267.
Proof. exact (@lem2603920 (@lem2603930)). Qed.
Lemma lem2603933 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603934 : term258 = term265.
Proof. exact (@lem2603933 (NUMERAL 0) term64). Qed.
Lemma lem2603935 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603936 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603937 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603936 h1) (fun h1 : term265 = True => @lem2603935)). Qed.
Lemma lem2603938 : term265 = True.
Proof. exact (EQ_MP (@lem2603937) (@lem2603935)). Qed.
Lemma lem2603939 : term258 = True.
Proof. exact (TRANS (@lem2603934) (@lem2603938)). Qed.
Lemma lem2603940 : True = term258.
Proof. exact (SYM (@lem2603939)). Qed.
Lemma lem2603941 : term258.
Proof. exact (EQ_MP (@lem2603940) (@lem0)). Qed.
Lemma lem2603942 : term262 = term268.
Proof. exact (@lem2603931 (@lem2603941)). Qed.
Lemma lem2603944 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2603945 : term144 = term145.
Proof. exact (@lem2603944 term64 term64). Qed.
Lemma lem2603946 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2603947 : term147 = term64.
Proof. exact (EQ_MP (@lem2603946) (@lem940073)). Qed.
Lemma lem2603948 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2603949 : term145 = term63.
Proof. exact (MK_COMB (@lem2603948) (@lem2603947)). Qed.
Lemma lem2603950 : term144 = term63.
Proof. exact (TRANS (@lem2603945) (@lem2603949)). Qed.
Lemma lem2603952 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2603953 : term270 = term160.
Proof. exact (@lem2603952 term64). Qed.
Lemma lem2603954 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2603955 : term271 = term260.
Proof. exact (MK_COMB (@lem2603954) (@lem2603953)). Qed.
Lemma lem2603956 : term268 = term258.
Proof. exact (MK_COMB (@lem2603955) (@lem2603950)). Qed.
Lemma lem2603958 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2603959 : term258 = term265.
Proof. exact (@lem2603958 (NUMERAL 0) term64). Qed.
Lemma lem2603960 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2603961 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2603962 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2603961 h1) (fun h1 : term265 = True => @lem2603960)). Qed.
Lemma lem2603963 : term265 = True.
Proof. exact (EQ_MP (@lem2603962) (@lem2603960)). Qed.
Lemma lem2603964 : term258 = True.
Proof. exact (TRANS (@lem2603959) (@lem2603963)). Qed.
Lemma lem2603965 : term268 = True.
Proof. exact (TRANS (@lem2603956) (@lem2603964)). Qed.
Lemma lem2603966 : term262 = True.
Proof. exact (TRANS (@lem2603942) (@lem2603965)). Qed.
Lemma lem2603967 : term258 = True.
Proof. exact (TRANS (@lem2603919) (@lem2603966)). Qed.
Lemma lem2603968 : term257 = True.
Proof. exact (TRANS (@lem2603910) (@lem2603967)). Qed.
Lemma lem2603969 : True = term257.
Proof. exact (SYM (@lem2603968)). Qed.
Lemma lem2603970 : term257.
Proof. exact (EQ_MP (@lem2603969) (@lem0)). Qed.
Lemma lem2603971 (c : int) (n : int) (m : int) (h1 : term419 c n m) : term335 c n m.
Proof. exact (conj (@lem2603970) (@lem2603833 c n m h1)). Qed.
Lemma lem2603973 (x : real) (y : real) : term273 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2603974 (c : int) (n : int) (m : int) : term336 c n m.
Proof. exact (@lem2603973 term63 (term202 c n m)). Qed.
Lemma lem2603975 (c : int) (n : int) (m : int) (h1 : term419 c n m) : term337 c n m.
Proof. exact (@lem2603974 c n m (@lem2603971 c n m h1)). Qed.
Lemma lem2603976 (c : int) (n : int) (m : int) : (term338 c n m) = (term202 c n m).
Proof. exact (@lem1982733 (term202 c n m)). Qed.
Lemma lem2603977 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2603978 (c : int) (n : int) (m : int) : (term339 c n m) = (term204 c n m).
Proof. exact (MK_COMB (@lem2603977) (@lem2603976 c n m)). Qed.
Lemma lem2603979 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2603980 (c : int) (n : int) (m : int) : (term337 c n m) = (term205 c n m).
Proof. exact (MK_COMB (@lem2603978 c n m) (@lem2603979)). Qed.
Lemma lem2603981 (c : int) (n : int) (m : int) (h1 : term419 c n m) : term205 c n m.
Proof. exact (EQ_MP (@lem2603980 c n m) (@lem2603975 c n m h1)). Qed.
Lemma lem2603982 (c : int) (n : int) (m : int) (h1 : term419 c n m) : term225 c n m.
Proof. exact (conj (@lem2603981 c n m h1) (@lem2603907 c n m h1)). Qed.
Lemma lem2603984 (x : real) (y : real) : term361 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2603985 (c : int) (n : int) (m : int) : term369 c n m.
Proof. exact (@lem2603984 (term202 c n m) (term186 c n m)). Qed.
Lemma lem2603986 (c : int) (n : int) (m : int) (h1 : term419 c n m) : term370 c n m.
Proof. exact (@lem2603985 c n m (@lem2603982 c n m h1)). Qed.
Lemma lem2603987 (c : int) (n : int) (m : int) : (term371 c n m) = (term372 c n m).
Proof. exact (@lem1982753 (term126 c n) (term40 c n) (term200 m) (term184 m)). Qed.
Lemma lem2603988 (c : int) (n : int) : (term291 c n) = (term292 c n).
Proof. exact (@lem1982713 term127 (term40 c n)). Qed.
Lemma lem2603990 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2603991 : term63 = term151.
Proof. exact (@lem2603990 term64). Qed.
Lemma lem2603993 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2603994 : term127 = term137.
Proof. exact (@lem2603993 term64). Qed.
Lemma lem2603995 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2603996 : term293 = term294.
Proof. exact (MK_COMB (@lem2603995) (@lem2603994)). Qed.
Lemma lem2603997 : term295 = term296.
Proof. exact (MK_COMB (@lem2603996) (@lem2603991)). Qed.
Lemma lem2603998 : term297.
Proof. exact (@lem1981473 term127 term63 term63 term63 term160 term63). Qed.
Lemma lem2604000 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2604001 : term258 = term265.
Proof. exact (@lem2604000 (NUMERAL 0) term64). Qed.
Lemma lem2604002 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2604003 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2604004 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2604003 h1) (fun h1 : term265 = True => @lem2604002)). Qed.
Lemma lem2604005 : term265 = True.
Proof. exact (EQ_MP (@lem2604004) (@lem2604002)). Qed.
Lemma lem2604006 : term258 = True.
Proof. exact (TRANS (@lem2604001) (@lem2604005)). Qed.
Lemma lem2604007 : True = term258.
Proof. exact (SYM (@lem2604006)). Qed.
Lemma lem2604008 : term258.
Proof. exact (EQ_MP (@lem2604007) (@lem0)). Qed.
Lemma lem2604009 : term298.
Proof. exact (@lem2603998 (@lem2604008)). Qed.
Lemma lem2604011 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2604012 : term258 = term265.
Proof. exact (@lem2604011 (NUMERAL 0) term64). Qed.
Lemma lem2604013 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2604014 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2604015 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2604014 h1) (fun h1 : term265 = True => @lem2604013)). Qed.
Lemma lem2604016 : term265 = True.
Proof. exact (EQ_MP (@lem2604015) (@lem2604013)). Qed.
Lemma lem2604017 : term258 = True.
Proof. exact (TRANS (@lem2604012) (@lem2604016)). Qed.
Lemma lem2604018 : True = term258.
Proof. exact (SYM (@lem2604017)). Qed.
Lemma lem2604019 : term258.
Proof. exact (EQ_MP (@lem2604018) (@lem0)). Qed.
Lemma lem2604020 : term299.
Proof. exact (@lem2604009 (@lem2604019)). Qed.
Lemma lem2604022 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2604023 : term258 = term265.
Proof. exact (@lem2604022 (NUMERAL 0) term64). Qed.
Lemma lem2604024 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2604025 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2604026 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2604025 h1) (fun h1 : term265 = True => @lem2604024)). Qed.
Lemma lem2604027 : term265 = True.
Proof. exact (EQ_MP (@lem2604026) (@lem2604024)). Qed.
Lemma lem2604028 : term258 = True.
Proof. exact (TRANS (@lem2604023) (@lem2604027)). Qed.
Lemma lem2604029 : True = term258.
Proof. exact (SYM (@lem2604028)). Qed.
Lemma lem2604030 : term258.
Proof. exact (EQ_MP (@lem2604029) (@lem0)). Qed.
Lemma lem2604031 : term300.
Proof. exact (@lem2604020 (@lem2604030)). Qed.
Lemma lem2604033 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2604034 : term144 = term145.
Proof. exact (@lem2604033 term64 term64). Qed.
Lemma lem2604035 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2604036 : term147 = term64.
Proof. exact (EQ_MP (@lem2604035) (@lem940073)). Qed.
Lemma lem2604037 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2604038 : term145 = term63.
Proof. exact (MK_COMB (@lem2604037) (@lem2604036)). Qed.
Lemma lem2604039 : term144 = term63.
Proof. exact (TRANS (@lem2604034) (@lem2604038)). Qed.
Lemma lem2604041 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2604042 : term172 = term177.
Proof. exact (@lem2604041 term64 term64). Qed.
Lemma lem2604043 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2604044 : term147 = term64.
Proof. exact (EQ_MP (@lem2604043) (@lem940073)). Qed.
Lemma lem2604045 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2604046 : term145 = term63.
Proof. exact (MK_COMB (@lem2604045) (@lem2604044)). Qed.
Lemma lem2604047 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2604048 : term177 = term127.
Proof. exact (MK_COMB (@lem2604047) (@lem2604046)). Qed.
Lemma lem2604049 : term172 = term127.
Proof. exact (TRANS (@lem2604042) (@lem2604048)). Qed.
Lemma lem2604050 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2604051 : term301 = term293.
Proof. exact (MK_COMB (@lem2604050) (@lem2604049)). Qed.
Lemma lem2604052 : term302 = term295.
Proof. exact (MK_COMB (@lem2604051) (@lem2604039)). Qed.
Lemma lem2604054 (m : nat) : (term303 m) = term160.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2604055 : term295 = term160.
Proof. exact (@lem2604054 term64). Qed.
Lemma lem2604056 : term302 = term160.
Proof. exact (TRANS (@lem2604052) (@lem2604055)). Qed.
Lemma lem2604057 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2604058 : term304 = term305.
Proof. exact (MK_COMB (@lem2604057) (@lem2604056)). Qed.
Lemma lem2604059 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2604060 : term306 = term270.
Proof. exact (MK_COMB (@lem2604058) (@lem2604059)). Qed.
Lemma lem2604062 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2604063 : term270 = term160.
Proof. exact (@lem2604062 term64). Qed.
Lemma lem2604064 : term306 = term160.
Proof. exact (TRANS (@lem2604060) (@lem2604063)). Qed.
Lemma lem2604066 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2604067 : term144 = term145.
Proof. exact (@lem2604066 term64 term64). Qed.
Lemma lem2604068 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2604069 : term147 = term64.
Proof. exact (EQ_MP (@lem2604068) (@lem940073)). Qed.
Lemma lem2604070 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2604071 : term145 = term63.
Proof. exact (MK_COMB (@lem2604070) (@lem2604069)). Qed.
Lemma lem2604072 : term144 = term63.
Proof. exact (TRANS (@lem2604067) (@lem2604071)). Qed.
Lemma lem2604073 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem2604074 : term307 = term270.
Proof. exact (MK_COMB (@lem2604073) (@lem2604072)). Qed.
Lemma lem2604076 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2604077 : term270 = term160.
Proof. exact (@lem2604076 term64). Qed.
Lemma lem2604078 : term307 = term160.
Proof. exact (TRANS (@lem2604074) (@lem2604077)). Qed.
Lemma lem2604079 : term160 = term307.
Proof. exact (SYM (@lem2604078)). Qed.
Lemma lem2604080 : term306 = term307.
Proof. exact (TRANS (@lem2604064) (@lem2604079)). Qed.
Lemma lem2604081 : term296 = term259.
Proof. exact (@lem2604031 (@lem2604080)). Qed.
Lemma lem2604082 : term295 = term259.
Proof. exact (TRANS (@lem2603997) (@lem2604081)). Qed.
Lemma lem2604084 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2604085 : term259 = term160.
Proof. exact (@lem2604084 term160). Qed.
Lemma lem2604086 : term295 = term160.
Proof. exact (TRANS (@lem2604082) (@lem2604085)). Qed.
Lemma lem2604087 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2604088 : term308 = term305.
Proof. exact (MK_COMB (@lem2604087) (@lem2604086)). Qed.
Lemma lem2604089 (c : int) (n : int) : (term40 c n) = (term40 c n).
Proof. exact (eq_refl (term40 c n)). Qed.
Lemma lem2604090 (c : int) (n : int) : (term292 c n) = (term309 c n).
Proof. exact (MK_COMB (@lem2604088) (@lem2604089 c n)). Qed.
Lemma lem2604091 (c : int) (n : int) : (term291 c n) = (term309 c n).
Proof. exact (TRANS (@lem2603988 c n) (@lem2604090 c n)). Qed.
Lemma lem2604092 (c : int) (n : int) : (term309 c n) = term160.
Proof. exact (@lem1982719 (term40 c n)). Qed.
Lemma lem2604093 (c : int) (n : int) : (term291 c n) = term160.
Proof. exact (TRANS (@lem2604091 c n) (@lem2604092 c n)). Qed.
Lemma lem2604094 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2604095 (c : int) (n : int) : (term310 c n) = term311.
Proof. exact (MK_COMB (@lem2604094) (@lem2604093 c n)). Qed.
Lemma lem2604096 (m : int) : (term373 m) = (term374 m).
Proof. exact (@lem1982753 (term124 m) (real_of_int m) term127 term127). Qed.
Lemma lem2604097 (m : int) : (term314 m) = (term315 m).
Proof. exact (@lem1982713 term127 (real_of_int m)). Qed.
Lemma lem2604099 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2604100 : term63 = term151.
Proof. exact (@lem2604099 term64). Qed.
Lemma lem2604102 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2604103 : term127 = term137.
Proof. exact (@lem2604102 term64). Qed.
Lemma lem2604104 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2604105 : term293 = term294.
Proof. exact (MK_COMB (@lem2604104) (@lem2604103)). Qed.
Lemma lem2604106 : term295 = term296.
Proof. exact (MK_COMB (@lem2604105) (@lem2604100)). Qed.
Lemma lem2604107 : term297.
Proof. exact (@lem1981473 term127 term63 term63 term63 term160 term63). Qed.
Lemma lem2604109 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2604110 : term258 = term265.
Proof. exact (@lem2604109 (NUMERAL 0) term64). Qed.
Lemma lem2604111 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2604112 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2604113 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2604112 h1) (fun h1 : term265 = True => @lem2604111)). Qed.
Lemma lem2604114 : term265 = True.
Proof. exact (EQ_MP (@lem2604113) (@lem2604111)). Qed.
Lemma lem2604115 : term258 = True.
Proof. exact (TRANS (@lem2604110) (@lem2604114)). Qed.
Lemma lem2604116 : True = term258.
Proof. exact (SYM (@lem2604115)). Qed.
Lemma lem2604117 : term258.
Proof. exact (EQ_MP (@lem2604116) (@lem0)). Qed.
Lemma lem2604118 : term298.
Proof. exact (@lem2604107 (@lem2604117)). Qed.
Lemma lem2604120 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2604121 : term258 = term265.
Proof. exact (@lem2604120 (NUMERAL 0) term64). Qed.
Lemma lem2604122 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2604123 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2604124 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2604123 h1) (fun h1 : term265 = True => @lem2604122)). Qed.
Lemma lem2604125 : term265 = True.
Proof. exact (EQ_MP (@lem2604124) (@lem2604122)). Qed.
Lemma lem2604126 : term258 = True.
Proof. exact (TRANS (@lem2604121) (@lem2604125)). Qed.
Lemma lem2604127 : True = term258.
Proof. exact (SYM (@lem2604126)). Qed.
Lemma lem2604128 : term258.
Proof. exact (EQ_MP (@lem2604127) (@lem0)). Qed.
Lemma lem2604129 : term299.
Proof. exact (@lem2604118 (@lem2604128)). Qed.
Lemma lem2604131 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2604132 : term258 = term265.
Proof. exact (@lem2604131 (NUMERAL 0) term64). Qed.
Lemma lem2604133 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2604134 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2604135 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2604134 h1) (fun h1 : term265 = True => @lem2604133)). Qed.
Lemma lem2604136 : term265 = True.
Proof. exact (EQ_MP (@lem2604135) (@lem2604133)). Qed.
Lemma lem2604137 : term258 = True.
Proof. exact (TRANS (@lem2604132) (@lem2604136)). Qed.
Lemma lem2604138 : True = term258.
Proof. exact (SYM (@lem2604137)). Qed.
Lemma lem2604139 : term258.
Proof. exact (EQ_MP (@lem2604138) (@lem0)). Qed.
Lemma lem2604140 : term300.
Proof. exact (@lem2604129 (@lem2604139)). Qed.
Lemma lem2604142 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2604143 : term144 = term145.
Proof. exact (@lem2604142 term64 term64). Qed.
Lemma lem2604144 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2604145 : term147 = term64.
Proof. exact (EQ_MP (@lem2604144) (@lem940073)). Qed.
Lemma lem2604146 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2604147 : term145 = term63.
Proof. exact (MK_COMB (@lem2604146) (@lem2604145)). Qed.
Lemma lem2604148 : term144 = term63.
Proof. exact (TRANS (@lem2604143) (@lem2604147)). Qed.
Lemma lem2604150 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2604151 : term172 = term177.
Proof. exact (@lem2604150 term64 term64). Qed.
Lemma lem2604152 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2604153 : term147 = term64.
Proof. exact (EQ_MP (@lem2604152) (@lem940073)). Qed.
Lemma lem2604154 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2604155 : term145 = term63.
Proof. exact (MK_COMB (@lem2604154) (@lem2604153)). Qed.
Lemma lem2604156 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2604157 : term177 = term127.
Proof. exact (MK_COMB (@lem2604156) (@lem2604155)). Qed.
Lemma lem2604158 : term172 = term127.
Proof. exact (TRANS (@lem2604151) (@lem2604157)). Qed.
Lemma lem2604159 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2604160 : term301 = term293.
Proof. exact (MK_COMB (@lem2604159) (@lem2604158)). Qed.
Lemma lem2604161 : term302 = term295.
Proof. exact (MK_COMB (@lem2604160) (@lem2604148)). Qed.
Lemma lem2604163 (m : nat) : (term303 m) = term160.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2604164 : term295 = term160.
Proof. exact (@lem2604163 term64). Qed.
Lemma lem2604165 : term302 = term160.
Proof. exact (TRANS (@lem2604161) (@lem2604164)). Qed.
Lemma lem2604166 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2604167 : term304 = term305.
Proof. exact (MK_COMB (@lem2604166) (@lem2604165)). Qed.
Lemma lem2604168 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2604169 : term306 = term270.
Proof. exact (MK_COMB (@lem2604167) (@lem2604168)). Qed.
Lemma lem2604171 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2604172 : term270 = term160.
Proof. exact (@lem2604171 term64). Qed.
Lemma lem2604173 : term306 = term160.
Proof. exact (TRANS (@lem2604169) (@lem2604172)). Qed.
Lemma lem2604175 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2604176 : term144 = term145.
Proof. exact (@lem2604175 term64 term64). Qed.
Lemma lem2604177 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2604178 : term147 = term64.
Proof. exact (EQ_MP (@lem2604177) (@lem940073)). Qed.
Lemma lem2604179 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2604180 : term145 = term63.
Proof. exact (MK_COMB (@lem2604179) (@lem2604178)). Qed.
Lemma lem2604181 : term144 = term63.
Proof. exact (TRANS (@lem2604176) (@lem2604180)). Qed.
Lemma lem2604182 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem2604183 : term307 = term270.
Proof. exact (MK_COMB (@lem2604182) (@lem2604181)). Qed.
Lemma lem2604185 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2604186 : term270 = term160.
Proof. exact (@lem2604185 term64). Qed.
Lemma lem2604187 : term307 = term160.
Proof. exact (TRANS (@lem2604183) (@lem2604186)). Qed.
Lemma lem2604188 : term160 = term307.
Proof. exact (SYM (@lem2604187)). Qed.
Lemma lem2604189 : term306 = term307.
Proof. exact (TRANS (@lem2604173) (@lem2604188)). Qed.
Lemma lem2604190 : term296 = term259.
Proof. exact (@lem2604140 (@lem2604189)). Qed.
Lemma lem2604191 : term295 = term259.
Proof. exact (TRANS (@lem2604106) (@lem2604190)). Qed.
Lemma lem2604193 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2604194 : term259 = term160.
Proof. exact (@lem2604193 term160). Qed.
Lemma lem2604195 : term295 = term160.
Proof. exact (TRANS (@lem2604191) (@lem2604194)). Qed.
Lemma lem2604196 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2604197 : term308 = term305.
Proof. exact (MK_COMB (@lem2604196) (@lem2604195)). Qed.
Lemma lem2604198 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2604199 (m : int) : (term315 m) = (term316 m).
Proof. exact (MK_COMB (@lem2604197) (@lem2604198 m)). Qed.
Lemma lem2604200 (m : int) : (term314 m) = (term316 m).
Proof. exact (TRANS (@lem2604097 m) (@lem2604199 m)). Qed.
Lemma lem2604201 (m : int) : (term316 m) = term160.
Proof. exact (@lem1982719 (real_of_int m)). Qed.
Lemma lem2604202 (m : int) : (term314 m) = term160.
Proof. exact (TRANS (@lem2604200 m) (@lem2604201 m)). Qed.
Lemma lem2604203 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2604204 (m : int) : (term317 m) = term311.
Proof. exact (MK_COMB (@lem2604203) (@lem2604202 m)). Qed.
Lemma lem2604206 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2604207 : term127 = term137.
Proof. exact (@lem2604206 term64). Qed.
Lemma lem2604209 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2604210 : term127 = term137.
Proof. exact (@lem2604209 term64). Qed.
Lemma lem2604211 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2604212 : term293 = term294.
Proof. exact (MK_COMB (@lem2604211) (@lem2604210)). Qed.
Lemma lem2604213 : term375 = term376.
Proof. exact (MK_COMB (@lem2604212) (@lem2604207)). Qed.
Lemma lem2604214 : term377.
Proof. exact (@lem1981473 term127 term63 term127 term63 term378 term63). Qed.
Lemma lem2604216 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2604217 : term258 = term265.
Proof. exact (@lem2604216 (NUMERAL 0) term64). Qed.
Lemma lem2604218 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2604219 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2604220 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2604219 h1) (fun h1 : term265 = True => @lem2604218)). Qed.
Lemma lem2604221 : term265 = True.
Proof. exact (EQ_MP (@lem2604220) (@lem2604218)). Qed.
Lemma lem2604222 : term258 = True.
Proof. exact (TRANS (@lem2604217) (@lem2604221)). Qed.
Lemma lem2604223 : True = term258.
Proof. exact (SYM (@lem2604222)). Qed.
Lemma lem2604224 : term258.
Proof. exact (EQ_MP (@lem2604223) (@lem0)). Qed.
Lemma lem2604225 : term379.
Proof. exact (@lem2604214 (@lem2604224)). Qed.
Lemma lem2604227 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2604228 : term258 = term265.
Proof. exact (@lem2604227 (NUMERAL 0) term64). Qed.
Lemma lem2604229 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2604230 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2604231 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2604230 h1) (fun h1 : term265 = True => @lem2604229)). Qed.
Lemma lem2604232 : term265 = True.
Proof. exact (EQ_MP (@lem2604231) (@lem2604229)). Qed.
Lemma lem2604233 : term258 = True.
Proof. exact (TRANS (@lem2604228) (@lem2604232)). Qed.
Lemma lem2604234 : True = term258.
Proof. exact (SYM (@lem2604233)). Qed.
Lemma lem2604235 : term258.
Proof. exact (EQ_MP (@lem2604234) (@lem0)). Qed.
Lemma lem2604236 : term380.
Proof. exact (@lem2604225 (@lem2604235)). Qed.
Lemma lem2604238 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2604239 : term258 = term265.
Proof. exact (@lem2604238 (NUMERAL 0) term64). Qed.
Lemma lem2604240 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2604241 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2604242 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2604241 h1) (fun h1 : term265 = True => @lem2604240)). Qed.
Lemma lem2604243 : term265 = True.
Proof. exact (EQ_MP (@lem2604242) (@lem2604240)). Qed.
Lemma lem2604244 : term258 = True.
Proof. exact (TRANS (@lem2604239) (@lem2604243)). Qed.
Lemma lem2604245 : True = term258.
Proof. exact (SYM (@lem2604244)). Qed.
Lemma lem2604246 : term258.
Proof. exact (EQ_MP (@lem2604245) (@lem0)). Qed.
Lemma lem2604247 : term381.
Proof. exact (@lem2604236 (@lem2604246)). Qed.
Lemma lem2604249 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2604250 : term172 = term177.
Proof. exact (@lem2604249 term64 term64). Qed.
Lemma lem2604251 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2604252 : term147 = term64.
Proof. exact (EQ_MP (@lem2604251) (@lem940073)). Qed.
Lemma lem2604253 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2604254 : term145 = term63.
Proof. exact (MK_COMB (@lem2604253) (@lem2604252)). Qed.
Lemma lem2604255 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2604256 : term177 = term127.
Proof. exact (MK_COMB (@lem2604255) (@lem2604254)). Qed.
Lemma lem2604257 : term172 = term127.
Proof. exact (TRANS (@lem2604250) (@lem2604256)). Qed.
Lemma lem2604259 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2604260 : term172 = term177.
Proof. exact (@lem2604259 term64 term64). Qed.
Lemma lem2604261 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2604262 : term147 = term64.
Proof. exact (EQ_MP (@lem2604261) (@lem940073)). Qed.
Lemma lem2604263 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2604264 : term145 = term63.
Proof. exact (MK_COMB (@lem2604263) (@lem2604262)). Qed.
Lemma lem2604265 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2604266 : term177 = term127.
Proof. exact (MK_COMB (@lem2604265) (@lem2604264)). Qed.
Lemma lem2604267 : term172 = term127.
Proof. exact (TRANS (@lem2604260) (@lem2604266)). Qed.
Lemma lem2604268 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2604269 : term301 = term293.
Proof. exact (MK_COMB (@lem2604268) (@lem2604267)). Qed.
Lemma lem2604270 : term382 = term375.
Proof. exact (MK_COMB (@lem2604269) (@lem2604257)). Qed.
Lemma lem2604271 : term375 = term383.
Proof. exact (@lem1367763 term64 term64). Qed.
Lemma lem2604272 : term384 = term385.
Proof. exact (@lem706885). Qed.
Lemma lem2604273 : (term384 = term385) = (term386 = term387).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term385). Qed.
Lemma lem2604274 : term386 = term387.
Proof. exact (EQ_MP (@lem2604273) (@lem2604272)). Qed.
Lemma lem2604275 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2604276 : term388 = term389.
Proof. exact (MK_COMB (@lem2604275) (@lem2604274)). Qed.
Lemma lem2604277 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2604278 : term383 = term378.
Proof. exact (MK_COMB (@lem2604277) (@lem2604276)). Qed.
Lemma lem2604279 : term375 = term378.
Proof. exact (TRANS (@lem2604271) (@lem2604278)). Qed.
Lemma lem2604280 : term382 = term378.
Proof. exact (TRANS (@lem2604270) (@lem2604279)). Qed.
Lemma lem2604281 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2604282 : term390 = term391.
Proof. exact (MK_COMB (@lem2604281) (@lem2604280)). Qed.
Lemma lem2604283 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2604284 : term392 = term393.
Proof. exact (MK_COMB (@lem2604282) (@lem2604283)). Qed.
Lemma lem2604286 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2604287 : term393 = term394.
Proof. exact (@lem2604286 term387 term64). Qed.
Lemma lem2604288 : term395 = term385.
Proof. exact (@lem996237 term385). Qed.
Lemma lem2604289 : (term395 = term385) = (term396 = term387).
Proof. exact (@lem1007663 term385 (BIT1 0) term385). Qed.
Lemma lem2604290 : term396 = term387.
Proof. exact (EQ_MP (@lem2604289) (@lem2604288)). Qed.
Lemma lem2604291 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2604292 : term397 = term389.
Proof. exact (MK_COMB (@lem2604291) (@lem2604290)). Qed.
Lemma lem2604293 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2604294 : term394 = term378.
Proof. exact (MK_COMB (@lem2604293) (@lem2604292)). Qed.
Lemma lem2604295 : term393 = term378.
Proof. exact (TRANS (@lem2604287) (@lem2604294)). Qed.
Lemma lem2604296 : term392 = term378.
Proof. exact (TRANS (@lem2604284) (@lem2604295)). Qed.
Lemma lem2604298 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2604299 : term144 = term145.
Proof. exact (@lem2604298 term64 term64). Qed.
Lemma lem2604300 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2604301 : term147 = term64.
Proof. exact (EQ_MP (@lem2604300) (@lem940073)). Qed.
Lemma lem2604302 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2604303 : term145 = term63.
Proof. exact (MK_COMB (@lem2604302) (@lem2604301)). Qed.
Lemma lem2604304 : term144 = term63.
Proof. exact (TRANS (@lem2604299) (@lem2604303)). Qed.
Lemma lem2604305 : term391 = term391.
Proof. exact (eq_refl term391). Qed.
Lemma lem2604306 : term398 = term393.
Proof. exact (MK_COMB (@lem2604305) (@lem2604304)). Qed.
Lemma lem2604308 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2604309 : term393 = term394.
Proof. exact (@lem2604308 term387 term64). Qed.
Lemma lem2604310 : term395 = term385.
Proof. exact (@lem996237 term385). Qed.
Lemma lem2604311 : (term395 = term385) = (term396 = term387).
Proof. exact (@lem1007663 term385 (BIT1 0) term385). Qed.
Lemma lem2604312 : term396 = term387.
Proof. exact (EQ_MP (@lem2604311) (@lem2604310)). Qed.
Lemma lem2604313 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2604314 : term397 = term389.
Proof. exact (MK_COMB (@lem2604313) (@lem2604312)). Qed.
Lemma lem2604315 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2604316 : term394 = term378.
Proof. exact (MK_COMB (@lem2604315) (@lem2604314)). Qed.
Lemma lem2604317 : term393 = term378.
Proof. exact (TRANS (@lem2604309) (@lem2604316)). Qed.
Lemma lem2604318 : term398 = term378.
Proof. exact (TRANS (@lem2604306) (@lem2604317)). Qed.
Lemma lem2604319 : term378 = term398.
Proof. exact (SYM (@lem2604318)). Qed.
Lemma lem2604320 : term392 = term398.
Proof. exact (TRANS (@lem2604296) (@lem2604319)). Qed.
Lemma lem2604321 : term376 = term399.
Proof. exact (@lem2604247 (@lem2604320)). Qed.
Lemma lem2604322 : term375 = term399.
Proof. exact (TRANS (@lem2604213) (@lem2604321)). Qed.
Lemma lem2604324 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2604325 : term399 = term378.
Proof. exact (@lem2604324 term378). Qed.
Lemma lem2604326 : term375 = term378.
Proof. exact (TRANS (@lem2604322) (@lem2604325)). Qed.
Lemma lem2604327 (m : int) : (term374 m) = term400.
Proof. exact (MK_COMB (@lem2604204 m) (@lem2604326)). Qed.
Lemma lem2604328 (m : int) : (term373 m) = term400.
Proof. exact (TRANS (@lem2604096 m) (@lem2604327 m)). Qed.
Lemma lem2604329 : term400 = term378.
Proof. exact (@lem1982721 term378). Qed.
Lemma lem2604330 (m : int) : (term373 m) = term378.
Proof. exact (TRANS (@lem2604328 m) (@lem2604329)). Qed.
Lemma lem2604331 (c : int) (n : int) (m : int) : (term372 c n m) = term400.
Proof. exact (MK_COMB (@lem2604095 c n) (@lem2604330 m)). Qed.
Lemma lem2604332 (c : int) (n : int) (m : int) : (term371 c n m) = term400.
Proof. exact (TRANS (@lem2603987 c n m) (@lem2604331 c n m)). Qed.
Lemma lem2604333 : term400 = term378.
Proof. exact (@lem1982721 term378). Qed.
Lemma lem2604334 (c : int) (n : int) (m : int) : (term371 c n m) = term378.
Proof. exact (TRANS (@lem2604332 c n m) (@lem2604333)). Qed.
Lemma lem2604335 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2604336 (c : int) (n : int) (m : int) : (term401 c n m) = term402.
Proof. exact (MK_COMB (@lem2604335) (@lem2604334 c n m)). Qed.
Lemma lem2604337 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2604338 (c : int) (n : int) (m : int) : (term370 c n m) = term403.
Proof. exact (MK_COMB (@lem2604336 c n m) (@lem2604337)). Qed.
Lemma lem2604339 (c : int) (n : int) (m : int) (h1 : term419 c n m) : term403.
Proof. exact (EQ_MP (@lem2604338 c n m) (@lem2603986 c n m h1)). Qed.
Lemma lem2604341 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2604342 : term403 = term404.
Proof. exact (@lem2604341 term160 term378). Qed.
Lemma lem2604344 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2604345 : term378 = term399.
Proof. exact (@lem2604344 term387). Qed.
Lemma lem2604347 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2604348 : term160 = term259.
Proof. exact (@lem2604347 (NUMERAL 0)). Qed.
Lemma lem2604349 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2604350 : term323 = term324.
Proof. exact (MK_COMB (@lem2604349) (@lem2604348)). Qed.
Lemma lem2604351 : term404 = term405.
Proof. exact (MK_COMB (@lem2604350) (@lem2604345)). Qed.
Lemma lem2604352 : term406.
Proof. exact (@lem1980026 term160 term63 term378 term63). Qed.
Lemma lem2604354 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2604355 : term258 = term265.
Proof. exact (@lem2604354 (NUMERAL 0) term64). Qed.
Lemma lem2604356 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2604357 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2604358 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2604357 h1) (fun h1 : term265 = True => @lem2604356)). Qed.
Lemma lem2604359 : term265 = True.
Proof. exact (EQ_MP (@lem2604358) (@lem2604356)). Qed.
Lemma lem2604360 : term258 = True.
Proof. exact (TRANS (@lem2604355) (@lem2604359)). Qed.
Lemma lem2604361 : True = term258.
Proof. exact (SYM (@lem2604360)). Qed.
Lemma lem2604362 : term258.
Proof. exact (EQ_MP (@lem2604361) (@lem0)). Qed.
Lemma lem2604363 : term407.
Proof. exact (@lem2604352 (@lem2604362)). Qed.
Lemma lem2604365 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2604366 : term258 = term265.
Proof. exact (@lem2604365 (NUMERAL 0) term64). Qed.
Lemma lem2604367 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2604368 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2604369 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2604368 h1) (fun h1 : term265 = True => @lem2604367)). Qed.
Lemma lem2604370 : term265 = True.
Proof. exact (EQ_MP (@lem2604369) (@lem2604367)). Qed.
Lemma lem2604371 : term258 = True.
Proof. exact (TRANS (@lem2604366) (@lem2604370)). Qed.
Lemma lem2604372 : True = term258.
Proof. exact (SYM (@lem2604371)). Qed.
Lemma lem2604373 : term258.
Proof. exact (EQ_MP (@lem2604372) (@lem0)). Qed.
Lemma lem2604374 : term405 = term408.
Proof. exact (@lem2604363 (@lem2604373)). Qed.
Lemma lem2604376 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2604377 : term393 = term394.
Proof. exact (@lem2604376 term387 term64). Qed.
Lemma lem2604378 : term395 = term385.
Proof. exact (@lem996237 term385). Qed.
Lemma lem2604379 : (term395 = term385) = (term396 = term387).
Proof. exact (@lem1007663 term385 (BIT1 0) term385). Qed.
Lemma lem2604380 : term396 = term387.
Proof. exact (EQ_MP (@lem2604379) (@lem2604378)). Qed.
Lemma lem2604381 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2604382 : term397 = term389.
Proof. exact (MK_COMB (@lem2604381) (@lem2604380)). Qed.
Lemma lem2604383 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2604384 : term394 = term378.
Proof. exact (MK_COMB (@lem2604383) (@lem2604382)). Qed.
Lemma lem2604385 : term393 = term378.
Proof. exact (TRANS (@lem2604377) (@lem2604384)). Qed.
Lemma lem2604387 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2604388 : term270 = term160.
Proof. exact (@lem2604387 term64). Qed.
Lemma lem2604389 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2604390 : term329 = term323.
Proof. exact (MK_COMB (@lem2604389) (@lem2604388)). Qed.
Lemma lem2604391 : term408 = term404.
Proof. exact (MK_COMB (@lem2604390) (@lem2604385)). Qed.
Lemma lem2604393 (m : nat) (n : nat) : (term330 m n) = (term331 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2604394 : term404 = term409.
Proof. exact (@lem2604393 (NUMERAL 0) term387). Qed.
Lemma lem2604395 : term410 = term385.
Proof. exact (@lem912803). Qed.
Lemma lem2604396 (h1 : term410 = term385) : (term387 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term385 h1). Qed.
Lemma lem2604397 : (term410 = term385) = ((term387 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term410 = term385 => @lem2604396 h1) (fun h1 : (term387 = (NUMERAL 0)) = False => @lem2604395)). Qed.
Lemma lem2604398 : (term387 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2604397) (@lem2604395)). Qed.
Lemma lem2604399 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2604400 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2604401 : term333 = (and True).
Proof. exact (MK_COMB (@lem2604400) (@lem2604399)). Qed.
Lemma lem2604402 : term409 = (True /\ False).
Proof. exact (MK_COMB (@lem2604401) (@lem2604398)). Qed.
Lemma lem2604404 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2604405 : term409 = False.
Proof. exact (TRANS (@lem2604402) (@lem2604404)). Qed.
Lemma lem2604406 : term404 = False.
Proof. exact (TRANS (@lem2604394) (@lem2604405)). Qed.
Lemma lem2604407 : term408 = False.
Proof. exact (TRANS (@lem2604391) (@lem2604406)). Qed.
Lemma lem2604408 : term405 = False.
Proof. exact (TRANS (@lem2604374) (@lem2604407)). Qed.
Lemma lem2604409 : term404 = False.
Proof. exact (TRANS (@lem2604351) (@lem2604408)). Qed.
Lemma lem2604410 : term403 = False.
Proof. exact (TRANS (@lem2604342) (@lem2604409)). Qed.
Lemma lem2604411 (c : int) (n : int) (m : int) (h1 : term419 c n m) : False.
Proof. exact (EQ_MP (@lem2604410) (@lem2604339 c n m h1)). Qed.
Lemma lem2604412 (c : int) (n : int) (m : int) (h1 : term247 c n m) : False.
Proof. exact (or_elim (@lem2603367 c n m h1) (fun h0 : term411 c n m => @lem2603828 c n m h0) (fun h0 : term419 c n m => @lem2604411 c n m h0)). Qed.
Lemma lem2604413 (c : int) (n : int) (m : int) (h1 : term252 c n m) : False.
Proof. exact (or_elim (@lem2602320 c n m h1) (fun h0 : term249 c n m => @lem2603366 c n m h0) (fun h0 : term247 c n m => @lem2604412 c n m h0)). Qed.
Lemma lem2604414 (c : int) (n : int) (m : int) (h1 : term255 c n m) : False.
Proof. exact (or_elim (@lem2601511 c n m h1) (fun h0 : term253 c n m => @lem2602319 c n m h0) (fun h0 : term252 c n m => @lem2604413 c n m h0)). Qed.
Lemma lem2604416 (c : int) (n : int) (m : int) (h1 : term255 c n m) : term255 c n m.
Proof. exact (h1). Qed.
Lemma lem2604417 (c : int) (n : int) (m : int) (h1 : term255 c n m) : (term255 c n m) = False.
Proof. exact (prop_ext (fun h2 : term255 c n m => @lem2604414 c n m h1) (fun h2 : False => @lem2604416 c n m h1)). Qed.
Lemma lem2604418 (c : int) (n : int) (m : int) (h1 : term255 c n m) : False.
Proof. exact (EQ_MP (@lem2604417 c n m h1) (@lem2604416 c n m h1)). Qed.
Lemma lem2604419 (n : int) (c : int) (m : int) (h1 : term122 n c m) : term122 n c m.
Proof. exact (h1). Qed.
Lemma lem2604420 (n : int) (c : int) (m : int) (h1 : term122 n c m) : term255 c n m.
Proof. exact (EQ_MP (@lem2601477 c n m) (@lem2604419 n c m h1)). Qed.
Lemma lem2604421 (n : int) (c : int) (m : int) (h1 : term122 n c m) : (term255 c n m) = False.
Proof. exact (prop_ext (fun h2 : term255 c n m => @lem2604418 c n m h2) (fun h2 : False => @lem2604420 n c m h1)). Qed.
Lemma lem2604422 (n : int) (c : int) (m : int) (h1 : term122 n c m) : False.
Proof. exact (EQ_MP (@lem2604421 n c m h1) (@lem2604420 n c m h1)). Qed.
Lemma lem2604423 (n : int) (c : int) (m : int) : term420 n c m.
Proof. exact (fun h0 : term122 n c m => @lem2604422 n c m h0). Qed.
Lemma lem2604424 (n : int) (c : int) (m : int) : term421 n c m.
Proof. exact (@lem1386578 (term422 n c m)). Qed.
Lemma lem2604427 (n : int) (c : int) (m : int) : term422 n c m.
Proof. exact (@lem2604424 n c m (@lem2604423 n c m)). Qed.
Lemma lem2604428 (m : int) (n : int) (c : int) : (term120 n c m) = (term34 m n c).
Proof. exact (SYM (@lem2600339 n c m)). Qed.
Lemma lem2604429 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2604430 (m : int) (n : int) (c : int) : (term422 n c m) = (term0 m n c).
Proof. exact (MK_COMB (@lem2604429) (@lem2604428 m n c)). Qed.
Lemma lem2604431 (m : int) (n : int) (c : int) : term0 m n c.
Proof. exact (EQ_MP (@lem2604430 m n c) (@lem2604427 n c m)). Qed.
Lemma lem2604433 (a : int) (b : int) : (term423 a b) = ((term424 a b) = (term425 a b)).
Proof. exact (@lem2318604 ((term424 a b) = (term425 a b))). Qed.
Lemma lem2604444 (a : int) (b : int) : (term426 a b) = (term427 a b).
Proof. exact (@lem16933 (term427 a b)). Qed.
Lemma lem2604447 (a : int) (b : int) : (term428 a b) = (term428 a b).
Proof. exact (eq_refl (term428 a b)). Qed.
Lemma lem2604449 (a : int) (b : int) : (term429 a b) = (term429 a b).
Proof. exact (eq_refl (term429 a b)). Qed.
Lemma lem2604450 (a : int) (b : int) : (term430 a b) = (term431 a b).
Proof. exact (MK_COMB (@lem2604449 a b) (@lem2604444 a b)). Qed.
Lemma lem2604451 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2604452 (a : int) (b : int) : (term432 a b) = (term433 a b).
Proof. exact (MK_COMB (@lem2604451) (@lem2604450 a b)). Qed.
Lemma lem2604453 (a : int) (b : int) : (term434 a b) = (term435 a b).
Proof. exact (MK_COMB (@lem2604452 a b) (@lem2604447 a b)). Qed.
Lemma lem2604454 (a : int) (b : int) : (term436 a b) = (term434 a b).
Proof. exact (@lem17646 (term424 a b) (term425 a b)). Qed.
Lemma lem2604474 (a : int) (b : int) : (term436 a b) = (term435 a b).
Proof. exact (TRANS (@lem2604454 a b) (@lem2604453 a b)). Qed.
Lemma lem2604477 (x : int) (y : int) : (int_le x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2604478 (a : int) (b : int) : (term424 a b) = (term437 a b).
Proof. exact (@lem2604477 (int_neg a) b). Qed.
Lemma lem2604480 (x : int) : (term43 x) = (term44 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2604481 (a : int) : (term43 a) = (term44 a).
Proof. exact (@lem2604480 a). Qed.
Lemma lem2604482 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2604483 (a : int) : (term438 a) = (term439 a).
Proof. exact (MK_COMB (@lem2604482) (@lem2604481 a)). Qed.
Lemma lem2604484 (b : int) : (real_of_int b) = (real_of_int b).
Proof. exact (eq_refl (real_of_int b)). Qed.
Lemma lem2604485 (a : int) (b : int) : (term437 a b) = (term440 a b).
Proof. exact (MK_COMB (@lem2604483 a) (@lem2604484 b)). Qed.
Lemma lem2604487 (a : int) (b : int) : (term424 a b) = (term440 a b).
Proof. exact (TRANS (@lem2604478 a b) (@lem2604485 a b)). Qed.
Lemma lem2604489 (x : int) (y : int) : (int_lt x y) = (term50 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem2604490 (a : int) (b : int) : (term427 a b) = (term441 a b).
Proof. exact (@lem2604489 a (int_neg b)). Qed.
Lemma lem2604492 (x : int) (y : int) : (int_le x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2604493 (a : int) (b : int) : (term441 a b) = (term442 a b).
Proof. exact (@lem2604492 (term75 a) (int_neg b)). Qed.
Lemma lem2604495 (x : int) (y : int) : (term54 x y) = (term55 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2604496 (a : int) : (term76 a) = (term77 a).
Proof. exact (@lem2604495 a term58). Qed.
Lemma lem2604498 (n : nat) : (term61 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2604499 : term62 = term63.
Proof. exact (@lem2604498 term64). Qed.
Lemma lem2604500 (a : int) : (term78 a) = (term78 a).
Proof. exact (eq_refl (term78 a)). Qed.
Lemma lem2604501 (a : int) : (term77 a) = (term79 a).
Proof. exact (MK_COMB (@lem2604500 a) (@lem2604499)). Qed.
Lemma lem2604502 (a : int) : (term76 a) = (term79 a).
Proof. exact (TRANS (@lem2604496 a) (@lem2604501 a)). Qed.
Lemma lem2604503 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2604504 (a : int) : (term80 a) = (term81 a).
Proof. exact (MK_COMB (@lem2604503) (@lem2604502 a)). Qed.
Lemma lem2604506 (x : int) : (term43 x) = (term44 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2604507 (b : int) : (term43 b) = (term44 b).
Proof. exact (@lem2604506 b). Qed.
Lemma lem2604508 (a : int) (b : int) : (term442 a b) = (term443 a b).
Proof. exact (MK_COMB (@lem2604504 a) (@lem2604507 b)). Qed.
Lemma lem2604509 (a : int) (b : int) : (term441 a b) = (term443 a b).
Proof. exact (TRANS (@lem2604493 a b) (@lem2604508 a b)). Qed.
Lemma lem2604510 (a : int) (b : int) : (term427 a b) = (term443 a b).
Proof. exact (TRANS (@lem2604490 a b) (@lem2604509 a b)). Qed.
Lemma lem2604511 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2604512 (a : int) (b : int) : (term429 a b) = (term444 a b).
Proof. exact (MK_COMB (@lem2604511) (@lem2604487 a b)). Qed.
Lemma lem2604513 (a : int) (b : int) : (term431 a b) = (term445 a b).
Proof. exact (MK_COMB (@lem2604512 a b) (@lem2604510 a b)). Qed.
Lemma lem2604515 (y : int) (x : int) : (term446 x y) = (term50 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem2604516 (b : int) (a : int) : (term447 a b) = (term441 b a).
Proof. exact (@lem2604515 b (int_neg a)). Qed.
Lemma lem2604518 (x : int) (y : int) : (int_le x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2604519 (b : int) (a : int) : (term441 b a) = (term442 b a).
Proof. exact (@lem2604518 (term75 b) (int_neg a)). Qed.
Lemma lem2604521 (x : int) (y : int) : (term54 x y) = (term55 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2604522 (b : int) : (term76 b) = (term77 b).
Proof. exact (@lem2604521 b term58). Qed.
Lemma lem2604524 (n : nat) : (term61 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2604525 : term62 = term63.
Proof. exact (@lem2604524 term64). Qed.
Lemma lem2604526 (b : int) : (term78 b) = (term78 b).
Proof. exact (eq_refl (term78 b)). Qed.
Lemma lem2604527 (b : int) : (term77 b) = (term79 b).
Proof. exact (MK_COMB (@lem2604526 b) (@lem2604525)). Qed.
Lemma lem2604528 (b : int) : (term76 b) = (term79 b).
Proof. exact (TRANS (@lem2604522 b) (@lem2604527 b)). Qed.
Lemma lem2604529 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2604530 (b : int) : (term80 b) = (term81 b).
Proof. exact (MK_COMB (@lem2604529) (@lem2604528 b)). Qed.
Lemma lem2604532 (x : int) : (term43 x) = (term44 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2604533 (a : int) : (term43 a) = (term44 a).
Proof. exact (@lem2604532 a). Qed.
Lemma lem2604534 (b : int) (a : int) : (term442 b a) = (term443 b a).
Proof. exact (MK_COMB (@lem2604530 b) (@lem2604533 a)). Qed.
Lemma lem2604535 (b : int) (a : int) : (term441 b a) = (term443 b a).
Proof. exact (TRANS (@lem2604519 b a) (@lem2604534 b a)). Qed.
Lemma lem2604536 (b : int) (a : int) : (term447 a b) = (term443 b a).
Proof. exact (TRANS (@lem2604516 b a) (@lem2604535 b a)). Qed.
Lemma lem2604538 (y : int) (x : int) : (term35 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem2604539 (b : int) (a : int) : (term425 a b) = (term424 b a).
Proof. exact (@lem2604538 (int_neg b) a). Qed.
Lemma lem2604541 (x : int) (y : int) : (int_le x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2604542 (b : int) (a : int) : (term424 b a) = (term437 b a).
Proof. exact (@lem2604541 (int_neg b) a). Qed.
Lemma lem2604544 (x : int) : (term43 x) = (term44 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2604545 (b : int) : (term43 b) = (term44 b).
Proof. exact (@lem2604544 b). Qed.
Lemma lem2604546 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2604547 (b : int) : (term438 b) = (term439 b).
Proof. exact (MK_COMB (@lem2604546) (@lem2604545 b)). Qed.
Lemma lem2604548 (a : int) : (real_of_int a) = (real_of_int a).
Proof. exact (eq_refl (real_of_int a)). Qed.
Lemma lem2604549 (b : int) (a : int) : (term437 b a) = (term440 b a).
Proof. exact (MK_COMB (@lem2604547 b) (@lem2604548 a)). Qed.
Lemma lem2604550 (b : int) (a : int) : (term424 b a) = (term440 b a).
Proof. exact (TRANS (@lem2604542 b a) (@lem2604549 b a)). Qed.
Lemma lem2604551 (b : int) (a : int) : (term425 a b) = (term440 b a).
Proof. exact (TRANS (@lem2604539 b a) (@lem2604550 b a)). Qed.
Lemma lem2604552 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2604553 (b : int) (a : int) : (term448 a b) = (term449 b a).
Proof. exact (MK_COMB (@lem2604552) (@lem2604536 b a)). Qed.
Lemma lem2604554 (b : int) (a : int) : (term428 a b) = (term450 b a).
Proof. exact (MK_COMB (@lem2604553 b a) (@lem2604551 b a)). Qed.
Lemma lem2604555 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2604556 (a : int) (b : int) : (term433 a b) = (term451 a b).
Proof. exact (MK_COMB (@lem2604555) (@lem2604513 a b)). Qed.
Lemma lem2604557 (b : int) (a : int) : (term435 a b) = (term452 b a).
Proof. exact (MK_COMB (@lem2604556 a b) (@lem2604554 b a)). Qed.
Lemma lem2604558 (b : int) (a : int) : (term436 a b) = (term452 b a).
Proof. exact (TRANS (@lem2604474 a b) (@lem2604557 b a)). Qed.
Lemma lem2604562 (t : Prop) : (term121 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2604598 (b : int) (a : int) : (term453 b a) = (term452 b a).
Proof. exact (@lem2604562 (term452 b a)). Qed.
Lemma lem2604599 (b : int) (a : int) : (term440 a b) = (term454 b a).
Proof. exact (@lem1988287 (real_of_int b) (term44 a)). Qed.
Lemma lem2604606 (a : int) : (term44 a) = (term124 a).
Proof. exact (@lem1982785 (real_of_int a)). Qed.
Lemma lem2604609 (b : int) : (term129 b) = (term129 b).
Proof. exact (eq_refl (term129 b)). Qed.
Lemma lem2604610 (b : int) (a : int) : (term455 b a) = (term456 b a).
Proof. exact (MK_COMB (@lem2604609 b) (@lem2604606 a)). Qed.
Lemma lem2604611 (b : int) (a : int) : (term456 b a) = (term457 b a).
Proof. exact (@lem1982792 (real_of_int b) (term124 a)). Qed.
Lemma lem2604612 (a : int) : (term180 a) = (term181 a).
Proof. exact (@lem1982749 term127 term127 (real_of_int a)). Qed.
Lemma lem2604614 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2604615 : term127 = term137.
Proof. exact (@lem2604614 term64). Qed.
Lemma lem2604617 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2604618 : term127 = term137.
Proof. exact (@lem2604617 term64). Qed.
Lemma lem2604619 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2604620 : term128 = term138.
Proof. exact (MK_COMB (@lem2604619) (@lem2604618)). Qed.
Lemma lem2604621 : term139 = term140.
Proof. exact (MK_COMB (@lem2604620) (@lem2604615)). Qed.
Lemma lem2604622 : term140 = term141.
Proof. exact (@lem1981613 term127 term127 term63 term63). Qed.
Lemma lem2604624 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2604625 : term144 = term145.
Proof. exact (@lem2604624 term64 term64). Qed.
Lemma lem2604626 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2604627 : term147 = term64.
Proof. exact (EQ_MP (@lem2604626) (@lem940073)). Qed.
Lemma lem2604628 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2604629 : term145 = term63.
Proof. exact (MK_COMB (@lem2604628) (@lem2604627)). Qed.
Lemma lem2604630 : term144 = term63.
Proof. exact (TRANS (@lem2604625) (@lem2604629)). Qed.
Lemma lem2604632 (m : nat) (n : nat) : (term148 m n) = (term143 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2604633 : term139 = term145.
Proof. exact (@lem2604632 term64 term64). Qed.
Lemma lem2604634 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2604635 : term147 = term64.
Proof. exact (EQ_MP (@lem2604634) (@lem940073)). Qed.
Lemma lem2604636 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2604637 : term145 = term63.
Proof. exact (MK_COMB (@lem2604636) (@lem2604635)). Qed.
Lemma lem2604638 : term139 = term63.
Proof. exact (TRANS (@lem2604633) (@lem2604637)). Qed.
Lemma lem2604639 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2604640 : term149 = term150.
Proof. exact (MK_COMB (@lem2604639) (@lem2604638)). Qed.
Lemma lem2604641 : term141 = term151.
Proof. exact (MK_COMB (@lem2604640) (@lem2604630)). Qed.
Lemma lem2604642 : term140 = term151.
Proof. exact (TRANS (@lem2604622) (@lem2604641)). Qed.
Lemma lem2604643 : term139 = term151.
Proof. exact (TRANS (@lem2604621) (@lem2604642)). Qed.
Lemma lem2604645 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2604646 : term151 = term63.
Proof. exact (@lem2604645 term63). Qed.
Lemma lem2604647 : term139 = term63.
Proof. exact (TRANS (@lem2604643) (@lem2604646)). Qed.
Lemma lem2604648 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2604649 : term153 = term154.
Proof. exact (MK_COMB (@lem2604648) (@lem2604647)). Qed.
Lemma lem2604650 (a : int) : (real_of_int a) = (real_of_int a).
Proof. exact (eq_refl (real_of_int a)). Qed.
Lemma lem2604651 (a : int) : (term181 a) = (term182 a).
Proof. exact (MK_COMB (@lem2604649) (@lem2604650 a)). Qed.
Lemma lem2604652 (a : int) : (term180 a) = (term182 a).
Proof. exact (TRANS (@lem2604612 a) (@lem2604651 a)). Qed.
Lemma lem2604653 (a : int) : (term182 a) = (real_of_int a).
Proof. exact (@lem1982709 (real_of_int a)). Qed.
Lemma lem2604654 (a : int) : (term180 a) = (real_of_int a).
Proof. exact (TRANS (@lem2604652 a) (@lem2604653 a)). Qed.
Lemma lem2604655 (b : int) : (term78 b) = (term78 b).
Proof. exact (eq_refl (term78 b)). Qed.
Lemma lem2604656 (b : int) (a : int) : (term457 b a) = (term55 b a).
Proof. exact (MK_COMB (@lem2604655 b) (@lem2604654 a)). Qed.
Lemma lem2604657 (a : int) (b : int) : (term55 b a) = (term55 a b).
Proof. exact (@lem1982761 (real_of_int a) (real_of_int b)). Qed.
Lemma lem2604658 (a : int) (b : int) : (term457 b a) = (term55 a b).
Proof. exact (TRANS (@lem2604656 b a) (@lem2604657 a b)). Qed.
Lemma lem2604659 (a : int) (b : int) : (term456 b a) = (term55 a b).
Proof. exact (TRANS (@lem2604611 b a) (@lem2604658 a b)). Qed.
Lemma lem2604660 (a : int) (b : int) : (term455 b a) = (term55 a b).
Proof. exact (TRANS (@lem2604610 b a) (@lem2604659 a b)). Qed.
Lemma lem2604661 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2604662 (a : int) (b : int) : (term458 b a) = (term459 a b).
Proof. exact (MK_COMB (@lem2604661) (@lem2604660 a b)). Qed.
Lemma lem2604663 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2604664 (a : int) (b : int) : (term454 b a) = (term460 a b).
Proof. exact (MK_COMB (@lem2604662 a b) (@lem2604663)). Qed.
Lemma lem2604665 (a : int) (b : int) : (term440 a b) = (term460 a b).
Proof. exact (TRANS (@lem2604599 b a) (@lem2604664 a b)). Qed.
Lemma lem2604666 (b : int) (a : int) : (term443 a b) = (term461 b a).
Proof. exact (@lem1988287 (term44 b) (term79 a)). Qed.
Lemma lem2604673 (a : int) : (term79 a) = (term79 a).
Proof. exact (eq_refl (term79 a)). Qed.
Lemma lem2604680 (b : int) : (term44 b) = (term124 b).
Proof. exact (@lem1982785 (real_of_int b)). Qed.
Lemma lem2604681 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2604682 (b : int) : (term207 b) = (term208 b).
Proof. exact (MK_COMB (@lem2604681) (@lem2604680 b)). Qed.
Lemma lem2604683 (b : int) (a : int) : (term462 b a) = (term463 b a).
Proof. exact (MK_COMB (@lem2604682 b) (@lem2604673 a)). Qed.
Lemma lem2604684 (b : int) (a : int) : (term463 b a) = (term464 b a).
Proof. exact (@lem1982792 (term124 b) (term79 a)). Qed.
Lemma lem2604685 (a : int) : (term198 a) = (term199 a).
Proof. exact (@lem1982781 (real_of_int a) term127 term63). Qed.
Lemma lem2604687 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2604688 : term63 = term151.
Proof. exact (@lem2604687 term64). Qed.
Lemma lem2604690 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2604691 : term127 = term137.
Proof. exact (@lem2604690 term64). Qed.
Lemma lem2604692 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2604693 : term128 = term138.
Proof. exact (MK_COMB (@lem2604692) (@lem2604691)). Qed.
Lemma lem2604694 : term172 = term173.
Proof. exact (MK_COMB (@lem2604693) (@lem2604688)). Qed.
Lemma lem2604695 : term173 = term174.
Proof. exact (@lem1981613 term127 term63 term63 term63). Qed.
Lemma lem2604697 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2604698 : term144 = term145.
Proof. exact (@lem2604697 term64 term64). Qed.
Lemma lem2604699 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2604700 : term147 = term64.
Proof. exact (EQ_MP (@lem2604699) (@lem940073)). Qed.
Lemma lem2604701 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2604702 : term145 = term63.
Proof. exact (MK_COMB (@lem2604701) (@lem2604700)). Qed.
Lemma lem2604703 : term144 = term63.
Proof. exact (TRANS (@lem2604698) (@lem2604702)). Qed.
Lemma lem2604705 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2604706 : term172 = term177.
Proof. exact (@lem2604705 term64 term64). Qed.
Lemma lem2604707 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2604708 : term147 = term64.
Proof. exact (EQ_MP (@lem2604707) (@lem940073)). Qed.
Lemma lem2604709 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2604710 : term145 = term63.
Proof. exact (MK_COMB (@lem2604709) (@lem2604708)). Qed.
Lemma lem2604711 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2604712 : term177 = term127.
Proof. exact (MK_COMB (@lem2604711) (@lem2604710)). Qed.
Lemma lem2604713 : term172 = term127.
Proof. exact (TRANS (@lem2604706) (@lem2604712)). Qed.
Lemma lem2604714 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2604715 : term178 = term179.
Proof. exact (MK_COMB (@lem2604714) (@lem2604713)). Qed.
Lemma lem2604716 : term174 = term137.
Proof. exact (MK_COMB (@lem2604715) (@lem2604703)). Qed.
Lemma lem2604717 : term173 = term137.
Proof. exact (TRANS (@lem2604695) (@lem2604716)). Qed.
Lemma lem2604718 : term172 = term137.
Proof. exact (TRANS (@lem2604694) (@lem2604717)). Qed.
Lemma lem2604720 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2604721 : term137 = term127.
Proof. exact (@lem2604720 term127). Qed.
Lemma lem2604722 : term172 = term127.
Proof. exact (TRANS (@lem2604718) (@lem2604721)). Qed.
Lemma lem2604725 (a : int) : (term163 a) = (term163 a).
Proof. exact (eq_refl (term163 a)). Qed.
Lemma lem2604726 (a : int) : (term199 a) = (term200 a).
Proof. exact (MK_COMB (@lem2604725 a) (@lem2604722)). Qed.
Lemma lem2604727 (a : int) : (term198 a) = (term200 a).
Proof. exact (TRANS (@lem2604685 a) (@lem2604726 a)). Qed.
Lemma lem2604728 (b : int) : (term163 b) = (term163 b).
Proof. exact (eq_refl (term163 b)). Qed.
Lemma lem2604729 (b : int) (a : int) : (term464 b a) = (term465 b a).
Proof. exact (MK_COMB (@lem2604728 b) (@lem2604727 a)). Qed.
Lemma lem2604734 (a : int) (b : int) : (term465 b a) = (term465 a b).
Proof. exact (@lem1982757 (term124 a) (term124 b) term127). Qed.
Lemma lem2604735 (a : int) (b : int) : (term464 b a) = (term465 a b).
Proof. exact (TRANS (@lem2604729 b a) (@lem2604734 a b)). Qed.
Lemma lem2604736 (a : int) (b : int) : (term463 b a) = (term465 a b).
Proof. exact (TRANS (@lem2604684 b a) (@lem2604735 a b)). Qed.
Lemma lem2604737 (a : int) (b : int) : (term462 b a) = (term465 a b).
Proof. exact (TRANS (@lem2604683 b a) (@lem2604736 a b)). Qed.
Lemma lem2604738 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2604739 (a : int) (b : int) : (term466 b a) = (term467 a b).
Proof. exact (MK_COMB (@lem2604738) (@lem2604737 a b)). Qed.
Lemma lem2604740 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2604741 (a : int) (b : int) : (term461 b a) = (term468 a b).
Proof. exact (MK_COMB (@lem2604739 a b) (@lem2604740)). Qed.
Lemma lem2604742 (a : int) (b : int) : (term443 a b) = (term468 a b).
Proof. exact (TRANS (@lem2604666 b a) (@lem2604741 a b)). Qed.
Lemma lem2604743 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2604744 (a : int) (b : int) : (term444 a b) = (term469 a b).
Proof. exact (MK_COMB (@lem2604743) (@lem2604665 a b)). Qed.
Lemma lem2604745 (a : int) (b : int) : (term445 a b) = (term470 a b).
Proof. exact (MK_COMB (@lem2604744 a b) (@lem2604742 a b)). Qed.
Lemma lem2604746 (a : int) (b : int) : (term443 b a) = (term461 a b).
Proof. exact (@lem1988287 (term44 a) (term79 b)). Qed.
Lemma lem2604753 (b : int) : (term79 b) = (term79 b).
Proof. exact (eq_refl (term79 b)). Qed.
Lemma lem2604760 (a : int) : (term44 a) = (term124 a).
Proof. exact (@lem1982785 (real_of_int a)). Qed.
Lemma lem2604761 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2604762 (a : int) : (term207 a) = (term208 a).
Proof. exact (MK_COMB (@lem2604761) (@lem2604760 a)). Qed.
Lemma lem2604763 (a : int) (b : int) : (term462 a b) = (term463 a b).
Proof. exact (MK_COMB (@lem2604762 a) (@lem2604753 b)). Qed.
Lemma lem2604764 (a : int) (b : int) : (term463 a b) = (term464 a b).
Proof. exact (@lem1982792 (term124 a) (term79 b)). Qed.
Lemma lem2604765 (b : int) : (term198 b) = (term199 b).
Proof. exact (@lem1982781 (real_of_int b) term127 term63). Qed.
Lemma lem2604767 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2604768 : term63 = term151.
Proof. exact (@lem2604767 term64). Qed.
Lemma lem2604770 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2604771 : term127 = term137.
Proof. exact (@lem2604770 term64). Qed.
Lemma lem2604772 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2604773 : term128 = term138.
Proof. exact (MK_COMB (@lem2604772) (@lem2604771)). Qed.
Lemma lem2604774 : term172 = term173.
Proof. exact (MK_COMB (@lem2604773) (@lem2604768)). Qed.
Lemma lem2604775 : term173 = term174.
Proof. exact (@lem1981613 term127 term63 term63 term63). Qed.
Lemma lem2604777 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2604778 : term144 = term145.
Proof. exact (@lem2604777 term64 term64). Qed.
Lemma lem2604779 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2604780 : term147 = term64.
Proof. exact (EQ_MP (@lem2604779) (@lem940073)). Qed.
Lemma lem2604781 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2604782 : term145 = term63.
Proof. exact (MK_COMB (@lem2604781) (@lem2604780)). Qed.
Lemma lem2604783 : term144 = term63.
Proof. exact (TRANS (@lem2604778) (@lem2604782)). Qed.
Lemma lem2604785 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2604786 : term172 = term177.
Proof. exact (@lem2604785 term64 term64). Qed.
Lemma lem2604787 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2604788 : term147 = term64.
Proof. exact (EQ_MP (@lem2604787) (@lem940073)). Qed.
Lemma lem2604789 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2604790 : term145 = term63.
Proof. exact (MK_COMB (@lem2604789) (@lem2604788)). Qed.
Lemma lem2604791 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2604792 : term177 = term127.
Proof. exact (MK_COMB (@lem2604791) (@lem2604790)). Qed.
Lemma lem2604793 : term172 = term127.
Proof. exact (TRANS (@lem2604786) (@lem2604792)). Qed.
Lemma lem2604794 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2604795 : term178 = term179.
Proof. exact (MK_COMB (@lem2604794) (@lem2604793)). Qed.
Lemma lem2604796 : term174 = term137.
Proof. exact (MK_COMB (@lem2604795) (@lem2604783)). Qed.
Lemma lem2604797 : term173 = term137.
Proof. exact (TRANS (@lem2604775) (@lem2604796)). Qed.
Lemma lem2604798 : term172 = term137.
Proof. exact (TRANS (@lem2604774) (@lem2604797)). Qed.
Lemma lem2604800 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2604801 : term137 = term127.
Proof. exact (@lem2604800 term127). Qed.
Lemma lem2604802 : term172 = term127.
Proof. exact (TRANS (@lem2604798) (@lem2604801)). Qed.
Lemma lem2604805 (b : int) : (term163 b) = (term163 b).
Proof. exact (eq_refl (term163 b)). Qed.
Lemma lem2604806 (b : int) : (term199 b) = (term200 b).
Proof. exact (MK_COMB (@lem2604805 b) (@lem2604802)). Qed.
Lemma lem2604807 (b : int) : (term198 b) = (term200 b).
Proof. exact (TRANS (@lem2604765 b) (@lem2604806 b)). Qed.
Lemma lem2604808 (a : int) : (term163 a) = (term163 a).
Proof. exact (eq_refl (term163 a)). Qed.
Lemma lem2604811 (a : int) (b : int) : (term464 a b) = (term465 a b).
Proof. exact (MK_COMB (@lem2604808 a) (@lem2604807 b)). Qed.
Lemma lem2604812 (a : int) (b : int) : (term463 a b) = (term465 a b).
Proof. exact (TRANS (@lem2604764 a b) (@lem2604811 a b)). Qed.
Lemma lem2604813 (a : int) (b : int) : (term462 a b) = (term465 a b).
Proof. exact (TRANS (@lem2604763 a b) (@lem2604812 a b)). Qed.
Lemma lem2604814 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2604815 (a : int) (b : int) : (term466 a b) = (term467 a b).
Proof. exact (MK_COMB (@lem2604814) (@lem2604813 a b)). Qed.
Lemma lem2604816 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2604817 (a : int) (b : int) : (term461 a b) = (term468 a b).
Proof. exact (MK_COMB (@lem2604815 a b) (@lem2604816)). Qed.
Lemma lem2604818 (a : int) (b : int) : (term443 b a) = (term468 a b).
Proof. exact (TRANS (@lem2604746 a b) (@lem2604817 a b)). Qed.
Lemma lem2604819 (a : int) (b : int) : (term440 b a) = (term454 a b).
Proof. exact (@lem1988287 (real_of_int a) (term44 b)). Qed.
Lemma lem2604826 (b : int) : (term44 b) = (term124 b).
Proof. exact (@lem1982785 (real_of_int b)). Qed.
Lemma lem2604829 (a : int) : (term129 a) = (term129 a).
Proof. exact (eq_refl (term129 a)). Qed.
Lemma lem2604830 (a : int) (b : int) : (term455 a b) = (term456 a b).
Proof. exact (MK_COMB (@lem2604829 a) (@lem2604826 b)). Qed.
Lemma lem2604831 (a : int) (b : int) : (term456 a b) = (term457 a b).
Proof. exact (@lem1982792 (real_of_int a) (term124 b)). Qed.
Lemma lem2604832 (b : int) : (term180 b) = (term181 b).
Proof. exact (@lem1982749 term127 term127 (real_of_int b)). Qed.
Lemma lem2604834 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2604835 : term127 = term137.
Proof. exact (@lem2604834 term64). Qed.
Lemma lem2604837 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2604838 : term127 = term137.
Proof. exact (@lem2604837 term64). Qed.
Lemma lem2604839 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2604840 : term128 = term138.
Proof. exact (MK_COMB (@lem2604839) (@lem2604838)). Qed.
Lemma lem2604841 : term139 = term140.
Proof. exact (MK_COMB (@lem2604840) (@lem2604835)). Qed.
Lemma lem2604842 : term140 = term141.
Proof. exact (@lem1981613 term127 term127 term63 term63). Qed.
Lemma lem2604844 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2604845 : term144 = term145.
Proof. exact (@lem2604844 term64 term64). Qed.
Lemma lem2604846 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2604847 : term147 = term64.
Proof. exact (EQ_MP (@lem2604846) (@lem940073)). Qed.
Lemma lem2604848 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2604849 : term145 = term63.
Proof. exact (MK_COMB (@lem2604848) (@lem2604847)). Qed.
Lemma lem2604850 : term144 = term63.
Proof. exact (TRANS (@lem2604845) (@lem2604849)). Qed.
Lemma lem2604852 (m : nat) (n : nat) : (term148 m n) = (term143 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2604853 : term139 = term145.
Proof. exact (@lem2604852 term64 term64). Qed.
Lemma lem2604854 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2604855 : term147 = term64.
Proof. exact (EQ_MP (@lem2604854) (@lem940073)). Qed.
Lemma lem2604856 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2604857 : term145 = term63.
Proof. exact (MK_COMB (@lem2604856) (@lem2604855)). Qed.
Lemma lem2604858 : term139 = term63.
Proof. exact (TRANS (@lem2604853) (@lem2604857)). Qed.
Lemma lem2604859 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2604860 : term149 = term150.
Proof. exact (MK_COMB (@lem2604859) (@lem2604858)). Qed.
Lemma lem2604861 : term141 = term151.
Proof. exact (MK_COMB (@lem2604860) (@lem2604850)). Qed.
Lemma lem2604862 : term140 = term151.
Proof. exact (TRANS (@lem2604842) (@lem2604861)). Qed.
Lemma lem2604863 : term139 = term151.
Proof. exact (TRANS (@lem2604841) (@lem2604862)). Qed.
Lemma lem2604865 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2604866 : term151 = term63.
Proof. exact (@lem2604865 term63). Qed.
Lemma lem2604867 : term139 = term63.
Proof. exact (TRANS (@lem2604863) (@lem2604866)). Qed.
Lemma lem2604868 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2604869 : term153 = term154.
Proof. exact (MK_COMB (@lem2604868) (@lem2604867)). Qed.
Lemma lem2604870 (b : int) : (real_of_int b) = (real_of_int b).
Proof. exact (eq_refl (real_of_int b)). Qed.
Lemma lem2604871 (b : int) : (term181 b) = (term182 b).
Proof. exact (MK_COMB (@lem2604869) (@lem2604870 b)). Qed.
Lemma lem2604872 (b : int) : (term180 b) = (term182 b).
Proof. exact (TRANS (@lem2604832 b) (@lem2604871 b)). Qed.
Lemma lem2604873 (b : int) : (term182 b) = (real_of_int b).
Proof. exact (@lem1982709 (real_of_int b)). Qed.
Lemma lem2604874 (b : int) : (term180 b) = (real_of_int b).
Proof. exact (TRANS (@lem2604872 b) (@lem2604873 b)). Qed.
Lemma lem2604875 (a : int) : (term78 a) = (term78 a).
Proof. exact (eq_refl (term78 a)). Qed.
Lemma lem2604878 (a : int) (b : int) : (term457 a b) = (term55 a b).
Proof. exact (MK_COMB (@lem2604875 a) (@lem2604874 b)). Qed.
Lemma lem2604879 (a : int) (b : int) : (term456 a b) = (term55 a b).
Proof. exact (TRANS (@lem2604831 a b) (@lem2604878 a b)). Qed.
Lemma lem2604880 (a : int) (b : int) : (term455 a b) = (term55 a b).
Proof. exact (TRANS (@lem2604830 a b) (@lem2604879 a b)). Qed.
Lemma lem2604881 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2604882 (a : int) (b : int) : (term458 a b) = (term459 a b).
Proof. exact (MK_COMB (@lem2604881) (@lem2604880 a b)). Qed.
Lemma lem2604883 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2604884 (a : int) (b : int) : (term454 a b) = (term460 a b).
Proof. exact (MK_COMB (@lem2604882 a b) (@lem2604883)). Qed.
Lemma lem2604885 (a : int) (b : int) : (term440 b a) = (term460 a b).
Proof. exact (TRANS (@lem2604819 a b) (@lem2604884 a b)). Qed.
Lemma lem2604886 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2604887 (a : int) (b : int) : (term449 b a) = (term471 a b).
Proof. exact (MK_COMB (@lem2604886) (@lem2604818 a b)). Qed.
Lemma lem2604888 (a : int) (b : int) : (term450 b a) = (term472 a b).
Proof. exact (MK_COMB (@lem2604887 a b) (@lem2604885 a b)). Qed.
Lemma lem2604889 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2604890 (a : int) (b : int) : (term451 a b) = (term473 a b).
Proof. exact (MK_COMB (@lem2604889) (@lem2604745 a b)). Qed.
Lemma lem2604891 (a : int) (b : int) : (term452 b a) = (term474 a b).
Proof. exact (MK_COMB (@lem2604890 a b) (@lem2604888 a b)). Qed.
Lemma lem2604916 (a : int) (b : int) : (term453 b a) = (term474 a b).
Proof. exact (TRANS (@lem2604598 b a) (@lem2604891 a b)). Qed.
Lemma lem2604926 (a : int) (b : int) (h1 : term474 a b) : term474 a b.
Proof. exact (h1). Qed.
Lemma lem2604927 (a : int) (b : int) (h1 : term470 a b) : term470 a b.
Proof. exact (h1). Qed.
Lemma lem2604928 (a : int) (b : int) (h1 : term470 a b) : term468 a b.
Proof. exact (proj2 (@lem2604927 a b h1)). Qed.
Lemma lem2604929 (a : int) (b : int) (h1 : term470 a b) : term460 a b.
Proof. exact (proj1 (@lem2604927 a b h1)). Qed.
Lemma lem2604931 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2604932 : term257 = term258.
Proof. exact (@lem2604931 term160 term63). Qed.
Lemma lem2604934 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2604935 : term63 = term151.
Proof. exact (@lem2604934 term64). Qed.
Lemma lem2604937 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2604938 : term160 = term259.
Proof. exact (@lem2604937 (NUMERAL 0)). Qed.
Lemma lem2604939 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2604940 : term260 = term261.
Proof. exact (MK_COMB (@lem2604939) (@lem2604938)). Qed.
Lemma lem2604941 : term258 = term262.
Proof. exact (MK_COMB (@lem2604940) (@lem2604935)). Qed.
Lemma lem2604942 : term263.
Proof. exact (@lem1980255 term160 term63 term63 term63). Qed.
Lemma lem2604944 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2604945 : term258 = term265.
Proof. exact (@lem2604944 (NUMERAL 0) term64). Qed.
Lemma lem2604946 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2604947 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2604948 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2604947 h1) (fun h1 : term265 = True => @lem2604946)). Qed.
Lemma lem2604949 : term265 = True.
Proof. exact (EQ_MP (@lem2604948) (@lem2604946)). Qed.
Lemma lem2604950 : term258 = True.
Proof. exact (TRANS (@lem2604945) (@lem2604949)). Qed.
Lemma lem2604951 : True = term258.
Proof. exact (SYM (@lem2604950)). Qed.
Lemma lem2604952 : term258.
Proof. exact (EQ_MP (@lem2604951) (@lem0)). Qed.
Lemma lem2604953 : term267.
Proof. exact (@lem2604942 (@lem2604952)). Qed.
Lemma lem2604955 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2604956 : term258 = term265.
Proof. exact (@lem2604955 (NUMERAL 0) term64). Qed.
Lemma lem2604957 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2604958 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2604959 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2604958 h1) (fun h1 : term265 = True => @lem2604957)). Qed.
Lemma lem2604960 : term265 = True.
Proof. exact (EQ_MP (@lem2604959) (@lem2604957)). Qed.
Lemma lem2604961 : term258 = True.
Proof. exact (TRANS (@lem2604956) (@lem2604960)). Qed.
Lemma lem2604962 : True = term258.
Proof. exact (SYM (@lem2604961)). Qed.
Lemma lem2604963 : term258.
Proof. exact (EQ_MP (@lem2604962) (@lem0)). Qed.
Lemma lem2604964 : term262 = term268.
Proof. exact (@lem2604953 (@lem2604963)). Qed.
Lemma lem2604966 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2604967 : term144 = term145.
Proof. exact (@lem2604966 term64 term64). Qed.
Lemma lem2604968 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2604969 : term147 = term64.
Proof. exact (EQ_MP (@lem2604968) (@lem940073)). Qed.
Lemma lem2604970 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2604971 : term145 = term63.
Proof. exact (MK_COMB (@lem2604970) (@lem2604969)). Qed.
Lemma lem2604972 : term144 = term63.
Proof. exact (TRANS (@lem2604967) (@lem2604971)). Qed.
Lemma lem2604974 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2604975 : term270 = term160.
Proof. exact (@lem2604974 term64). Qed.
Lemma lem2604976 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2604977 : term271 = term260.
Proof. exact (MK_COMB (@lem2604976) (@lem2604975)). Qed.
Lemma lem2604978 : term268 = term258.
Proof. exact (MK_COMB (@lem2604977) (@lem2604972)). Qed.
Lemma lem2604980 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2604981 : term258 = term265.
Proof. exact (@lem2604980 (NUMERAL 0) term64). Qed.
Lemma lem2604982 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2604983 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2604984 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2604983 h1) (fun h1 : term265 = True => @lem2604982)). Qed.
Lemma lem2604985 : term265 = True.
Proof. exact (EQ_MP (@lem2604984) (@lem2604982)). Qed.
Lemma lem2604986 : term258 = True.
Proof. exact (TRANS (@lem2604981) (@lem2604985)). Qed.
Lemma lem2604987 : term268 = True.
Proof. exact (TRANS (@lem2604978) (@lem2604986)). Qed.
Lemma lem2604988 : term262 = True.
Proof. exact (TRANS (@lem2604964) (@lem2604987)). Qed.
Lemma lem2604989 : term258 = True.
Proof. exact (TRANS (@lem2604941) (@lem2604988)). Qed.
Lemma lem2604990 : term257 = True.
Proof. exact (TRANS (@lem2604932) (@lem2604989)). Qed.
Lemma lem2604991 : True = term257.
Proof. exact (SYM (@lem2604990)). Qed.
Lemma lem2604992 : term257.
Proof. exact (EQ_MP (@lem2604991) (@lem0)). Qed.
Lemma lem2604993 (a : int) (b : int) (h1 : term470 a b) : term475 a b.
Proof. exact (conj (@lem2604992) (@lem2604929 a b h1)). Qed.
Lemma lem2604995 (x : real) (y : real) : term273 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2604996 (a : int) (b : int) : term476 a b.
Proof. exact (@lem2604995 term63 (term55 a b)). Qed.
Lemma lem2604997 (a : int) (b : int) (h1 : term470 a b) : term477 a b.
Proof. exact (@lem2604996 a b (@lem2604993 a b h1)). Qed.
Lemma lem2604998 (a : int) (b : int) : (term478 a b) = (term55 a b).
Proof. exact (@lem1982733 (term55 a b)). Qed.
Lemma lem2604999 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2605000 (a : int) (b : int) : (term479 a b) = (term459 a b).
Proof. exact (MK_COMB (@lem2604999) (@lem2604998 a b)). Qed.
Lemma lem2605001 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2605002 (a : int) (b : int) : (term477 a b) = (term460 a b).
Proof. exact (MK_COMB (@lem2605000 a b) (@lem2605001)). Qed.
Lemma lem2605003 (a : int) (b : int) (h1 : term470 a b) : term460 a b.
Proof. exact (EQ_MP (@lem2605002 a b) (@lem2604997 a b h1)). Qed.
Lemma lem2605005 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2605006 : term257 = term258.
Proof. exact (@lem2605005 term160 term63). Qed.
Lemma lem2605008 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2605009 : term63 = term151.
Proof. exact (@lem2605008 term64). Qed.
Lemma lem2605011 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2605012 : term160 = term259.
Proof. exact (@lem2605011 (NUMERAL 0)). Qed.
Lemma lem2605013 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2605014 : term260 = term261.
Proof. exact (MK_COMB (@lem2605013) (@lem2605012)). Qed.
Lemma lem2605015 : term258 = term262.
Proof. exact (MK_COMB (@lem2605014) (@lem2605009)). Qed.
Lemma lem2605016 : term263.
Proof. exact (@lem1980255 term160 term63 term63 term63). Qed.
Lemma lem2605018 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2605019 : term258 = term265.
Proof. exact (@lem2605018 (NUMERAL 0) term64). Qed.
Lemma lem2605020 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2605021 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2605022 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2605021 h1) (fun h1 : term265 = True => @lem2605020)). Qed.
Lemma lem2605023 : term265 = True.
Proof. exact (EQ_MP (@lem2605022) (@lem2605020)). Qed.
Lemma lem2605024 : term258 = True.
Proof. exact (TRANS (@lem2605019) (@lem2605023)). Qed.
Lemma lem2605025 : True = term258.
Proof. exact (SYM (@lem2605024)). Qed.
Lemma lem2605026 : term258.
Proof. exact (EQ_MP (@lem2605025) (@lem0)). Qed.
Lemma lem2605027 : term267.
Proof. exact (@lem2605016 (@lem2605026)). Qed.
Lemma lem2605029 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2605030 : term258 = term265.
Proof. exact (@lem2605029 (NUMERAL 0) term64). Qed.
Lemma lem2605031 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2605032 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2605033 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2605032 h1) (fun h1 : term265 = True => @lem2605031)). Qed.
Lemma lem2605034 : term265 = True.
Proof. exact (EQ_MP (@lem2605033) (@lem2605031)). Qed.
Lemma lem2605035 : term258 = True.
Proof. exact (TRANS (@lem2605030) (@lem2605034)). Qed.
Lemma lem2605036 : True = term258.
Proof. exact (SYM (@lem2605035)). Qed.
Lemma lem2605037 : term258.
Proof. exact (EQ_MP (@lem2605036) (@lem0)). Qed.
Lemma lem2605038 : term262 = term268.
Proof. exact (@lem2605027 (@lem2605037)). Qed.
Lemma lem2605040 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2605041 : term144 = term145.
Proof. exact (@lem2605040 term64 term64). Qed.
Lemma lem2605042 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2605043 : term147 = term64.
Proof. exact (EQ_MP (@lem2605042) (@lem940073)). Qed.
Lemma lem2605044 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2605045 : term145 = term63.
Proof. exact (MK_COMB (@lem2605044) (@lem2605043)). Qed.
Lemma lem2605046 : term144 = term63.
Proof. exact (TRANS (@lem2605041) (@lem2605045)). Qed.
Lemma lem2605048 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2605049 : term270 = term160.
Proof. exact (@lem2605048 term64). Qed.
Lemma lem2605050 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2605051 : term271 = term260.
Proof. exact (MK_COMB (@lem2605050) (@lem2605049)). Qed.
Lemma lem2605052 : term268 = term258.
Proof. exact (MK_COMB (@lem2605051) (@lem2605046)). Qed.
Lemma lem2605054 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2605055 : term258 = term265.
Proof. exact (@lem2605054 (NUMERAL 0) term64). Qed.
Lemma lem2605056 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2605057 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2605058 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2605057 h1) (fun h1 : term265 = True => @lem2605056)). Qed.
Lemma lem2605059 : term265 = True.
Proof. exact (EQ_MP (@lem2605058) (@lem2605056)). Qed.
Lemma lem2605060 : term258 = True.
Proof. exact (TRANS (@lem2605055) (@lem2605059)). Qed.
Lemma lem2605061 : term268 = True.
Proof. exact (TRANS (@lem2605052) (@lem2605060)). Qed.
Lemma lem2605062 : term262 = True.
Proof. exact (TRANS (@lem2605038) (@lem2605061)). Qed.
Lemma lem2605063 : term258 = True.
Proof. exact (TRANS (@lem2605015) (@lem2605062)). Qed.
Lemma lem2605064 : term257 = True.
Proof. exact (TRANS (@lem2605006) (@lem2605063)). Qed.
Lemma lem2605065 : True = term257.
Proof. exact (SYM (@lem2605064)). Qed.
Lemma lem2605066 : term257.
Proof. exact (EQ_MP (@lem2605065) (@lem0)). Qed.
Lemma lem2605067 (a : int) (b : int) (h1 : term470 a b) : term480 a b.
Proof. exact (conj (@lem2605066) (@lem2604928 a b h1)). Qed.
Lemma lem2605069 (x : real) (y : real) : term273 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2605070 (a : int) (b : int) : term481 a b.
Proof. exact (@lem2605069 term63 (term465 a b)). Qed.
Lemma lem2605071 (a : int) (b : int) (h1 : term470 a b) : term482 a b.
Proof. exact (@lem2605070 a b (@lem2605067 a b h1)). Qed.
Lemma lem2605072 (a : int) (b : int) : (term483 a b) = (term465 a b).
Proof. exact (@lem1982733 (term465 a b)). Qed.
Lemma lem2605073 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2605074 (a : int) (b : int) : (term484 a b) = (term467 a b).
Proof. exact (MK_COMB (@lem2605073) (@lem2605072 a b)). Qed.
Lemma lem2605075 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2605076 (a : int) (b : int) : (term482 a b) = (term468 a b).
Proof. exact (MK_COMB (@lem2605074 a b) (@lem2605075)). Qed.
Lemma lem2605077 (a : int) (b : int) (h1 : term470 a b) : term468 a b.
Proof. exact (EQ_MP (@lem2605076 a b) (@lem2605071 a b h1)). Qed.
Lemma lem2605078 (a : int) (b : int) (h1 : term470 a b) : term472 a b.
Proof. exact (conj (@lem2605077 a b h1) (@lem2605003 a b h1)). Qed.
Lemma lem2605080 (x : real) (y : real) : term361 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2605081 (a : int) (b : int) : term485 a b.
Proof. exact (@lem2605080 (term465 a b) (term55 a b)). Qed.
Lemma lem2605082 (a : int) (b : int) (h1 : term470 a b) : term486 a b.
Proof. exact (@lem2605081 a b (@lem2605078 a b h1)). Qed.
Lemma lem2605083 (a : int) (b : int) : (term487 a b) = (term488 a b).
Proof. exact (@lem1982753 (term124 a) (real_of_int a) (term200 b) (real_of_int b)). Qed.
Lemma lem2605084 (a : int) : (term314 a) = (term315 a).
Proof. exact (@lem1982713 term127 (real_of_int a)). Qed.
Lemma lem2605086 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2605087 : term63 = term151.
Proof. exact (@lem2605086 term64). Qed.
Lemma lem2605089 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2605090 : term127 = term137.
Proof. exact (@lem2605089 term64). Qed.
Lemma lem2605091 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2605092 : term293 = term294.
Proof. exact (MK_COMB (@lem2605091) (@lem2605090)). Qed.
Lemma lem2605093 : term295 = term296.
Proof. exact (MK_COMB (@lem2605092) (@lem2605087)). Qed.
Lemma lem2605094 : term297.
Proof. exact (@lem1981473 term127 term63 term63 term63 term160 term63). Qed.
Lemma lem2605096 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2605097 : term258 = term265.
Proof. exact (@lem2605096 (NUMERAL 0) term64). Qed.
Lemma lem2605098 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2605099 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2605100 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2605099 h1) (fun h1 : term265 = True => @lem2605098)). Qed.
Lemma lem2605101 : term265 = True.
Proof. exact (EQ_MP (@lem2605100) (@lem2605098)). Qed.
Lemma lem2605102 : term258 = True.
Proof. exact (TRANS (@lem2605097) (@lem2605101)). Qed.
Lemma lem2605103 : True = term258.
Proof. exact (SYM (@lem2605102)). Qed.
Lemma lem2605104 : term258.
Proof. exact (EQ_MP (@lem2605103) (@lem0)). Qed.
Lemma lem2605105 : term298.
Proof. exact (@lem2605094 (@lem2605104)). Qed.
Lemma lem2605107 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2605108 : term258 = term265.
Proof. exact (@lem2605107 (NUMERAL 0) term64). Qed.
Lemma lem2605109 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2605110 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2605111 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2605110 h1) (fun h1 : term265 = True => @lem2605109)). Qed.
Lemma lem2605112 : term265 = True.
Proof. exact (EQ_MP (@lem2605111) (@lem2605109)). Qed.
Lemma lem2605113 : term258 = True.
Proof. exact (TRANS (@lem2605108) (@lem2605112)). Qed.
Lemma lem2605114 : True = term258.
Proof. exact (SYM (@lem2605113)). Qed.
Lemma lem2605115 : term258.
Proof. exact (EQ_MP (@lem2605114) (@lem0)). Qed.
Lemma lem2605116 : term299.
Proof. exact (@lem2605105 (@lem2605115)). Qed.
Lemma lem2605118 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2605119 : term258 = term265.
Proof. exact (@lem2605118 (NUMERAL 0) term64). Qed.
Lemma lem2605120 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2605121 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2605122 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2605121 h1) (fun h1 : term265 = True => @lem2605120)). Qed.
Lemma lem2605123 : term265 = True.
Proof. exact (EQ_MP (@lem2605122) (@lem2605120)). Qed.
Lemma lem2605124 : term258 = True.
Proof. exact (TRANS (@lem2605119) (@lem2605123)). Qed.
Lemma lem2605125 : True = term258.
Proof. exact (SYM (@lem2605124)). Qed.
Lemma lem2605126 : term258.
Proof. exact (EQ_MP (@lem2605125) (@lem0)). Qed.
Lemma lem2605127 : term300.
Proof. exact (@lem2605116 (@lem2605126)). Qed.
Lemma lem2605129 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2605130 : term144 = term145.
Proof. exact (@lem2605129 term64 term64). Qed.
Lemma lem2605131 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2605132 : term147 = term64.
Proof. exact (EQ_MP (@lem2605131) (@lem940073)). Qed.
Lemma lem2605133 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2605134 : term145 = term63.
Proof. exact (MK_COMB (@lem2605133) (@lem2605132)). Qed.
Lemma lem2605135 : term144 = term63.
Proof. exact (TRANS (@lem2605130) (@lem2605134)). Qed.
Lemma lem2605137 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2605138 : term172 = term177.
Proof. exact (@lem2605137 term64 term64). Qed.
Lemma lem2605139 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2605140 : term147 = term64.
Proof. exact (EQ_MP (@lem2605139) (@lem940073)). Qed.
Lemma lem2605141 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2605142 : term145 = term63.
Proof. exact (MK_COMB (@lem2605141) (@lem2605140)). Qed.
Lemma lem2605143 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2605144 : term177 = term127.
Proof. exact (MK_COMB (@lem2605143) (@lem2605142)). Qed.
Lemma lem2605145 : term172 = term127.
Proof. exact (TRANS (@lem2605138) (@lem2605144)). Qed.
Lemma lem2605146 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2605147 : term301 = term293.
Proof. exact (MK_COMB (@lem2605146) (@lem2605145)). Qed.
Lemma lem2605148 : term302 = term295.
Proof. exact (MK_COMB (@lem2605147) (@lem2605135)). Qed.
Lemma lem2605150 (m : nat) : (term303 m) = term160.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2605151 : term295 = term160.
Proof. exact (@lem2605150 term64). Qed.
Lemma lem2605152 : term302 = term160.
Proof. exact (TRANS (@lem2605148) (@lem2605151)). Qed.
Lemma lem2605153 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2605154 : term304 = term305.
Proof. exact (MK_COMB (@lem2605153) (@lem2605152)). Qed.
Lemma lem2605155 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2605156 : term306 = term270.
Proof. exact (MK_COMB (@lem2605154) (@lem2605155)). Qed.
Lemma lem2605158 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2605159 : term270 = term160.
Proof. exact (@lem2605158 term64). Qed.
Lemma lem2605160 : term306 = term160.
Proof. exact (TRANS (@lem2605156) (@lem2605159)). Qed.
Lemma lem2605162 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2605163 : term144 = term145.
Proof. exact (@lem2605162 term64 term64). Qed.
Lemma lem2605164 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2605165 : term147 = term64.
Proof. exact (EQ_MP (@lem2605164) (@lem940073)). Qed.
Lemma lem2605166 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2605167 : term145 = term63.
Proof. exact (MK_COMB (@lem2605166) (@lem2605165)). Qed.
Lemma lem2605168 : term144 = term63.
Proof. exact (TRANS (@lem2605163) (@lem2605167)). Qed.
Lemma lem2605169 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem2605170 : term307 = term270.
Proof. exact (MK_COMB (@lem2605169) (@lem2605168)). Qed.
Lemma lem2605172 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2605173 : term270 = term160.
Proof. exact (@lem2605172 term64). Qed.
Lemma lem2605174 : term307 = term160.
Proof. exact (TRANS (@lem2605170) (@lem2605173)). Qed.
Lemma lem2605175 : term160 = term307.
Proof. exact (SYM (@lem2605174)). Qed.
Lemma lem2605176 : term306 = term307.
Proof. exact (TRANS (@lem2605160) (@lem2605175)). Qed.
Lemma lem2605177 : term296 = term259.
Proof. exact (@lem2605127 (@lem2605176)). Qed.
Lemma lem2605178 : term295 = term259.
Proof. exact (TRANS (@lem2605093) (@lem2605177)). Qed.
Lemma lem2605180 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2605181 : term259 = term160.
Proof. exact (@lem2605180 term160). Qed.
Lemma lem2605182 : term295 = term160.
Proof. exact (TRANS (@lem2605178) (@lem2605181)). Qed.
Lemma lem2605183 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2605184 : term308 = term305.
Proof. exact (MK_COMB (@lem2605183) (@lem2605182)). Qed.
Lemma lem2605185 (a : int) : (real_of_int a) = (real_of_int a).
Proof. exact (eq_refl (real_of_int a)). Qed.
Lemma lem2605186 (a : int) : (term315 a) = (term316 a).
Proof. exact (MK_COMB (@lem2605184) (@lem2605185 a)). Qed.
Lemma lem2605187 (a : int) : (term314 a) = (term316 a).
Proof. exact (TRANS (@lem2605084 a) (@lem2605186 a)). Qed.
Lemma lem2605188 (a : int) : (term316 a) = term160.
Proof. exact (@lem1982719 (real_of_int a)). Qed.
Lemma lem2605189 (a : int) : (term314 a) = term160.
Proof. exact (TRANS (@lem2605187 a) (@lem2605188 a)). Qed.
Lemma lem2605190 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2605191 (a : int) : (term317 a) = term311.
Proof. exact (MK_COMB (@lem2605190) (@lem2605189 a)). Qed.
Lemma lem2605192 (b : int) : (term366 b) = (term313 b).
Proof. exact (@lem1982759 (term124 b) (real_of_int b) term127). Qed.
Lemma lem2605193 (b : int) : (term314 b) = (term315 b).
Proof. exact (@lem1982713 term127 (real_of_int b)). Qed.
Lemma lem2605195 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2605196 : term63 = term151.
Proof. exact (@lem2605195 term64). Qed.
Lemma lem2605198 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2605199 : term127 = term137.
Proof. exact (@lem2605198 term64). Qed.
Lemma lem2605200 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2605201 : term293 = term294.
Proof. exact (MK_COMB (@lem2605200) (@lem2605199)). Qed.
Lemma lem2605202 : term295 = term296.
Proof. exact (MK_COMB (@lem2605201) (@lem2605196)). Qed.
Lemma lem2605203 : term297.
Proof. exact (@lem1981473 term127 term63 term63 term63 term160 term63). Qed.
Lemma lem2605205 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2605206 : term258 = term265.
Proof. exact (@lem2605205 (NUMERAL 0) term64). Qed.
Lemma lem2605207 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2605208 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2605209 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2605208 h1) (fun h1 : term265 = True => @lem2605207)). Qed.
Lemma lem2605210 : term265 = True.
Proof. exact (EQ_MP (@lem2605209) (@lem2605207)). Qed.
Lemma lem2605211 : term258 = True.
Proof. exact (TRANS (@lem2605206) (@lem2605210)). Qed.
Lemma lem2605212 : True = term258.
Proof. exact (SYM (@lem2605211)). Qed.
Lemma lem2605213 : term258.
Proof. exact (EQ_MP (@lem2605212) (@lem0)). Qed.
Lemma lem2605214 : term298.
Proof. exact (@lem2605203 (@lem2605213)). Qed.
Lemma lem2605216 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2605217 : term258 = term265.
Proof. exact (@lem2605216 (NUMERAL 0) term64). Qed.
Lemma lem2605218 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2605219 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2605220 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2605219 h1) (fun h1 : term265 = True => @lem2605218)). Qed.
Lemma lem2605221 : term265 = True.
Proof. exact (EQ_MP (@lem2605220) (@lem2605218)). Qed.
Lemma lem2605222 : term258 = True.
Proof. exact (TRANS (@lem2605217) (@lem2605221)). Qed.
Lemma lem2605223 : True = term258.
Proof. exact (SYM (@lem2605222)). Qed.
Lemma lem2605224 : term258.
Proof. exact (EQ_MP (@lem2605223) (@lem0)). Qed.
Lemma lem2605225 : term299.
Proof. exact (@lem2605214 (@lem2605224)). Qed.
Lemma lem2605227 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2605228 : term258 = term265.
Proof. exact (@lem2605227 (NUMERAL 0) term64). Qed.
Lemma lem2605229 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2605230 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2605231 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2605230 h1) (fun h1 : term265 = True => @lem2605229)). Qed.
Lemma lem2605232 : term265 = True.
Proof. exact (EQ_MP (@lem2605231) (@lem2605229)). Qed.
Lemma lem2605233 : term258 = True.
Proof. exact (TRANS (@lem2605228) (@lem2605232)). Qed.
Lemma lem2605234 : True = term258.
Proof. exact (SYM (@lem2605233)). Qed.
Lemma lem2605235 : term258.
Proof. exact (EQ_MP (@lem2605234) (@lem0)). Qed.
Lemma lem2605236 : term300.
Proof. exact (@lem2605225 (@lem2605235)). Qed.
Lemma lem2605238 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2605239 : term144 = term145.
Proof. exact (@lem2605238 term64 term64). Qed.
Lemma lem2605240 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2605241 : term147 = term64.
Proof. exact (EQ_MP (@lem2605240) (@lem940073)). Qed.
Lemma lem2605242 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2605243 : term145 = term63.
Proof. exact (MK_COMB (@lem2605242) (@lem2605241)). Qed.
Lemma lem2605244 : term144 = term63.
Proof. exact (TRANS (@lem2605239) (@lem2605243)). Qed.
Lemma lem2605246 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2605247 : term172 = term177.
Proof. exact (@lem2605246 term64 term64). Qed.
Lemma lem2605248 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2605249 : term147 = term64.
Proof. exact (EQ_MP (@lem2605248) (@lem940073)). Qed.
Lemma lem2605250 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2605251 : term145 = term63.
Proof. exact (MK_COMB (@lem2605250) (@lem2605249)). Qed.
Lemma lem2605252 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2605253 : term177 = term127.
Proof. exact (MK_COMB (@lem2605252) (@lem2605251)). Qed.
Lemma lem2605254 : term172 = term127.
Proof. exact (TRANS (@lem2605247) (@lem2605253)). Qed.
Lemma lem2605255 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2605256 : term301 = term293.
Proof. exact (MK_COMB (@lem2605255) (@lem2605254)). Qed.
Lemma lem2605257 : term302 = term295.
Proof. exact (MK_COMB (@lem2605256) (@lem2605244)). Qed.
Lemma lem2605259 (m : nat) : (term303 m) = term160.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2605260 : term295 = term160.
Proof. exact (@lem2605259 term64). Qed.
Lemma lem2605261 : term302 = term160.
Proof. exact (TRANS (@lem2605257) (@lem2605260)). Qed.
Lemma lem2605262 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2605263 : term304 = term305.
Proof. exact (MK_COMB (@lem2605262) (@lem2605261)). Qed.
Lemma lem2605264 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2605265 : term306 = term270.
Proof. exact (MK_COMB (@lem2605263) (@lem2605264)). Qed.
Lemma lem2605267 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2605268 : term270 = term160.
Proof. exact (@lem2605267 term64). Qed.
Lemma lem2605269 : term306 = term160.
Proof. exact (TRANS (@lem2605265) (@lem2605268)). Qed.
Lemma lem2605271 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2605272 : term144 = term145.
Proof. exact (@lem2605271 term64 term64). Qed.
Lemma lem2605273 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2605274 : term147 = term64.
Proof. exact (EQ_MP (@lem2605273) (@lem940073)). Qed.
Lemma lem2605275 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2605276 : term145 = term63.
Proof. exact (MK_COMB (@lem2605275) (@lem2605274)). Qed.
Lemma lem2605277 : term144 = term63.
Proof. exact (TRANS (@lem2605272) (@lem2605276)). Qed.
Lemma lem2605278 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem2605279 : term307 = term270.
Proof. exact (MK_COMB (@lem2605278) (@lem2605277)). Qed.
Lemma lem2605281 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2605282 : term270 = term160.
Proof. exact (@lem2605281 term64). Qed.
Lemma lem2605283 : term307 = term160.
Proof. exact (TRANS (@lem2605279) (@lem2605282)). Qed.
Lemma lem2605284 : term160 = term307.
Proof. exact (SYM (@lem2605283)). Qed.
Lemma lem2605285 : term306 = term307.
Proof. exact (TRANS (@lem2605269) (@lem2605284)). Qed.
Lemma lem2605286 : term296 = term259.
Proof. exact (@lem2605236 (@lem2605285)). Qed.
Lemma lem2605287 : term295 = term259.
Proof. exact (TRANS (@lem2605202) (@lem2605286)). Qed.
Lemma lem2605289 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2605290 : term259 = term160.
Proof. exact (@lem2605289 term160). Qed.
Lemma lem2605291 : term295 = term160.
Proof. exact (TRANS (@lem2605287) (@lem2605290)). Qed.
Lemma lem2605292 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2605293 : term308 = term305.
Proof. exact (MK_COMB (@lem2605292) (@lem2605291)). Qed.
Lemma lem2605294 (b : int) : (real_of_int b) = (real_of_int b).
Proof. exact (eq_refl (real_of_int b)). Qed.
Lemma lem2605295 (b : int) : (term315 b) = (term316 b).
Proof. exact (MK_COMB (@lem2605293) (@lem2605294 b)). Qed.
Lemma lem2605296 (b : int) : (term314 b) = (term316 b).
Proof. exact (TRANS (@lem2605193 b) (@lem2605295 b)). Qed.
Lemma lem2605297 (b : int) : (term316 b) = term160.
Proof. exact (@lem1982719 (real_of_int b)). Qed.
Lemma lem2605298 (b : int) : (term314 b) = term160.
Proof. exact (TRANS (@lem2605296 b) (@lem2605297 b)). Qed.
Lemma lem2605299 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2605300 (b : int) : (term317 b) = term311.
Proof. exact (MK_COMB (@lem2605299) (@lem2605298 b)). Qed.
Lemma lem2605301 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem2605302 (b : int) : (term313 b) = term318.
Proof. exact (MK_COMB (@lem2605300 b) (@lem2605301)). Qed.
Lemma lem2605303 (b : int) : (term366 b) = term318.
Proof. exact (TRANS (@lem2605192 b) (@lem2605302 b)). Qed.
Lemma lem2605304 : term318 = term127.
Proof. exact (@lem1982721 term127). Qed.
Lemma lem2605305 (b : int) : (term366 b) = term127.
Proof. exact (TRANS (@lem2605303 b) (@lem2605304)). Qed.
Lemma lem2605306 (a : int) (b : int) : (term488 a b) = term318.
Proof. exact (MK_COMB (@lem2605191 a) (@lem2605305 b)). Qed.
Lemma lem2605307 (a : int) (b : int) : (term487 a b) = term318.
Proof. exact (TRANS (@lem2605083 a b) (@lem2605306 a b)). Qed.
Lemma lem2605308 : term318 = term127.
Proof. exact (@lem1982721 term127). Qed.
Lemma lem2605309 (a : int) (b : int) : (term487 a b) = term127.
Proof. exact (TRANS (@lem2605307 a b) (@lem2605308)). Qed.
Lemma lem2605310 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2605311 (a : int) (b : int) : (term489 a b) = term320.
Proof. exact (MK_COMB (@lem2605310) (@lem2605309 a b)). Qed.
Lemma lem2605312 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2605313 (a : int) (b : int) : (term486 a b) = term321.
Proof. exact (MK_COMB (@lem2605311 a b) (@lem2605312)). Qed.
Lemma lem2605314 (a : int) (b : int) (h1 : term470 a b) : term321.
Proof. exact (EQ_MP (@lem2605313 a b) (@lem2605082 a b h1)). Qed.
Lemma lem2605316 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2605317 : term321 = term322.
Proof. exact (@lem2605316 term160 term127). Qed.
Lemma lem2605319 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2605320 : term127 = term137.
Proof. exact (@lem2605319 term64). Qed.
Lemma lem2605322 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2605323 : term160 = term259.
Proof. exact (@lem2605322 (NUMERAL 0)). Qed.
Lemma lem2605324 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2605325 : term323 = term324.
Proof. exact (MK_COMB (@lem2605324) (@lem2605323)). Qed.
Lemma lem2605326 : term322 = term325.
Proof. exact (MK_COMB (@lem2605325) (@lem2605320)). Qed.
Lemma lem2605327 : term326.
Proof. exact (@lem1980026 term160 term63 term127 term63). Qed.
Lemma lem2605329 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2605330 : term258 = term265.
Proof. exact (@lem2605329 (NUMERAL 0) term64). Qed.
Lemma lem2605331 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2605332 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2605333 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2605332 h1) (fun h1 : term265 = True => @lem2605331)). Qed.
Lemma lem2605334 : term265 = True.
Proof. exact (EQ_MP (@lem2605333) (@lem2605331)). Qed.
Lemma lem2605335 : term258 = True.
Proof. exact (TRANS (@lem2605330) (@lem2605334)). Qed.
Lemma lem2605336 : True = term258.
Proof. exact (SYM (@lem2605335)). Qed.
Lemma lem2605337 : term258.
Proof. exact (EQ_MP (@lem2605336) (@lem0)). Qed.
Lemma lem2605338 : term327.
Proof. exact (@lem2605327 (@lem2605337)). Qed.
Lemma lem2605340 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2605341 : term258 = term265.
Proof. exact (@lem2605340 (NUMERAL 0) term64). Qed.
Lemma lem2605342 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2605343 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2605344 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2605343 h1) (fun h1 : term265 = True => @lem2605342)). Qed.
Lemma lem2605345 : term265 = True.
Proof. exact (EQ_MP (@lem2605344) (@lem2605342)). Qed.
Lemma lem2605346 : term258 = True.
Proof. exact (TRANS (@lem2605341) (@lem2605345)). Qed.
Lemma lem2605347 : True = term258.
Proof. exact (SYM (@lem2605346)). Qed.
Lemma lem2605348 : term258.
Proof. exact (EQ_MP (@lem2605347) (@lem0)). Qed.
Lemma lem2605349 : term325 = term328.
Proof. exact (@lem2605338 (@lem2605348)). Qed.
Lemma lem2605351 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2605352 : term172 = term177.
Proof. exact (@lem2605351 term64 term64). Qed.
Lemma lem2605353 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2605354 : term147 = term64.
Proof. exact (EQ_MP (@lem2605353) (@lem940073)). Qed.
Lemma lem2605355 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2605356 : term145 = term63.
Proof. exact (MK_COMB (@lem2605355) (@lem2605354)). Qed.
Lemma lem2605357 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2605358 : term177 = term127.
Proof. exact (MK_COMB (@lem2605357) (@lem2605356)). Qed.
Lemma lem2605359 : term172 = term127.
Proof. exact (TRANS (@lem2605352) (@lem2605358)). Qed.
Lemma lem2605361 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2605362 : term270 = term160.
Proof. exact (@lem2605361 term64). Qed.
Lemma lem2605363 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2605364 : term329 = term323.
Proof. exact (MK_COMB (@lem2605363) (@lem2605362)). Qed.
Lemma lem2605365 : term328 = term322.
Proof. exact (MK_COMB (@lem2605364) (@lem2605359)). Qed.
Lemma lem2605367 (m : nat) (n : nat) : (term330 m n) = (term331 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2605368 : term322 = term332.
Proof. exact (@lem2605367 (NUMERAL 0) term64). Qed.
Lemma lem2605369 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2605370 (h1 : term266 = (BIT1 0)) : (term64 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2605371 : (term266 = (BIT1 0)) = ((term64 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2605370 h1) (fun h1 : (term64 = (NUMERAL 0)) = False => @lem2605369)). Qed.
Lemma lem2605372 : (term64 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2605371) (@lem2605369)). Qed.
Lemma lem2605373 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2605374 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2605375 : term333 = (and True).
Proof. exact (MK_COMB (@lem2605374) (@lem2605373)). Qed.
Lemma lem2605376 : term332 = (True /\ False).
Proof. exact (MK_COMB (@lem2605375) (@lem2605372)). Qed.
Lemma lem2605378 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2605379 : term332 = False.
Proof. exact (TRANS (@lem2605376) (@lem2605378)). Qed.
Lemma lem2605380 : term322 = False.
Proof. exact (TRANS (@lem2605368) (@lem2605379)). Qed.
Lemma lem2605381 : term328 = False.
Proof. exact (TRANS (@lem2605365) (@lem2605380)). Qed.
Lemma lem2605382 : term325 = False.
Proof. exact (TRANS (@lem2605349) (@lem2605381)). Qed.
Lemma lem2605383 : term322 = False.
Proof. exact (TRANS (@lem2605326) (@lem2605382)). Qed.
Lemma lem2605384 : term321 = False.
Proof. exact (TRANS (@lem2605317) (@lem2605383)). Qed.
Lemma lem2605385 (a : int) (b : int) (h1 : term470 a b) : False.
Proof. exact (EQ_MP (@lem2605384) (@lem2605314 a b h1)). Qed.
Lemma lem2605386 (a : int) (b : int) (h1 : term472 a b) : term472 a b.
Proof. exact (h1). Qed.
Lemma lem2605387 (a : int) (b : int) (h1 : term472 a b) : term460 a b.
Proof. exact (proj2 (@lem2605386 a b h1)). Qed.
Lemma lem2605388 (a : int) (b : int) (h1 : term472 a b) : term468 a b.
Proof. exact (proj1 (@lem2605386 a b h1)). Qed.
Lemma lem2605390 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2605391 : term257 = term258.
Proof. exact (@lem2605390 term160 term63). Qed.
Lemma lem2605393 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2605394 : term63 = term151.
Proof. exact (@lem2605393 term64). Qed.
Lemma lem2605396 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2605397 : term160 = term259.
Proof. exact (@lem2605396 (NUMERAL 0)). Qed.
Lemma lem2605398 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2605399 : term260 = term261.
Proof. exact (MK_COMB (@lem2605398) (@lem2605397)). Qed.
Lemma lem2605400 : term258 = term262.
Proof. exact (MK_COMB (@lem2605399) (@lem2605394)). Qed.
Lemma lem2605401 : term263.
Proof. exact (@lem1980255 term160 term63 term63 term63). Qed.
Lemma lem2605403 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2605404 : term258 = term265.
Proof. exact (@lem2605403 (NUMERAL 0) term64). Qed.
Lemma lem2605405 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2605406 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2605407 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2605406 h1) (fun h1 : term265 = True => @lem2605405)). Qed.
Lemma lem2605408 : term265 = True.
Proof. exact (EQ_MP (@lem2605407) (@lem2605405)). Qed.
Lemma lem2605409 : term258 = True.
Proof. exact (TRANS (@lem2605404) (@lem2605408)). Qed.
Lemma lem2605410 : True = term258.
Proof. exact (SYM (@lem2605409)). Qed.
Lemma lem2605411 : term258.
Proof. exact (EQ_MP (@lem2605410) (@lem0)). Qed.
Lemma lem2605412 : term267.
Proof. exact (@lem2605401 (@lem2605411)). Qed.
Lemma lem2605414 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2605415 : term258 = term265.
Proof. exact (@lem2605414 (NUMERAL 0) term64). Qed.
Lemma lem2605416 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2605417 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2605418 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2605417 h1) (fun h1 : term265 = True => @lem2605416)). Qed.
Lemma lem2605419 : term265 = True.
Proof. exact (EQ_MP (@lem2605418) (@lem2605416)). Qed.
Lemma lem2605420 : term258 = True.
Proof. exact (TRANS (@lem2605415) (@lem2605419)). Qed.
Lemma lem2605421 : True = term258.
Proof. exact (SYM (@lem2605420)). Qed.
Lemma lem2605422 : term258.
Proof. exact (EQ_MP (@lem2605421) (@lem0)). Qed.
Lemma lem2605423 : term262 = term268.
Proof. exact (@lem2605412 (@lem2605422)). Qed.
Lemma lem2605425 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2605426 : term144 = term145.
Proof. exact (@lem2605425 term64 term64). Qed.
Lemma lem2605427 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2605428 : term147 = term64.
Proof. exact (EQ_MP (@lem2605427) (@lem940073)). Qed.
Lemma lem2605429 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2605430 : term145 = term63.
Proof. exact (MK_COMB (@lem2605429) (@lem2605428)). Qed.
Lemma lem2605431 : term144 = term63.
Proof. exact (TRANS (@lem2605426) (@lem2605430)). Qed.
Lemma lem2605433 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2605434 : term270 = term160.
Proof. exact (@lem2605433 term64). Qed.
Lemma lem2605435 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2605436 : term271 = term260.
Proof. exact (MK_COMB (@lem2605435) (@lem2605434)). Qed.
Lemma lem2605437 : term268 = term258.
Proof. exact (MK_COMB (@lem2605436) (@lem2605431)). Qed.
Lemma lem2605439 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2605440 : term258 = term265.
Proof. exact (@lem2605439 (NUMERAL 0) term64). Qed.
Lemma lem2605441 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2605442 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2605443 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2605442 h1) (fun h1 : term265 = True => @lem2605441)). Qed.
Lemma lem2605444 : term265 = True.
Proof. exact (EQ_MP (@lem2605443) (@lem2605441)). Qed.
Lemma lem2605445 : term258 = True.
Proof. exact (TRANS (@lem2605440) (@lem2605444)). Qed.
Lemma lem2605446 : term268 = True.
Proof. exact (TRANS (@lem2605437) (@lem2605445)). Qed.
Lemma lem2605447 : term262 = True.
Proof. exact (TRANS (@lem2605423) (@lem2605446)). Qed.
Lemma lem2605448 : term258 = True.
Proof. exact (TRANS (@lem2605400) (@lem2605447)). Qed.
Lemma lem2605449 : term257 = True.
Proof. exact (TRANS (@lem2605391) (@lem2605448)). Qed.
Lemma lem2605450 : True = term257.
Proof. exact (SYM (@lem2605449)). Qed.
Lemma lem2605451 : term257.
Proof. exact (EQ_MP (@lem2605450) (@lem0)). Qed.
Lemma lem2605452 (a : int) (b : int) (h1 : term472 a b) : term475 a b.
Proof. exact (conj (@lem2605451) (@lem2605387 a b h1)). Qed.
Lemma lem2605454 (x : real) (y : real) : term273 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2605455 (a : int) (b : int) : term476 a b.
Proof. exact (@lem2605454 term63 (term55 a b)). Qed.
Lemma lem2605456 (a : int) (b : int) (h1 : term472 a b) : term477 a b.
Proof. exact (@lem2605455 a b (@lem2605452 a b h1)). Qed.
Lemma lem2605457 (a : int) (b : int) : (term478 a b) = (term55 a b).
Proof. exact (@lem1982733 (term55 a b)). Qed.
Lemma lem2605458 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2605459 (a : int) (b : int) : (term479 a b) = (term459 a b).
Proof. exact (MK_COMB (@lem2605458) (@lem2605457 a b)). Qed.
Lemma lem2605460 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2605461 (a : int) (b : int) : (term477 a b) = (term460 a b).
Proof. exact (MK_COMB (@lem2605459 a b) (@lem2605460)). Qed.
Lemma lem2605462 (a : int) (b : int) (h1 : term472 a b) : term460 a b.
Proof. exact (EQ_MP (@lem2605461 a b) (@lem2605456 a b h1)). Qed.
Lemma lem2605464 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2605465 : term257 = term258.
Proof. exact (@lem2605464 term160 term63). Qed.
Lemma lem2605467 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2605468 : term63 = term151.
Proof. exact (@lem2605467 term64). Qed.
Lemma lem2605470 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2605471 : term160 = term259.
Proof. exact (@lem2605470 (NUMERAL 0)). Qed.
Lemma lem2605472 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2605473 : term260 = term261.
Proof. exact (MK_COMB (@lem2605472) (@lem2605471)). Qed.
Lemma lem2605474 : term258 = term262.
Proof. exact (MK_COMB (@lem2605473) (@lem2605468)). Qed.
Lemma lem2605475 : term263.
Proof. exact (@lem1980255 term160 term63 term63 term63). Qed.
Lemma lem2605477 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2605478 : term258 = term265.
Proof. exact (@lem2605477 (NUMERAL 0) term64). Qed.
Lemma lem2605479 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2605480 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2605481 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2605480 h1) (fun h1 : term265 = True => @lem2605479)). Qed.
Lemma lem2605482 : term265 = True.
Proof. exact (EQ_MP (@lem2605481) (@lem2605479)). Qed.
Lemma lem2605483 : term258 = True.
Proof. exact (TRANS (@lem2605478) (@lem2605482)). Qed.
Lemma lem2605484 : True = term258.
Proof. exact (SYM (@lem2605483)). Qed.
Lemma lem2605485 : term258.
Proof. exact (EQ_MP (@lem2605484) (@lem0)). Qed.
Lemma lem2605486 : term267.
Proof. exact (@lem2605475 (@lem2605485)). Qed.
Lemma lem2605488 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2605489 : term258 = term265.
Proof. exact (@lem2605488 (NUMERAL 0) term64). Qed.
Lemma lem2605490 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2605491 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2605492 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2605491 h1) (fun h1 : term265 = True => @lem2605490)). Qed.
Lemma lem2605493 : term265 = True.
Proof. exact (EQ_MP (@lem2605492) (@lem2605490)). Qed.
Lemma lem2605494 : term258 = True.
Proof. exact (TRANS (@lem2605489) (@lem2605493)). Qed.
Lemma lem2605495 : True = term258.
Proof. exact (SYM (@lem2605494)). Qed.
Lemma lem2605496 : term258.
Proof. exact (EQ_MP (@lem2605495) (@lem0)). Qed.
Lemma lem2605497 : term262 = term268.
Proof. exact (@lem2605486 (@lem2605496)). Qed.
Lemma lem2605499 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2605500 : term144 = term145.
Proof. exact (@lem2605499 term64 term64). Qed.
Lemma lem2605501 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2605502 : term147 = term64.
Proof. exact (EQ_MP (@lem2605501) (@lem940073)). Qed.
Lemma lem2605503 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2605504 : term145 = term63.
Proof. exact (MK_COMB (@lem2605503) (@lem2605502)). Qed.
Lemma lem2605505 : term144 = term63.
Proof. exact (TRANS (@lem2605500) (@lem2605504)). Qed.
Lemma lem2605507 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2605508 : term270 = term160.
Proof. exact (@lem2605507 term64). Qed.
Lemma lem2605509 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2605510 : term271 = term260.
Proof. exact (MK_COMB (@lem2605509) (@lem2605508)). Qed.
Lemma lem2605511 : term268 = term258.
Proof. exact (MK_COMB (@lem2605510) (@lem2605505)). Qed.
Lemma lem2605513 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2605514 : term258 = term265.
Proof. exact (@lem2605513 (NUMERAL 0) term64). Qed.
Lemma lem2605515 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2605516 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2605517 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2605516 h1) (fun h1 : term265 = True => @lem2605515)). Qed.
Lemma lem2605518 : term265 = True.
Proof. exact (EQ_MP (@lem2605517) (@lem2605515)). Qed.
Lemma lem2605519 : term258 = True.
Proof. exact (TRANS (@lem2605514) (@lem2605518)). Qed.
Lemma lem2605520 : term268 = True.
Proof. exact (TRANS (@lem2605511) (@lem2605519)). Qed.
Lemma lem2605521 : term262 = True.
Proof. exact (TRANS (@lem2605497) (@lem2605520)). Qed.
Lemma lem2605522 : term258 = True.
Proof. exact (TRANS (@lem2605474) (@lem2605521)). Qed.
Lemma lem2605523 : term257 = True.
Proof. exact (TRANS (@lem2605465) (@lem2605522)). Qed.
Lemma lem2605524 : True = term257.
Proof. exact (SYM (@lem2605523)). Qed.
Lemma lem2605525 : term257.
Proof. exact (EQ_MP (@lem2605524) (@lem0)). Qed.
Lemma lem2605526 (a : int) (b : int) (h1 : term472 a b) : term480 a b.
Proof. exact (conj (@lem2605525) (@lem2605388 a b h1)). Qed.
Lemma lem2605528 (x : real) (y : real) : term273 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2605529 (a : int) (b : int) : term481 a b.
Proof. exact (@lem2605528 term63 (term465 a b)). Qed.
Lemma lem2605530 (a : int) (b : int) (h1 : term472 a b) : term482 a b.
Proof. exact (@lem2605529 a b (@lem2605526 a b h1)). Qed.
Lemma lem2605531 (a : int) (b : int) : (term483 a b) = (term465 a b).
Proof. exact (@lem1982733 (term465 a b)). Qed.
Lemma lem2605532 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2605533 (a : int) (b : int) : (term484 a b) = (term467 a b).
Proof. exact (MK_COMB (@lem2605532) (@lem2605531 a b)). Qed.
Lemma lem2605534 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2605535 (a : int) (b : int) : (term482 a b) = (term468 a b).
Proof. exact (MK_COMB (@lem2605533 a b) (@lem2605534)). Qed.
Lemma lem2605536 (a : int) (b : int) (h1 : term472 a b) : term468 a b.
Proof. exact (EQ_MP (@lem2605535 a b) (@lem2605530 a b h1)). Qed.
Lemma lem2605537 (a : int) (b : int) (h1 : term472 a b) : term472 a b.
Proof. exact (conj (@lem2605536 a b h1) (@lem2605462 a b h1)). Qed.
Lemma lem2605539 (x : real) (y : real) : term361 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2605540 (a : int) (b : int) : term485 a b.
Proof. exact (@lem2605539 (term465 a b) (term55 a b)). Qed.
Lemma lem2605541 (a : int) (b : int) (h1 : term472 a b) : term486 a b.
Proof. exact (@lem2605540 a b (@lem2605537 a b h1)). Qed.
Lemma lem2605542 (a : int) (b : int) : (term487 a b) = (term488 a b).
Proof. exact (@lem1982753 (term124 a) (real_of_int a) (term200 b) (real_of_int b)). Qed.
Lemma lem2605543 (a : int) : (term314 a) = (term315 a).
Proof. exact (@lem1982713 term127 (real_of_int a)). Qed.
Lemma lem2605545 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2605546 : term63 = term151.
Proof. exact (@lem2605545 term64). Qed.
Lemma lem2605548 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2605549 : term127 = term137.
Proof. exact (@lem2605548 term64). Qed.
Lemma lem2605550 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2605551 : term293 = term294.
Proof. exact (MK_COMB (@lem2605550) (@lem2605549)). Qed.
Lemma lem2605552 : term295 = term296.
Proof. exact (MK_COMB (@lem2605551) (@lem2605546)). Qed.
Lemma lem2605553 : term297.
Proof. exact (@lem1981473 term127 term63 term63 term63 term160 term63). Qed.
Lemma lem2605555 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2605556 : term258 = term265.
Proof. exact (@lem2605555 (NUMERAL 0) term64). Qed.
Lemma lem2605557 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2605558 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2605559 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2605558 h1) (fun h1 : term265 = True => @lem2605557)). Qed.
Lemma lem2605560 : term265 = True.
Proof. exact (EQ_MP (@lem2605559) (@lem2605557)). Qed.
Lemma lem2605561 : term258 = True.
Proof. exact (TRANS (@lem2605556) (@lem2605560)). Qed.
Lemma lem2605562 : True = term258.
Proof. exact (SYM (@lem2605561)). Qed.
Lemma lem2605563 : term258.
Proof. exact (EQ_MP (@lem2605562) (@lem0)). Qed.
Lemma lem2605564 : term298.
Proof. exact (@lem2605553 (@lem2605563)). Qed.
Lemma lem2605566 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2605567 : term258 = term265.
Proof. exact (@lem2605566 (NUMERAL 0) term64). Qed.
Lemma lem2605568 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2605569 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2605570 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2605569 h1) (fun h1 : term265 = True => @lem2605568)). Qed.
Lemma lem2605571 : term265 = True.
Proof. exact (EQ_MP (@lem2605570) (@lem2605568)). Qed.
Lemma lem2605572 : term258 = True.
Proof. exact (TRANS (@lem2605567) (@lem2605571)). Qed.
Lemma lem2605573 : True = term258.
Proof. exact (SYM (@lem2605572)). Qed.
Lemma lem2605574 : term258.
Proof. exact (EQ_MP (@lem2605573) (@lem0)). Qed.
Lemma lem2605575 : term299.
Proof. exact (@lem2605564 (@lem2605574)). Qed.
Lemma lem2605577 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2605578 : term258 = term265.
Proof. exact (@lem2605577 (NUMERAL 0) term64). Qed.
Lemma lem2605579 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2605580 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2605581 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2605580 h1) (fun h1 : term265 = True => @lem2605579)). Qed.
Lemma lem2605582 : term265 = True.
Proof. exact (EQ_MP (@lem2605581) (@lem2605579)). Qed.
Lemma lem2605583 : term258 = True.
Proof. exact (TRANS (@lem2605578) (@lem2605582)). Qed.
Lemma lem2605584 : True = term258.
Proof. exact (SYM (@lem2605583)). Qed.
Lemma lem2605585 : term258.
Proof. exact (EQ_MP (@lem2605584) (@lem0)). Qed.
Lemma lem2605586 : term300.
Proof. exact (@lem2605575 (@lem2605585)). Qed.
Lemma lem2605588 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2605589 : term144 = term145.
Proof. exact (@lem2605588 term64 term64). Qed.
Lemma lem2605590 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2605591 : term147 = term64.
Proof. exact (EQ_MP (@lem2605590) (@lem940073)). Qed.
Lemma lem2605592 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2605593 : term145 = term63.
Proof. exact (MK_COMB (@lem2605592) (@lem2605591)). Qed.
Lemma lem2605594 : term144 = term63.
Proof. exact (TRANS (@lem2605589) (@lem2605593)). Qed.
Lemma lem2605596 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2605597 : term172 = term177.
Proof. exact (@lem2605596 term64 term64). Qed.
Lemma lem2605598 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2605599 : term147 = term64.
Proof. exact (EQ_MP (@lem2605598) (@lem940073)). Qed.
Lemma lem2605600 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2605601 : term145 = term63.
Proof. exact (MK_COMB (@lem2605600) (@lem2605599)). Qed.
Lemma lem2605602 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2605603 : term177 = term127.
Proof. exact (MK_COMB (@lem2605602) (@lem2605601)). Qed.
Lemma lem2605604 : term172 = term127.
Proof. exact (TRANS (@lem2605597) (@lem2605603)). Qed.
Lemma lem2605605 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2605606 : term301 = term293.
Proof. exact (MK_COMB (@lem2605605) (@lem2605604)). Qed.
Lemma lem2605607 : term302 = term295.
Proof. exact (MK_COMB (@lem2605606) (@lem2605594)). Qed.
Lemma lem2605609 (m : nat) : (term303 m) = term160.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2605610 : term295 = term160.
Proof. exact (@lem2605609 term64). Qed.
Lemma lem2605611 : term302 = term160.
Proof. exact (TRANS (@lem2605607) (@lem2605610)). Qed.
Lemma lem2605612 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2605613 : term304 = term305.
Proof. exact (MK_COMB (@lem2605612) (@lem2605611)). Qed.
Lemma lem2605614 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2605615 : term306 = term270.
Proof. exact (MK_COMB (@lem2605613) (@lem2605614)). Qed.
Lemma lem2605617 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2605618 : term270 = term160.
Proof. exact (@lem2605617 term64). Qed.
Lemma lem2605619 : term306 = term160.
Proof. exact (TRANS (@lem2605615) (@lem2605618)). Qed.
Lemma lem2605621 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2605622 : term144 = term145.
Proof. exact (@lem2605621 term64 term64). Qed.
Lemma lem2605623 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2605624 : term147 = term64.
Proof. exact (EQ_MP (@lem2605623) (@lem940073)). Qed.
Lemma lem2605625 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2605626 : term145 = term63.
Proof. exact (MK_COMB (@lem2605625) (@lem2605624)). Qed.
Lemma lem2605627 : term144 = term63.
Proof. exact (TRANS (@lem2605622) (@lem2605626)). Qed.
Lemma lem2605628 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem2605629 : term307 = term270.
Proof. exact (MK_COMB (@lem2605628) (@lem2605627)). Qed.
Lemma lem2605631 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2605632 : term270 = term160.
Proof. exact (@lem2605631 term64). Qed.
Lemma lem2605633 : term307 = term160.
Proof. exact (TRANS (@lem2605629) (@lem2605632)). Qed.
Lemma lem2605634 : term160 = term307.
Proof. exact (SYM (@lem2605633)). Qed.
Lemma lem2605635 : term306 = term307.
Proof. exact (TRANS (@lem2605619) (@lem2605634)). Qed.
Lemma lem2605636 : term296 = term259.
Proof. exact (@lem2605586 (@lem2605635)). Qed.
Lemma lem2605637 : term295 = term259.
Proof. exact (TRANS (@lem2605552) (@lem2605636)). Qed.
Lemma lem2605639 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2605640 : term259 = term160.
Proof. exact (@lem2605639 term160). Qed.
Lemma lem2605641 : term295 = term160.
Proof. exact (TRANS (@lem2605637) (@lem2605640)). Qed.
Lemma lem2605642 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2605643 : term308 = term305.
Proof. exact (MK_COMB (@lem2605642) (@lem2605641)). Qed.
Lemma lem2605644 (a : int) : (real_of_int a) = (real_of_int a).
Proof. exact (eq_refl (real_of_int a)). Qed.
Lemma lem2605645 (a : int) : (term315 a) = (term316 a).
Proof. exact (MK_COMB (@lem2605643) (@lem2605644 a)). Qed.
Lemma lem2605646 (a : int) : (term314 a) = (term316 a).
Proof. exact (TRANS (@lem2605543 a) (@lem2605645 a)). Qed.
Lemma lem2605647 (a : int) : (term316 a) = term160.
Proof. exact (@lem1982719 (real_of_int a)). Qed.
Lemma lem2605648 (a : int) : (term314 a) = term160.
Proof. exact (TRANS (@lem2605646 a) (@lem2605647 a)). Qed.
Lemma lem2605649 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2605650 (a : int) : (term317 a) = term311.
Proof. exact (MK_COMB (@lem2605649) (@lem2605648 a)). Qed.
Lemma lem2605651 (b : int) : (term366 b) = (term313 b).
Proof. exact (@lem1982759 (term124 b) (real_of_int b) term127). Qed.
Lemma lem2605652 (b : int) : (term314 b) = (term315 b).
Proof. exact (@lem1982713 term127 (real_of_int b)). Qed.
Lemma lem2605654 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2605655 : term63 = term151.
Proof. exact (@lem2605654 term64). Qed.
Lemma lem2605657 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2605658 : term127 = term137.
Proof. exact (@lem2605657 term64). Qed.
Lemma lem2605659 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2605660 : term293 = term294.
Proof. exact (MK_COMB (@lem2605659) (@lem2605658)). Qed.
Lemma lem2605661 : term295 = term296.
Proof. exact (MK_COMB (@lem2605660) (@lem2605655)). Qed.
Lemma lem2605662 : term297.
Proof. exact (@lem1981473 term127 term63 term63 term63 term160 term63). Qed.
Lemma lem2605664 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2605665 : term258 = term265.
Proof. exact (@lem2605664 (NUMERAL 0) term64). Qed.
Lemma lem2605666 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2605667 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2605668 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2605667 h1) (fun h1 : term265 = True => @lem2605666)). Qed.
Lemma lem2605669 : term265 = True.
Proof. exact (EQ_MP (@lem2605668) (@lem2605666)). Qed.
Lemma lem2605670 : term258 = True.
Proof. exact (TRANS (@lem2605665) (@lem2605669)). Qed.
Lemma lem2605671 : True = term258.
Proof. exact (SYM (@lem2605670)). Qed.
Lemma lem2605672 : term258.
Proof. exact (EQ_MP (@lem2605671) (@lem0)). Qed.
Lemma lem2605673 : term298.
Proof. exact (@lem2605662 (@lem2605672)). Qed.
Lemma lem2605675 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2605676 : term258 = term265.
Proof. exact (@lem2605675 (NUMERAL 0) term64). Qed.
Lemma lem2605677 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2605678 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2605679 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2605678 h1) (fun h1 : term265 = True => @lem2605677)). Qed.
Lemma lem2605680 : term265 = True.
Proof. exact (EQ_MP (@lem2605679) (@lem2605677)). Qed.
Lemma lem2605681 : term258 = True.
Proof. exact (TRANS (@lem2605676) (@lem2605680)). Qed.
Lemma lem2605682 : True = term258.
Proof. exact (SYM (@lem2605681)). Qed.
Lemma lem2605683 : term258.
Proof. exact (EQ_MP (@lem2605682) (@lem0)). Qed.
Lemma lem2605684 : term299.
Proof. exact (@lem2605673 (@lem2605683)). Qed.
Lemma lem2605686 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2605687 : term258 = term265.
Proof. exact (@lem2605686 (NUMERAL 0) term64). Qed.
Lemma lem2605688 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2605689 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2605690 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2605689 h1) (fun h1 : term265 = True => @lem2605688)). Qed.
Lemma lem2605691 : term265 = True.
Proof. exact (EQ_MP (@lem2605690) (@lem2605688)). Qed.
Lemma lem2605692 : term258 = True.
Proof. exact (TRANS (@lem2605687) (@lem2605691)). Qed.
Lemma lem2605693 : True = term258.
Proof. exact (SYM (@lem2605692)). Qed.
Lemma lem2605694 : term258.
Proof. exact (EQ_MP (@lem2605693) (@lem0)). Qed.
Lemma lem2605695 : term300.
Proof. exact (@lem2605684 (@lem2605694)). Qed.
Lemma lem2605697 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2605698 : term144 = term145.
Proof. exact (@lem2605697 term64 term64). Qed.
Lemma lem2605699 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2605700 : term147 = term64.
Proof. exact (EQ_MP (@lem2605699) (@lem940073)). Qed.
Lemma lem2605701 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2605702 : term145 = term63.
Proof. exact (MK_COMB (@lem2605701) (@lem2605700)). Qed.
Lemma lem2605703 : term144 = term63.
Proof. exact (TRANS (@lem2605698) (@lem2605702)). Qed.
Lemma lem2605705 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2605706 : term172 = term177.
Proof. exact (@lem2605705 term64 term64). Qed.
Lemma lem2605707 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2605708 : term147 = term64.
Proof. exact (EQ_MP (@lem2605707) (@lem940073)). Qed.
Lemma lem2605709 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2605710 : term145 = term63.
Proof. exact (MK_COMB (@lem2605709) (@lem2605708)). Qed.
Lemma lem2605711 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2605712 : term177 = term127.
Proof. exact (MK_COMB (@lem2605711) (@lem2605710)). Qed.
Lemma lem2605713 : term172 = term127.
Proof. exact (TRANS (@lem2605706) (@lem2605712)). Qed.
Lemma lem2605714 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2605715 : term301 = term293.
Proof. exact (MK_COMB (@lem2605714) (@lem2605713)). Qed.
Lemma lem2605716 : term302 = term295.
Proof. exact (MK_COMB (@lem2605715) (@lem2605703)). Qed.
Lemma lem2605718 (m : nat) : (term303 m) = term160.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2605719 : term295 = term160.
Proof. exact (@lem2605718 term64). Qed.
Lemma lem2605720 : term302 = term160.
Proof. exact (TRANS (@lem2605716) (@lem2605719)). Qed.
Lemma lem2605721 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2605722 : term304 = term305.
Proof. exact (MK_COMB (@lem2605721) (@lem2605720)). Qed.
Lemma lem2605723 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2605724 : term306 = term270.
Proof. exact (MK_COMB (@lem2605722) (@lem2605723)). Qed.
Lemma lem2605726 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2605727 : term270 = term160.
Proof. exact (@lem2605726 term64). Qed.
Lemma lem2605728 : term306 = term160.
Proof. exact (TRANS (@lem2605724) (@lem2605727)). Qed.
Lemma lem2605730 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2605731 : term144 = term145.
Proof. exact (@lem2605730 term64 term64). Qed.
Lemma lem2605732 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2605733 : term147 = term64.
Proof. exact (EQ_MP (@lem2605732) (@lem940073)). Qed.
Lemma lem2605734 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2605735 : term145 = term63.
Proof. exact (MK_COMB (@lem2605734) (@lem2605733)). Qed.
Lemma lem2605736 : term144 = term63.
Proof. exact (TRANS (@lem2605731) (@lem2605735)). Qed.
Lemma lem2605737 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem2605738 : term307 = term270.
Proof. exact (MK_COMB (@lem2605737) (@lem2605736)). Qed.
Lemma lem2605740 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2605741 : term270 = term160.
Proof. exact (@lem2605740 term64). Qed.
Lemma lem2605742 : term307 = term160.
Proof. exact (TRANS (@lem2605738) (@lem2605741)). Qed.
Lemma lem2605743 : term160 = term307.
Proof. exact (SYM (@lem2605742)). Qed.
Lemma lem2605744 : term306 = term307.
Proof. exact (TRANS (@lem2605728) (@lem2605743)). Qed.
Lemma lem2605745 : term296 = term259.
Proof. exact (@lem2605695 (@lem2605744)). Qed.
Lemma lem2605746 : term295 = term259.
Proof. exact (TRANS (@lem2605661) (@lem2605745)). Qed.
Lemma lem2605748 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2605749 : term259 = term160.
Proof. exact (@lem2605748 term160). Qed.
Lemma lem2605750 : term295 = term160.
Proof. exact (TRANS (@lem2605746) (@lem2605749)). Qed.
Lemma lem2605751 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2605752 : term308 = term305.
Proof. exact (MK_COMB (@lem2605751) (@lem2605750)). Qed.
Lemma lem2605753 (b : int) : (real_of_int b) = (real_of_int b).
Proof. exact (eq_refl (real_of_int b)). Qed.
Lemma lem2605754 (b : int) : (term315 b) = (term316 b).
Proof. exact (MK_COMB (@lem2605752) (@lem2605753 b)). Qed.
Lemma lem2605755 (b : int) : (term314 b) = (term316 b).
Proof. exact (TRANS (@lem2605652 b) (@lem2605754 b)). Qed.
Lemma lem2605756 (b : int) : (term316 b) = term160.
Proof. exact (@lem1982719 (real_of_int b)). Qed.
Lemma lem2605757 (b : int) : (term314 b) = term160.
Proof. exact (TRANS (@lem2605755 b) (@lem2605756 b)). Qed.
Lemma lem2605758 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2605759 (b : int) : (term317 b) = term311.
Proof. exact (MK_COMB (@lem2605758) (@lem2605757 b)). Qed.
Lemma lem2605760 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem2605761 (b : int) : (term313 b) = term318.
Proof. exact (MK_COMB (@lem2605759 b) (@lem2605760)). Qed.
Lemma lem2605762 (b : int) : (term366 b) = term318.
Proof. exact (TRANS (@lem2605651 b) (@lem2605761 b)). Qed.
Lemma lem2605763 : term318 = term127.
Proof. exact (@lem1982721 term127). Qed.
Lemma lem2605764 (b : int) : (term366 b) = term127.
Proof. exact (TRANS (@lem2605762 b) (@lem2605763)). Qed.
Lemma lem2605765 (a : int) (b : int) : (term488 a b) = term318.
Proof. exact (MK_COMB (@lem2605650 a) (@lem2605764 b)). Qed.
Lemma lem2605766 (a : int) (b : int) : (term487 a b) = term318.
Proof. exact (TRANS (@lem2605542 a b) (@lem2605765 a b)). Qed.
Lemma lem2605767 : term318 = term127.
Proof. exact (@lem1982721 term127). Qed.
Lemma lem2605768 (a : int) (b : int) : (term487 a b) = term127.
Proof. exact (TRANS (@lem2605766 a b) (@lem2605767)). Qed.
Lemma lem2605769 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2605770 (a : int) (b : int) : (term489 a b) = term320.
Proof. exact (MK_COMB (@lem2605769) (@lem2605768 a b)). Qed.
Lemma lem2605771 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2605772 (a : int) (b : int) : (term486 a b) = term321.
Proof. exact (MK_COMB (@lem2605770 a b) (@lem2605771)). Qed.
Lemma lem2605773 (a : int) (b : int) (h1 : term472 a b) : term321.
Proof. exact (EQ_MP (@lem2605772 a b) (@lem2605541 a b h1)). Qed.
Lemma lem2605775 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2605776 : term321 = term322.
Proof. exact (@lem2605775 term160 term127). Qed.
Lemma lem2605778 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2605779 : term127 = term137.
Proof. exact (@lem2605778 term64). Qed.
Lemma lem2605781 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2605782 : term160 = term259.
Proof. exact (@lem2605781 (NUMERAL 0)). Qed.
Lemma lem2605783 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2605784 : term323 = term324.
Proof. exact (MK_COMB (@lem2605783) (@lem2605782)). Qed.
Lemma lem2605785 : term322 = term325.
Proof. exact (MK_COMB (@lem2605784) (@lem2605779)). Qed.
Lemma lem2605786 : term326.
Proof. exact (@lem1980026 term160 term63 term127 term63). Qed.
Lemma lem2605788 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2605789 : term258 = term265.
Proof. exact (@lem2605788 (NUMERAL 0) term64). Qed.
Lemma lem2605790 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2605791 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2605792 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2605791 h1) (fun h1 : term265 = True => @lem2605790)). Qed.
Lemma lem2605793 : term265 = True.
Proof. exact (EQ_MP (@lem2605792) (@lem2605790)). Qed.
Lemma lem2605794 : term258 = True.
Proof. exact (TRANS (@lem2605789) (@lem2605793)). Qed.
Lemma lem2605795 : True = term258.
Proof. exact (SYM (@lem2605794)). Qed.
Lemma lem2605796 : term258.
Proof. exact (EQ_MP (@lem2605795) (@lem0)). Qed.
Lemma lem2605797 : term327.
Proof. exact (@lem2605786 (@lem2605796)). Qed.
Lemma lem2605799 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2605800 : term258 = term265.
Proof. exact (@lem2605799 (NUMERAL 0) term64). Qed.
Lemma lem2605801 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2605802 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2605803 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2605802 h1) (fun h1 : term265 = True => @lem2605801)). Qed.
Lemma lem2605804 : term265 = True.
Proof. exact (EQ_MP (@lem2605803) (@lem2605801)). Qed.
Lemma lem2605805 : term258 = True.
Proof. exact (TRANS (@lem2605800) (@lem2605804)). Qed.
Lemma lem2605806 : True = term258.
Proof. exact (SYM (@lem2605805)). Qed.
Lemma lem2605807 : term258.
Proof. exact (EQ_MP (@lem2605806) (@lem0)). Qed.
Lemma lem2605808 : term325 = term328.
Proof. exact (@lem2605797 (@lem2605807)). Qed.
Lemma lem2605810 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2605811 : term172 = term177.
Proof. exact (@lem2605810 term64 term64). Qed.
Lemma lem2605812 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2605813 : term147 = term64.
Proof. exact (EQ_MP (@lem2605812) (@lem940073)). Qed.
Lemma lem2605814 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2605815 : term145 = term63.
Proof. exact (MK_COMB (@lem2605814) (@lem2605813)). Qed.
Lemma lem2605816 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2605817 : term177 = term127.
Proof. exact (MK_COMB (@lem2605816) (@lem2605815)). Qed.
Lemma lem2605818 : term172 = term127.
Proof. exact (TRANS (@lem2605811) (@lem2605817)). Qed.
Lemma lem2605820 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2605821 : term270 = term160.
Proof. exact (@lem2605820 term64). Qed.
Lemma lem2605822 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2605823 : term329 = term323.
Proof. exact (MK_COMB (@lem2605822) (@lem2605821)). Qed.
Lemma lem2605824 : term328 = term322.
Proof. exact (MK_COMB (@lem2605823) (@lem2605818)). Qed.
Lemma lem2605826 (m : nat) (n : nat) : (term330 m n) = (term331 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2605827 : term322 = term332.
Proof. exact (@lem2605826 (NUMERAL 0) term64). Qed.
Lemma lem2605828 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2605829 (h1 : term266 = (BIT1 0)) : (term64 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2605830 : (term266 = (BIT1 0)) = ((term64 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2605829 h1) (fun h1 : (term64 = (NUMERAL 0)) = False => @lem2605828)). Qed.
Lemma lem2605831 : (term64 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2605830) (@lem2605828)). Qed.
Lemma lem2605832 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2605833 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2605834 : term333 = (and True).
Proof. exact (MK_COMB (@lem2605833) (@lem2605832)). Qed.
Lemma lem2605835 : term332 = (True /\ False).
Proof. exact (MK_COMB (@lem2605834) (@lem2605831)). Qed.
Lemma lem2605837 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2605838 : term332 = False.
Proof. exact (TRANS (@lem2605835) (@lem2605837)). Qed.
Lemma lem2605839 : term322 = False.
Proof. exact (TRANS (@lem2605827) (@lem2605838)). Qed.
Lemma lem2605840 : term328 = False.
Proof. exact (TRANS (@lem2605824) (@lem2605839)). Qed.
Lemma lem2605841 : term325 = False.
Proof. exact (TRANS (@lem2605808) (@lem2605840)). Qed.
Lemma lem2605842 : term322 = False.
Proof. exact (TRANS (@lem2605785) (@lem2605841)). Qed.
Lemma lem2605843 : term321 = False.
Proof. exact (TRANS (@lem2605776) (@lem2605842)). Qed.
Lemma lem2605844 (a : int) (b : int) (h1 : term472 a b) : False.
Proof. exact (EQ_MP (@lem2605843) (@lem2605773 a b h1)). Qed.
Lemma lem2605845 (a : int) (b : int) (h1 : term474 a b) : False.
Proof. exact (or_elim (@lem2604926 a b h1) (fun h0 : term470 a b => @lem2605385 a b h0) (fun h0 : term472 a b => @lem2605844 a b h0)). Qed.
Lemma lem2605847 (a : int) (b : int) (h1 : term474 a b) : term474 a b.
Proof. exact (h1). Qed.
Lemma lem2605848 (a : int) (b : int) (h1 : term474 a b) : (term474 a b) = False.
Proof. exact (prop_ext (fun h2 : term474 a b => @lem2605845 a b h1) (fun h2 : False => @lem2605847 a b h1)). Qed.
Lemma lem2605849 (a : int) (b : int) (h1 : term474 a b) : False.
Proof. exact (EQ_MP (@lem2605848 a b h1) (@lem2605847 a b h1)). Qed.
Lemma lem2605850 (b : int) (a : int) (h1 : term453 b a) : term453 b a.
Proof. exact (h1). Qed.
Lemma lem2605851 (b : int) (a : int) (h1 : term453 b a) : term474 a b.
Proof. exact (EQ_MP (@lem2604916 a b) (@lem2605850 b a h1)). Qed.
Lemma lem2605852 (b : int) (a : int) (h1 : term453 b a) : (term474 a b) = False.
Proof. exact (prop_ext (fun h2 : term474 a b => @lem2605849 a b h2) (fun h2 : False => @lem2605851 b a h1)). Qed.
Lemma lem2605853 (b : int) (a : int) (h1 : term453 b a) : False.
Proof. exact (EQ_MP (@lem2605852 b a h1) (@lem2605851 b a h1)). Qed.
Lemma lem2605854 (b : int) (a : int) : term490 b a.
Proof. exact (fun h0 : term453 b a => @lem2605853 b a h0). Qed.
Lemma lem2605855 (b : int) (a : int) : term491 b a.
Proof. exact (@lem1386578 (term492 b a)). Qed.
Lemma lem2605858 (b : int) (a : int) : term492 b a.
Proof. exact (@lem2605855 b a (@lem2605854 b a)). Qed.
Lemma lem2605859 (a : int) (b : int) : (term452 b a) = (term436 a b).
Proof. exact (SYM (@lem2604558 b a)). Qed.
Lemma lem2605860 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2605861 (a : int) (b : int) : (term492 b a) = (term423 a b).
Proof. exact (MK_COMB (@lem2605860) (@lem2605859 a b)). Qed.
Lemma lem2605862 (a : int) (b : int) : term423 a b.
Proof. exact (EQ_MP (@lem2605861 a b) (@lem2605858 b a)). Qed.
Lemma lem2605866 (x : int) (y : int) (h1 : (int_le x y) = (term493 x y)) : (int_le x y) = (term493 x y).
Proof. exact (h1). Qed.
Lemma lem2605867 (x : int) (y : int) (h1 : (int_le x y) = (term493 x y)) : (term493 x y) = (int_le x y).
Proof. exact (SYM (@lem2605866 x y h1)). Qed.
Lemma lem2605868 (x : int) (y : int) (h1 : (term493 x y) = (int_le x y)) : (term493 x y) = (int_le x y).
Proof. exact (h1). Qed.
Lemma lem2605869 (x : int) (y : int) (h1 : (term493 x y) = (int_le x y)) : (int_le x y) = (term493 x y).
Proof. exact (SYM (@lem2605868 x y h1)). Qed.
Lemma lem2605870 (x : int) (y : int) : ((int_le x y) = (term493 x y)) = ((term493 x y) = (int_le x y)).
Proof. exact (prop_ext (fun h1 : (int_le x y) = (term493 x y) => @lem2605867 x y h1) (fun h1 : (term493 x y) = (int_le x y) => @lem2605869 x y h1)). Qed.
Lemma lem2605871 (x : int) : (term494 x) = (term495 x).
Proof. exact (fun_ext (fun y : int => @lem2605870 x y)). Qed.
Lemma lem2605872 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2605873 (x : int) : (term496 x) = (term497 x).
Proof. exact (MK_COMB (@lem2605872) (@lem2605871 x)). Qed.
Lemma lem2605874 : term498 = term499.
Proof. exact (fun_ext (fun x : int => @lem2605873 x)). Qed.
Lemma lem2605875 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2605876 : term500 = term501.
Proof. exact (MK_COMB (@lem2605875) (@lem2605874)). Qed.
Lemma lem2605877 : term501.
Proof. exact (EQ_MP (@lem2605876) (@lem2332494)). Qed.
Lemma lem2605878 (x : int) : term502 x.
Proof. exact (@lem2605877 x). Qed.
Lemma lem2605879 (x : int) : (term502 x) = (term497 x).
Proof. exact (eq_refl (term502 x)). Qed.
Lemma lem2605880 (x : int) : term497 x.
Proof. exact (EQ_MP (@lem2605879 x) (@lem2605878 x)). Qed.
Lemma lem2605881 (x : int) (y : int) : term503 x y.
Proof. exact (@lem2605880 x y). Qed.
Lemma lem2605882 (x : int) (y : int) : (term503 x y) = ((term493 x y) = (int_le x y)).
Proof. exact (eq_refl (term503 x y)). Qed.
Lemma lem2605884 (x : int) : term504 x.
Proof. exact (@lem2305041 x). Qed.
Lemma lem2605885 (x : int) : (term504 x) = (term505 x).
Proof. exact (eq_refl (term504 x)). Qed.
Lemma lem2605886 (x : int) : term505 x.
Proof. exact (EQ_MP (@lem2605885 x) (@lem2605884 x)). Qed.
Lemma lem2605887 (x : int) (y : int) : term506 x y.
Proof. exact (@lem2605886 x y). Qed.
Lemma lem2605888 (x : int) (y : int) : (term506 x y) = (term507 x y).
Proof. exact (eq_refl (term506 x y)). Qed.
Lemma lem2605889 (x : int) (y : int) : term507 x y.
Proof. exact (EQ_MP (@lem2605888 x y) (@lem2605887 x y)). Qed.
Lemma lem2605890 (x : int) (y : int) (z : int) : term508 x y z.
Proof. exact (@lem2605889 x y z). Qed.
Lemma lem2605891 (x : int) (z : int) (y : int) : (term508 x y z) = ((term509 x y z) = (term510 x z y)).
Proof. exact (eq_refl (term508 x y z)). Qed.
Lemma lem2605893 (n : nat) (q : int) : (term511 n q) = ((term512 q n) = (term513 n q)).
Proof. exact (@lem2318604 ((term512 q n) = (term513 n q))). Qed.
Lemma lem2605906 (y : int) (x : int) : (term100 x y) = (term101 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2605907 (q : int) (n : nat) : (term514 n q) = (term515 q n).
Proof. exact (@lem2605906 (term513 n q) (term512 q n)). Qed.
Lemma lem2605909 (x : int) (y : int) : (int_le x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2605910 (n : nat) (q : int) : (term516 n q) = (term517 n q).
Proof. exact (@lem2605909 (term518 q n) (term513 n q)). Qed.
Lemma lem2605912 (x : int) (y : int) : (term54 x y) = (term55 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2605913 (q : int) (n : nat) : (term519 q n) = (term520 q n).
Proof. exact (@lem2605912 (term512 q n) term58). Qed.
Lemma lem2605915 (x : int) : (term43 x) = (term44 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2605916 (q : int) (n : nat) : (term521 q n) = (term522 q n).
Proof. exact (@lem2605915 (term523 q n)). Qed.
Lemma lem2605918 (x : int) (y : int) : (term54 x y) = (term55 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2605919 (q : int) (n : nat) : (term524 q n) = (term525 q n).
Proof. exact (@lem2605918 (term526 q n) term527). Qed.
Lemma lem2605921 (x : int) (y : int) : (term39 x y) = (term40 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2605922 (q : int) (n : nat) : (term528 q n) = (term529 q n).
Proof. exact (@lem2605921 q (int_of_num n)). Qed.
Lemma lem2605924 (n : nat) : (term61 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2605925 (q : int) : (term45 q) = (term45 q).
Proof. exact (eq_refl (term45 q)). Qed.
Lemma lem2605926 (q : int) (n : nat) : (term529 q n) = (term530 q n).
Proof. exact (MK_COMB (@lem2605925 q) (@lem2605924 n)). Qed.
Lemma lem2605927 (q : int) (n : nat) : (term528 q n) = (term530 q n).
Proof. exact (TRANS (@lem2605922 q n) (@lem2605926 q n)). Qed.
Lemma lem2605928 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2605929 (q : int) (n : nat) : (term531 q n) = (term532 q n).
Proof. exact (MK_COMB (@lem2605928) (@lem2605927 q n)). Qed.
Lemma lem2605931 (n : nat) : (term61 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2605932 : term533 = term160.
Proof. exact (@lem2605931 (NUMERAL 0)). Qed.
Lemma lem2605933 (q : int) (n : nat) : (term525 q n) = (term534 q n).
Proof. exact (MK_COMB (@lem2605929 q n) (@lem2605932)). Qed.
Lemma lem2605934 (q : int) (n : nat) : (term524 q n) = (term534 q n).
Proof. exact (TRANS (@lem2605919 q n) (@lem2605933 q n)). Qed.
Lemma lem2605935 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2605936 (q : int) (n : nat) : (term522 q n) = (term535 q n).
Proof. exact (MK_COMB (@lem2605935) (@lem2605934 q n)). Qed.
Lemma lem2605937 (q : int) (n : nat) : (term521 q n) = (term535 q n).
Proof. exact (TRANS (@lem2605916 q n) (@lem2605936 q n)). Qed.
Lemma lem2605938 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2605939 (q : int) (n : nat) : (term536 q n) = (term537 q n).
Proof. exact (MK_COMB (@lem2605938) (@lem2605937 q n)). Qed.
Lemma lem2605941 (n : nat) : (term61 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2605942 : term62 = term63.
Proof. exact (@lem2605941 term64). Qed.
Lemma lem2605943 (q : int) (n : nat) : (term520 q n) = (term538 q n).
Proof. exact (MK_COMB (@lem2605939 q n) (@lem2605942)). Qed.
Lemma lem2605944 (q : int) (n : nat) : (term519 q n) = (term538 q n).
Proof. exact (TRANS (@lem2605913 q n) (@lem2605943 q n)). Qed.
Lemma lem2605945 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2605946 (q : int) (n : nat) : (term539 q n) = (term540 q n).
Proof. exact (MK_COMB (@lem2605945) (@lem2605944 q n)). Qed.
Lemma lem2605948 (x : int) (y : int) : (term39 x y) = (term40 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2605949 (n : nat) (q : int) : (term541 n q) = (term542 n q).
Proof. exact (@lem2605948 (int_of_num n) (int_neg q)). Qed.
Lemma lem2605951 (n : nat) : (term61 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2605952 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2605953 (n : nat) : (term543 n) = (term544 n).
Proof. exact (MK_COMB (@lem2605952) (@lem2605951 n)). Qed.
Lemma lem2605955 (x : int) : (term43 x) = (term44 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2605956 (q : int) : (term43 q) = (term44 q).
Proof. exact (@lem2605955 q). Qed.
Lemma lem2605957 (n : nat) (q : int) : (term542 n q) = (term545 n q).
Proof. exact (MK_COMB (@lem2605953 n) (@lem2605956 q)). Qed.
Lemma lem2605958 (n : nat) (q : int) : (term541 n q) = (term545 n q).
Proof. exact (TRANS (@lem2605949 n q) (@lem2605957 n q)). Qed.
Lemma lem2605959 (n : nat) (q : int) : (term517 n q) = (term546 n q).
Proof. exact (MK_COMB (@lem2605946 q n) (@lem2605958 n q)). Qed.
Lemma lem2605960 (n : nat) (q : int) : (term516 n q) = (term546 n q).
Proof. exact (TRANS (@lem2605910 n q) (@lem2605959 n q)). Qed.
Lemma lem2605961 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2605962 (n : nat) (q : int) : (term547 n q) = (term548 n q).
Proof. exact (MK_COMB (@lem2605961) (@lem2605960 n q)). Qed.
Lemma lem2605964 (x : int) (y : int) : (int_le x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2605965 (q : int) (n : nat) : (term549 q n) = (term550 q n).
Proof. exact (@lem2605964 (term551 n q) (term512 q n)). Qed.
Lemma lem2605967 (x : int) (y : int) : (term54 x y) = (term55 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2605968 (n : nat) (q : int) : (term552 n q) = (term553 n q).
Proof. exact (@lem2605967 (term513 n q) term58). Qed.
Lemma lem2605970 (x : int) (y : int) : (term39 x y) = (term40 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2605971 (n : nat) (q : int) : (term541 n q) = (term542 n q).
Proof. exact (@lem2605970 (int_of_num n) (int_neg q)). Qed.
Lemma lem2605973 (n : nat) : (term61 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2605974 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2605975 (n : nat) : (term543 n) = (term544 n).
Proof. exact (MK_COMB (@lem2605974) (@lem2605973 n)). Qed.
Lemma lem2605977 (x : int) : (term43 x) = (term44 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2605978 (q : int) : (term43 q) = (term44 q).
Proof. exact (@lem2605977 q). Qed.
Lemma lem2605979 (n : nat) (q : int) : (term542 n q) = (term545 n q).
Proof. exact (MK_COMB (@lem2605975 n) (@lem2605978 q)). Qed.
Lemma lem2605980 (n : nat) (q : int) : (term541 n q) = (term545 n q).
Proof. exact (TRANS (@lem2605971 n q) (@lem2605979 n q)). Qed.
Lemma lem2605981 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2605982 (n : nat) (q : int) : (term554 n q) = (term555 n q).
Proof. exact (MK_COMB (@lem2605981) (@lem2605980 n q)). Qed.
Lemma lem2605984 (n : nat) : (term61 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2605985 : term62 = term63.
Proof. exact (@lem2605984 term64). Qed.
Lemma lem2605986 (n : nat) (q : int) : (term553 n q) = (term556 n q).
Proof. exact (MK_COMB (@lem2605982 n q) (@lem2605985)). Qed.
Lemma lem2605987 (n : nat) (q : int) : (term552 n q) = (term556 n q).
Proof. exact (TRANS (@lem2605968 n q) (@lem2605986 n q)). Qed.
Lemma lem2605988 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2605989 (n : nat) (q : int) : (term557 n q) = (term558 n q).
Proof. exact (MK_COMB (@lem2605988) (@lem2605987 n q)). Qed.
Lemma lem2605991 (x : int) : (term43 x) = (term44 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2605992 (q : int) (n : nat) : (term521 q n) = (term522 q n).
Proof. exact (@lem2605991 (term523 q n)). Qed.
Lemma lem2605994 (x : int) (y : int) : (term54 x y) = (term55 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2605995 (q : int) (n : nat) : (term524 q n) = (term525 q n).
Proof. exact (@lem2605994 (term526 q n) term527). Qed.
Lemma lem2605997 (x : int) (y : int) : (term39 x y) = (term40 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2605998 (q : int) (n : nat) : (term528 q n) = (term529 q n).
Proof. exact (@lem2605997 q (int_of_num n)). Qed.
Lemma lem2606000 (n : nat) : (term61 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2606001 (q : int) : (term45 q) = (term45 q).
Proof. exact (eq_refl (term45 q)). Qed.
Lemma lem2606002 (q : int) (n : nat) : (term529 q n) = (term530 q n).
Proof. exact (MK_COMB (@lem2606001 q) (@lem2606000 n)). Qed.
Lemma lem2606003 (q : int) (n : nat) : (term528 q n) = (term530 q n).
Proof. exact (TRANS (@lem2605998 q n) (@lem2606002 q n)). Qed.
Lemma lem2606004 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2606005 (q : int) (n : nat) : (term531 q n) = (term532 q n).
Proof. exact (MK_COMB (@lem2606004) (@lem2606003 q n)). Qed.
Lemma lem2606007 (n : nat) : (term61 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2606008 : term533 = term160.
Proof. exact (@lem2606007 (NUMERAL 0)). Qed.
Lemma lem2606009 (q : int) (n : nat) : (term525 q n) = (term534 q n).
Proof. exact (MK_COMB (@lem2606005 q n) (@lem2606008)). Qed.
Lemma lem2606010 (q : int) (n : nat) : (term524 q n) = (term534 q n).
Proof. exact (TRANS (@lem2605995 q n) (@lem2606009 q n)). Qed.
Lemma lem2606011 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2606012 (q : int) (n : nat) : (term522 q n) = (term535 q n).
Proof. exact (MK_COMB (@lem2606011) (@lem2606010 q n)). Qed.
Lemma lem2606013 (q : int) (n : nat) : (term521 q n) = (term535 q n).
Proof. exact (TRANS (@lem2605992 q n) (@lem2606012 q n)). Qed.
Lemma lem2606014 (q : int) (n : nat) : (term550 q n) = (term559 q n).
Proof. exact (MK_COMB (@lem2605989 n q) (@lem2606013 q n)). Qed.
Lemma lem2606015 (q : int) (n : nat) : (term549 q n) = (term559 q n).
Proof. exact (TRANS (@lem2605965 q n) (@lem2606014 q n)). Qed.
Lemma lem2606016 (q : int) (n : nat) : (term515 q n) = (term560 q n).
Proof. exact (MK_COMB (@lem2605962 n q) (@lem2606015 q n)). Qed.
Lemma lem2606018 (q : int) (n : nat) : (term514 n q) = (term560 q n).
Proof. exact (TRANS (@lem2605907 q n) (@lem2606016 q n)). Qed.
Lemma lem2606022 (t : Prop) : (term121 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2606038 (q : int) (n : nat) : (term561 q n) = (term560 q n).
Proof. exact (@lem2606022 (term560 q n)). Qed.
Lemma lem2606039 (q : int) (n : nat) : (term546 n q) = (term562 q n).
Proof. exact (@lem1988287 (term545 n q) (term538 q n)). Qed.
Lemma lem2606040 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2606053 (q : int) (n : nat) : (term534 q n) = (term530 q n).
Proof. exact (@lem1982723 (term530 q n)). Qed.
Lemma lem2606054 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2606055 (q : int) (n : nat) : (term535 q n) = (term563 q n).
Proof. exact (MK_COMB (@lem2606054) (@lem2606053 q n)). Qed.
Lemma lem2606058 (q : int) (n : nat) : (term563 q n) = (term564 q n).
Proof. exact (@lem1982785 (term530 q n)). Qed.
Lemma lem2606059 (q : int) (n : nat) : (term535 q n) = (term564 q n).
Proof. exact (TRANS (@lem2606055 q n) (@lem2606058 q n)). Qed.
Lemma lem2606060 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2606061 (q : int) (n : nat) : (term537 q n) = (term565 q n).
Proof. exact (MK_COMB (@lem2606060) (@lem2606059 q n)). Qed.
Lemma lem2606064 (q : int) (n : nat) : (term538 q n) = (term566 q n).
Proof. exact (MK_COMB (@lem2606061 q n) (@lem2606040)). Qed.
Lemma lem2606071 (q : int) : (term44 q) = (term124 q).
Proof. exact (@lem1982785 (real_of_int q)). Qed.
Lemma lem2606074 (n : nat) : (term544 n) = (term544 n).
Proof. exact (eq_refl (term544 n)). Qed.
Lemma lem2606075 (n : nat) (q : int) : (term545 n q) = (term567 n q).
Proof. exact (MK_COMB (@lem2606074 n) (@lem2606071 q)). Qed.
Lemma lem2606076 (n : nat) (q : int) : (term567 n q) = (term568 n q).
Proof. exact (@lem1982751 term127 (real_of_num n) (real_of_int q)). Qed.
Lemma lem2606077 (q : int) (n : nat) : (term569 n q) = (term530 q n).
Proof. exact (@lem1982747 (real_of_int q) (real_of_num n)). Qed.
Lemma lem2606078 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem2606079 (q : int) (n : nat) : (term568 n q) = (term564 q n).
Proof. exact (MK_COMB (@lem2606078) (@lem2606077 q n)). Qed.
Lemma lem2606080 (q : int) (n : nat) : (term567 n q) = (term564 q n).
Proof. exact (TRANS (@lem2606076 n q) (@lem2606079 q n)). Qed.
Lemma lem2606081 (q : int) (n : nat) : (term545 n q) = (term564 q n).
Proof. exact (TRANS (@lem2606075 n q) (@lem2606080 q n)). Qed.
Lemma lem2606082 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2606083 (q : int) (n : nat) : (term570 n q) = (term571 q n).
Proof. exact (MK_COMB (@lem2606082) (@lem2606081 q n)). Qed.
Lemma lem2606084 (q : int) (n : nat) : (term572 q n) = (term573 q n).
Proof. exact (MK_COMB (@lem2606083 q n) (@lem2606064 q n)). Qed.
Lemma lem2606085 (q : int) (n : nat) : (term573 q n) = (term574 q n).
Proof. exact (@lem1982792 (term564 q n) (term566 q n)). Qed.
Lemma lem2606086 (q : int) (n : nat) : (term575 q n) = (term576 q n).
Proof. exact (@lem1982781 (term564 q n) term127 term63). Qed.
Lemma lem2606088 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2606089 : term63 = term151.
Proof. exact (@lem2606088 term64). Qed.
Lemma lem2606091 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2606092 : term127 = term137.
Proof. exact (@lem2606091 term64). Qed.
Lemma lem2606093 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2606094 : term128 = term138.
Proof. exact (MK_COMB (@lem2606093) (@lem2606092)). Qed.
Lemma lem2606095 : term172 = term173.
Proof. exact (MK_COMB (@lem2606094) (@lem2606089)). Qed.
Lemma lem2606096 : term173 = term174.
Proof. exact (@lem1981613 term127 term63 term63 term63). Qed.
Lemma lem2606098 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2606099 : term144 = term145.
Proof. exact (@lem2606098 term64 term64). Qed.
Lemma lem2606100 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2606101 : term147 = term64.
Proof. exact (EQ_MP (@lem2606100) (@lem940073)). Qed.
Lemma lem2606102 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2606103 : term145 = term63.
Proof. exact (MK_COMB (@lem2606102) (@lem2606101)). Qed.
Lemma lem2606104 : term144 = term63.
Proof. exact (TRANS (@lem2606099) (@lem2606103)). Qed.
Lemma lem2606106 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2606107 : term172 = term177.
Proof. exact (@lem2606106 term64 term64). Qed.
Lemma lem2606108 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2606109 : term147 = term64.
Proof. exact (EQ_MP (@lem2606108) (@lem940073)). Qed.
Lemma lem2606110 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2606111 : term145 = term63.
Proof. exact (MK_COMB (@lem2606110) (@lem2606109)). Qed.
Lemma lem2606112 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2606113 : term177 = term127.
Proof. exact (MK_COMB (@lem2606112) (@lem2606111)). Qed.
Lemma lem2606114 : term172 = term127.
Proof. exact (TRANS (@lem2606107) (@lem2606113)). Qed.
Lemma lem2606115 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2606116 : term178 = term179.
Proof. exact (MK_COMB (@lem2606115) (@lem2606114)). Qed.
Lemma lem2606117 : term174 = term137.
Proof. exact (MK_COMB (@lem2606116) (@lem2606104)). Qed.
Lemma lem2606118 : term173 = term137.
Proof. exact (TRANS (@lem2606096) (@lem2606117)). Qed.
Lemma lem2606119 : term172 = term137.
Proof. exact (TRANS (@lem2606095) (@lem2606118)). Qed.
Lemma lem2606121 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2606122 : term137 = term127.
Proof. exact (@lem2606121 term127). Qed.
Lemma lem2606123 : term172 = term127.
Proof. exact (TRANS (@lem2606119) (@lem2606122)). Qed.
Lemma lem2606124 (q : int) (n : nat) : (term577 q n) = (term578 q n).
Proof. exact (@lem1982749 term127 term127 (term530 q n)). Qed.
Lemma lem2606126 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2606127 : term127 = term137.
Proof. exact (@lem2606126 term64). Qed.
Lemma lem2606129 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2606130 : term127 = term137.
Proof. exact (@lem2606129 term64). Qed.
Lemma lem2606131 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2606132 : term128 = term138.
Proof. exact (MK_COMB (@lem2606131) (@lem2606130)). Qed.
Lemma lem2606133 : term139 = term140.
Proof. exact (MK_COMB (@lem2606132) (@lem2606127)). Qed.
Lemma lem2606134 : term140 = term141.
Proof. exact (@lem1981613 term127 term127 term63 term63). Qed.
Lemma lem2606136 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2606137 : term144 = term145.
Proof. exact (@lem2606136 term64 term64). Qed.
Lemma lem2606138 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2606139 : term147 = term64.
Proof. exact (EQ_MP (@lem2606138) (@lem940073)). Qed.
Lemma lem2606140 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2606141 : term145 = term63.
Proof. exact (MK_COMB (@lem2606140) (@lem2606139)). Qed.
Lemma lem2606142 : term144 = term63.
Proof. exact (TRANS (@lem2606137) (@lem2606141)). Qed.
Lemma lem2606144 (m : nat) (n : nat) : (term148 m n) = (term143 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2606145 : term139 = term145.
Proof. exact (@lem2606144 term64 term64). Qed.
Lemma lem2606146 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2606147 : term147 = term64.
Proof. exact (EQ_MP (@lem2606146) (@lem940073)). Qed.
Lemma lem2606148 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2606149 : term145 = term63.
Proof. exact (MK_COMB (@lem2606148) (@lem2606147)). Qed.
Lemma lem2606150 : term139 = term63.
Proof. exact (TRANS (@lem2606145) (@lem2606149)). Qed.
Lemma lem2606151 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2606152 : term149 = term150.
Proof. exact (MK_COMB (@lem2606151) (@lem2606150)). Qed.
Lemma lem2606153 : term141 = term151.
Proof. exact (MK_COMB (@lem2606152) (@lem2606142)). Qed.
Lemma lem2606154 : term140 = term151.
Proof. exact (TRANS (@lem2606134) (@lem2606153)). Qed.
Lemma lem2606155 : term139 = term151.
Proof. exact (TRANS (@lem2606133) (@lem2606154)). Qed.
Lemma lem2606157 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2606158 : term151 = term63.
Proof. exact (@lem2606157 term63). Qed.
Lemma lem2606159 : term139 = term63.
Proof. exact (TRANS (@lem2606155) (@lem2606158)). Qed.
Lemma lem2606160 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2606161 : term153 = term154.
Proof. exact (MK_COMB (@lem2606160) (@lem2606159)). Qed.
Lemma lem2606162 (q : int) (n : nat) : (term530 q n) = (term530 q n).
Proof. exact (eq_refl (term530 q n)). Qed.
Lemma lem2606163 (q : int) (n : nat) : (term578 q n) = (term579 q n).
Proof. exact (MK_COMB (@lem2606161) (@lem2606162 q n)). Qed.
Lemma lem2606164 (q : int) (n : nat) : (term577 q n) = (term579 q n).
Proof. exact (TRANS (@lem2606124 q n) (@lem2606163 q n)). Qed.
Lemma lem2606165 (q : int) (n : nat) : (term579 q n) = (term530 q n).
Proof. exact (@lem1982709 (term530 q n)). Qed.
Lemma lem2606166 (q : int) (n : nat) : (term577 q n) = (term530 q n).
Proof. exact (TRANS (@lem2606164 q n) (@lem2606165 q n)). Qed.
Lemma lem2606167 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2606168 (q : int) (n : nat) : (term580 q n) = (term532 q n).
Proof. exact (MK_COMB (@lem2606167) (@lem2606166 q n)). Qed.
Lemma lem2606169 (q : int) (n : nat) : (term576 q n) = (term581 q n).
Proof. exact (MK_COMB (@lem2606168 q n) (@lem2606123)). Qed.
Lemma lem2606170 (q : int) (n : nat) : (term575 q n) = (term581 q n).
Proof. exact (TRANS (@lem2606086 q n) (@lem2606169 q n)). Qed.
Lemma lem2606171 (q : int) (n : nat) : (term565 q n) = (term565 q n).
Proof. exact (eq_refl (term565 q n)). Qed.
Lemma lem2606172 (q : int) (n : nat) : (term574 q n) = (term582 q n).
Proof. exact (MK_COMB (@lem2606171 q n) (@lem2606170 q n)). Qed.
Lemma lem2606173 (q : int) (n : nat) : (term582 q n) = (term583 q n).
Proof. exact (@lem1982763 (term564 q n) (term530 q n) term127). Qed.
Lemma lem2606174 (q : int) (n : nat) : (term584 q n) = (term585 q n).
Proof. exact (@lem1982713 term127 (term530 q n)). Qed.
Lemma lem2606176 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2606177 : term63 = term151.
Proof. exact (@lem2606176 term64). Qed.
Lemma lem2606179 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2606180 : term127 = term137.
Proof. exact (@lem2606179 term64). Qed.
Lemma lem2606181 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2606182 : term293 = term294.
Proof. exact (MK_COMB (@lem2606181) (@lem2606180)). Qed.
Lemma lem2606183 : term295 = term296.
Proof. exact (MK_COMB (@lem2606182) (@lem2606177)). Qed.
Lemma lem2606184 : term297.
Proof. exact (@lem1981473 term127 term63 term63 term63 term160 term63). Qed.
Lemma lem2606186 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2606187 : term258 = term265.
Proof. exact (@lem2606186 (NUMERAL 0) term64). Qed.
Lemma lem2606188 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2606189 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2606190 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2606189 h1) (fun h1 : term265 = True => @lem2606188)). Qed.
Lemma lem2606191 : term265 = True.
Proof. exact (EQ_MP (@lem2606190) (@lem2606188)). Qed.
Lemma lem2606192 : term258 = True.
Proof. exact (TRANS (@lem2606187) (@lem2606191)). Qed.
Lemma lem2606193 : True = term258.
Proof. exact (SYM (@lem2606192)). Qed.
Lemma lem2606194 : term258.
Proof. exact (EQ_MP (@lem2606193) (@lem0)). Qed.
Lemma lem2606195 : term298.
Proof. exact (@lem2606184 (@lem2606194)). Qed.
Lemma lem2606197 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2606198 : term258 = term265.
Proof. exact (@lem2606197 (NUMERAL 0) term64). Qed.
Lemma lem2606199 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2606200 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2606201 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2606200 h1) (fun h1 : term265 = True => @lem2606199)). Qed.
Lemma lem2606202 : term265 = True.
Proof. exact (EQ_MP (@lem2606201) (@lem2606199)). Qed.
Lemma lem2606203 : term258 = True.
Proof. exact (TRANS (@lem2606198) (@lem2606202)). Qed.
Lemma lem2606204 : True = term258.
Proof. exact (SYM (@lem2606203)). Qed.
Lemma lem2606205 : term258.
Proof. exact (EQ_MP (@lem2606204) (@lem0)). Qed.
Lemma lem2606206 : term299.
Proof. exact (@lem2606195 (@lem2606205)). Qed.
Lemma lem2606208 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2606209 : term258 = term265.
Proof. exact (@lem2606208 (NUMERAL 0) term64). Qed.
Lemma lem2606210 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2606211 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2606212 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2606211 h1) (fun h1 : term265 = True => @lem2606210)). Qed.
Lemma lem2606213 : term265 = True.
Proof. exact (EQ_MP (@lem2606212) (@lem2606210)). Qed.
Lemma lem2606214 : term258 = True.
Proof. exact (TRANS (@lem2606209) (@lem2606213)). Qed.
Lemma lem2606215 : True = term258.
Proof. exact (SYM (@lem2606214)). Qed.
Lemma lem2606216 : term258.
Proof. exact (EQ_MP (@lem2606215) (@lem0)). Qed.
Lemma lem2606217 : term300.
Proof. exact (@lem2606206 (@lem2606216)). Qed.
Lemma lem2606219 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2606220 : term144 = term145.
Proof. exact (@lem2606219 term64 term64). Qed.
Lemma lem2606221 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2606222 : term147 = term64.
Proof. exact (EQ_MP (@lem2606221) (@lem940073)). Qed.
Lemma lem2606223 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2606224 : term145 = term63.
Proof. exact (MK_COMB (@lem2606223) (@lem2606222)). Qed.
Lemma lem2606225 : term144 = term63.
Proof. exact (TRANS (@lem2606220) (@lem2606224)). Qed.
Lemma lem2606227 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2606228 : term172 = term177.
Proof. exact (@lem2606227 term64 term64). Qed.
Lemma lem2606229 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2606230 : term147 = term64.
Proof. exact (EQ_MP (@lem2606229) (@lem940073)). Qed.
Lemma lem2606231 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2606232 : term145 = term63.
Proof. exact (MK_COMB (@lem2606231) (@lem2606230)). Qed.
Lemma lem2606233 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2606234 : term177 = term127.
Proof. exact (MK_COMB (@lem2606233) (@lem2606232)). Qed.
Lemma lem2606235 : term172 = term127.
Proof. exact (TRANS (@lem2606228) (@lem2606234)). Qed.
Lemma lem2606236 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2606237 : term301 = term293.
Proof. exact (MK_COMB (@lem2606236) (@lem2606235)). Qed.
Lemma lem2606238 : term302 = term295.
Proof. exact (MK_COMB (@lem2606237) (@lem2606225)). Qed.
Lemma lem2606240 (m : nat) : (term303 m) = term160.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2606241 : term295 = term160.
Proof. exact (@lem2606240 term64). Qed.
Lemma lem2606242 : term302 = term160.
Proof. exact (TRANS (@lem2606238) (@lem2606241)). Qed.
Lemma lem2606243 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2606244 : term304 = term305.
Proof. exact (MK_COMB (@lem2606243) (@lem2606242)). Qed.
Lemma lem2606245 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2606246 : term306 = term270.
Proof. exact (MK_COMB (@lem2606244) (@lem2606245)). Qed.
Lemma lem2606248 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2606249 : term270 = term160.
Proof. exact (@lem2606248 term64). Qed.
Lemma lem2606250 : term306 = term160.
Proof. exact (TRANS (@lem2606246) (@lem2606249)). Qed.
Lemma lem2606252 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2606253 : term144 = term145.
Proof. exact (@lem2606252 term64 term64). Qed.
Lemma lem2606254 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2606255 : term147 = term64.
Proof. exact (EQ_MP (@lem2606254) (@lem940073)). Qed.
Lemma lem2606256 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2606257 : term145 = term63.
Proof. exact (MK_COMB (@lem2606256) (@lem2606255)). Qed.
Lemma lem2606258 : term144 = term63.
Proof. exact (TRANS (@lem2606253) (@lem2606257)). Qed.
Lemma lem2606259 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem2606260 : term307 = term270.
Proof. exact (MK_COMB (@lem2606259) (@lem2606258)). Qed.
Lemma lem2606262 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2606263 : term270 = term160.
Proof. exact (@lem2606262 term64). Qed.
Lemma lem2606264 : term307 = term160.
Proof. exact (TRANS (@lem2606260) (@lem2606263)). Qed.
Lemma lem2606265 : term160 = term307.
Proof. exact (SYM (@lem2606264)). Qed.
Lemma lem2606266 : term306 = term307.
Proof. exact (TRANS (@lem2606250) (@lem2606265)). Qed.
Lemma lem2606267 : term296 = term259.
Proof. exact (@lem2606217 (@lem2606266)). Qed.
Lemma lem2606268 : term295 = term259.
Proof. exact (TRANS (@lem2606183) (@lem2606267)). Qed.
Lemma lem2606270 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2606271 : term259 = term160.
Proof. exact (@lem2606270 term160). Qed.
Lemma lem2606272 : term295 = term160.
Proof. exact (TRANS (@lem2606268) (@lem2606271)). Qed.
Lemma lem2606273 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2606274 : term308 = term305.
Proof. exact (MK_COMB (@lem2606273) (@lem2606272)). Qed.
Lemma lem2606275 (q : int) (n : nat) : (term530 q n) = (term530 q n).
Proof. exact (eq_refl (term530 q n)). Qed.
Lemma lem2606276 (q : int) (n : nat) : (term585 q n) = (term586 q n).
Proof. exact (MK_COMB (@lem2606274) (@lem2606275 q n)). Qed.
Lemma lem2606277 (q : int) (n : nat) : (term584 q n) = (term586 q n).
Proof. exact (TRANS (@lem2606174 q n) (@lem2606276 q n)). Qed.
Lemma lem2606278 (q : int) (n : nat) : (term586 q n) = term160.
Proof. exact (@lem1982719 (term530 q n)). Qed.
Lemma lem2606279 (q : int) (n : nat) : (term584 q n) = term160.
Proof. exact (TRANS (@lem2606277 q n) (@lem2606278 q n)). Qed.
Lemma lem2606280 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2606281 (q : int) (n : nat) : (term587 q n) = term311.
Proof. exact (MK_COMB (@lem2606280) (@lem2606279 q n)). Qed.
Lemma lem2606282 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem2606283 (q : int) (n : nat) : (term583 q n) = term318.
Proof. exact (MK_COMB (@lem2606281 q n) (@lem2606282)). Qed.
Lemma lem2606284 (q : int) (n : nat) : (term582 q n) = term318.
Proof. exact (TRANS (@lem2606173 q n) (@lem2606283 q n)). Qed.
Lemma lem2606285 : term318 = term127.
Proof. exact (@lem1982721 term127). Qed.
Lemma lem2606286 (q : int) (n : nat) : (term582 q n) = term127.
Proof. exact (TRANS (@lem2606284 q n) (@lem2606285)). Qed.
Lemma lem2606287 (q : int) (n : nat) : (term574 q n) = term127.
Proof. exact (TRANS (@lem2606172 q n) (@lem2606286 q n)). Qed.
Lemma lem2606288 (q : int) (n : nat) : (term573 q n) = term127.
Proof. exact (TRANS (@lem2606085 q n) (@lem2606287 q n)). Qed.
Lemma lem2606289 (q : int) (n : nat) : (term572 q n) = term127.
Proof. exact (TRANS (@lem2606084 q n) (@lem2606288 q n)). Qed.
Lemma lem2606290 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2606291 (q : int) (n : nat) : (term588 q n) = term320.
Proof. exact (MK_COMB (@lem2606290) (@lem2606289 q n)). Qed.
Lemma lem2606292 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2606293 (q : int) (n : nat) : (term562 q n) = term321.
Proof. exact (MK_COMB (@lem2606291 q n) (@lem2606292)). Qed.
Lemma lem2606294 (n : nat) (q : int) : (term546 n q) = term321.
Proof. exact (TRANS (@lem2606039 q n) (@lem2606293 q n)). Qed.
Lemma lem2606295 (n : nat) (q : int) : (term559 q n) = (term589 n q).
Proof. exact (@lem1988287 (term535 q n) (term556 n q)). Qed.
Lemma lem2606296 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2606303 (q : int) : (term44 q) = (term124 q).
Proof. exact (@lem1982785 (real_of_int q)). Qed.
Lemma lem2606306 (n : nat) : (term544 n) = (term544 n).
Proof. exact (eq_refl (term544 n)). Qed.
Lemma lem2606307 (n : nat) (q : int) : (term545 n q) = (term567 n q).
Proof. exact (MK_COMB (@lem2606306 n) (@lem2606303 q)). Qed.
Lemma lem2606308 (n : nat) (q : int) : (term567 n q) = (term568 n q).
Proof. exact (@lem1982751 term127 (real_of_num n) (real_of_int q)). Qed.
Lemma lem2606309 (q : int) (n : nat) : (term569 n q) = (term530 q n).
Proof. exact (@lem1982747 (real_of_int q) (real_of_num n)). Qed.
Lemma lem2606310 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem2606311 (q : int) (n : nat) : (term568 n q) = (term564 q n).
Proof. exact (MK_COMB (@lem2606310) (@lem2606309 q n)). Qed.
Lemma lem2606312 (q : int) (n : nat) : (term567 n q) = (term564 q n).
Proof. exact (TRANS (@lem2606308 n q) (@lem2606311 q n)). Qed.
Lemma lem2606313 (q : int) (n : nat) : (term545 n q) = (term564 q n).
Proof. exact (TRANS (@lem2606307 n q) (@lem2606312 q n)). Qed.
Lemma lem2606314 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2606315 (q : int) (n : nat) : (term555 n q) = (term565 q n).
Proof. exact (MK_COMB (@lem2606314) (@lem2606313 q n)). Qed.
Lemma lem2606318 (q : int) (n : nat) : (term556 n q) = (term566 q n).
Proof. exact (MK_COMB (@lem2606315 q n) (@lem2606296)). Qed.
Lemma lem2606331 (q : int) (n : nat) : (term534 q n) = (term530 q n).
Proof. exact (@lem1982723 (term530 q n)). Qed.
Lemma lem2606332 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2606333 (q : int) (n : nat) : (term535 q n) = (term563 q n).
Proof. exact (MK_COMB (@lem2606332) (@lem2606331 q n)). Qed.
Lemma lem2606336 (q : int) (n : nat) : (term563 q n) = (term564 q n).
Proof. exact (@lem1982785 (term530 q n)). Qed.
Lemma lem2606337 (q : int) (n : nat) : (term535 q n) = (term564 q n).
Proof. exact (TRANS (@lem2606333 q n) (@lem2606336 q n)). Qed.
Lemma lem2606338 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2606339 (q : int) (n : nat) : (term590 q n) = (term571 q n).
Proof. exact (MK_COMB (@lem2606338) (@lem2606337 q n)). Qed.
Lemma lem2606340 (q : int) (n : nat) : (term591 n q) = (term573 q n).
Proof. exact (MK_COMB (@lem2606339 q n) (@lem2606318 q n)). Qed.
Lemma lem2606341 (q : int) (n : nat) : (term573 q n) = (term574 q n).
Proof. exact (@lem1982792 (term564 q n) (term566 q n)). Qed.
Lemma lem2606342 (q : int) (n : nat) : (term575 q n) = (term576 q n).
Proof. exact (@lem1982781 (term564 q n) term127 term63). Qed.
Lemma lem2606344 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2606345 : term63 = term151.
Proof. exact (@lem2606344 term64). Qed.
Lemma lem2606347 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2606348 : term127 = term137.
Proof. exact (@lem2606347 term64). Qed.
Lemma lem2606349 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2606350 : term128 = term138.
Proof. exact (MK_COMB (@lem2606349) (@lem2606348)). Qed.
Lemma lem2606351 : term172 = term173.
Proof. exact (MK_COMB (@lem2606350) (@lem2606345)). Qed.
Lemma lem2606352 : term173 = term174.
Proof. exact (@lem1981613 term127 term63 term63 term63). Qed.
Lemma lem2606354 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2606355 : term144 = term145.
Proof. exact (@lem2606354 term64 term64). Qed.
Lemma lem2606356 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2606357 : term147 = term64.
Proof. exact (EQ_MP (@lem2606356) (@lem940073)). Qed.
Lemma lem2606358 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2606359 : term145 = term63.
Proof. exact (MK_COMB (@lem2606358) (@lem2606357)). Qed.
Lemma lem2606360 : term144 = term63.
Proof. exact (TRANS (@lem2606355) (@lem2606359)). Qed.
Lemma lem2606362 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2606363 : term172 = term177.
Proof. exact (@lem2606362 term64 term64). Qed.
Lemma lem2606364 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2606365 : term147 = term64.
Proof. exact (EQ_MP (@lem2606364) (@lem940073)). Qed.
Lemma lem2606366 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2606367 : term145 = term63.
Proof. exact (MK_COMB (@lem2606366) (@lem2606365)). Qed.
Lemma lem2606368 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2606369 : term177 = term127.
Proof. exact (MK_COMB (@lem2606368) (@lem2606367)). Qed.
Lemma lem2606370 : term172 = term127.
Proof. exact (TRANS (@lem2606363) (@lem2606369)). Qed.
Lemma lem2606371 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2606372 : term178 = term179.
Proof. exact (MK_COMB (@lem2606371) (@lem2606370)). Qed.
Lemma lem2606373 : term174 = term137.
Proof. exact (MK_COMB (@lem2606372) (@lem2606360)). Qed.
Lemma lem2606374 : term173 = term137.
Proof. exact (TRANS (@lem2606352) (@lem2606373)). Qed.
Lemma lem2606375 : term172 = term137.
Proof. exact (TRANS (@lem2606351) (@lem2606374)). Qed.
Lemma lem2606377 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2606378 : term137 = term127.
Proof. exact (@lem2606377 term127). Qed.
Lemma lem2606379 : term172 = term127.
Proof. exact (TRANS (@lem2606375) (@lem2606378)). Qed.
Lemma lem2606380 (q : int) (n : nat) : (term577 q n) = (term578 q n).
Proof. exact (@lem1982749 term127 term127 (term530 q n)). Qed.
Lemma lem2606382 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2606383 : term127 = term137.
Proof. exact (@lem2606382 term64). Qed.
Lemma lem2606385 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2606386 : term127 = term137.
Proof. exact (@lem2606385 term64). Qed.
Lemma lem2606387 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2606388 : term128 = term138.
Proof. exact (MK_COMB (@lem2606387) (@lem2606386)). Qed.
Lemma lem2606389 : term139 = term140.
Proof. exact (MK_COMB (@lem2606388) (@lem2606383)). Qed.
Lemma lem2606390 : term140 = term141.
Proof. exact (@lem1981613 term127 term127 term63 term63). Qed.
Lemma lem2606392 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2606393 : term144 = term145.
Proof. exact (@lem2606392 term64 term64). Qed.
Lemma lem2606394 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2606395 : term147 = term64.
Proof. exact (EQ_MP (@lem2606394) (@lem940073)). Qed.
Lemma lem2606396 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2606397 : term145 = term63.
Proof. exact (MK_COMB (@lem2606396) (@lem2606395)). Qed.
Lemma lem2606398 : term144 = term63.
Proof. exact (TRANS (@lem2606393) (@lem2606397)). Qed.
Lemma lem2606400 (m : nat) (n : nat) : (term148 m n) = (term143 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2606401 : term139 = term145.
Proof. exact (@lem2606400 term64 term64). Qed.
Lemma lem2606402 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2606403 : term147 = term64.
Proof. exact (EQ_MP (@lem2606402) (@lem940073)). Qed.
Lemma lem2606404 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2606405 : term145 = term63.
Proof. exact (MK_COMB (@lem2606404) (@lem2606403)). Qed.
Lemma lem2606406 : term139 = term63.
Proof. exact (TRANS (@lem2606401) (@lem2606405)). Qed.
Lemma lem2606407 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2606408 : term149 = term150.
Proof. exact (MK_COMB (@lem2606407) (@lem2606406)). Qed.
Lemma lem2606409 : term141 = term151.
Proof. exact (MK_COMB (@lem2606408) (@lem2606398)). Qed.
Lemma lem2606410 : term140 = term151.
Proof. exact (TRANS (@lem2606390) (@lem2606409)). Qed.
Lemma lem2606411 : term139 = term151.
Proof. exact (TRANS (@lem2606389) (@lem2606410)). Qed.
Lemma lem2606413 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2606414 : term151 = term63.
Proof. exact (@lem2606413 term63). Qed.
Lemma lem2606415 : term139 = term63.
Proof. exact (TRANS (@lem2606411) (@lem2606414)). Qed.
Lemma lem2606416 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2606417 : term153 = term154.
Proof. exact (MK_COMB (@lem2606416) (@lem2606415)). Qed.
Lemma lem2606418 (q : int) (n : nat) : (term530 q n) = (term530 q n).
Proof. exact (eq_refl (term530 q n)). Qed.
Lemma lem2606419 (q : int) (n : nat) : (term578 q n) = (term579 q n).
Proof. exact (MK_COMB (@lem2606417) (@lem2606418 q n)). Qed.
Lemma lem2606420 (q : int) (n : nat) : (term577 q n) = (term579 q n).
Proof. exact (TRANS (@lem2606380 q n) (@lem2606419 q n)). Qed.
Lemma lem2606421 (q : int) (n : nat) : (term579 q n) = (term530 q n).
Proof. exact (@lem1982709 (term530 q n)). Qed.
Lemma lem2606422 (q : int) (n : nat) : (term577 q n) = (term530 q n).
Proof. exact (TRANS (@lem2606420 q n) (@lem2606421 q n)). Qed.
Lemma lem2606423 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2606424 (q : int) (n : nat) : (term580 q n) = (term532 q n).
Proof. exact (MK_COMB (@lem2606423) (@lem2606422 q n)). Qed.
Lemma lem2606425 (q : int) (n : nat) : (term576 q n) = (term581 q n).
Proof. exact (MK_COMB (@lem2606424 q n) (@lem2606379)). Qed.
Lemma lem2606426 (q : int) (n : nat) : (term575 q n) = (term581 q n).
Proof. exact (TRANS (@lem2606342 q n) (@lem2606425 q n)). Qed.
Lemma lem2606427 (q : int) (n : nat) : (term565 q n) = (term565 q n).
Proof. exact (eq_refl (term565 q n)). Qed.
Lemma lem2606428 (q : int) (n : nat) : (term574 q n) = (term582 q n).
Proof. exact (MK_COMB (@lem2606427 q n) (@lem2606426 q n)). Qed.
Lemma lem2606429 (q : int) (n : nat) : (term582 q n) = (term583 q n).
Proof. exact (@lem1982763 (term564 q n) (term530 q n) term127). Qed.
Lemma lem2606430 (q : int) (n : nat) : (term584 q n) = (term585 q n).
Proof. exact (@lem1982713 term127 (term530 q n)). Qed.
Lemma lem2606432 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2606433 : term63 = term151.
Proof. exact (@lem2606432 term64). Qed.
Lemma lem2606435 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2606436 : term127 = term137.
Proof. exact (@lem2606435 term64). Qed.
Lemma lem2606437 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2606438 : term293 = term294.
Proof. exact (MK_COMB (@lem2606437) (@lem2606436)). Qed.
Lemma lem2606439 : term295 = term296.
Proof. exact (MK_COMB (@lem2606438) (@lem2606433)). Qed.
Lemma lem2606440 : term297.
Proof. exact (@lem1981473 term127 term63 term63 term63 term160 term63). Qed.
Lemma lem2606442 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2606443 : term258 = term265.
Proof. exact (@lem2606442 (NUMERAL 0) term64). Qed.
Lemma lem2606444 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2606445 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2606446 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2606445 h1) (fun h1 : term265 = True => @lem2606444)). Qed.
Lemma lem2606447 : term265 = True.
Proof. exact (EQ_MP (@lem2606446) (@lem2606444)). Qed.
Lemma lem2606448 : term258 = True.
Proof. exact (TRANS (@lem2606443) (@lem2606447)). Qed.
Lemma lem2606449 : True = term258.
Proof. exact (SYM (@lem2606448)). Qed.
Lemma lem2606450 : term258.
Proof. exact (EQ_MP (@lem2606449) (@lem0)). Qed.
Lemma lem2606451 : term298.
Proof. exact (@lem2606440 (@lem2606450)). Qed.
Lemma lem2606453 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2606454 : term258 = term265.
Proof. exact (@lem2606453 (NUMERAL 0) term64). Qed.
Lemma lem2606455 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2606456 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2606457 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2606456 h1) (fun h1 : term265 = True => @lem2606455)). Qed.
Lemma lem2606458 : term265 = True.
Proof. exact (EQ_MP (@lem2606457) (@lem2606455)). Qed.
Lemma lem2606459 : term258 = True.
Proof. exact (TRANS (@lem2606454) (@lem2606458)). Qed.
Lemma lem2606460 : True = term258.
Proof. exact (SYM (@lem2606459)). Qed.
Lemma lem2606461 : term258.
Proof. exact (EQ_MP (@lem2606460) (@lem0)). Qed.
Lemma lem2606462 : term299.
Proof. exact (@lem2606451 (@lem2606461)). Qed.
Lemma lem2606464 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2606465 : term258 = term265.
Proof. exact (@lem2606464 (NUMERAL 0) term64). Qed.
Lemma lem2606466 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2606467 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2606468 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2606467 h1) (fun h1 : term265 = True => @lem2606466)). Qed.
Lemma lem2606469 : term265 = True.
Proof. exact (EQ_MP (@lem2606468) (@lem2606466)). Qed.
Lemma lem2606470 : term258 = True.
Proof. exact (TRANS (@lem2606465) (@lem2606469)). Qed.
Lemma lem2606471 : True = term258.
Proof. exact (SYM (@lem2606470)). Qed.
Lemma lem2606472 : term258.
Proof. exact (EQ_MP (@lem2606471) (@lem0)). Qed.
Lemma lem2606473 : term300.
Proof. exact (@lem2606462 (@lem2606472)). Qed.
Lemma lem2606475 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2606476 : term144 = term145.
Proof. exact (@lem2606475 term64 term64). Qed.
Lemma lem2606477 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2606478 : term147 = term64.
Proof. exact (EQ_MP (@lem2606477) (@lem940073)). Qed.
Lemma lem2606479 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2606480 : term145 = term63.
Proof. exact (MK_COMB (@lem2606479) (@lem2606478)). Qed.
Lemma lem2606481 : term144 = term63.
Proof. exact (TRANS (@lem2606476) (@lem2606480)). Qed.
Lemma lem2606483 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2606484 : term172 = term177.
Proof. exact (@lem2606483 term64 term64). Qed.
Lemma lem2606485 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2606486 : term147 = term64.
Proof. exact (EQ_MP (@lem2606485) (@lem940073)). Qed.
Lemma lem2606487 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2606488 : term145 = term63.
Proof. exact (MK_COMB (@lem2606487) (@lem2606486)). Qed.
Lemma lem2606489 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2606490 : term177 = term127.
Proof. exact (MK_COMB (@lem2606489) (@lem2606488)). Qed.
Lemma lem2606491 : term172 = term127.
Proof. exact (TRANS (@lem2606484) (@lem2606490)). Qed.
Lemma lem2606492 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2606493 : term301 = term293.
Proof. exact (MK_COMB (@lem2606492) (@lem2606491)). Qed.
Lemma lem2606494 : term302 = term295.
Proof. exact (MK_COMB (@lem2606493) (@lem2606481)). Qed.
Lemma lem2606496 (m : nat) : (term303 m) = term160.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2606497 : term295 = term160.
Proof. exact (@lem2606496 term64). Qed.
Lemma lem2606498 : term302 = term160.
Proof. exact (TRANS (@lem2606494) (@lem2606497)). Qed.
Lemma lem2606499 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2606500 : term304 = term305.
Proof. exact (MK_COMB (@lem2606499) (@lem2606498)). Qed.
Lemma lem2606501 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2606502 : term306 = term270.
Proof. exact (MK_COMB (@lem2606500) (@lem2606501)). Qed.
Lemma lem2606504 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2606505 : term270 = term160.
Proof. exact (@lem2606504 term64). Qed.
Lemma lem2606506 : term306 = term160.
Proof. exact (TRANS (@lem2606502) (@lem2606505)). Qed.
Lemma lem2606508 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2606509 : term144 = term145.
Proof. exact (@lem2606508 term64 term64). Qed.
Lemma lem2606510 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2606511 : term147 = term64.
Proof. exact (EQ_MP (@lem2606510) (@lem940073)). Qed.
Lemma lem2606512 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2606513 : term145 = term63.
Proof. exact (MK_COMB (@lem2606512) (@lem2606511)). Qed.
Lemma lem2606514 : term144 = term63.
Proof. exact (TRANS (@lem2606509) (@lem2606513)). Qed.
Lemma lem2606515 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem2606516 : term307 = term270.
Proof. exact (MK_COMB (@lem2606515) (@lem2606514)). Qed.
Lemma lem2606518 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2606519 : term270 = term160.
Proof. exact (@lem2606518 term64). Qed.
Lemma lem2606520 : term307 = term160.
Proof. exact (TRANS (@lem2606516) (@lem2606519)). Qed.
Lemma lem2606521 : term160 = term307.
Proof. exact (SYM (@lem2606520)). Qed.
Lemma lem2606522 : term306 = term307.
Proof. exact (TRANS (@lem2606506) (@lem2606521)). Qed.
Lemma lem2606523 : term296 = term259.
Proof. exact (@lem2606473 (@lem2606522)). Qed.
Lemma lem2606524 : term295 = term259.
Proof. exact (TRANS (@lem2606439) (@lem2606523)). Qed.
Lemma lem2606526 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2606527 : term259 = term160.
Proof. exact (@lem2606526 term160). Qed.
Lemma lem2606528 : term295 = term160.
Proof. exact (TRANS (@lem2606524) (@lem2606527)). Qed.
Lemma lem2606529 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2606530 : term308 = term305.
Proof. exact (MK_COMB (@lem2606529) (@lem2606528)). Qed.
Lemma lem2606531 (q : int) (n : nat) : (term530 q n) = (term530 q n).
Proof. exact (eq_refl (term530 q n)). Qed.
Lemma lem2606532 (q : int) (n : nat) : (term585 q n) = (term586 q n).
Proof. exact (MK_COMB (@lem2606530) (@lem2606531 q n)). Qed.
Lemma lem2606533 (q : int) (n : nat) : (term584 q n) = (term586 q n).
Proof. exact (TRANS (@lem2606430 q n) (@lem2606532 q n)). Qed.
Lemma lem2606534 (q : int) (n : nat) : (term586 q n) = term160.
Proof. exact (@lem1982719 (term530 q n)). Qed.
Lemma lem2606535 (q : int) (n : nat) : (term584 q n) = term160.
Proof. exact (TRANS (@lem2606533 q n) (@lem2606534 q n)). Qed.
Lemma lem2606536 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2606537 (q : int) (n : nat) : (term587 q n) = term311.
Proof. exact (MK_COMB (@lem2606536) (@lem2606535 q n)). Qed.
Lemma lem2606538 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem2606539 (q : int) (n : nat) : (term583 q n) = term318.
Proof. exact (MK_COMB (@lem2606537 q n) (@lem2606538)). Qed.
Lemma lem2606540 (q : int) (n : nat) : (term582 q n) = term318.
Proof. exact (TRANS (@lem2606429 q n) (@lem2606539 q n)). Qed.
Lemma lem2606541 : term318 = term127.
Proof. exact (@lem1982721 term127). Qed.
Lemma lem2606542 (q : int) (n : nat) : (term582 q n) = term127.
Proof. exact (TRANS (@lem2606540 q n) (@lem2606541)). Qed.
Lemma lem2606543 (q : int) (n : nat) : (term574 q n) = term127.
Proof. exact (TRANS (@lem2606428 q n) (@lem2606542 q n)). Qed.
Lemma lem2606544 (q : int) (n : nat) : (term573 q n) = term127.
Proof. exact (TRANS (@lem2606341 q n) (@lem2606543 q n)). Qed.
Lemma lem2606545 (n : nat) (q : int) : (term591 n q) = term127.
Proof. exact (TRANS (@lem2606340 q n) (@lem2606544 q n)). Qed.
Lemma lem2606546 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2606547 (n : nat) (q : int) : (term592 n q) = term320.
Proof. exact (MK_COMB (@lem2606546) (@lem2606545 n q)). Qed.
Lemma lem2606548 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2606549 (n : nat) (q : int) : (term589 n q) = term321.
Proof. exact (MK_COMB (@lem2606547 n q) (@lem2606548)). Qed.
Lemma lem2606550 (q : int) (n : nat) : (term559 q n) = term321.
Proof. exact (TRANS (@lem2606295 n q) (@lem2606549 n q)). Qed.
Lemma lem2606551 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2606552 (n : nat) (q : int) : (term548 n q) = term593.
Proof. exact (MK_COMB (@lem2606551) (@lem2606294 n q)). Qed.
Lemma lem2606553 (q : int) (n : nat) : (term560 q n) = term594.
Proof. exact (MK_COMB (@lem2606552 n q) (@lem2606550 q n)). Qed.
Lemma lem2606566 (q : int) (n : nat) : (term561 q n) = term594.
Proof. exact (TRANS (@lem2606038 q n) (@lem2606553 q n)). Qed.
Lemma lem2606576 (h1 : term594) : term594.
Proof. exact (h1). Qed.
Lemma lem2606577 (h1 : term321) : term321.
Proof. exact (h1). Qed.
Lemma lem2606579 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2606580 : term321 = term322.
Proof. exact (@lem2606579 term160 term127). Qed.
Lemma lem2606582 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2606583 : term127 = term137.
Proof. exact (@lem2606582 term64). Qed.
Lemma lem2606585 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2606586 : term160 = term259.
Proof. exact (@lem2606585 (NUMERAL 0)). Qed.
Lemma lem2606587 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2606588 : term323 = term324.
Proof. exact (MK_COMB (@lem2606587) (@lem2606586)). Qed.
Lemma lem2606589 : term322 = term325.
Proof. exact (MK_COMB (@lem2606588) (@lem2606583)). Qed.
Lemma lem2606590 : term326.
Proof. exact (@lem1980026 term160 term63 term127 term63). Qed.
Lemma lem2606592 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2606593 : term258 = term265.
Proof. exact (@lem2606592 (NUMERAL 0) term64). Qed.
Lemma lem2606594 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2606595 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2606596 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2606595 h1) (fun h1 : term265 = True => @lem2606594)). Qed.
Lemma lem2606597 : term265 = True.
Proof. exact (EQ_MP (@lem2606596) (@lem2606594)). Qed.
Lemma lem2606598 : term258 = True.
Proof. exact (TRANS (@lem2606593) (@lem2606597)). Qed.
Lemma lem2606599 : True = term258.
Proof. exact (SYM (@lem2606598)). Qed.
Lemma lem2606600 : term258.
Proof. exact (EQ_MP (@lem2606599) (@lem0)). Qed.
Lemma lem2606601 : term327.
Proof. exact (@lem2606590 (@lem2606600)). Qed.
Lemma lem2606603 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2606604 : term258 = term265.
Proof. exact (@lem2606603 (NUMERAL 0) term64). Qed.
Lemma lem2606605 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2606606 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2606607 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2606606 h1) (fun h1 : term265 = True => @lem2606605)). Qed.
Lemma lem2606608 : term265 = True.
Proof. exact (EQ_MP (@lem2606607) (@lem2606605)). Qed.
Lemma lem2606609 : term258 = True.
Proof. exact (TRANS (@lem2606604) (@lem2606608)). Qed.
Lemma lem2606610 : True = term258.
Proof. exact (SYM (@lem2606609)). Qed.
Lemma lem2606611 : term258.
Proof. exact (EQ_MP (@lem2606610) (@lem0)). Qed.
Lemma lem2606612 : term325 = term328.
Proof. exact (@lem2606601 (@lem2606611)). Qed.
Lemma lem2606614 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2606615 : term172 = term177.
Proof. exact (@lem2606614 term64 term64). Qed.
Lemma lem2606616 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2606617 : term147 = term64.
Proof. exact (EQ_MP (@lem2606616) (@lem940073)). Qed.
Lemma lem2606618 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2606619 : term145 = term63.
Proof. exact (MK_COMB (@lem2606618) (@lem2606617)). Qed.
Lemma lem2606620 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2606621 : term177 = term127.
Proof. exact (MK_COMB (@lem2606620) (@lem2606619)). Qed.
Lemma lem2606622 : term172 = term127.
Proof. exact (TRANS (@lem2606615) (@lem2606621)). Qed.
Lemma lem2606624 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2606625 : term270 = term160.
Proof. exact (@lem2606624 term64). Qed.
Lemma lem2606626 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2606627 : term329 = term323.
Proof. exact (MK_COMB (@lem2606626) (@lem2606625)). Qed.
Lemma lem2606628 : term328 = term322.
Proof. exact (MK_COMB (@lem2606627) (@lem2606622)). Qed.
Lemma lem2606630 (m : nat) (n : nat) : (term330 m n) = (term331 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2606631 : term322 = term332.
Proof. exact (@lem2606630 (NUMERAL 0) term64). Qed.
Lemma lem2606632 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2606633 (h1 : term266 = (BIT1 0)) : (term64 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2606634 : (term266 = (BIT1 0)) = ((term64 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2606633 h1) (fun h1 : (term64 = (NUMERAL 0)) = False => @lem2606632)). Qed.
Lemma lem2606635 : (term64 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2606634) (@lem2606632)). Qed.
Lemma lem2606636 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2606637 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2606638 : term333 = (and True).
Proof. exact (MK_COMB (@lem2606637) (@lem2606636)). Qed.
Lemma lem2606639 : term332 = (True /\ False).
Proof. exact (MK_COMB (@lem2606638) (@lem2606635)). Qed.
Lemma lem2606641 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2606642 : term332 = False.
Proof. exact (TRANS (@lem2606639) (@lem2606641)). Qed.
Lemma lem2606643 : term322 = False.
Proof. exact (TRANS (@lem2606631) (@lem2606642)). Qed.
Lemma lem2606644 : term328 = False.
Proof. exact (TRANS (@lem2606628) (@lem2606643)). Qed.
Lemma lem2606645 : term325 = False.
Proof. exact (TRANS (@lem2606612) (@lem2606644)). Qed.
Lemma lem2606646 : term322 = False.
Proof. exact (TRANS (@lem2606589) (@lem2606645)). Qed.
Lemma lem2606647 : term321 = False.
Proof. exact (TRANS (@lem2606580) (@lem2606646)). Qed.
Lemma lem2606648 (h1 : term321) : False.
Proof. exact (EQ_MP (@lem2606647) (@lem2606577 h1)). Qed.
Lemma lem2606649 (h1 : term321) : term321.
Proof. exact (h1). Qed.
Lemma lem2606651 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2606652 : term321 = term322.
Proof. exact (@lem2606651 term160 term127). Qed.
Lemma lem2606654 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2606655 : term127 = term137.
Proof. exact (@lem2606654 term64). Qed.
Lemma lem2606657 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2606658 : term160 = term259.
Proof. exact (@lem2606657 (NUMERAL 0)). Qed.
Lemma lem2606659 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2606660 : term323 = term324.
Proof. exact (MK_COMB (@lem2606659) (@lem2606658)). Qed.
Lemma lem2606661 : term322 = term325.
Proof. exact (MK_COMB (@lem2606660) (@lem2606655)). Qed.
Lemma lem2606662 : term326.
Proof. exact (@lem1980026 term160 term63 term127 term63). Qed.
Lemma lem2606664 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2606665 : term258 = term265.
Proof. exact (@lem2606664 (NUMERAL 0) term64). Qed.
Lemma lem2606666 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2606667 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2606668 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2606667 h1) (fun h1 : term265 = True => @lem2606666)). Qed.
Lemma lem2606669 : term265 = True.
Proof. exact (EQ_MP (@lem2606668) (@lem2606666)). Qed.
Lemma lem2606670 : term258 = True.
Proof. exact (TRANS (@lem2606665) (@lem2606669)). Qed.
Lemma lem2606671 : True = term258.
Proof. exact (SYM (@lem2606670)). Qed.
Lemma lem2606672 : term258.
Proof. exact (EQ_MP (@lem2606671) (@lem0)). Qed.
Lemma lem2606673 : term327.
Proof. exact (@lem2606662 (@lem2606672)). Qed.
Lemma lem2606675 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2606676 : term258 = term265.
Proof. exact (@lem2606675 (NUMERAL 0) term64). Qed.
Lemma lem2606677 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2606678 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2606679 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2606678 h1) (fun h1 : term265 = True => @lem2606677)). Qed.
Lemma lem2606680 : term265 = True.
Proof. exact (EQ_MP (@lem2606679) (@lem2606677)). Qed.
Lemma lem2606681 : term258 = True.
Proof. exact (TRANS (@lem2606676) (@lem2606680)). Qed.
Lemma lem2606682 : True = term258.
Proof. exact (SYM (@lem2606681)). Qed.
Lemma lem2606683 : term258.
Proof. exact (EQ_MP (@lem2606682) (@lem0)). Qed.
Lemma lem2606684 : term325 = term328.
Proof. exact (@lem2606673 (@lem2606683)). Qed.
Lemma lem2606686 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2606687 : term172 = term177.
Proof. exact (@lem2606686 term64 term64). Qed.
Lemma lem2606688 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2606689 : term147 = term64.
Proof. exact (EQ_MP (@lem2606688) (@lem940073)). Qed.
Lemma lem2606690 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2606691 : term145 = term63.
Proof. exact (MK_COMB (@lem2606690) (@lem2606689)). Qed.
Lemma lem2606692 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2606693 : term177 = term127.
Proof. exact (MK_COMB (@lem2606692) (@lem2606691)). Qed.
Lemma lem2606694 : term172 = term127.
Proof. exact (TRANS (@lem2606687) (@lem2606693)). Qed.
Lemma lem2606696 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2606697 : term270 = term160.
Proof. exact (@lem2606696 term64). Qed.
Lemma lem2606698 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2606699 : term329 = term323.
Proof. exact (MK_COMB (@lem2606698) (@lem2606697)). Qed.
Lemma lem2606700 : term328 = term322.
Proof. exact (MK_COMB (@lem2606699) (@lem2606694)). Qed.
Lemma lem2606702 (m : nat) (n : nat) : (term330 m n) = (term331 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2606703 : term322 = term332.
Proof. exact (@lem2606702 (NUMERAL 0) term64). Qed.
Lemma lem2606704 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2606705 (h1 : term266 = (BIT1 0)) : (term64 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2606706 : (term266 = (BIT1 0)) = ((term64 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2606705 h1) (fun h1 : (term64 = (NUMERAL 0)) = False => @lem2606704)). Qed.
Lemma lem2606707 : (term64 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2606706) (@lem2606704)). Qed.
Lemma lem2606708 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2606709 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2606710 : term333 = (and True).
Proof. exact (MK_COMB (@lem2606709) (@lem2606708)). Qed.
Lemma lem2606711 : term332 = (True /\ False).
Proof. exact (MK_COMB (@lem2606710) (@lem2606707)). Qed.
Lemma lem2606713 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2606714 : term332 = False.
Proof. exact (TRANS (@lem2606711) (@lem2606713)). Qed.
Lemma lem2606715 : term322 = False.
Proof. exact (TRANS (@lem2606703) (@lem2606714)). Qed.
Lemma lem2606716 : term328 = False.
Proof. exact (TRANS (@lem2606700) (@lem2606715)). Qed.
Lemma lem2606717 : term325 = False.
Proof. exact (TRANS (@lem2606684) (@lem2606716)). Qed.
Lemma lem2606718 : term322 = False.
Proof. exact (TRANS (@lem2606661) (@lem2606717)). Qed.
Lemma lem2606719 : term321 = False.
Proof. exact (TRANS (@lem2606652) (@lem2606718)). Qed.
Lemma lem2606720 (h1 : term321) : False.
Proof. exact (EQ_MP (@lem2606719) (@lem2606649 h1)). Qed.
Lemma lem2606721 (h1 : term594) : False.
Proof. exact (or_elim (@lem2606576 h1) (fun h0 : term321 => @lem2606648 h0) (fun h0 : term321 => @lem2606720 h0)). Qed.
Lemma lem2606723 (h1 : term594) : term594.
Proof. exact (h1). Qed.
Lemma lem2606724 (h1 : term594) : term594 = False.
Proof. exact (prop_ext (fun h2 : term594 => @lem2606721 h1) (fun h2 : False => @lem2606723 h1)). Qed.
Lemma lem2606725 (h1 : term594) : False.
Proof. exact (EQ_MP (@lem2606724 h1) (@lem2606723 h1)). Qed.
Lemma lem2606726 (q : int) (n : nat) (h1 : term561 q n) : term561 q n.
Proof. exact (h1). Qed.
Lemma lem2606727 (q : int) (n : nat) (h1 : term561 q n) : term594.
Proof. exact (EQ_MP (@lem2606566 q n) (@lem2606726 q n h1)). Qed.
Lemma lem2606728 (q : int) (n : nat) (h1 : term561 q n) : term594 = False.
Proof. exact (prop_ext (fun h2 : term594 => @lem2606725 h2) (fun h2 : False => @lem2606727 q n h1)). Qed.
Lemma lem2606729 (q : int) (n : nat) (h1 : term561 q n) : False.
Proof. exact (EQ_MP (@lem2606728 q n h1) (@lem2606727 q n h1)). Qed.
Lemma lem2606730 (q : int) (n : nat) : term595 q n.
Proof. exact (fun h0 : term561 q n => @lem2606729 q n h0). Qed.
Lemma lem2606731 (q : int) (n : nat) : term596 q n.
Proof. exact (@lem1386578 (term597 q n)). Qed.
Lemma lem2606734 (q : int) (n : nat) : term597 q n.
Proof. exact (@lem2606731 q n (@lem2606730 q n)). Qed.
Lemma lem2606735 (n : nat) (q : int) : (term560 q n) = (term514 n q).
Proof. exact (SYM (@lem2606018 q n)). Qed.
Lemma lem2606736 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2606737 (n : nat) (q : int) : (term597 q n) = (term511 n q).
Proof. exact (MK_COMB (@lem2606736) (@lem2606735 n q)). Qed.
Lemma lem2606738 (n : nat) (q : int) : term511 n q.
Proof. exact (EQ_MP (@lem2606737 n q) (@lem2606734 q n)). Qed.
Lemma lem2606740 (m : nat) (n : nat) (q : int) (h1 : (term598 m n) = q) : (term598 m n) = q.
Proof. exact (h1). Qed.
Lemma lem2606741 (m : nat) (n : nat) (q : int) (h1 : (term598 m n) = q) : term599 m n.
Proof. exact (ex_intro (term600 m n) q (@lem2606740 m n q h1)). Qed.
Lemma lem2606742 (m : nat) (n : nat) (h1 : term599 m n) : term599 m n.
Proof. exact (h1). Qed.
Lemma lem2606743 (m : nat) (n : nat) (h1 : term599 m n) : term599 m n.
Proof. exact (ex_elim (@lem2606742 m n h1) (fun q : int => fun h0 : term600 m n q => @lem2606741 m n q h0)). Qed.
Lemma lem2606744 (m : nat) (n : nat) : (term598 m n) = (term598 m n).
Proof. exact (eq_refl (term598 m n)). Qed.
Lemma lem2606745 (m : nat) (n : nat) : term599 m n.
Proof. exact (ex_intro (term600 m n) (term598 m n) (@lem2606744 m n)). Qed.
Lemma lem2606746 (m : nat) (n : nat) : (term599 m n) = (term599 m n).
Proof. exact (prop_ext (fun h1 : term599 m n => @lem2606743 m n h1) (fun h1 : term599 m n => @lem2606745 m n)). Qed.
Lemma lem2606747 (m : nat) (n : nat) : term599 m n.
Proof. exact (EQ_MP (@lem2606746 m n) (@lem2606745 m n)). Qed.
Lemma lem2606748 (m : nat) (n : nat) (r : int) (h1 : (term601 m n) = r) : (term601 m n) = r.
Proof. exact (h1). Qed.
Lemma lem2606749 (m : nat) (n : nat) (r : int) (h1 : (term601 m n) = r) : term602 m n.
Proof. exact (ex_intro (term603 m n) r (@lem2606748 m n r h1)). Qed.
Lemma lem2606750 (m : nat) (n : nat) (h1 : term602 m n) : term602 m n.
Proof. exact (h1). Qed.
Lemma lem2606751 (m : nat) (n : nat) (h1 : term602 m n) : term602 m n.
Proof. exact (ex_elim (@lem2606750 m n h1) (fun r : int => fun h0 : term603 m n r => @lem2606749 m n r h0)). Qed.
Lemma lem2606752 (m : nat) (n : nat) : (term601 m n) = (term601 m n).
Proof. exact (eq_refl (term601 m n)). Qed.
Lemma lem2606753 (m : nat) (n : nat) : term602 m n.
Proof. exact (ex_intro (term603 m n) (term601 m n) (@lem2606752 m n)). Qed.
Lemma lem2606754 (m : nat) (n : nat) : (term602 m n) = (term602 m n).
Proof. exact (prop_ext (fun h1 : term602 m n => @lem2606751 m n h1) (fun h1 : term602 m n => @lem2606753 m n)). Qed.
Lemma lem2606755 (m : nat) (n : nat) : term602 m n.
Proof. exact (EQ_MP (@lem2606754 m n) (@lem2606753 m n)). Qed.
Lemma lem2606756 (m : nat) : term604 m.
Proof. exact (@lem2389435 (int_of_num m)). Qed.
Lemma lem2606757 (m : nat) : (term604 m) = (term605 m).
Proof. exact (eq_refl (term604 m)). Qed.
Lemma lem2606758 (m : nat) : term605 m.
Proof. exact (EQ_MP (@lem2606757 m) (@lem2606756 m)). Qed.
Lemma lem2606759 (m : nat) (n : nat) : term606 m n.
Proof. exact (@lem2606758 m (int_of_num n)). Qed.
Lemma lem2606760 (m : nat) (n : nat) : (term606 m n) = (term607 m n).
Proof. exact (eq_refl (term606 m n)). Qed.
Lemma lem2606761 (m : nat) (n : nat) : term607 m n.
Proof. exact (EQ_MP (@lem2606760 m n) (@lem2606759 m n)). Qed.
Lemma lem2606762 (m : int) : term608 m.
Proof. exact (@lem2586280 m). Qed.
Lemma lem2606763 (m : int) : (term608 m) = (term609 m).
Proof. exact (eq_refl (term608 m)). Qed.
Lemma lem2606764 (m : int) : term609 m.
Proof. exact (EQ_MP (@lem2606763 m) (@lem2606762 m)). Qed.
Lemma lem2606765 (m : int) (n : int) : term610 m n.
Proof. exact (@lem2606764 m n). Qed.
Lemma lem2606766 (m : int) (n : int) : (term610 m n) = ((term611 m n) = (term612 m n)).
Proof. exact (eq_refl (term610 m n)). Qed.
Lemma lem2606768 (m : nat) (n : nat) : (term613 m n) = (term614 m n).
Proof. exact (@lem2318604 (term614 m n)). Qed.
Lemma lem2606771 (t : Prop) : (term121 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2606779 (m : nat) (n : nat) : (term615 m n) = (term616 m n).
Proof. exact (@lem2606771 (term616 m n)). Qed.
Lemma lem2606781 (x : int) (y : int) : (int_lt x y) = (term50 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem2606782 (m : nat) (n : nat) : (term616 m n) = (term617 m n).
Proof. exact (@lem2606781 (int_of_num m) (term618 n)). Qed.
Lemma lem2606784 (x : int) (y : int) : (int_le x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2606785 (m : nat) (n : nat) : (term617 m n) = (term619 m n).
Proof. exact (@lem2606784 (term620 m) (term618 n)). Qed.
Lemma lem2606787 (x : int) (y : int) : (term54 x y) = (term55 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2606788 (m : nat) : (term621 m) = (term622 m).
Proof. exact (@lem2606787 (int_of_num m) term58). Qed.
Lemma lem2606790 (n : nat) : (term61 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2606791 (m : nat) : (term61 m) = (real_of_num m).
Proof. exact (@lem2606790 m). Qed.
Lemma lem2606792 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2606793 (m : nat) : (term623 m) = (term624 m).
Proof. exact (MK_COMB (@lem2606792) (@lem2606791 m)). Qed.
Lemma lem2606795 (n : nat) : (term61 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2606796 : term62 = term63.
Proof. exact (@lem2606795 term64). Qed.
Lemma lem2606797 (m : nat) : (term622 m) = (term625 m).
Proof. exact (MK_COMB (@lem2606793 m) (@lem2606796)). Qed.
Lemma lem2606798 (m : nat) : (term621 m) = (term625 m).
Proof. exact (TRANS (@lem2606788 m) (@lem2606797 m)). Qed.
Lemma lem2606799 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2606800 (m : nat) : (term626 m) = (term627 m).
Proof. exact (MK_COMB (@lem2606799) (@lem2606798 m)). Qed.
Lemma lem2606802 (x : int) : (term43 x) = (term44 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2606803 (n : nat) : (term628 n) = (term629 n).
Proof. exact (@lem2606802 (int_of_num n)). Qed.
Lemma lem2606805 (n : nat) : (term61 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2606806 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2606807 (n : nat) : (term629 n) = (term135 n).
Proof. exact (MK_COMB (@lem2606806) (@lem2606805 n)). Qed.
Lemma lem2606808 (n : nat) : (term628 n) = (term135 n).
Proof. exact (TRANS (@lem2606803 n) (@lem2606807 n)). Qed.
Lemma lem2606809 (m : nat) (n : nat) : (term619 m n) = (term630 m n).
Proof. exact (MK_COMB (@lem2606800 m) (@lem2606808 n)). Qed.
Lemma lem2606810 (m : nat) (n : nat) : (term617 m n) = (term630 m n).
Proof. exact (TRANS (@lem2606785 m n) (@lem2606809 m n)). Qed.
Lemma lem2606811 (m : nat) (n : nat) : (term616 m n) = (term630 m n).
Proof. exact (TRANS (@lem2606782 m n) (@lem2606810 m n)). Qed.
Lemma lem2606812 (m : nat) (n : nat) : (term615 m n) = (term630 m n).
Proof. exact (TRANS (@lem2606779 m n) (@lem2606811 m n)). Qed.
Lemma lem2606816 (t : Prop) : (term121 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2606822 (m : nat) (n : nat) : (term631 m n) = (term630 m n).
Proof. exact (@lem2606816 (term630 m n)). Qed.
Lemma lem2606823 (n : nat) (m : nat) : (term630 m n) = (term632 n m).
Proof. exact (@lem1988287 (term135 n) (term625 m)). Qed.
Lemma lem2606830 (m : nat) : (term625 m) = (term625 m).
Proof. exact (eq_refl (term625 m)). Qed.
Lemma lem2606837 (n : nat) : (term135 n) = (term633 n).
Proof. exact (@lem1982785 (real_of_num n)). Qed.
Lemma lem2606838 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2606839 (n : nat) : (term634 n) = (term635 n).
Proof. exact (MK_COMB (@lem2606838) (@lem2606837 n)). Qed.
Lemma lem2606840 (n : nat) (m : nat) : (term636 n m) = (term637 n m).
Proof. exact (MK_COMB (@lem2606839 n) (@lem2606830 m)). Qed.
Lemma lem2606841 (n : nat) (m : nat) : (term637 n m) = (term638 n m).
Proof. exact (@lem1982792 (term633 n) (term625 m)). Qed.
Lemma lem2606842 (m : nat) : (term639 m) = (term640 m).
Proof. exact (@lem1982781 (real_of_num m) term127 term63). Qed.
Lemma lem2606844 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2606845 : term63 = term151.
Proof. exact (@lem2606844 term64). Qed.
Lemma lem2606847 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2606848 : term127 = term137.
Proof. exact (@lem2606847 term64). Qed.
Lemma lem2606849 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2606850 : term128 = term138.
Proof. exact (MK_COMB (@lem2606849) (@lem2606848)). Qed.
Lemma lem2606851 : term172 = term173.
Proof. exact (MK_COMB (@lem2606850) (@lem2606845)). Qed.
Lemma lem2606852 : term173 = term174.
Proof. exact (@lem1981613 term127 term63 term63 term63). Qed.
Lemma lem2606854 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2606855 : term144 = term145.
Proof. exact (@lem2606854 term64 term64). Qed.
Lemma lem2606856 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2606857 : term147 = term64.
Proof. exact (EQ_MP (@lem2606856) (@lem940073)). Qed.
Lemma lem2606858 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2606859 : term145 = term63.
Proof. exact (MK_COMB (@lem2606858) (@lem2606857)). Qed.
Lemma lem2606860 : term144 = term63.
Proof. exact (TRANS (@lem2606855) (@lem2606859)). Qed.
Lemma lem2606862 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2606863 : term172 = term177.
Proof. exact (@lem2606862 term64 term64). Qed.
Lemma lem2606864 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2606865 : term147 = term64.
Proof. exact (EQ_MP (@lem2606864) (@lem940073)). Qed.
Lemma lem2606866 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2606867 : term145 = term63.
Proof. exact (MK_COMB (@lem2606866) (@lem2606865)). Qed.
Lemma lem2606868 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2606869 : term177 = term127.
Proof. exact (MK_COMB (@lem2606868) (@lem2606867)). Qed.
Lemma lem2606870 : term172 = term127.
Proof. exact (TRANS (@lem2606863) (@lem2606869)). Qed.
Lemma lem2606871 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2606872 : term178 = term179.
Proof. exact (MK_COMB (@lem2606871) (@lem2606870)). Qed.
Lemma lem2606873 : term174 = term137.
Proof. exact (MK_COMB (@lem2606872) (@lem2606860)). Qed.
Lemma lem2606874 : term173 = term137.
Proof. exact (TRANS (@lem2606852) (@lem2606873)). Qed.
Lemma lem2606875 : term172 = term137.
Proof. exact (TRANS (@lem2606851) (@lem2606874)). Qed.
Lemma lem2606877 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2606878 : term137 = term127.
Proof. exact (@lem2606877 term127). Qed.
Lemma lem2606879 : term172 = term127.
Proof. exact (TRANS (@lem2606875) (@lem2606878)). Qed.
Lemma lem2606882 (m : nat) : (term641 m) = (term641 m).
Proof. exact (eq_refl (term641 m)). Qed.
Lemma lem2606883 (m : nat) : (term640 m) = (term642 m).
Proof. exact (MK_COMB (@lem2606882 m) (@lem2606879)). Qed.
Lemma lem2606884 (m : nat) : (term639 m) = (term642 m).
Proof. exact (TRANS (@lem2606842 m) (@lem2606883 m)). Qed.
Lemma lem2606885 (n : nat) : (term641 n) = (term641 n).
Proof. exact (eq_refl (term641 n)). Qed.
Lemma lem2606886 (n : nat) (m : nat) : (term638 n m) = (term643 n m).
Proof. exact (MK_COMB (@lem2606885 n) (@lem2606884 m)). Qed.
Lemma lem2606891 (m : nat) (n : nat) : (term643 n m) = (term643 m n).
Proof. exact (@lem1982757 (term633 m) (term633 n) term127). Qed.
Lemma lem2606892 (m : nat) (n : nat) : (term638 n m) = (term643 m n).
Proof. exact (TRANS (@lem2606886 n m) (@lem2606891 m n)). Qed.
Lemma lem2606893 (m : nat) (n : nat) : (term637 n m) = (term643 m n).
Proof. exact (TRANS (@lem2606841 n m) (@lem2606892 m n)). Qed.
Lemma lem2606894 (m : nat) (n : nat) : (term636 n m) = (term643 m n).
Proof. exact (TRANS (@lem2606840 n m) (@lem2606893 m n)). Qed.
Lemma lem2606895 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2606896 (m : nat) (n : nat) : (term644 n m) = (term645 m n).
Proof. exact (MK_COMB (@lem2606895) (@lem2606894 m n)). Qed.
Lemma lem2606897 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2606898 (m : nat) (n : nat) : (term632 n m) = (term646 m n).
Proof. exact (MK_COMB (@lem2606896 m n) (@lem2606897)). Qed.
Lemma lem2606899 (m : nat) (n : nat) : (term630 m n) = (term646 m n).
Proof. exact (TRANS (@lem2606823 n m) (@lem2606898 m n)). Qed.
Lemma lem2606908 (m : nat) (n : nat) : (term631 m n) = (term646 m n).
Proof. exact (TRANS (@lem2606822 m n) (@lem2606899 m n)). Qed.
Lemma lem2606912 (m : nat) (n : nat) (h1 : term646 m n) : term646 m n.
Proof. exact (h1). Qed.
Lemma lem2606913 (m : nat) : term647 m.
Proof. exact (@lem1396812 m). Qed.
Lemma lem2606914 (n : nat) : term647 n.
Proof. exact (@lem1396812 n). Qed.
Lemma lem2606916 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2606917 : term257 = term258.
Proof. exact (@lem2606916 term160 term63). Qed.
Lemma lem2606919 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2606920 : term63 = term151.
Proof. exact (@lem2606919 term64). Qed.
Lemma lem2606922 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2606923 : term160 = term259.
Proof. exact (@lem2606922 (NUMERAL 0)). Qed.
Lemma lem2606924 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2606925 : term260 = term261.
Proof. exact (MK_COMB (@lem2606924) (@lem2606923)). Qed.
Lemma lem2606926 : term258 = term262.
Proof. exact (MK_COMB (@lem2606925) (@lem2606920)). Qed.
Lemma lem2606927 : term263.
Proof. exact (@lem1980255 term160 term63 term63 term63). Qed.
Lemma lem2606929 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2606930 : term258 = term265.
Proof. exact (@lem2606929 (NUMERAL 0) term64). Qed.
Lemma lem2606931 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2606932 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2606933 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2606932 h1) (fun h1 : term265 = True => @lem2606931)). Qed.
Lemma lem2606934 : term265 = True.
Proof. exact (EQ_MP (@lem2606933) (@lem2606931)). Qed.
Lemma lem2606935 : term258 = True.
Proof. exact (TRANS (@lem2606930) (@lem2606934)). Qed.
Lemma lem2606936 : True = term258.
Proof. exact (SYM (@lem2606935)). Qed.
Lemma lem2606937 : term258.
Proof. exact (EQ_MP (@lem2606936) (@lem0)). Qed.
Lemma lem2606938 : term267.
Proof. exact (@lem2606927 (@lem2606937)). Qed.
Lemma lem2606940 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2606941 : term258 = term265.
Proof. exact (@lem2606940 (NUMERAL 0) term64). Qed.
Lemma lem2606942 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2606943 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2606944 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2606943 h1) (fun h1 : term265 = True => @lem2606942)). Qed.
Lemma lem2606945 : term265 = True.
Proof. exact (EQ_MP (@lem2606944) (@lem2606942)). Qed.
Lemma lem2606946 : term258 = True.
Proof. exact (TRANS (@lem2606941) (@lem2606945)). Qed.
Lemma lem2606947 : True = term258.
Proof. exact (SYM (@lem2606946)). Qed.
Lemma lem2606948 : term258.
Proof. exact (EQ_MP (@lem2606947) (@lem0)). Qed.
Lemma lem2606949 : term262 = term268.
Proof. exact (@lem2606938 (@lem2606948)). Qed.
Lemma lem2606951 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2606952 : term144 = term145.
Proof. exact (@lem2606951 term64 term64). Qed.
Lemma lem2606953 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2606954 : term147 = term64.
Proof. exact (EQ_MP (@lem2606953) (@lem940073)). Qed.
Lemma lem2606955 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2606956 : term145 = term63.
Proof. exact (MK_COMB (@lem2606955) (@lem2606954)). Qed.
Lemma lem2606957 : term144 = term63.
Proof. exact (TRANS (@lem2606952) (@lem2606956)). Qed.
Lemma lem2606959 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2606960 : term270 = term160.
Proof. exact (@lem2606959 term64). Qed.
Lemma lem2606961 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2606962 : term271 = term260.
Proof. exact (MK_COMB (@lem2606961) (@lem2606960)). Qed.
Lemma lem2606963 : term268 = term258.
Proof. exact (MK_COMB (@lem2606962) (@lem2606957)). Qed.
Lemma lem2606965 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2606966 : term258 = term265.
Proof. exact (@lem2606965 (NUMERAL 0) term64). Qed.
Lemma lem2606967 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2606968 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2606969 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2606968 h1) (fun h1 : term265 = True => @lem2606967)). Qed.
Lemma lem2606970 : term265 = True.
Proof. exact (EQ_MP (@lem2606969) (@lem2606967)). Qed.
Lemma lem2606971 : term258 = True.
Proof. exact (TRANS (@lem2606966) (@lem2606970)). Qed.
Lemma lem2606972 : term268 = True.
Proof. exact (TRANS (@lem2606963) (@lem2606971)). Qed.
Lemma lem2606973 : term262 = True.
Proof. exact (TRANS (@lem2606949) (@lem2606972)). Qed.
Lemma lem2606974 : term258 = True.
Proof. exact (TRANS (@lem2606926) (@lem2606973)). Qed.
Lemma lem2606975 : term257 = True.
Proof. exact (TRANS (@lem2606917) (@lem2606974)). Qed.
Lemma lem2606976 : True = term257.
Proof. exact (SYM (@lem2606975)). Qed.
Lemma lem2606977 : term257.
Proof. exact (EQ_MP (@lem2606976) (@lem0)). Qed.
Lemma lem2606978 (m : nat) : term648 m.
Proof. exact (conj (@lem2606977) (@lem2606913 m)). Qed.
Lemma lem2606980 (x : real) (y : real) : term273 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2606981 (m : nat) : term649 m.
Proof. exact (@lem2606980 term63 (real_of_num m)). Qed.
Lemma lem2606982 (m : nat) : term650 m.
Proof. exact (@lem2606981 m (@lem2606978 m)). Qed.
Lemma lem2606983 (m : nat) : (term651 m) = (real_of_num m).
Proof. exact (@lem1982733 (real_of_num m)). Qed.
Lemma lem2606984 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2606985 (m : nat) : (term652 m) = (term653 m).
Proof. exact (MK_COMB (@lem2606984) (@lem2606983 m)). Qed.
Lemma lem2606986 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2606987 (m : nat) : (term650 m) = (term647 m).
Proof. exact (MK_COMB (@lem2606985 m) (@lem2606986)). Qed.
Lemma lem2606988 (m : nat) : term647 m.
Proof. exact (EQ_MP (@lem2606987 m) (@lem2606982 m)). Qed.
Lemma lem2606990 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2606991 : term257 = term258.
Proof. exact (@lem2606990 term160 term63). Qed.
Lemma lem2606993 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2606994 : term63 = term151.
Proof. exact (@lem2606993 term64). Qed.
Lemma lem2606996 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2606997 : term160 = term259.
Proof. exact (@lem2606996 (NUMERAL 0)). Qed.
Lemma lem2606998 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2606999 : term260 = term261.
Proof. exact (MK_COMB (@lem2606998) (@lem2606997)). Qed.
Lemma lem2607000 : term258 = term262.
Proof. exact (MK_COMB (@lem2606999) (@lem2606994)). Qed.
Lemma lem2607001 : term263.
Proof. exact (@lem1980255 term160 term63 term63 term63). Qed.
Lemma lem2607003 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2607004 : term258 = term265.
Proof. exact (@lem2607003 (NUMERAL 0) term64). Qed.
Lemma lem2607005 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2607006 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2607007 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2607006 h1) (fun h1 : term265 = True => @lem2607005)). Qed.
Lemma lem2607008 : term265 = True.
Proof. exact (EQ_MP (@lem2607007) (@lem2607005)). Qed.
Lemma lem2607009 : term258 = True.
Proof. exact (TRANS (@lem2607004) (@lem2607008)). Qed.
Lemma lem2607010 : True = term258.
Proof. exact (SYM (@lem2607009)). Qed.
Lemma lem2607011 : term258.
Proof. exact (EQ_MP (@lem2607010) (@lem0)). Qed.
Lemma lem2607012 : term267.
Proof. exact (@lem2607001 (@lem2607011)). Qed.
Lemma lem2607014 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2607015 : term258 = term265.
Proof. exact (@lem2607014 (NUMERAL 0) term64). Qed.
Lemma lem2607016 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2607017 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2607018 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2607017 h1) (fun h1 : term265 = True => @lem2607016)). Qed.
Lemma lem2607019 : term265 = True.
Proof. exact (EQ_MP (@lem2607018) (@lem2607016)). Qed.
Lemma lem2607020 : term258 = True.
Proof. exact (TRANS (@lem2607015) (@lem2607019)). Qed.
Lemma lem2607021 : True = term258.
Proof. exact (SYM (@lem2607020)). Qed.
Lemma lem2607022 : term258.
Proof. exact (EQ_MP (@lem2607021) (@lem0)). Qed.
Lemma lem2607023 : term262 = term268.
Proof. exact (@lem2607012 (@lem2607022)). Qed.
Lemma lem2607025 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2607026 : term144 = term145.
Proof. exact (@lem2607025 term64 term64). Qed.
Lemma lem2607027 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2607028 : term147 = term64.
Proof. exact (EQ_MP (@lem2607027) (@lem940073)). Qed.
Lemma lem2607029 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2607030 : term145 = term63.
Proof. exact (MK_COMB (@lem2607029) (@lem2607028)). Qed.
Lemma lem2607031 : term144 = term63.
Proof. exact (TRANS (@lem2607026) (@lem2607030)). Qed.
Lemma lem2607033 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2607034 : term270 = term160.
Proof. exact (@lem2607033 term64). Qed.
Lemma lem2607035 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2607036 : term271 = term260.
Proof. exact (MK_COMB (@lem2607035) (@lem2607034)). Qed.
Lemma lem2607037 : term268 = term258.
Proof. exact (MK_COMB (@lem2607036) (@lem2607031)). Qed.
Lemma lem2607039 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2607040 : term258 = term265.
Proof. exact (@lem2607039 (NUMERAL 0) term64). Qed.
Lemma lem2607041 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2607042 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2607043 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2607042 h1) (fun h1 : term265 = True => @lem2607041)). Qed.
Lemma lem2607044 : term265 = True.
Proof. exact (EQ_MP (@lem2607043) (@lem2607041)). Qed.
Lemma lem2607045 : term258 = True.
Proof. exact (TRANS (@lem2607040) (@lem2607044)). Qed.
Lemma lem2607046 : term268 = True.
Proof. exact (TRANS (@lem2607037) (@lem2607045)). Qed.
Lemma lem2607047 : term262 = True.
Proof. exact (TRANS (@lem2607023) (@lem2607046)). Qed.
Lemma lem2607048 : term258 = True.
Proof. exact (TRANS (@lem2607000) (@lem2607047)). Qed.
Lemma lem2607049 : term257 = True.
Proof. exact (TRANS (@lem2606991) (@lem2607048)). Qed.
Lemma lem2607050 : True = term257.
Proof. exact (SYM (@lem2607049)). Qed.
Lemma lem2607051 : term257.
Proof. exact (EQ_MP (@lem2607050) (@lem0)). Qed.
Lemma lem2607052 (n : nat) : term648 n.
Proof. exact (conj (@lem2607051) (@lem2606914 n)). Qed.
Lemma lem2607054 (x : real) (y : real) : term273 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2607055 (n : nat) : term649 n.
Proof. exact (@lem2607054 term63 (real_of_num n)). Qed.
Lemma lem2607056 (n : nat) : term650 n.
Proof. exact (@lem2607055 n (@lem2607052 n)). Qed.
Lemma lem2607057 (n : nat) : (term651 n) = (real_of_num n).
Proof. exact (@lem1982733 (real_of_num n)). Qed.
Lemma lem2607058 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2607059 (n : nat) : (term652 n) = (term653 n).
Proof. exact (MK_COMB (@lem2607058) (@lem2607057 n)). Qed.
Lemma lem2607060 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2607061 (n : nat) : (term650 n) = (term647 n).
Proof. exact (MK_COMB (@lem2607059 n) (@lem2607060)). Qed.
Lemma lem2607062 (n : nat) : term647 n.
Proof. exact (EQ_MP (@lem2607061 n) (@lem2607056 n)). Qed.
Lemma lem2607064 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2607065 : term257 = term258.
Proof. exact (@lem2607064 term160 term63). Qed.
Lemma lem2607067 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2607068 : term63 = term151.
Proof. exact (@lem2607067 term64). Qed.
Lemma lem2607070 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2607071 : term160 = term259.
Proof. exact (@lem2607070 (NUMERAL 0)). Qed.
Lemma lem2607072 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2607073 : term260 = term261.
Proof. exact (MK_COMB (@lem2607072) (@lem2607071)). Qed.
Lemma lem2607074 : term258 = term262.
Proof. exact (MK_COMB (@lem2607073) (@lem2607068)). Qed.
Lemma lem2607075 : term263.
Proof. exact (@lem1980255 term160 term63 term63 term63). Qed.
Lemma lem2607077 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2607078 : term258 = term265.
Proof. exact (@lem2607077 (NUMERAL 0) term64). Qed.
Lemma lem2607079 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2607080 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2607081 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2607080 h1) (fun h1 : term265 = True => @lem2607079)). Qed.
Lemma lem2607082 : term265 = True.
Proof. exact (EQ_MP (@lem2607081) (@lem2607079)). Qed.
Lemma lem2607083 : term258 = True.
Proof. exact (TRANS (@lem2607078) (@lem2607082)). Qed.
Lemma lem2607084 : True = term258.
Proof. exact (SYM (@lem2607083)). Qed.
Lemma lem2607085 : term258.
Proof. exact (EQ_MP (@lem2607084) (@lem0)). Qed.
Lemma lem2607086 : term267.
Proof. exact (@lem2607075 (@lem2607085)). Qed.
Lemma lem2607088 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2607089 : term258 = term265.
Proof. exact (@lem2607088 (NUMERAL 0) term64). Qed.
Lemma lem2607090 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2607091 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2607092 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2607091 h1) (fun h1 : term265 = True => @lem2607090)). Qed.
Lemma lem2607093 : term265 = True.
Proof. exact (EQ_MP (@lem2607092) (@lem2607090)). Qed.
Lemma lem2607094 : term258 = True.
Proof. exact (TRANS (@lem2607089) (@lem2607093)). Qed.
Lemma lem2607095 : True = term258.
Proof. exact (SYM (@lem2607094)). Qed.
Lemma lem2607096 : term258.
Proof. exact (EQ_MP (@lem2607095) (@lem0)). Qed.
Lemma lem2607097 : term262 = term268.
Proof. exact (@lem2607086 (@lem2607096)). Qed.
Lemma lem2607099 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2607100 : term144 = term145.
Proof. exact (@lem2607099 term64 term64). Qed.
Lemma lem2607101 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2607102 : term147 = term64.
Proof. exact (EQ_MP (@lem2607101) (@lem940073)). Qed.
Lemma lem2607103 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2607104 : term145 = term63.
Proof. exact (MK_COMB (@lem2607103) (@lem2607102)). Qed.
Lemma lem2607105 : term144 = term63.
Proof. exact (TRANS (@lem2607100) (@lem2607104)). Qed.
Lemma lem2607107 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2607108 : term270 = term160.
Proof. exact (@lem2607107 term64). Qed.
Lemma lem2607109 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2607110 : term271 = term260.
Proof. exact (MK_COMB (@lem2607109) (@lem2607108)). Qed.
Lemma lem2607111 : term268 = term258.
Proof. exact (MK_COMB (@lem2607110) (@lem2607105)). Qed.
Lemma lem2607113 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2607114 : term258 = term265.
Proof. exact (@lem2607113 (NUMERAL 0) term64). Qed.
Lemma lem2607115 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2607116 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2607117 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2607116 h1) (fun h1 : term265 = True => @lem2607115)). Qed.
Lemma lem2607118 : term265 = True.
Proof. exact (EQ_MP (@lem2607117) (@lem2607115)). Qed.
Lemma lem2607119 : term258 = True.
Proof. exact (TRANS (@lem2607114) (@lem2607118)). Qed.
Lemma lem2607120 : term268 = True.
Proof. exact (TRANS (@lem2607111) (@lem2607119)). Qed.
Lemma lem2607121 : term262 = True.
Proof. exact (TRANS (@lem2607097) (@lem2607120)). Qed.
Lemma lem2607122 : term258 = True.
Proof. exact (TRANS (@lem2607074) (@lem2607121)). Qed.
Lemma lem2607123 : term257 = True.
Proof. exact (TRANS (@lem2607065) (@lem2607122)). Qed.
Lemma lem2607124 : True = term257.
Proof. exact (SYM (@lem2607123)). Qed.
Lemma lem2607125 : term257.
Proof. exact (EQ_MP (@lem2607124) (@lem0)). Qed.
Lemma lem2607126 (m : nat) (n : nat) (h1 : term646 m n) : term654 m n.
Proof. exact (conj (@lem2607125) (@lem2606912 m n h1)). Qed.
Lemma lem2607128 (x : real) (y : real) : term273 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2607129 (m : nat) (n : nat) : term655 m n.
Proof. exact (@lem2607128 term63 (term643 m n)). Qed.
Lemma lem2607130 (m : nat) (n : nat) (h1 : term646 m n) : term656 m n.
Proof. exact (@lem2607129 m n (@lem2607126 m n h1)). Qed.
Lemma lem2607131 (m : nat) (n : nat) : (term657 m n) = (term643 m n).
Proof. exact (@lem1982733 (term643 m n)). Qed.
Lemma lem2607132 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2607133 (m : nat) (n : nat) : (term658 m n) = (term645 m n).
Proof. exact (MK_COMB (@lem2607132) (@lem2607131 m n)). Qed.
Lemma lem2607134 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2607135 (m : nat) (n : nat) : (term656 m n) = (term646 m n).
Proof. exact (MK_COMB (@lem2607133 m n) (@lem2607134)). Qed.
Lemma lem2607136 (m : nat) (n : nat) (h1 : term646 m n) : term646 m n.
Proof. exact (EQ_MP (@lem2607135 m n) (@lem2607130 m n h1)). Qed.
Lemma lem2607137 (m : nat) (n : nat) (h1 : term646 m n) : term659 m n.
Proof. exact (conj (@lem2607136 m n h1) (@lem2607062 n)). Qed.
Lemma lem2607139 (x : real) (y : real) : term361 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2607140 (m : nat) (n : nat) : term660 m n.
Proof. exact (@lem2607139 (term643 m n) (real_of_num n)). Qed.
Lemma lem2607141 (m : nat) (n : nat) (h1 : term646 m n) : term661 m n.
Proof. exact (@lem2607140 m n (@lem2607137 m n h1)). Qed.
Lemma lem2607142 (m : nat) (n : nat) : (term662 m n) = (term663 m n).
Proof. exact (@lem1982755 (term633 m) (term642 n) (real_of_num n)). Qed.
Lemma lem2607143 (n : nat) : (term664 n) = (term665 n).
Proof. exact (@lem1982759 (term633 n) (real_of_num n) term127). Qed.
Lemma lem2607144 (n : nat) : (term666 n) = (term667 n).
Proof. exact (@lem1982713 term127 (real_of_num n)). Qed.
Lemma lem2607146 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2607147 : term63 = term151.
Proof. exact (@lem2607146 term64). Qed.
Lemma lem2607149 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2607150 : term127 = term137.
Proof. exact (@lem2607149 term64). Qed.
Lemma lem2607151 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2607152 : term293 = term294.
Proof. exact (MK_COMB (@lem2607151) (@lem2607150)). Qed.
Lemma lem2607153 : term295 = term296.
Proof. exact (MK_COMB (@lem2607152) (@lem2607147)). Qed.
Lemma lem2607154 : term297.
Proof. exact (@lem1981473 term127 term63 term63 term63 term160 term63). Qed.
Lemma lem2607156 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2607157 : term258 = term265.
Proof. exact (@lem2607156 (NUMERAL 0) term64). Qed.
Lemma lem2607158 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2607159 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2607160 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2607159 h1) (fun h1 : term265 = True => @lem2607158)). Qed.
Lemma lem2607161 : term265 = True.
Proof. exact (EQ_MP (@lem2607160) (@lem2607158)). Qed.
Lemma lem2607162 : term258 = True.
Proof. exact (TRANS (@lem2607157) (@lem2607161)). Qed.
Lemma lem2607163 : True = term258.
Proof. exact (SYM (@lem2607162)). Qed.
Lemma lem2607164 : term258.
Proof. exact (EQ_MP (@lem2607163) (@lem0)). Qed.
Lemma lem2607165 : term298.
Proof. exact (@lem2607154 (@lem2607164)). Qed.
Lemma lem2607167 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2607168 : term258 = term265.
Proof. exact (@lem2607167 (NUMERAL 0) term64). Qed.
Lemma lem2607169 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2607170 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2607171 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2607170 h1) (fun h1 : term265 = True => @lem2607169)). Qed.
Lemma lem2607172 : term265 = True.
Proof. exact (EQ_MP (@lem2607171) (@lem2607169)). Qed.
Lemma lem2607173 : term258 = True.
Proof. exact (TRANS (@lem2607168) (@lem2607172)). Qed.
Lemma lem2607174 : True = term258.
Proof. exact (SYM (@lem2607173)). Qed.
Lemma lem2607175 : term258.
Proof. exact (EQ_MP (@lem2607174) (@lem0)). Qed.
Lemma lem2607176 : term299.
Proof. exact (@lem2607165 (@lem2607175)). Qed.
Lemma lem2607178 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2607179 : term258 = term265.
Proof. exact (@lem2607178 (NUMERAL 0) term64). Qed.
Lemma lem2607180 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2607181 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2607182 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2607181 h1) (fun h1 : term265 = True => @lem2607180)). Qed.
Lemma lem2607183 : term265 = True.
Proof. exact (EQ_MP (@lem2607182) (@lem2607180)). Qed.
Lemma lem2607184 : term258 = True.
Proof. exact (TRANS (@lem2607179) (@lem2607183)). Qed.
Lemma lem2607185 : True = term258.
Proof. exact (SYM (@lem2607184)). Qed.
Lemma lem2607186 : term258.
Proof. exact (EQ_MP (@lem2607185) (@lem0)). Qed.
Lemma lem2607187 : term300.
Proof. exact (@lem2607176 (@lem2607186)). Qed.
Lemma lem2607189 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2607190 : term144 = term145.
Proof. exact (@lem2607189 term64 term64). Qed.
Lemma lem2607191 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2607192 : term147 = term64.
Proof. exact (EQ_MP (@lem2607191) (@lem940073)). Qed.
Lemma lem2607193 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2607194 : term145 = term63.
Proof. exact (MK_COMB (@lem2607193) (@lem2607192)). Qed.
Lemma lem2607195 : term144 = term63.
Proof. exact (TRANS (@lem2607190) (@lem2607194)). Qed.
Lemma lem2607197 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2607198 : term172 = term177.
Proof. exact (@lem2607197 term64 term64). Qed.
Lemma lem2607199 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2607200 : term147 = term64.
Proof. exact (EQ_MP (@lem2607199) (@lem940073)). Qed.
Lemma lem2607201 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2607202 : term145 = term63.
Proof. exact (MK_COMB (@lem2607201) (@lem2607200)). Qed.
Lemma lem2607203 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2607204 : term177 = term127.
Proof. exact (MK_COMB (@lem2607203) (@lem2607202)). Qed.
Lemma lem2607205 : term172 = term127.
Proof. exact (TRANS (@lem2607198) (@lem2607204)). Qed.
Lemma lem2607206 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2607207 : term301 = term293.
Proof. exact (MK_COMB (@lem2607206) (@lem2607205)). Qed.
Lemma lem2607208 : term302 = term295.
Proof. exact (MK_COMB (@lem2607207) (@lem2607195)). Qed.
Lemma lem2607210 (m : nat) : (term303 m) = term160.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2607211 : term295 = term160.
Proof. exact (@lem2607210 term64). Qed.
Lemma lem2607212 : term302 = term160.
Proof. exact (TRANS (@lem2607208) (@lem2607211)). Qed.
Lemma lem2607213 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2607214 : term304 = term305.
Proof. exact (MK_COMB (@lem2607213) (@lem2607212)). Qed.
Lemma lem2607215 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2607216 : term306 = term270.
Proof. exact (MK_COMB (@lem2607214) (@lem2607215)). Qed.
Lemma lem2607218 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2607219 : term270 = term160.
Proof. exact (@lem2607218 term64). Qed.
Lemma lem2607220 : term306 = term160.
Proof. exact (TRANS (@lem2607216) (@lem2607219)). Qed.
Lemma lem2607222 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2607223 : term144 = term145.
Proof. exact (@lem2607222 term64 term64). Qed.
Lemma lem2607224 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2607225 : term147 = term64.
Proof. exact (EQ_MP (@lem2607224) (@lem940073)). Qed.
Lemma lem2607226 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2607227 : term145 = term63.
Proof. exact (MK_COMB (@lem2607226) (@lem2607225)). Qed.
Lemma lem2607228 : term144 = term63.
Proof. exact (TRANS (@lem2607223) (@lem2607227)). Qed.
Lemma lem2607229 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem2607230 : term307 = term270.
Proof. exact (MK_COMB (@lem2607229) (@lem2607228)). Qed.
Lemma lem2607232 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2607233 : term270 = term160.
Proof. exact (@lem2607232 term64). Qed.
Lemma lem2607234 : term307 = term160.
Proof. exact (TRANS (@lem2607230) (@lem2607233)). Qed.
Lemma lem2607235 : term160 = term307.
Proof. exact (SYM (@lem2607234)). Qed.
Lemma lem2607236 : term306 = term307.
Proof. exact (TRANS (@lem2607220) (@lem2607235)). Qed.
Lemma lem2607237 : term296 = term259.
Proof. exact (@lem2607187 (@lem2607236)). Qed.
Lemma lem2607238 : term295 = term259.
Proof. exact (TRANS (@lem2607153) (@lem2607237)). Qed.
Lemma lem2607240 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2607241 : term259 = term160.
Proof. exact (@lem2607240 term160). Qed.
Lemma lem2607242 : term295 = term160.
Proof. exact (TRANS (@lem2607238) (@lem2607241)). Qed.
Lemma lem2607243 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2607244 : term308 = term305.
Proof. exact (MK_COMB (@lem2607243) (@lem2607242)). Qed.
Lemma lem2607245 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2607246 (n : nat) : (term667 n) = (term269 n).
Proof. exact (MK_COMB (@lem2607244) (@lem2607245 n)). Qed.
Lemma lem2607247 (n : nat) : (term666 n) = (term269 n).
Proof. exact (TRANS (@lem2607144 n) (@lem2607246 n)). Qed.
Lemma lem2607248 (n : nat) : (term269 n) = term160.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem2607249 (n : nat) : (term666 n) = term160.
Proof. exact (TRANS (@lem2607247 n) (@lem2607248 n)). Qed.
Lemma lem2607250 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2607251 (n : nat) : (term668 n) = term311.
Proof. exact (MK_COMB (@lem2607250) (@lem2607249 n)). Qed.
Lemma lem2607252 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem2607253 (n : nat) : (term665 n) = term318.
Proof. exact (MK_COMB (@lem2607251 n) (@lem2607252)). Qed.
Lemma lem2607254 (n : nat) : (term664 n) = term318.
Proof. exact (TRANS (@lem2607143 n) (@lem2607253 n)). Qed.
Lemma lem2607255 : term318 = term127.
Proof. exact (@lem1982721 term127). Qed.
Lemma lem2607256 (n : nat) : (term664 n) = term127.
Proof. exact (TRANS (@lem2607254 n) (@lem2607255)). Qed.
Lemma lem2607257 (m : nat) : (term641 m) = (term641 m).
Proof. exact (eq_refl (term641 m)). Qed.
Lemma lem2607258 (n : nat) (m : nat) : (term663 m n) = (term642 m).
Proof. exact (MK_COMB (@lem2607257 m) (@lem2607256 n)). Qed.
Lemma lem2607259 (n : nat) (m : nat) : (term662 m n) = (term642 m).
Proof. exact (TRANS (@lem2607142 m n) (@lem2607258 n m)). Qed.
Lemma lem2607260 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2607261 (n : nat) (m : nat) : (term669 m n) = (term670 m).
Proof. exact (MK_COMB (@lem2607260) (@lem2607259 n m)). Qed.
Lemma lem2607262 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2607263 (n : nat) (m : nat) : (term661 m n) = (term671 m).
Proof. exact (MK_COMB (@lem2607261 n m) (@lem2607262)). Qed.
Lemma lem2607264 (m : nat) (n : nat) (h1 : term646 m n) : term671 m.
Proof. exact (EQ_MP (@lem2607263 n m) (@lem2607141 m n h1)). Qed.
Lemma lem2607266 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2607267 : term257 = term258.
Proof. exact (@lem2607266 term160 term63). Qed.
Lemma lem2607269 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2607270 : term63 = term151.
Proof. exact (@lem2607269 term64). Qed.
Lemma lem2607272 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2607273 : term160 = term259.
Proof. exact (@lem2607272 (NUMERAL 0)). Qed.
Lemma lem2607274 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2607275 : term260 = term261.
Proof. exact (MK_COMB (@lem2607274) (@lem2607273)). Qed.
Lemma lem2607276 : term258 = term262.
Proof. exact (MK_COMB (@lem2607275) (@lem2607270)). Qed.
Lemma lem2607277 : term263.
Proof. exact (@lem1980255 term160 term63 term63 term63). Qed.
Lemma lem2607279 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2607280 : term258 = term265.
Proof. exact (@lem2607279 (NUMERAL 0) term64). Qed.
Lemma lem2607281 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2607282 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2607283 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2607282 h1) (fun h1 : term265 = True => @lem2607281)). Qed.
Lemma lem2607284 : term265 = True.
Proof. exact (EQ_MP (@lem2607283) (@lem2607281)). Qed.
Lemma lem2607285 : term258 = True.
Proof. exact (TRANS (@lem2607280) (@lem2607284)). Qed.
Lemma lem2607286 : True = term258.
Proof. exact (SYM (@lem2607285)). Qed.
Lemma lem2607287 : term258.
Proof. exact (EQ_MP (@lem2607286) (@lem0)). Qed.
Lemma lem2607288 : term267.
Proof. exact (@lem2607277 (@lem2607287)). Qed.
Lemma lem2607290 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2607291 : term258 = term265.
Proof. exact (@lem2607290 (NUMERAL 0) term64). Qed.
Lemma lem2607292 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2607293 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2607294 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2607293 h1) (fun h1 : term265 = True => @lem2607292)). Qed.
Lemma lem2607295 : term265 = True.
Proof. exact (EQ_MP (@lem2607294) (@lem2607292)). Qed.
Lemma lem2607296 : term258 = True.
Proof. exact (TRANS (@lem2607291) (@lem2607295)). Qed.
Lemma lem2607297 : True = term258.
Proof. exact (SYM (@lem2607296)). Qed.
Lemma lem2607298 : term258.
Proof. exact (EQ_MP (@lem2607297) (@lem0)). Qed.
Lemma lem2607299 : term262 = term268.
Proof. exact (@lem2607288 (@lem2607298)). Qed.
Lemma lem2607301 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2607302 : term144 = term145.
Proof. exact (@lem2607301 term64 term64). Qed.
Lemma lem2607303 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2607304 : term147 = term64.
Proof. exact (EQ_MP (@lem2607303) (@lem940073)). Qed.
Lemma lem2607305 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2607306 : term145 = term63.
Proof. exact (MK_COMB (@lem2607305) (@lem2607304)). Qed.
Lemma lem2607307 : term144 = term63.
Proof. exact (TRANS (@lem2607302) (@lem2607306)). Qed.
Lemma lem2607309 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2607310 : term270 = term160.
Proof. exact (@lem2607309 term64). Qed.
Lemma lem2607311 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2607312 : term271 = term260.
Proof. exact (MK_COMB (@lem2607311) (@lem2607310)). Qed.
Lemma lem2607313 : term268 = term258.
Proof. exact (MK_COMB (@lem2607312) (@lem2607307)). Qed.
Lemma lem2607315 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2607316 : term258 = term265.
Proof. exact (@lem2607315 (NUMERAL 0) term64). Qed.
Lemma lem2607317 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2607318 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2607319 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2607318 h1) (fun h1 : term265 = True => @lem2607317)). Qed.
Lemma lem2607320 : term265 = True.
Proof. exact (EQ_MP (@lem2607319) (@lem2607317)). Qed.
Lemma lem2607321 : term258 = True.
Proof. exact (TRANS (@lem2607316) (@lem2607320)). Qed.
Lemma lem2607322 : term268 = True.
Proof. exact (TRANS (@lem2607313) (@lem2607321)). Qed.
Lemma lem2607323 : term262 = True.
Proof. exact (TRANS (@lem2607299) (@lem2607322)). Qed.
Lemma lem2607324 : term258 = True.
Proof. exact (TRANS (@lem2607276) (@lem2607323)). Qed.
Lemma lem2607325 : term257 = True.
Proof. exact (TRANS (@lem2607267) (@lem2607324)). Qed.
Lemma lem2607326 : True = term257.
Proof. exact (SYM (@lem2607325)). Qed.
Lemma lem2607327 : term257.
Proof. exact (EQ_MP (@lem2607326) (@lem0)). Qed.
Lemma lem2607328 (m : nat) (n : nat) (h1 : term646 m n) : term672 m.
Proof. exact (conj (@lem2607327) (@lem2607264 m n h1)). Qed.
Lemma lem2607330 (x : real) (y : real) : term273 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2607331 (m : nat) : term673 m.
Proof. exact (@lem2607330 term63 (term642 m)). Qed.
Lemma lem2607332 (m : nat) (n : nat) (h1 : term646 m n) : term674 m.
Proof. exact (@lem2607331 m (@lem2607328 m n h1)). Qed.
Lemma lem2607333 (m : nat) : (term675 m) = (term642 m).
Proof. exact (@lem1982733 (term642 m)). Qed.
Lemma lem2607334 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2607335 (m : nat) : (term676 m) = (term670 m).
Proof. exact (MK_COMB (@lem2607334) (@lem2607333 m)). Qed.
Lemma lem2607336 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2607337 (m : nat) : (term674 m) = (term671 m).
Proof. exact (MK_COMB (@lem2607335 m) (@lem2607336)). Qed.
Lemma lem2607338 (m : nat) (n : nat) (h1 : term646 m n) : term671 m.
Proof. exact (EQ_MP (@lem2607337 m) (@lem2607332 m n h1)). Qed.
Lemma lem2607339 (m : nat) (n : nat) (h1 : term646 m n) : term677 m.
Proof. exact (conj (@lem2607338 m n h1) (@lem2606988 m)). Qed.
Lemma lem2607341 (x : real) (y : real) : term361 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2607342 (m : nat) : term678 m.
Proof. exact (@lem2607341 (term642 m) (real_of_num m)). Qed.
Lemma lem2607343 (m : nat) (n : nat) (h1 : term646 m n) : term679 m.
Proof. exact (@lem2607342 m (@lem2607339 m n h1)). Qed.
Lemma lem2607344 (m : nat) : (term664 m) = (term665 m).
Proof. exact (@lem1982759 (term633 m) (real_of_num m) term127). Qed.
Lemma lem2607345 (m : nat) : (term666 m) = (term667 m).
Proof. exact (@lem1982713 term127 (real_of_num m)). Qed.
Lemma lem2607347 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2607348 : term63 = term151.
Proof. exact (@lem2607347 term64). Qed.
Lemma lem2607350 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2607351 : term127 = term137.
Proof. exact (@lem2607350 term64). Qed.
Lemma lem2607352 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2607353 : term293 = term294.
Proof. exact (MK_COMB (@lem2607352) (@lem2607351)). Qed.
Lemma lem2607354 : term295 = term296.
Proof. exact (MK_COMB (@lem2607353) (@lem2607348)). Qed.
Lemma lem2607355 : term297.
Proof. exact (@lem1981473 term127 term63 term63 term63 term160 term63). Qed.
Lemma lem2607357 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2607358 : term258 = term265.
Proof. exact (@lem2607357 (NUMERAL 0) term64). Qed.
Lemma lem2607359 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2607360 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2607361 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2607360 h1) (fun h1 : term265 = True => @lem2607359)). Qed.
Lemma lem2607362 : term265 = True.
Proof. exact (EQ_MP (@lem2607361) (@lem2607359)). Qed.
Lemma lem2607363 : term258 = True.
Proof. exact (TRANS (@lem2607358) (@lem2607362)). Qed.
Lemma lem2607364 : True = term258.
Proof. exact (SYM (@lem2607363)). Qed.
Lemma lem2607365 : term258.
Proof. exact (EQ_MP (@lem2607364) (@lem0)). Qed.
Lemma lem2607366 : term298.
Proof. exact (@lem2607355 (@lem2607365)). Qed.
Lemma lem2607368 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2607369 : term258 = term265.
Proof. exact (@lem2607368 (NUMERAL 0) term64). Qed.
Lemma lem2607370 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2607371 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2607372 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2607371 h1) (fun h1 : term265 = True => @lem2607370)). Qed.
Lemma lem2607373 : term265 = True.
Proof. exact (EQ_MP (@lem2607372) (@lem2607370)). Qed.
Lemma lem2607374 : term258 = True.
Proof. exact (TRANS (@lem2607369) (@lem2607373)). Qed.
Lemma lem2607375 : True = term258.
Proof. exact (SYM (@lem2607374)). Qed.
Lemma lem2607376 : term258.
Proof. exact (EQ_MP (@lem2607375) (@lem0)). Qed.
Lemma lem2607377 : term299.
Proof. exact (@lem2607366 (@lem2607376)). Qed.
Lemma lem2607379 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2607380 : term258 = term265.
Proof. exact (@lem2607379 (NUMERAL 0) term64). Qed.
Lemma lem2607381 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2607382 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2607383 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2607382 h1) (fun h1 : term265 = True => @lem2607381)). Qed.
Lemma lem2607384 : term265 = True.
Proof. exact (EQ_MP (@lem2607383) (@lem2607381)). Qed.
Lemma lem2607385 : term258 = True.
Proof. exact (TRANS (@lem2607380) (@lem2607384)). Qed.
Lemma lem2607386 : True = term258.
Proof. exact (SYM (@lem2607385)). Qed.
Lemma lem2607387 : term258.
Proof. exact (EQ_MP (@lem2607386) (@lem0)). Qed.
Lemma lem2607388 : term300.
Proof. exact (@lem2607377 (@lem2607387)). Qed.
Lemma lem2607390 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2607391 : term144 = term145.
Proof. exact (@lem2607390 term64 term64). Qed.
Lemma lem2607392 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2607393 : term147 = term64.
Proof. exact (EQ_MP (@lem2607392) (@lem940073)). Qed.
Lemma lem2607394 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2607395 : term145 = term63.
Proof. exact (MK_COMB (@lem2607394) (@lem2607393)). Qed.
Lemma lem2607396 : term144 = term63.
Proof. exact (TRANS (@lem2607391) (@lem2607395)). Qed.
Lemma lem2607398 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2607399 : term172 = term177.
Proof. exact (@lem2607398 term64 term64). Qed.
Lemma lem2607400 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2607401 : term147 = term64.
Proof. exact (EQ_MP (@lem2607400) (@lem940073)). Qed.
Lemma lem2607402 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2607403 : term145 = term63.
Proof. exact (MK_COMB (@lem2607402) (@lem2607401)). Qed.
Lemma lem2607404 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2607405 : term177 = term127.
Proof. exact (MK_COMB (@lem2607404) (@lem2607403)). Qed.
Lemma lem2607406 : term172 = term127.
Proof. exact (TRANS (@lem2607399) (@lem2607405)). Qed.
Lemma lem2607407 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2607408 : term301 = term293.
Proof. exact (MK_COMB (@lem2607407) (@lem2607406)). Qed.
Lemma lem2607409 : term302 = term295.
Proof. exact (MK_COMB (@lem2607408) (@lem2607396)). Qed.
Lemma lem2607411 (m : nat) : (term303 m) = term160.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2607412 : term295 = term160.
Proof. exact (@lem2607411 term64). Qed.
Lemma lem2607413 : term302 = term160.
Proof. exact (TRANS (@lem2607409) (@lem2607412)). Qed.
Lemma lem2607414 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2607415 : term304 = term305.
Proof. exact (MK_COMB (@lem2607414) (@lem2607413)). Qed.
Lemma lem2607416 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2607417 : term306 = term270.
Proof. exact (MK_COMB (@lem2607415) (@lem2607416)). Qed.
Lemma lem2607419 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2607420 : term270 = term160.
Proof. exact (@lem2607419 term64). Qed.
Lemma lem2607421 : term306 = term160.
Proof. exact (TRANS (@lem2607417) (@lem2607420)). Qed.
Lemma lem2607423 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2607424 : term144 = term145.
Proof. exact (@lem2607423 term64 term64). Qed.
Lemma lem2607425 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2607426 : term147 = term64.
Proof. exact (EQ_MP (@lem2607425) (@lem940073)). Qed.
Lemma lem2607427 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2607428 : term145 = term63.
Proof. exact (MK_COMB (@lem2607427) (@lem2607426)). Qed.
Lemma lem2607429 : term144 = term63.
Proof. exact (TRANS (@lem2607424) (@lem2607428)). Qed.
Lemma lem2607430 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem2607431 : term307 = term270.
Proof. exact (MK_COMB (@lem2607430) (@lem2607429)). Qed.
Lemma lem2607433 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2607434 : term270 = term160.
Proof. exact (@lem2607433 term64). Qed.
Lemma lem2607435 : term307 = term160.
Proof. exact (TRANS (@lem2607431) (@lem2607434)). Qed.
Lemma lem2607436 : term160 = term307.
Proof. exact (SYM (@lem2607435)). Qed.
Lemma lem2607437 : term306 = term307.
Proof. exact (TRANS (@lem2607421) (@lem2607436)). Qed.
Lemma lem2607438 : term296 = term259.
Proof. exact (@lem2607388 (@lem2607437)). Qed.
Lemma lem2607439 : term295 = term259.
Proof. exact (TRANS (@lem2607354) (@lem2607438)). Qed.
Lemma lem2607441 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2607442 : term259 = term160.
Proof. exact (@lem2607441 term160). Qed.
Lemma lem2607443 : term295 = term160.
Proof. exact (TRANS (@lem2607439) (@lem2607442)). Qed.
Lemma lem2607444 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2607445 : term308 = term305.
Proof. exact (MK_COMB (@lem2607444) (@lem2607443)). Qed.
Lemma lem2607446 (m : nat) : (real_of_num m) = (real_of_num m).
Proof. exact (eq_refl (real_of_num m)). Qed.
Lemma lem2607447 (m : nat) : (term667 m) = (term269 m).
Proof. exact (MK_COMB (@lem2607445) (@lem2607446 m)). Qed.
Lemma lem2607448 (m : nat) : (term666 m) = (term269 m).
Proof. exact (TRANS (@lem2607345 m) (@lem2607447 m)). Qed.
Lemma lem2607449 (m : nat) : (term269 m) = term160.
Proof. exact (@lem1982719 (real_of_num m)). Qed.
Lemma lem2607450 (m : nat) : (term666 m) = term160.
Proof. exact (TRANS (@lem2607448 m) (@lem2607449 m)). Qed.
Lemma lem2607451 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2607452 (m : nat) : (term668 m) = term311.
Proof. exact (MK_COMB (@lem2607451) (@lem2607450 m)). Qed.
Lemma lem2607453 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem2607454 (m : nat) : (term665 m) = term318.
Proof. exact (MK_COMB (@lem2607452 m) (@lem2607453)). Qed.
Lemma lem2607455 (m : nat) : (term664 m) = term318.
Proof. exact (TRANS (@lem2607344 m) (@lem2607454 m)). Qed.
Lemma lem2607456 : term318 = term127.
Proof. exact (@lem1982721 term127). Qed.
Lemma lem2607457 (m : nat) : (term664 m) = term127.
Proof. exact (TRANS (@lem2607455 m) (@lem2607456)). Qed.
Lemma lem2607458 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2607459 (m : nat) : (term680 m) = term320.
Proof. exact (MK_COMB (@lem2607458) (@lem2607457 m)). Qed.
Lemma lem2607460 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2607461 (m : nat) : (term679 m) = term321.
Proof. exact (MK_COMB (@lem2607459 m) (@lem2607460)). Qed.
Lemma lem2607462 (m : nat) (n : nat) (h1 : term646 m n) : term321.
Proof. exact (EQ_MP (@lem2607461 m) (@lem2607343 m n h1)). Qed.
Lemma lem2607464 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2607465 : term321 = term322.
Proof. exact (@lem2607464 term160 term127). Qed.
Lemma lem2607467 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2607468 : term127 = term137.
Proof. exact (@lem2607467 term64). Qed.
Lemma lem2607470 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2607471 : term160 = term259.
Proof. exact (@lem2607470 (NUMERAL 0)). Qed.
Lemma lem2607472 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2607473 : term323 = term324.
Proof. exact (MK_COMB (@lem2607472) (@lem2607471)). Qed.
Lemma lem2607474 : term322 = term325.
Proof. exact (MK_COMB (@lem2607473) (@lem2607468)). Qed.
Lemma lem2607475 : term326.
Proof. exact (@lem1980026 term160 term63 term127 term63). Qed.
Lemma lem2607477 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2607478 : term258 = term265.
Proof. exact (@lem2607477 (NUMERAL 0) term64). Qed.
Lemma lem2607479 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2607480 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2607481 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2607480 h1) (fun h1 : term265 = True => @lem2607479)). Qed.
Lemma lem2607482 : term265 = True.
Proof. exact (EQ_MP (@lem2607481) (@lem2607479)). Qed.
Lemma lem2607483 : term258 = True.
Proof. exact (TRANS (@lem2607478) (@lem2607482)). Qed.
Lemma lem2607484 : True = term258.
Proof. exact (SYM (@lem2607483)). Qed.
Lemma lem2607485 : term258.
Proof. exact (EQ_MP (@lem2607484) (@lem0)). Qed.
Lemma lem2607486 : term327.
Proof. exact (@lem2607475 (@lem2607485)). Qed.
Lemma lem2607488 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2607489 : term258 = term265.
Proof. exact (@lem2607488 (NUMERAL 0) term64). Qed.
Lemma lem2607490 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2607491 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2607492 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2607491 h1) (fun h1 : term265 = True => @lem2607490)). Qed.
Lemma lem2607493 : term265 = True.
Proof. exact (EQ_MP (@lem2607492) (@lem2607490)). Qed.
Lemma lem2607494 : term258 = True.
Proof. exact (TRANS (@lem2607489) (@lem2607493)). Qed.
Lemma lem2607495 : True = term258.
Proof. exact (SYM (@lem2607494)). Qed.
Lemma lem2607496 : term258.
Proof. exact (EQ_MP (@lem2607495) (@lem0)). Qed.
Lemma lem2607497 : term325 = term328.
Proof. exact (@lem2607486 (@lem2607496)). Qed.
Lemma lem2607499 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2607500 : term172 = term177.
Proof. exact (@lem2607499 term64 term64). Qed.
Lemma lem2607501 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2607502 : term147 = term64.
Proof. exact (EQ_MP (@lem2607501) (@lem940073)). Qed.
Lemma lem2607503 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2607504 : term145 = term63.
Proof. exact (MK_COMB (@lem2607503) (@lem2607502)). Qed.
Lemma lem2607505 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2607506 : term177 = term127.
Proof. exact (MK_COMB (@lem2607505) (@lem2607504)). Qed.
Lemma lem2607507 : term172 = term127.
Proof. exact (TRANS (@lem2607500) (@lem2607506)). Qed.
Lemma lem2607509 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2607510 : term270 = term160.
Proof. exact (@lem2607509 term64). Qed.
Lemma lem2607511 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2607512 : term329 = term323.
Proof. exact (MK_COMB (@lem2607511) (@lem2607510)). Qed.
Lemma lem2607513 : term328 = term322.
Proof. exact (MK_COMB (@lem2607512) (@lem2607507)). Qed.
Lemma lem2607515 (m : nat) (n : nat) : (term330 m n) = (term331 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2607516 : term322 = term332.
Proof. exact (@lem2607515 (NUMERAL 0) term64). Qed.
Lemma lem2607517 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2607518 (h1 : term266 = (BIT1 0)) : (term64 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2607519 : (term266 = (BIT1 0)) = ((term64 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2607518 h1) (fun h1 : (term64 = (NUMERAL 0)) = False => @lem2607517)). Qed.
Lemma lem2607520 : (term64 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2607519) (@lem2607517)). Qed.
Lemma lem2607521 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2607522 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2607523 : term333 = (and True).
Proof. exact (MK_COMB (@lem2607522) (@lem2607521)). Qed.
Lemma lem2607524 : term332 = (True /\ False).
Proof. exact (MK_COMB (@lem2607523) (@lem2607520)). Qed.
Lemma lem2607526 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2607527 : term332 = False.
Proof. exact (TRANS (@lem2607524) (@lem2607526)). Qed.
Lemma lem2607528 : term322 = False.
Proof. exact (TRANS (@lem2607516) (@lem2607527)). Qed.
Lemma lem2607529 : term328 = False.
Proof. exact (TRANS (@lem2607513) (@lem2607528)). Qed.
Lemma lem2607530 : term325 = False.
Proof. exact (TRANS (@lem2607497) (@lem2607529)). Qed.
Lemma lem2607531 : term322 = False.
Proof. exact (TRANS (@lem2607474) (@lem2607530)). Qed.
Lemma lem2607532 : term321 = False.
Proof. exact (TRANS (@lem2607465) (@lem2607531)). Qed.
Lemma lem2607533 (m : nat) (n : nat) (h1 : term646 m n) : False.
Proof. exact (EQ_MP (@lem2607532) (@lem2607462 m n h1)). Qed.
Lemma lem2607535 (m : nat) (n : nat) (h1 : term646 m n) : term646 m n.
Proof. exact (h1). Qed.
Lemma lem2607536 (m : nat) (n : nat) (h1 : term646 m n) : (term646 m n) = False.
Proof. exact (prop_ext (fun h2 : term646 m n => @lem2607533 m n h1) (fun h2 : False => @lem2607535 m n h1)). Qed.
Lemma lem2607537 (m : nat) (n : nat) (h1 : term646 m n) : False.
Proof. exact (EQ_MP (@lem2607536 m n h1) (@lem2607535 m n h1)). Qed.
Lemma lem2607538 (m : nat) (n : nat) (h1 : term631 m n) : term631 m n.
Proof. exact (h1). Qed.
Lemma lem2607539 (m : nat) (n : nat) (h1 : term631 m n) : term646 m n.
Proof. exact (EQ_MP (@lem2606908 m n) (@lem2607538 m n h1)). Qed.
Lemma lem2607540 (m : nat) (n : nat) (h1 : term631 m n) : (term646 m n) = False.
Proof. exact (prop_ext (fun h2 : term646 m n => @lem2607537 m n h2) (fun h2 : False => @lem2607539 m n h1)). Qed.
Lemma lem2607541 (m : nat) (n : nat) (h1 : term631 m n) : False.
Proof. exact (EQ_MP (@lem2607540 m n h1) (@lem2607539 m n h1)). Qed.
Lemma lem2607542 (m : nat) (n : nat) : term681 m n.
Proof. exact (fun h0 : term631 m n => @lem2607541 m n h0). Qed.
Lemma lem2607543 (m : nat) (n : nat) : term682 m n.
Proof. exact (@lem1386578 (term683 m n)). Qed.
Lemma lem2607546 (m : nat) (n : nat) : term683 m n.
Proof. exact (@lem2607543 m n (@lem2607542 m n)). Qed.
Lemma lem2607547 (m : nat) (n : nat) : (term630 m n) = (term615 m n).
Proof. exact (SYM (@lem2606812 m n)). Qed.
Lemma lem2607548 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2607549 (m : nat) (n : nat) : (term683 m n) = (term613 m n).
Proof. exact (MK_COMB (@lem2607548) (@lem2607547 m n)). Qed.
Lemma lem2607550 (m : nat) (n : nat) : term613 m n.
Proof. exact (EQ_MP (@lem2607549 m n) (@lem2607546 m n)). Qed.
Lemma lem2607551 (m : nat) (n : nat) : term614 m n.
Proof. exact (EQ_MP (@lem2606768 m n) (@lem2607550 m n)). Qed.
Lemma lem2607552 (m : nat) (n : nat) : term684 m n.
Proof. exact (@lem82 (term616 m n)). Qed.
Lemma lem2607554 (m : nat) : term685 m.
Proof. exact (@lem2307247 m). Qed.
Lemma lem2607555 (m : nat) : (term685 m) = (term686 m).
Proof. exact (eq_refl (term685 m)). Qed.
Lemma lem2607556 (m : nat) : term686 m.
Proof. exact (EQ_MP (@lem2607555 m) (@lem2607554 m)). Qed.
Lemma lem2607557 (m : nat) (n : nat) : term687 m n.
Proof. exact (@lem2607556 m n). Qed.
Lemma lem2607558 (m : nat) (n : nat) : (term687 m n) = ((term688 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term687 m n)). Qed.
Lemma lem2607560 (m : nat) : term689 m.
Proof. exact (@lem2307381 m). Qed.
Lemma lem2607561 (m : nat) : (term689 m) = (term690 m).
Proof. exact (eq_refl (term689 m)). Qed.
Lemma lem2607562 (m : nat) : term690 m.
Proof. exact (EQ_MP (@lem2607561 m) (@lem2607560 m)). Qed.
Lemma lem2607563 (m : nat) (n : nat) : term691 m n.
Proof. exact (@lem2607562 m n). Qed.
Lemma lem2607564 (m : nat) (n : nat) : (term691 m n) = ((term692 m n) = (term693 m n)).
Proof. exact (eq_refl (term691 m n)). Qed.
Lemma lem2607566 (x : int) : term694 x.
Proof. exact (@lem2306266 x). Qed.
Lemma lem2607567 (x : int) : (term694 x) = (term695 x).
Proof. exact (eq_refl (term694 x)). Qed.
Lemma lem2607568 (x : int) : term695 x.
Proof. exact (EQ_MP (@lem2607567 x) (@lem2607566 x)). Qed.
Lemma lem2607569 (x : int) (y : int) : term696 x y.
Proof. exact (@lem2607568 x y). Qed.
Lemma lem2607570 (x : int) (y : int) : (term696 x y) = ((term21 x y) = (term697 x y)).
Proof. exact (eq_refl (term696 x y)). Qed.
Lemma lem2607572 (P : int -> Prop) : term698 P.
Proof. exact (@lem2296993 P). Qed.
Lemma lem2607573 (P : int -> Prop) : (term698 P) = ((term699 P) = (term700 P)).
Proof. exact (eq_refl (term698 P)). Qed.
Lemma lem2607575 (m : nat) : term701 m.
Proof. exact (@lem2538105 m). Qed.
Lemma lem2607576 (m : nat) : (term701 m) = (term702 m).
Proof. exact (eq_refl (term701 m)). Qed.
Lemma lem2607577 (m : nat) : term702 m.
Proof. exact (EQ_MP (@lem2607576 m) (@lem2607575 m)). Qed.
Lemma lem2607578 (m : nat) (n : nat) : term703 m n.
Proof. exact (@lem2607577 m n). Qed.
Lemma lem2607579 (m : nat) (n : nat) : (term703 m n) = ((term598 m n) = (term704 m n)).
Proof. exact (eq_refl (term703 m n)). Qed.
Lemma lem2607591 (p : Prop) : term705 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem2607592 (p : Prop) : (term705 p) = (term706 p).
Proof. exact (eq_refl (term705 p)). Qed.
Lemma lem2607593 (p : Prop) : term706 p.
Proof. exact (EQ_MP (@lem2607592 p) (@lem2607591 p)). Qed.
Lemma lem2607594 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem2607595 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem2607606 (q : Prop) : (term707 q) = (term707 q).
Proof. exact (eq_refl (term707 q)). Qed.
Lemma lem2607607 (q : Prop) (p : Prop) (h1 : p = True) : (term708 q p) = (term709 q).
Proof. exact (MK_COMB (@lem2607606 q) (@lem2607594 p h1)). Qed.
Lemma lem2607608 (q : Prop) : (term709 q) = (term710 q).
Proof. exact (eq_refl (term709 q)). Qed.
Lemma lem2607609 (q : Prop) (p : Prop) : (term711 q p) = (term711 q p).
Proof. exact (eq_refl (term711 q p)). Qed.
Lemma lem2607610 (p : Prop) (q : Prop) : ((term708 q p) = (term709 q)) = ((term708 q p) = (term710 q)).
Proof. exact (MK_COMB (@lem2607609 q p) (@lem2607608 q)). Qed.
Lemma lem2607611 (p : Prop) (q : Prop) : (term708 q p) = (term712 p q).
Proof. exact (eq_refl (term708 q p)). Qed.
Lemma lem2607612 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2607613 (p : Prop) (q : Prop) : (term711 q p) = (term713 p q).
Proof. exact (MK_COMB (@lem2607612) (@lem2607611 p q)). Qed.
Lemma lem2607614 (q : Prop) : (term710 q) = (term710 q).
Proof. exact (eq_refl (term710 q)). Qed.
Lemma lem2607615 (p : Prop) (q : Prop) : ((term708 q p) = (term710 q)) = ((term712 p q) = (term710 q)).
Proof. exact (MK_COMB (@lem2607613 p q) (@lem2607614 q)). Qed.
Lemma lem2607616 (p : Prop) (q : Prop) : ((term708 q p) = (term709 q)) = ((term712 p q) = (term710 q)).
Proof. exact (TRANS (@lem2607610 p q) (@lem2607615 p q)). Qed.
Lemma lem2607617 (q : Prop) (p : Prop) (h1 : p = True) : (term712 p q) = (term710 q).
Proof. exact (EQ_MP (@lem2607616 p q) (@lem2607607 q p h1)). Qed.
Lemma lem2607618 (q : Prop) (p : Prop) (h1 : p = True) : (term710 q) = (term712 p q).
Proof. exact (SYM (@lem2607617 q p h1)). Qed.
Lemma lem2607619 (q : Prop) : (term707 q) = (term707 q).
Proof. exact (eq_refl (term707 q)). Qed.
Lemma lem2607620 (q : Prop) (p : Prop) (h1 : p = False) : (term708 q p) = (term714 q).
Proof. exact (MK_COMB (@lem2607619 q) (@lem2607595 p h1)). Qed.
Lemma lem2607621 (q : Prop) : (term714 q) = (term715 q).
Proof. exact (eq_refl (term714 q)). Qed.
Lemma lem2607622 (q : Prop) (p : Prop) : (term711 q p) = (term711 q p).
Proof. exact (eq_refl (term711 q p)). Qed.
Lemma lem2607623 (p : Prop) (q : Prop) : ((term708 q p) = (term714 q)) = ((term708 q p) = (term715 q)).
Proof. exact (MK_COMB (@lem2607622 q p) (@lem2607621 q)). Qed.
Lemma lem2607624 (p : Prop) (q : Prop) : (term708 q p) = (term712 p q).
Proof. exact (eq_refl (term708 q p)). Qed.
Lemma lem2607625 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2607626 (p : Prop) (q : Prop) : (term711 q p) = (term713 p q).
Proof. exact (MK_COMB (@lem2607625) (@lem2607624 p q)). Qed.
Lemma lem2607627 (q : Prop) : (term715 q) = (term715 q).
Proof. exact (eq_refl (term715 q)). Qed.
Lemma lem2607628 (p : Prop) (q : Prop) : ((term708 q p) = (term715 q)) = ((term712 p q) = (term715 q)).
Proof. exact (MK_COMB (@lem2607626 p q) (@lem2607627 q)). Qed.
Lemma lem2607629 (p : Prop) (q : Prop) : ((term708 q p) = (term714 q)) = ((term712 p q) = (term715 q)).
Proof. exact (TRANS (@lem2607623 p q) (@lem2607628 p q)). Qed.
Lemma lem2607630 (q : Prop) (p : Prop) (h1 : p = False) : (term712 p q) = (term715 q).
Proof. exact (EQ_MP (@lem2607629 p q) (@lem2607620 q p h1)). Qed.
Lemma lem2607631 (q : Prop) (p : Prop) (h1 : p = False) : (term715 q) = (term712 p q).
Proof. exact (SYM (@lem2607630 q p h1)). Qed.
Lemma lem2607635 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2607636 (q : Prop) : (term716 q) = (True -> q).
Proof. exact (@lem2607635 (True -> q)). Qed.
Lemma lem2607638 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem2607639 (q : Prop) : (True -> q) = q.
Proof. exact (@lem2607638 q). Qed.
Lemma lem2607640 (q : Prop) : (term716 q) = q.
Proof. exact (TRANS (@lem2607636 q) (@lem2607639 q)). Qed.
Lemma lem2607641 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2607642 (q : Prop) : (term717 q) = (imp q).
Proof. exact (MK_COMB (@lem2607641) (@lem2607640 q)). Qed.
Lemma lem2607644 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2607645 (q : Prop) : (True /\ q) = q.
Proof. exact (@lem2607644 q). Qed.
Lemma lem2607646 (q : Prop) : (term710 q) = (q -> q).
Proof. exact (MK_COMB (@lem2607642 q) (@lem2607645 q)). Qed.
Lemma lem2607648 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem2607649 (q : Prop) : (q -> q) = True.
Proof. exact (@lem2607648 q). Qed.
Lemma lem2607650 (q : Prop) : (term710 q) = True.
Proof. exact (TRANS (@lem2607646 q) (@lem2607649 q)). Qed.
Lemma lem2607651 (q : Prop) : True = (term710 q).
Proof. exact (SYM (@lem2607650 q)). Qed.
Lemma lem2607652 (q : Prop) : term710 q.
Proof. exact (EQ_MP (@lem2607651 q) (@lem0)). Qed.
Lemma lem2607656 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem2607657 (q : Prop) : (term718 q) = False.
Proof. exact (@lem2607656 (False -> q)). Qed.
Lemma lem2607658 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2607659 (q : Prop) : (term719 q) = (imp False).
Proof. exact (MK_COMB (@lem2607658) (@lem2607657 q)). Qed.
Lemma lem2607661 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem2607662 (q : Prop) : (False /\ q) = False.
Proof. exact (@lem2607661 q). Qed.
Lemma lem2607663 (q : Prop) : (term715 q) = (False -> False).
Proof. exact (MK_COMB (@lem2607659 q) (@lem2607662 q)). Qed.
Lemma lem2607665 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem2607666 : (False -> False) = True.
Proof. exact (@lem2607665 False). Qed.
Lemma lem2607667 (q : Prop) : (term715 q) = True.
Proof. exact (TRANS (@lem2607663 q) (@lem2607666)). Qed.
Lemma lem2607668 (q : Prop) : True = (term715 q).
Proof. exact (SYM (@lem2607667 q)). Qed.
Lemma lem2607669 (q : Prop) : term715 q.
Proof. exact (EQ_MP (@lem2607668 q) (@lem0)). Qed.
Lemma lem2607670 (q : Prop) (p : Prop) (h1 : p = False) : term712 p q.
Proof. exact (EQ_MP (@lem2607631 q p h1) (@lem2607669 q)). Qed.
Lemma lem2607671 (q : Prop) (p : Prop) (h1 : p = True) : term712 p q.
Proof. exact (EQ_MP (@lem2607618 q p h1) (@lem2607652 q)). Qed.
Lemma lem2607674 (p : Prop) (q : Prop) : term712 p q.
Proof. exact (or_elim (@lem2607593 p) (fun h0 : p = True => @lem2607671 q p h0) (fun h0 : p = False => @lem2607670 q p h0)). Qed.
Lemma lem2607675 (p : Prop) (q : Prop) (h1 : term712 p q) : term712 p q.
Proof. exact (h1). Qed.
Lemma lem2607676 (p : Prop) (q : Prop) (h1 : term720 p q) : term720 p q.
Proof. exact (h1). Qed.
Lemma lem2607677 (p : Prop) (q : Prop) (h1 : term720 p q) (h2 : term712 p q) : p /\ q.
Proof. exact (@lem2607675 p q h2 (@lem2607676 p q h1)). Qed.
Lemma lem2607678 (p : Prop) (q : Prop) (h1 : term720 p q) : term721 p q.
Proof. exact (fun h0 : term712 p q => @lem2607677 p q h1 h0). Qed.
Lemma lem2607679 (p : Prop) (q : Prop) (h1 : term712 p q) : term712 p q.
Proof. exact (h1). Qed.
Lemma lem2607680 (p : Prop) (q : Prop) (h1 : term720 p q) (h2 : term712 p q) : p /\ q.
Proof. exact (@lem2607678 p q h1 (@lem2607679 p q h2)). Qed.
Lemma lem2607681 (p : Prop) (q : Prop) (h1 : term712 p q) : term712 p q.
Proof. exact (fun h0 : term720 p q => @lem2607680 p q h0 h1). Qed.
Lemma lem2607682 (p : Prop) (q : Prop) : term722 p q.
Proof. exact (fun h0 : term712 p q => @lem2607681 p q h0). Qed.
Lemma lem2607684 (P : int -> Prop) : term698 P.
Proof. exact (@lem2296993 P). Qed.
Lemma lem2607685 (P : int -> Prop) : (term698 P) = ((term699 P) = (term700 P)).
Proof. exact (eq_refl (term698 P)). Qed.
Lemma lem2607687 (m : nat) : term685 m.
Proof. exact (@lem2307247 m). Qed.
Lemma lem2607688 (m : nat) : (term685 m) = (term686 m).
Proof. exact (eq_refl (term685 m)). Qed.
Lemma lem2607689 (m : nat) : term686 m.
Proof. exact (EQ_MP (@lem2607688 m) (@lem2607687 m)). Qed.
Lemma lem2607690 (m : nat) (n : nat) : term687 m n.
Proof. exact (@lem2607689 m n). Qed.
Lemma lem2607691 (m : nat) (n : nat) : (term687 m n) = ((term688 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term687 m n)). Qed.
Lemma lem2607693 {A : Type'} (P : Prop) : term723 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem2607694 {A : Type'} (P : Prop) : (term723 A P) = (term724 A P).
Proof. exact (eq_refl (term723 A P)). Qed.
Lemma lem2607695 {A : Type'} (P : Prop) : term724 A P.
Proof. exact (EQ_MP (@lem2607694 A P) (@lem2607693 A P)). Qed.
Lemma lem2607696 {A : Type'} (P : Prop) (Q : A -> Prop) : term725 A P Q.
Proof. exact (@lem2607695 A P Q). Qed.
Lemma lem2607697 {A : Type'} (P : Prop) (Q : A -> Prop) : (term725 A P Q) = ((term726 A P Q) = (term727 A P Q)).
Proof. exact (eq_refl (term725 A P Q)). Qed.
Lemma lem2607699 (n : nat) : (term728 n) = (term729 n).
Proof. exact (@lem2318604 (term729 n)). Qed.
Lemma lem2607702 (t : Prop) : (term121 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2607710 (n : nat) : (term730 n) = (term731 n).
Proof. exact (@lem2607702 (term731 n)). Qed.
Lemma lem2607712 (x : int) (y : int) : (int_lt x y) = (term50 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem2607713 (n : nat) : (term731 n) = (term732 n).
Proof. exact (@lem2607712 term527 (term618 n)). Qed.
Lemma lem2607715 (x : int) (y : int) : (int_le x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2607716 (n : nat) : (term732 n) = (term733 n).
Proof. exact (@lem2607715 term734 (term618 n)). Qed.
Lemma lem2607718 (x : int) (y : int) : (term54 x y) = (term55 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2607719 : term735 = term736.
Proof. exact (@lem2607718 term527 term58). Qed.
Lemma lem2607721 (n : nat) : (term61 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2607722 : term533 = term160.
Proof. exact (@lem2607721 (NUMERAL 0)). Qed.
Lemma lem2607723 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2607724 : term737 = term311.
Proof. exact (MK_COMB (@lem2607723) (@lem2607722)). Qed.
Lemma lem2607726 (n : nat) : (term61 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2607727 : term62 = term63.
Proof. exact (@lem2607726 term64). Qed.
Lemma lem2607728 : term736 = term738.
Proof. exact (MK_COMB (@lem2607724) (@lem2607727)). Qed.
Lemma lem2607729 : term735 = term738.
Proof. exact (TRANS (@lem2607719) (@lem2607728)). Qed.
Lemma lem2607730 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2607731 : term739 = term740.
Proof. exact (MK_COMB (@lem2607730) (@lem2607729)). Qed.
Lemma lem2607733 (x : int) : (term43 x) = (term44 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2607734 (n : nat) : (term628 n) = (term629 n).
Proof. exact (@lem2607733 (int_of_num n)). Qed.
Lemma lem2607736 (n : nat) : (term61 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2607737 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2607738 (n : nat) : (term629 n) = (term135 n).
Proof. exact (MK_COMB (@lem2607737) (@lem2607736 n)). Qed.
Lemma lem2607739 (n : nat) : (term628 n) = (term135 n).
Proof. exact (TRANS (@lem2607734 n) (@lem2607738 n)). Qed.
Lemma lem2607740 (n : nat) : (term733 n) = (term741 n).
Proof. exact (MK_COMB (@lem2607731) (@lem2607739 n)). Qed.
Lemma lem2607741 (n : nat) : (term732 n) = (term741 n).
Proof. exact (TRANS (@lem2607716 n) (@lem2607740 n)). Qed.
Lemma lem2607742 (n : nat) : (term731 n) = (term741 n).
Proof. exact (TRANS (@lem2607713 n) (@lem2607741 n)). Qed.
Lemma lem2607743 (n : nat) : (term730 n) = (term741 n).
Proof. exact (TRANS (@lem2607710 n) (@lem2607742 n)). Qed.
Lemma lem2607747 (t : Prop) : (term121 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2607753 (n : nat) : (term742 n) = (term741 n).
Proof. exact (@lem2607747 (term741 n)). Qed.
Lemma lem2607754 (n : nat) : (term741 n) = (term743 n).
Proof. exact (@lem1988287 (term135 n) term738). Qed.
Lemma lem2607761 : term738 = term63.
Proof. exact (@lem1982721 term63). Qed.
Lemma lem2607768 (n : nat) : (term135 n) = (term633 n).
Proof. exact (@lem1982785 (real_of_num n)). Qed.
Lemma lem2607769 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2607770 (n : nat) : (term634 n) = (term635 n).
Proof. exact (MK_COMB (@lem2607769) (@lem2607768 n)). Qed.
Lemma lem2607771 (n : nat) : (term744 n) = (term745 n).
Proof. exact (MK_COMB (@lem2607770 n) (@lem2607761)). Qed.
Lemma lem2607772 (n : nat) : (term745 n) = (term640 n).
Proof. exact (@lem1982792 (term633 n) term63). Qed.
Lemma lem2607774 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2607775 : term63 = term151.
Proof. exact (@lem2607774 term64). Qed.
Lemma lem2607777 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2607778 : term127 = term137.
Proof. exact (@lem2607777 term64). Qed.
Lemma lem2607779 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2607780 : term128 = term138.
Proof. exact (MK_COMB (@lem2607779) (@lem2607778)). Qed.
Lemma lem2607781 : term172 = term173.
Proof. exact (MK_COMB (@lem2607780) (@lem2607775)). Qed.
Lemma lem2607782 : term173 = term174.
Proof. exact (@lem1981613 term127 term63 term63 term63). Qed.
Lemma lem2607784 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2607785 : term144 = term145.
Proof. exact (@lem2607784 term64 term64). Qed.
Lemma lem2607786 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2607787 : term147 = term64.
Proof. exact (EQ_MP (@lem2607786) (@lem940073)). Qed.
Lemma lem2607788 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2607789 : term145 = term63.
Proof. exact (MK_COMB (@lem2607788) (@lem2607787)). Qed.
Lemma lem2607790 : term144 = term63.
Proof. exact (TRANS (@lem2607785) (@lem2607789)). Qed.
Lemma lem2607792 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2607793 : term172 = term177.
Proof. exact (@lem2607792 term64 term64). Qed.
Lemma lem2607794 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2607795 : term147 = term64.
Proof. exact (EQ_MP (@lem2607794) (@lem940073)). Qed.
Lemma lem2607796 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2607797 : term145 = term63.
Proof. exact (MK_COMB (@lem2607796) (@lem2607795)). Qed.
Lemma lem2607798 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2607799 : term177 = term127.
Proof. exact (MK_COMB (@lem2607798) (@lem2607797)). Qed.
Lemma lem2607800 : term172 = term127.
Proof. exact (TRANS (@lem2607793) (@lem2607799)). Qed.
Lemma lem2607801 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2607802 : term178 = term179.
Proof. exact (MK_COMB (@lem2607801) (@lem2607800)). Qed.
Lemma lem2607803 : term174 = term137.
Proof. exact (MK_COMB (@lem2607802) (@lem2607790)). Qed.
Lemma lem2607804 : term173 = term137.
Proof. exact (TRANS (@lem2607782) (@lem2607803)). Qed.
Lemma lem2607805 : term172 = term137.
Proof. exact (TRANS (@lem2607781) (@lem2607804)). Qed.
Lemma lem2607807 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2607808 : term137 = term127.
Proof. exact (@lem2607807 term127). Qed.
Lemma lem2607809 : term172 = term127.
Proof. exact (TRANS (@lem2607805) (@lem2607808)). Qed.
Lemma lem2607810 (n : nat) : (term641 n) = (term641 n).
Proof. exact (eq_refl (term641 n)). Qed.
Lemma lem2607813 (n : nat) : (term640 n) = (term642 n).
Proof. exact (MK_COMB (@lem2607810 n) (@lem2607809)). Qed.
Lemma lem2607814 (n : nat) : (term745 n) = (term642 n).
Proof. exact (TRANS (@lem2607772 n) (@lem2607813 n)). Qed.
Lemma lem2607815 (n : nat) : (term744 n) = (term642 n).
Proof. exact (TRANS (@lem2607771 n) (@lem2607814 n)). Qed.
Lemma lem2607816 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2607817 (n : nat) : (term746 n) = (term670 n).
Proof. exact (MK_COMB (@lem2607816) (@lem2607815 n)). Qed.
Lemma lem2607818 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2607819 (n : nat) : (term743 n) = (term671 n).
Proof. exact (MK_COMB (@lem2607817 n) (@lem2607818)). Qed.
Lemma lem2607820 (n : nat) : (term741 n) = (term671 n).
Proof. exact (TRANS (@lem2607754 n) (@lem2607819 n)). Qed.
Lemma lem2607829 (n : nat) : (term742 n) = (term671 n).
Proof. exact (TRANS (@lem2607753 n) (@lem2607820 n)). Qed.
Lemma lem2607833 (n : nat) (h1 : term671 n) : term671 n.
Proof. exact (h1). Qed.
Lemma lem2607834 (n : nat) : term647 n.
Proof. exact (@lem1396812 n). Qed.
Lemma lem2607836 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2607837 : term257 = term258.
Proof. exact (@lem2607836 term160 term63). Qed.
Lemma lem2607839 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2607840 : term63 = term151.
Proof. exact (@lem2607839 term64). Qed.
Lemma lem2607842 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2607843 : term160 = term259.
Proof. exact (@lem2607842 (NUMERAL 0)). Qed.
Lemma lem2607844 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2607845 : term260 = term261.
Proof. exact (MK_COMB (@lem2607844) (@lem2607843)). Qed.
Lemma lem2607846 : term258 = term262.
Proof. exact (MK_COMB (@lem2607845) (@lem2607840)). Qed.
Lemma lem2607847 : term263.
Proof. exact (@lem1980255 term160 term63 term63 term63). Qed.
Lemma lem2607849 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2607850 : term258 = term265.
Proof. exact (@lem2607849 (NUMERAL 0) term64). Qed.
Lemma lem2607851 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2607852 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2607853 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2607852 h1) (fun h1 : term265 = True => @lem2607851)). Qed.
Lemma lem2607854 : term265 = True.
Proof. exact (EQ_MP (@lem2607853) (@lem2607851)). Qed.
Lemma lem2607855 : term258 = True.
Proof. exact (TRANS (@lem2607850) (@lem2607854)). Qed.
Lemma lem2607856 : True = term258.
Proof. exact (SYM (@lem2607855)). Qed.
Lemma lem2607857 : term258.
Proof. exact (EQ_MP (@lem2607856) (@lem0)). Qed.
Lemma lem2607858 : term267.
Proof. exact (@lem2607847 (@lem2607857)). Qed.
Lemma lem2607860 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2607861 : term258 = term265.
Proof. exact (@lem2607860 (NUMERAL 0) term64). Qed.
Lemma lem2607862 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2607863 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2607864 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2607863 h1) (fun h1 : term265 = True => @lem2607862)). Qed.
Lemma lem2607865 : term265 = True.
Proof. exact (EQ_MP (@lem2607864) (@lem2607862)). Qed.
Lemma lem2607866 : term258 = True.
Proof. exact (TRANS (@lem2607861) (@lem2607865)). Qed.
Lemma lem2607867 : True = term258.
Proof. exact (SYM (@lem2607866)). Qed.
Lemma lem2607868 : term258.
Proof. exact (EQ_MP (@lem2607867) (@lem0)). Qed.
Lemma lem2607869 : term262 = term268.
Proof. exact (@lem2607858 (@lem2607868)). Qed.
Lemma lem2607871 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2607872 : term144 = term145.
Proof. exact (@lem2607871 term64 term64). Qed.
Lemma lem2607873 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2607874 : term147 = term64.
Proof. exact (EQ_MP (@lem2607873) (@lem940073)). Qed.
Lemma lem2607875 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2607876 : term145 = term63.
Proof. exact (MK_COMB (@lem2607875) (@lem2607874)). Qed.
Lemma lem2607877 : term144 = term63.
Proof. exact (TRANS (@lem2607872) (@lem2607876)). Qed.
Lemma lem2607879 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2607880 : term270 = term160.
Proof. exact (@lem2607879 term64). Qed.
Lemma lem2607881 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2607882 : term271 = term260.
Proof. exact (MK_COMB (@lem2607881) (@lem2607880)). Qed.
Lemma lem2607883 : term268 = term258.
Proof. exact (MK_COMB (@lem2607882) (@lem2607877)). Qed.
Lemma lem2607885 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2607886 : term258 = term265.
Proof. exact (@lem2607885 (NUMERAL 0) term64). Qed.
Lemma lem2607887 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2607888 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2607889 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2607888 h1) (fun h1 : term265 = True => @lem2607887)). Qed.
Lemma lem2607890 : term265 = True.
Proof. exact (EQ_MP (@lem2607889) (@lem2607887)). Qed.
Lemma lem2607891 : term258 = True.
Proof. exact (TRANS (@lem2607886) (@lem2607890)). Qed.
Lemma lem2607892 : term268 = True.
Proof. exact (TRANS (@lem2607883) (@lem2607891)). Qed.
Lemma lem2607893 : term262 = True.
Proof. exact (TRANS (@lem2607869) (@lem2607892)). Qed.
Lemma lem2607894 : term258 = True.
Proof. exact (TRANS (@lem2607846) (@lem2607893)). Qed.
Lemma lem2607895 : term257 = True.
Proof. exact (TRANS (@lem2607837) (@lem2607894)). Qed.
Lemma lem2607896 : True = term257.
Proof. exact (SYM (@lem2607895)). Qed.
Lemma lem2607897 : term257.
Proof. exact (EQ_MP (@lem2607896) (@lem0)). Qed.
Lemma lem2607898 (n : nat) : term648 n.
Proof. exact (conj (@lem2607897) (@lem2607834 n)). Qed.
Lemma lem2607900 (x : real) (y : real) : term273 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2607901 (n : nat) : term649 n.
Proof. exact (@lem2607900 term63 (real_of_num n)). Qed.
Lemma lem2607902 (n : nat) : term650 n.
Proof. exact (@lem2607901 n (@lem2607898 n)). Qed.
Lemma lem2607903 (n : nat) : (term651 n) = (real_of_num n).
Proof. exact (@lem1982733 (real_of_num n)). Qed.
Lemma lem2607904 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2607905 (n : nat) : (term652 n) = (term653 n).
Proof. exact (MK_COMB (@lem2607904) (@lem2607903 n)). Qed.
Lemma lem2607906 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2607907 (n : nat) : (term650 n) = (term647 n).
Proof. exact (MK_COMB (@lem2607905 n) (@lem2607906)). Qed.
Lemma lem2607908 (n : nat) : term647 n.
Proof. exact (EQ_MP (@lem2607907 n) (@lem2607902 n)). Qed.
Lemma lem2607910 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2607911 : term257 = term258.
Proof. exact (@lem2607910 term160 term63). Qed.
Lemma lem2607913 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2607914 : term63 = term151.
Proof. exact (@lem2607913 term64). Qed.
Lemma lem2607916 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2607917 : term160 = term259.
Proof. exact (@lem2607916 (NUMERAL 0)). Qed.
Lemma lem2607918 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2607919 : term260 = term261.
Proof. exact (MK_COMB (@lem2607918) (@lem2607917)). Qed.
Lemma lem2607920 : term258 = term262.
Proof. exact (MK_COMB (@lem2607919) (@lem2607914)). Qed.
Lemma lem2607921 : term263.
Proof. exact (@lem1980255 term160 term63 term63 term63). Qed.
Lemma lem2607923 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2607924 : term258 = term265.
Proof. exact (@lem2607923 (NUMERAL 0) term64). Qed.
Lemma lem2607925 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2607926 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2607927 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2607926 h1) (fun h1 : term265 = True => @lem2607925)). Qed.
Lemma lem2607928 : term265 = True.
Proof. exact (EQ_MP (@lem2607927) (@lem2607925)). Qed.
Lemma lem2607929 : term258 = True.
Proof. exact (TRANS (@lem2607924) (@lem2607928)). Qed.
Lemma lem2607930 : True = term258.
Proof. exact (SYM (@lem2607929)). Qed.
Lemma lem2607931 : term258.
Proof. exact (EQ_MP (@lem2607930) (@lem0)). Qed.
Lemma lem2607932 : term267.
Proof. exact (@lem2607921 (@lem2607931)). Qed.
Lemma lem2607934 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2607935 : term258 = term265.
Proof. exact (@lem2607934 (NUMERAL 0) term64). Qed.
Lemma lem2607936 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2607937 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2607938 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2607937 h1) (fun h1 : term265 = True => @lem2607936)). Qed.
Lemma lem2607939 : term265 = True.
Proof. exact (EQ_MP (@lem2607938) (@lem2607936)). Qed.
Lemma lem2607940 : term258 = True.
Proof. exact (TRANS (@lem2607935) (@lem2607939)). Qed.
Lemma lem2607941 : True = term258.
Proof. exact (SYM (@lem2607940)). Qed.
Lemma lem2607942 : term258.
Proof. exact (EQ_MP (@lem2607941) (@lem0)). Qed.
Lemma lem2607943 : term262 = term268.
Proof. exact (@lem2607932 (@lem2607942)). Qed.
Lemma lem2607945 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2607946 : term144 = term145.
Proof. exact (@lem2607945 term64 term64). Qed.
Lemma lem2607947 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2607948 : term147 = term64.
Proof. exact (EQ_MP (@lem2607947) (@lem940073)). Qed.
Lemma lem2607949 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2607950 : term145 = term63.
Proof. exact (MK_COMB (@lem2607949) (@lem2607948)). Qed.
Lemma lem2607951 : term144 = term63.
Proof. exact (TRANS (@lem2607946) (@lem2607950)). Qed.
Lemma lem2607953 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2607954 : term270 = term160.
Proof. exact (@lem2607953 term64). Qed.
Lemma lem2607955 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2607956 : term271 = term260.
Proof. exact (MK_COMB (@lem2607955) (@lem2607954)). Qed.
Lemma lem2607957 : term268 = term258.
Proof. exact (MK_COMB (@lem2607956) (@lem2607951)). Qed.
Lemma lem2607959 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2607960 : term258 = term265.
Proof. exact (@lem2607959 (NUMERAL 0) term64). Qed.
Lemma lem2607961 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2607962 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2607963 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2607962 h1) (fun h1 : term265 = True => @lem2607961)). Qed.
Lemma lem2607964 : term265 = True.
Proof. exact (EQ_MP (@lem2607963) (@lem2607961)). Qed.
Lemma lem2607965 : term258 = True.
Proof. exact (TRANS (@lem2607960) (@lem2607964)). Qed.
Lemma lem2607966 : term268 = True.
Proof. exact (TRANS (@lem2607957) (@lem2607965)). Qed.
Lemma lem2607967 : term262 = True.
Proof. exact (TRANS (@lem2607943) (@lem2607966)). Qed.
Lemma lem2607968 : term258 = True.
Proof. exact (TRANS (@lem2607920) (@lem2607967)). Qed.
Lemma lem2607969 : term257 = True.
Proof. exact (TRANS (@lem2607911) (@lem2607968)). Qed.
Lemma lem2607970 : True = term257.
Proof. exact (SYM (@lem2607969)). Qed.
Lemma lem2607971 : term257.
Proof. exact (EQ_MP (@lem2607970) (@lem0)). Qed.
Lemma lem2607972 (n : nat) (h1 : term671 n) : term672 n.
Proof. exact (conj (@lem2607971) (@lem2607833 n h1)). Qed.
Lemma lem2607974 (x : real) (y : real) : term273 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2607975 (n : nat) : term673 n.
Proof. exact (@lem2607974 term63 (term642 n)). Qed.
Lemma lem2607976 (n : nat) (h1 : term671 n) : term674 n.
Proof. exact (@lem2607975 n (@lem2607972 n h1)). Qed.
Lemma lem2607977 (n : nat) : (term675 n) = (term642 n).
Proof. exact (@lem1982733 (term642 n)). Qed.
Lemma lem2607978 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2607979 (n : nat) : (term676 n) = (term670 n).
Proof. exact (MK_COMB (@lem2607978) (@lem2607977 n)). Qed.
Lemma lem2607980 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2607981 (n : nat) : (term674 n) = (term671 n).
Proof. exact (MK_COMB (@lem2607979 n) (@lem2607980)). Qed.
Lemma lem2607982 (n : nat) (h1 : term671 n) : term671 n.
Proof. exact (EQ_MP (@lem2607981 n) (@lem2607976 n h1)). Qed.
Lemma lem2607983 (n : nat) (h1 : term671 n) : term677 n.
Proof. exact (conj (@lem2607982 n h1) (@lem2607908 n)). Qed.
Lemma lem2607985 (x : real) (y : real) : term361 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2607986 (n : nat) : term678 n.
Proof. exact (@lem2607985 (term642 n) (real_of_num n)). Qed.
Lemma lem2607987 (n : nat) (h1 : term671 n) : term679 n.
Proof. exact (@lem2607986 n (@lem2607983 n h1)). Qed.
Lemma lem2607988 (n : nat) : (term664 n) = (term665 n).
Proof. exact (@lem1982759 (term633 n) (real_of_num n) term127). Qed.
Lemma lem2607989 (n : nat) : (term666 n) = (term667 n).
Proof. exact (@lem1982713 term127 (real_of_num n)). Qed.
Lemma lem2607991 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2607992 : term63 = term151.
Proof. exact (@lem2607991 term64). Qed.
Lemma lem2607994 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2607995 : term127 = term137.
Proof. exact (@lem2607994 term64). Qed.
Lemma lem2607996 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2607997 : term293 = term294.
Proof. exact (MK_COMB (@lem2607996) (@lem2607995)). Qed.
Lemma lem2607998 : term295 = term296.
Proof. exact (MK_COMB (@lem2607997) (@lem2607992)). Qed.
Lemma lem2607999 : term297.
Proof. exact (@lem1981473 term127 term63 term63 term63 term160 term63). Qed.
Lemma lem2608001 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2608002 : term258 = term265.
Proof. exact (@lem2608001 (NUMERAL 0) term64). Qed.
Lemma lem2608003 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2608004 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2608005 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2608004 h1) (fun h1 : term265 = True => @lem2608003)). Qed.
Lemma lem2608006 : term265 = True.
Proof. exact (EQ_MP (@lem2608005) (@lem2608003)). Qed.
Lemma lem2608007 : term258 = True.
Proof. exact (TRANS (@lem2608002) (@lem2608006)). Qed.
Lemma lem2608008 : True = term258.
Proof. exact (SYM (@lem2608007)). Qed.
Lemma lem2608009 : term258.
Proof. exact (EQ_MP (@lem2608008) (@lem0)). Qed.
Lemma lem2608010 : term298.
Proof. exact (@lem2607999 (@lem2608009)). Qed.
Lemma lem2608012 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2608013 : term258 = term265.
Proof. exact (@lem2608012 (NUMERAL 0) term64). Qed.
Lemma lem2608014 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2608015 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2608016 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2608015 h1) (fun h1 : term265 = True => @lem2608014)). Qed.
Lemma lem2608017 : term265 = True.
Proof. exact (EQ_MP (@lem2608016) (@lem2608014)). Qed.
Lemma lem2608018 : term258 = True.
Proof. exact (TRANS (@lem2608013) (@lem2608017)). Qed.
Lemma lem2608019 : True = term258.
Proof. exact (SYM (@lem2608018)). Qed.
Lemma lem2608020 : term258.
Proof. exact (EQ_MP (@lem2608019) (@lem0)). Qed.
Lemma lem2608021 : term299.
Proof. exact (@lem2608010 (@lem2608020)). Qed.
Lemma lem2608023 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2608024 : term258 = term265.
Proof. exact (@lem2608023 (NUMERAL 0) term64). Qed.
Lemma lem2608025 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2608026 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2608027 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2608026 h1) (fun h1 : term265 = True => @lem2608025)). Qed.
Lemma lem2608028 : term265 = True.
Proof. exact (EQ_MP (@lem2608027) (@lem2608025)). Qed.
Lemma lem2608029 : term258 = True.
Proof. exact (TRANS (@lem2608024) (@lem2608028)). Qed.
Lemma lem2608030 : True = term258.
Proof. exact (SYM (@lem2608029)). Qed.
Lemma lem2608031 : term258.
Proof. exact (EQ_MP (@lem2608030) (@lem0)). Qed.
Lemma lem2608032 : term300.
Proof. exact (@lem2608021 (@lem2608031)). Qed.
Lemma lem2608034 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2608035 : term144 = term145.
Proof. exact (@lem2608034 term64 term64). Qed.
Lemma lem2608036 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2608037 : term147 = term64.
Proof. exact (EQ_MP (@lem2608036) (@lem940073)). Qed.
Lemma lem2608038 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2608039 : term145 = term63.
Proof. exact (MK_COMB (@lem2608038) (@lem2608037)). Qed.
Lemma lem2608040 : term144 = term63.
Proof. exact (TRANS (@lem2608035) (@lem2608039)). Qed.
Lemma lem2608042 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2608043 : term172 = term177.
Proof. exact (@lem2608042 term64 term64). Qed.
Lemma lem2608044 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2608045 : term147 = term64.
Proof. exact (EQ_MP (@lem2608044) (@lem940073)). Qed.
Lemma lem2608046 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2608047 : term145 = term63.
Proof. exact (MK_COMB (@lem2608046) (@lem2608045)). Qed.
Lemma lem2608048 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2608049 : term177 = term127.
Proof. exact (MK_COMB (@lem2608048) (@lem2608047)). Qed.
Lemma lem2608050 : term172 = term127.
Proof. exact (TRANS (@lem2608043) (@lem2608049)). Qed.
Lemma lem2608051 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2608052 : term301 = term293.
Proof. exact (MK_COMB (@lem2608051) (@lem2608050)). Qed.
Lemma lem2608053 : term302 = term295.
Proof. exact (MK_COMB (@lem2608052) (@lem2608040)). Qed.
Lemma lem2608055 (m : nat) : (term303 m) = term160.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2608056 : term295 = term160.
Proof. exact (@lem2608055 term64). Qed.
Lemma lem2608057 : term302 = term160.
Proof. exact (TRANS (@lem2608053) (@lem2608056)). Qed.
Lemma lem2608058 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2608059 : term304 = term305.
Proof. exact (MK_COMB (@lem2608058) (@lem2608057)). Qed.
Lemma lem2608060 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem2608061 : term306 = term270.
Proof. exact (MK_COMB (@lem2608059) (@lem2608060)). Qed.
Lemma lem2608063 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2608064 : term270 = term160.
Proof. exact (@lem2608063 term64). Qed.
Lemma lem2608065 : term306 = term160.
Proof. exact (TRANS (@lem2608061) (@lem2608064)). Qed.
Lemma lem2608067 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2608068 : term144 = term145.
Proof. exact (@lem2608067 term64 term64). Qed.
Lemma lem2608069 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2608070 : term147 = term64.
Proof. exact (EQ_MP (@lem2608069) (@lem940073)). Qed.
Lemma lem2608071 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2608072 : term145 = term63.
Proof. exact (MK_COMB (@lem2608071) (@lem2608070)). Qed.
Lemma lem2608073 : term144 = term63.
Proof. exact (TRANS (@lem2608068) (@lem2608072)). Qed.
Lemma lem2608074 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem2608075 : term307 = term270.
Proof. exact (MK_COMB (@lem2608074) (@lem2608073)). Qed.
Lemma lem2608077 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2608078 : term270 = term160.
Proof. exact (@lem2608077 term64). Qed.
Lemma lem2608079 : term307 = term160.
Proof. exact (TRANS (@lem2608075) (@lem2608078)). Qed.
Lemma lem2608080 : term160 = term307.
Proof. exact (SYM (@lem2608079)). Qed.
Lemma lem2608081 : term306 = term307.
Proof. exact (TRANS (@lem2608065) (@lem2608080)). Qed.
Lemma lem2608082 : term296 = term259.
Proof. exact (@lem2608032 (@lem2608081)). Qed.
Lemma lem2608083 : term295 = term259.
Proof. exact (TRANS (@lem2607998) (@lem2608082)). Qed.
Lemma lem2608085 (x : real) : (term152 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2608086 : term259 = term160.
Proof. exact (@lem2608085 term160). Qed.
Lemma lem2608087 : term295 = term160.
Proof. exact (TRANS (@lem2608083) (@lem2608086)). Qed.
Lemma lem2608088 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2608089 : term308 = term305.
Proof. exact (MK_COMB (@lem2608088) (@lem2608087)). Qed.
Lemma lem2608090 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2608091 (n : nat) : (term667 n) = (term269 n).
Proof. exact (MK_COMB (@lem2608089) (@lem2608090 n)). Qed.
Lemma lem2608092 (n : nat) : (term666 n) = (term269 n).
Proof. exact (TRANS (@lem2607989 n) (@lem2608091 n)). Qed.
Lemma lem2608093 (n : nat) : (term269 n) = term160.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem2608094 (n : nat) : (term666 n) = term160.
Proof. exact (TRANS (@lem2608092 n) (@lem2608093 n)). Qed.
Lemma lem2608095 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2608096 (n : nat) : (term668 n) = term311.
Proof. exact (MK_COMB (@lem2608095) (@lem2608094 n)). Qed.
Lemma lem2608097 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem2608098 (n : nat) : (term665 n) = term318.
Proof. exact (MK_COMB (@lem2608096 n) (@lem2608097)). Qed.
Lemma lem2608099 (n : nat) : (term664 n) = term318.
Proof. exact (TRANS (@lem2607988 n) (@lem2608098 n)). Qed.
Lemma lem2608100 : term318 = term127.
Proof. exact (@lem1982721 term127). Qed.
Lemma lem2608101 (n : nat) : (term664 n) = term127.
Proof. exact (TRANS (@lem2608099 n) (@lem2608100)). Qed.
Lemma lem2608102 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2608103 (n : nat) : (term680 n) = term320.
Proof. exact (MK_COMB (@lem2608102) (@lem2608101 n)). Qed.
Lemma lem2608104 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem2608105 (n : nat) : (term679 n) = term321.
Proof. exact (MK_COMB (@lem2608103 n) (@lem2608104)). Qed.
Lemma lem2608106 (n : nat) (h1 : term671 n) : term321.
Proof. exact (EQ_MP (@lem2608105 n) (@lem2607987 n h1)). Qed.
Lemma lem2608108 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2608109 : term321 = term322.
Proof. exact (@lem2608108 term160 term127). Qed.
Lemma lem2608111 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2608112 : term127 = term137.
Proof. exact (@lem2608111 term64). Qed.
Lemma lem2608114 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2608115 : term160 = term259.
Proof. exact (@lem2608114 (NUMERAL 0)). Qed.
Lemma lem2608116 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2608117 : term323 = term324.
Proof. exact (MK_COMB (@lem2608116) (@lem2608115)). Qed.
Lemma lem2608118 : term322 = term325.
Proof. exact (MK_COMB (@lem2608117) (@lem2608112)). Qed.
Lemma lem2608119 : term326.
Proof. exact (@lem1980026 term160 term63 term127 term63). Qed.
Lemma lem2608121 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2608122 : term258 = term265.
Proof. exact (@lem2608121 (NUMERAL 0) term64). Qed.
Lemma lem2608123 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2608124 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2608125 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2608124 h1) (fun h1 : term265 = True => @lem2608123)). Qed.
Lemma lem2608126 : term265 = True.
Proof. exact (EQ_MP (@lem2608125) (@lem2608123)). Qed.
Lemma lem2608127 : term258 = True.
Proof. exact (TRANS (@lem2608122) (@lem2608126)). Qed.
Lemma lem2608128 : True = term258.
Proof. exact (SYM (@lem2608127)). Qed.
Lemma lem2608129 : term258.
Proof. exact (EQ_MP (@lem2608128) (@lem0)). Qed.
Lemma lem2608130 : term327.
Proof. exact (@lem2608119 (@lem2608129)). Qed.
Lemma lem2608132 (m : nat) (n : nat) : (term264 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2608133 : term258 = term265.
Proof. exact (@lem2608132 (NUMERAL 0) term64). Qed.
Lemma lem2608134 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2608135 (h1 : term266 = (BIT1 0)) : term265 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2608136 : (term266 = (BIT1 0)) = (term265 = True).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2608135 h1) (fun h1 : term265 = True => @lem2608134)). Qed.
Lemma lem2608137 : term265 = True.
Proof. exact (EQ_MP (@lem2608136) (@lem2608134)). Qed.
Lemma lem2608138 : term258 = True.
Proof. exact (TRANS (@lem2608133) (@lem2608137)). Qed.
Lemma lem2608139 : True = term258.
Proof. exact (SYM (@lem2608138)). Qed.
Lemma lem2608140 : term258.
Proof. exact (EQ_MP (@lem2608139) (@lem0)). Qed.
Lemma lem2608141 : term325 = term328.
Proof. exact (@lem2608130 (@lem2608140)). Qed.
Lemma lem2608143 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2608144 : term172 = term177.
Proof. exact (@lem2608143 term64 term64). Qed.
Lemma lem2608145 : (term146 = (BIT1 0)) = (term147 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2608146 : term147 = term64.
Proof. exact (EQ_MP (@lem2608145) (@lem940073)). Qed.
Lemma lem2608147 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2608148 : term145 = term63.
Proof. exact (MK_COMB (@lem2608147) (@lem2608146)). Qed.
Lemma lem2608149 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2608150 : term177 = term127.
Proof. exact (MK_COMB (@lem2608149) (@lem2608148)). Qed.
Lemma lem2608151 : term172 = term127.
Proof. exact (TRANS (@lem2608144) (@lem2608150)). Qed.
Lemma lem2608153 (x : nat) : (term269 x) = term160.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2608154 : term270 = term160.
Proof. exact (@lem2608153 term64). Qed.
Lemma lem2608155 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2608156 : term329 = term323.
Proof. exact (MK_COMB (@lem2608155) (@lem2608154)). Qed.
Lemma lem2608157 : term328 = term322.
Proof. exact (MK_COMB (@lem2608156) (@lem2608151)). Qed.
Lemma lem2608159 (m : nat) (n : nat) : (term330 m n) = (term331 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2608160 : term322 = term332.
Proof. exact (@lem2608159 (NUMERAL 0) term64). Qed.
Lemma lem2608161 : term266 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2608162 (h1 : term266 = (BIT1 0)) : (term64 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2608163 : (term266 = (BIT1 0)) = ((term64 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term266 = (BIT1 0) => @lem2608162 h1) (fun h1 : (term64 = (NUMERAL 0)) = False => @lem2608161)). Qed.
Lemma lem2608164 : (term64 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2608163) (@lem2608161)). Qed.
Lemma lem2608165 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2608166 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2608167 : term333 = (and True).
Proof. exact (MK_COMB (@lem2608166) (@lem2608165)). Qed.
Lemma lem2608168 : term332 = (True /\ False).
Proof. exact (MK_COMB (@lem2608167) (@lem2608164)). Qed.
Lemma lem2608170 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2608171 : term332 = False.
Proof. exact (TRANS (@lem2608168) (@lem2608170)). Qed.
Lemma lem2608172 : term322 = False.
Proof. exact (TRANS (@lem2608160) (@lem2608171)). Qed.
Lemma lem2608173 : term328 = False.
Proof. exact (TRANS (@lem2608157) (@lem2608172)). Qed.
Lemma lem2608174 : term325 = False.
Proof. exact (TRANS (@lem2608141) (@lem2608173)). Qed.
Lemma lem2608175 : term322 = False.
Proof. exact (TRANS (@lem2608118) (@lem2608174)). Qed.
Lemma lem2608176 : term321 = False.
Proof. exact (TRANS (@lem2608109) (@lem2608175)). Qed.
Lemma lem2608177 (n : nat) (h1 : term671 n) : False.
Proof. exact (EQ_MP (@lem2608176) (@lem2608106 n h1)). Qed.
Lemma lem2608179 (n : nat) (h1 : term671 n) : term671 n.
Proof. exact (h1). Qed.
Lemma lem2608180 (n : nat) (h1 : term671 n) : (term671 n) = False.
Proof. exact (prop_ext (fun h2 : term671 n => @lem2608177 n h1) (fun h2 : False => @lem2608179 n h1)). Qed.
Lemma lem2608181 (n : nat) (h1 : term671 n) : False.
Proof. exact (EQ_MP (@lem2608180 n h1) (@lem2608179 n h1)). Qed.
Lemma lem2608182 (n : nat) (h1 : term742 n) : term742 n.
Proof. exact (h1). Qed.
Lemma lem2608183 (n : nat) (h1 : term742 n) : term671 n.
Proof. exact (EQ_MP (@lem2607829 n) (@lem2608182 n h1)). Qed.
Lemma lem2608184 (n : nat) (h1 : term742 n) : (term671 n) = False.
Proof. exact (prop_ext (fun h2 : term671 n => @lem2608181 n h2) (fun h2 : False => @lem2608183 n h1)). Qed.
Lemma lem2608185 (n : nat) (h1 : term742 n) : False.
Proof. exact (EQ_MP (@lem2608184 n h1) (@lem2608183 n h1)). Qed.
Lemma lem2608186 (n : nat) : term747 n.
Proof. exact (fun h0 : term742 n => @lem2608185 n h0). Qed.
Lemma lem2608187 (n : nat) : term748 n.
Proof. exact (@lem1386578 (term749 n)). Qed.
Lemma lem2608190 (n : nat) : term749 n.
Proof. exact (@lem2608187 n (@lem2608186 n)). Qed.
Lemma lem2608191 (n : nat) : (term741 n) = (term730 n).
Proof. exact (SYM (@lem2607743 n)). Qed.
Lemma lem2608192 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2608193 (n : nat) : (term749 n) = (term728 n).
Proof. exact (MK_COMB (@lem2608192) (@lem2608191 n)). Qed.
Lemma lem2608194 (n : nat) : term728 n.
Proof. exact (EQ_MP (@lem2608193 n) (@lem2608190 n)). Qed.
Lemma lem2608195 (n : nat) : term729 n.
Proof. exact (EQ_MP (@lem2607699 n) (@lem2608194 n)). Qed.
Lemma lem2608196 (n : nat) : term750 n.
Proof. exact (@lem82 (term731 n)). Qed.
Lemma lem2608198 (P : int -> Prop) : term698 P.
Proof. exact (@lem2296993 P). Qed.
Lemma lem2608199 (P : int -> Prop) : (term698 P) = ((term699 P) = (term700 P)).
Proof. exact (eq_refl (term698 P)). Qed.
Lemma lem2608202 (P : int -> Prop) : (term699 P) = (term700 P).
Proof. exact (EQ_MP (@lem2608199 P) (@lem2608198 P)). Qed.
Lemma lem2608203 : term751 = term752.
Proof. exact (@lem2608202 term753). Qed.
Lemma lem2608204 (a : int) : (term754 a) = (term755 a).
Proof. exact (eq_refl (term754 a)). Qed.
Lemma lem2608205 : term756 = term753.
Proof. exact (fun_ext (fun a : int => @lem2608204 a)). Qed.
Lemma lem2608206 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2608207 : term751 = term757.
Proof. exact (MK_COMB (@lem2608206) (@lem2608205)). Qed.
Lemma lem2608208 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2608209 : term758 = term759.
Proof. exact (MK_COMB (@lem2608208) (@lem2608207)). Qed.
Lemma lem2608210 (n : nat) : (term760 n) = (term761 n).
Proof. exact (eq_refl (term760 n)). Qed.
Lemma lem2608211 : term762 = term763.
Proof. exact (fun_ext (fun n : nat => @lem2608210 n)). Qed.
Lemma lem2608212 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2608213 : term764 = term765.
Proof. exact (MK_COMB (@lem2608212) (@lem2608211)). Qed.
Lemma lem2608214 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2608215 : term766 = term767.
Proof. exact (MK_COMB (@lem2608214) (@lem2608213)). Qed.
Lemma lem2608216 (n : nat) : (term768 n) = (term769 n).
Proof. exact (eq_refl (term768 n)). Qed.
Lemma lem2608217 : term770 = term771.
Proof. exact (fun_ext (fun n : nat => @lem2608216 n)). Qed.
Lemma lem2608218 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2608219 : term772 = term773.
Proof. exact (MK_COMB (@lem2608218) (@lem2608217)). Qed.
Lemma lem2608220 : term752 = term774.
Proof. exact (MK_COMB (@lem2608215) (@lem2608219)). Qed.
Lemma lem2608221 : (term751 = term752) = (term757 = term774).
Proof. exact (MK_COMB (@lem2608209) (@lem2608220)). Qed.
Lemma lem2608222 : term757 = term774.
Proof. exact (EQ_MP (@lem2608221) (@lem2608203)). Qed.
Lemma lem2608223 : term774 = term757.
Proof. exact (SYM (@lem2608222)). Qed.
Lemma lem2608257 (n : nat) : (term731 n) = False.
Proof. exact (@lem2608196 n (@lem2608195 n)). Qed.
Lemma lem2608258 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2608259 (n : nat) : (term775 n) = (imp False).
Proof. exact (MK_COMB (@lem2608258) (@lem2608257 n)). Qed.
Lemma lem2608262 (b : int) (n : nat) (c : int) : ((term776 b n c) = (term777 b n c)) = ((term776 b n c) = (term777 b n c)).
Proof. exact (eq_refl ((term776 b n c) = (term777 b n c))). Qed.
Lemma lem2608263 (b : int) (n : nat) (c : int) : (term778 b n c) = (term779 b n c).
Proof. exact (MK_COMB (@lem2608259 n) (@lem2608262 b n c)). Qed.
Lemma lem2608265 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem2608266 (b : int) (n : nat) (c : int) : (term779 b n c) = True.
Proof. exact (@lem2608265 ((term776 b n c) = (term777 b n c))). Qed.
Lemma lem2608267 (b : int) (n : nat) (c : int) : (term778 b n c) = True.
Proof. exact (TRANS (@lem2608263 b n c) (@lem2608266 b n c)). Qed.
Lemma lem2608268 (b : int) (n : nat) : (term780 b n) = term781.
Proof. exact (fun_ext (fun c : int => @lem2608267 b n c)). Qed.
Lemma lem2608269 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2608270 (b : int) (n : nat) : (term782 b n) = term783.
Proof. exact (MK_COMB (@lem2608269) (@lem2608268 b n)). Qed.
Lemma lem2608272 {A : Type'} (t : Prop) : (term784 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2608273 (t : Prop) : (term785 t) = t.
Proof. exact (@lem2608272 int t). Qed.
Lemma lem2608274 : term783 = True.
Proof. exact (@lem2608273 True). Qed.
Lemma lem2608275 (b : int) (n : nat) : (term782 b n) = True.
Proof. exact (TRANS (@lem2608270 b n) (@lem2608274)). Qed.
Lemma lem2608276 (n : nat) : (term786 n) = term781.
Proof. exact (fun_ext (fun b : int => @lem2608275 b n)). Qed.
Lemma lem2608277 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2608278 (n : nat) : (term769 n) = term783.
Proof. exact (MK_COMB (@lem2608277) (@lem2608276 n)). Qed.
Lemma lem2608280 {A : Type'} (t : Prop) : (term784 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2608281 (t : Prop) : (term785 t) = t.
Proof. exact (@lem2608280 int t). Qed.
Lemma lem2608282 : term783 = True.
Proof. exact (@lem2608281 True). Qed.
Lemma lem2608283 (n : nat) : (term769 n) = True.
Proof. exact (TRANS (@lem2608278 n) (@lem2608282)). Qed.
Lemma lem2608284 : term771 = term787.
Proof. exact (fun_ext (fun n : nat => @lem2608283 n)). Qed.
Lemma lem2608285 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2608286 : term773 = term788.
Proof. exact (MK_COMB (@lem2608285) (@lem2608284)). Qed.
Lemma lem2608288 {A : Type'} (t : Prop) : (term784 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2608289 (t : Prop) : (term789 t) = t.
Proof. exact (@lem2608288 nat t). Qed.
Lemma lem2608290 : term788 = True.
Proof. exact (@lem2608289 True). Qed.
Lemma lem2608291 : term773 = True.
Proof. exact (TRANS (@lem2608286) (@lem2608290)). Qed.
Lemma lem2608292 : term767 = term767.
Proof. exact (eq_refl term767). Qed.
Lemma lem2608293 : term774 = term790.
Proof. exact (MK_COMB (@lem2608292) (@lem2608291)). Qed.
Lemma lem2608295 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem2608296 : term790 = term765.
Proof. exact (@lem2608295 term765). Qed.
Lemma lem2608313 : term774 = term765.
Proof. exact (TRANS (@lem2608293) (@lem2608296)). Qed.
Lemma lem2608314 : term765 = term774.
Proof. exact (SYM (@lem2608313)). Qed.
Lemma lem2608320 {A : Type'} (P : Prop) (Q : A -> Prop) : (term726 A P Q) = (term727 A P Q).
Proof. exact (EQ_MP (@lem2607697 A P Q) (@lem2607696 A P Q)). Qed.
Lemma lem2608321 (P : Prop) (Q : int -> Prop) : (term791 P Q) = (term792 P Q).
Proof. exact (@lem2608320 int P Q). Qed.
Lemma lem2608322 (b : int) (n : nat) : (term793 b n) = (term794 b n).
Proof. exact (@lem2608321 (term795 n) (term796 b n)). Qed.
Lemma lem2608323 (b : int) (n : nat) (c : int) : (term797 b n c) = ((term798 b n c) = (term799 b n c)).
Proof. exact (eq_refl (term797 b n c)). Qed.
Lemma lem2608324 (n : nat) : (term800 n) = (term800 n).
Proof. exact (eq_refl (term800 n)). Qed.
Lemma lem2608325 (b : int) (n : nat) (c : int) : (term801 b n c) = (term802 b n c).
Proof. exact (MK_COMB (@lem2608324 n) (@lem2608323 b n c)). Qed.
Lemma lem2608326 (b : int) (n : nat) : (term803 b n) = (term804 b n).
Proof. exact (fun_ext (fun c : int => @lem2608325 b n c)). Qed.
Lemma lem2608327 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2608328 (b : int) (n : nat) : (term793 b n) = (term805 b n).
Proof. exact (MK_COMB (@lem2608327) (@lem2608326 b n)). Qed.
Lemma lem2608329 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2608330 (b : int) (n : nat) : (term806 b n) = (term807 b n).
Proof. exact (MK_COMB (@lem2608329) (@lem2608328 b n)). Qed.
Lemma lem2608331 (b : int) (n : nat) (c : int) : (term797 b n c) = ((term798 b n c) = (term799 b n c)).
Proof. exact (eq_refl (term797 b n c)). Qed.
Lemma lem2608332 (b : int) (n : nat) : (term808 b n) = (term796 b n).
Proof. exact (fun_ext (fun c : int => @lem2608331 b n c)). Qed.
Lemma lem2608333 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2608334 (b : int) (n : nat) : (term809 b n) = (term810 b n).
Proof. exact (MK_COMB (@lem2608333) (@lem2608332 b n)). Qed.
Lemma lem2608335 (n : nat) : (term800 n) = (term800 n).
Proof. exact (eq_refl (term800 n)). Qed.
Lemma lem2608336 (b : int) (n : nat) : (term794 b n) = (term811 b n).
Proof. exact (MK_COMB (@lem2608335 n) (@lem2608334 b n)). Qed.
Lemma lem2608337 (b : int) (n : nat) : ((term793 b n) = (term794 b n)) = ((term805 b n) = (term811 b n)).
Proof. exact (MK_COMB (@lem2608330 b n) (@lem2608336 b n)). Qed.
Lemma lem2608338 (b : int) (n : nat) : (term805 b n) = (term811 b n).
Proof. exact (EQ_MP (@lem2608337 b n) (@lem2608322 b n)). Qed.
Lemma lem2608342 (m : nat) (n : nat) : (term688 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem2607691 m n) (@lem2607690 m n)). Qed.
Lemma lem2608343 (n : nat) : (term795 n) = (term812 n).
Proof. exact (@lem2608342 (NUMERAL 0) n). Qed.
Lemma lem2608344 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2608345 (n : nat) : (term800 n) = (term813 n).
Proof. exact (MK_COMB (@lem2608344) (@lem2608343 n)). Qed.
Lemma lem2608352 (b : int) (n : nat) : (term810 b n) = (term810 b n).
Proof. exact (eq_refl (term810 b n)). Qed.
Lemma lem2608353 (b : int) (n : nat) : (term811 b n) = (term814 b n).
Proof. exact (MK_COMB (@lem2608345 n) (@lem2608352 b n)). Qed.
Lemma lem2608356 (b : int) (n : nat) : (term805 b n) = (term814 b n).
Proof. exact (TRANS (@lem2608338 b n) (@lem2608353 b n)). Qed.
Lemma lem2608357 (n : nat) : (term815 n) = (term816 n).
Proof. exact (fun_ext (fun b : int => @lem2608356 b n)). Qed.
Lemma lem2608358 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2608359 (n : nat) : (term761 n) = (term817 n).
Proof. exact (MK_COMB (@lem2608358) (@lem2608357 n)). Qed.
Lemma lem2608361 {A : Type'} (P : Prop) (Q : A -> Prop) : (term726 A P Q) = (term727 A P Q).
Proof. exact (EQ_MP (@lem2607697 A P Q) (@lem2607696 A P Q)). Qed.
Lemma lem2608362 (P : Prop) (Q : int -> Prop) : (term791 P Q) = (term792 P Q).
Proof. exact (@lem2608361 int P Q). Qed.
Lemma lem2608363 (n : nat) : (term818 n) = (term819 n).
Proof. exact (@lem2608362 (term812 n) (term820 n)). Qed.
Lemma lem2608364 (b : int) (n : nat) : (term821 n b) = (term810 b n).
Proof. exact (eq_refl (term821 n b)). Qed.
Lemma lem2608365 (n : nat) : (term813 n) = (term813 n).
Proof. exact (eq_refl (term813 n)). Qed.
Lemma lem2608366 (b : int) (n : nat) : (term822 n b) = (term814 b n).
Proof. exact (MK_COMB (@lem2608365 n) (@lem2608364 b n)). Qed.
Lemma lem2608367 (n : nat) : (term823 n) = (term816 n).
Proof. exact (fun_ext (fun b : int => @lem2608366 b n)). Qed.
Lemma lem2608368 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2608369 (n : nat) : (term818 n) = (term817 n).
Proof. exact (MK_COMB (@lem2608368) (@lem2608367 n)). Qed.
Lemma lem2608370 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2608371 (n : nat) : (term824 n) = (term825 n).
Proof. exact (MK_COMB (@lem2608370) (@lem2608369 n)). Qed.
Lemma lem2608372 (b : int) (n : nat) : (term821 n b) = (term810 b n).
Proof. exact (eq_refl (term821 n b)). Qed.
Lemma lem2608373 (n : nat) : (term826 n) = (term820 n).
Proof. exact (fun_ext (fun b : int => @lem2608372 b n)). Qed.
Lemma lem2608374 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2608375 (n : nat) : (term827 n) = (term828 n).
Proof. exact (MK_COMB (@lem2608374) (@lem2608373 n)). Qed.
Lemma lem2608376 (n : nat) : (term813 n) = (term813 n).
Proof. exact (eq_refl (term813 n)). Qed.
Lemma lem2608377 (n : nat) : (term819 n) = (term829 n).
Proof. exact (MK_COMB (@lem2608376 n) (@lem2608375 n)). Qed.
Lemma lem2608378 (n : nat) : ((term818 n) = (term819 n)) = ((term817 n) = (term829 n)).
Proof. exact (MK_COMB (@lem2608371 n) (@lem2608377 n)). Qed.
Lemma lem2608379 (n : nat) : (term817 n) = (term829 n).
Proof. exact (EQ_MP (@lem2608378 n) (@lem2608363 n)). Qed.
Lemma lem2608392 (n : nat) : (term761 n) = (term829 n).
Proof. exact (TRANS (@lem2608359 n) (@lem2608379 n)). Qed.
Lemma lem2608393 (n : nat) : (term829 n) = (term761 n).
Proof. exact (SYM (@lem2608392 n)). Qed.
Lemma lem2608394 (n : nat) (h1 : term812 n) : term812 n.
Proof. exact (h1). Qed.
Lemma lem2608396 (P : int -> Prop) : (term699 P) = (term700 P).
Proof. exact (EQ_MP (@lem2607685 P) (@lem2607684 P)). Qed.
Lemma lem2608397 (n : nat) : (term827 n) = (term830 n).
Proof. exact (@lem2608396 (term820 n)). Qed.
Lemma lem2608398 (b : int) (n : nat) : (term821 n b) = (term810 b n).
Proof. exact (eq_refl (term821 n b)). Qed.
Lemma lem2608399 (n : nat) : (term826 n) = (term820 n).
Proof. exact (fun_ext (fun b : int => @lem2608398 b n)). Qed.
Lemma lem2608400 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2608401 (n : nat) : (term827 n) = (term828 n).
Proof. exact (MK_COMB (@lem2608400) (@lem2608399 n)). Qed.
Lemma lem2608402 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2608403 (n : nat) : (term831 n) = (term832 n).
Proof. exact (MK_COMB (@lem2608402) (@lem2608401 n)). Qed.
Lemma lem2608404 (n' : nat) (n : nat) : (term833 n n') = (term834 n' n).
Proof. exact (eq_refl (term833 n n')). Qed.
Lemma lem2608405 (n : nat) : (term835 n) = (term836 n).
Proof. exact (fun_ext (fun n' : nat => @lem2608404 n' n)). Qed.
Lemma lem2608406 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2608407 (n : nat) : (term837 n) = (term838 n).
Proof. exact (MK_COMB (@lem2608406) (@lem2608405 n)). Qed.
Lemma lem2608408 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2608409 (n : nat) : (term839 n) = (term840 n).
Proof. exact (MK_COMB (@lem2608408) (@lem2608407 n)). Qed.
Lemma lem2608410 (n' : nat) (n : nat) : (term841 n n') = (term842 n' n).
Proof. exact (eq_refl (term841 n n')). Qed.
Lemma lem2608411 (n : nat) : (term843 n) = (term844 n).
Proof. exact (fun_ext (fun n' : nat => @lem2608410 n' n)). Qed.
Lemma lem2608412 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2608413 (n : nat) : (term845 n) = (term846 n).
Proof. exact (MK_COMB (@lem2608412) (@lem2608411 n)). Qed.
Lemma lem2608414 (n : nat) : (term830 n) = (term847 n).
Proof. exact (MK_COMB (@lem2608409 n) (@lem2608413 n)). Qed.
Lemma lem2608415 (n : nat) : ((term827 n) = (term830 n)) = ((term828 n) = (term847 n)).
Proof. exact (MK_COMB (@lem2608403 n) (@lem2608414 n)). Qed.
Lemma lem2608416 (n : nat) : (term828 n) = (term847 n).
Proof. exact (EQ_MP (@lem2608415 n) (@lem2608397 n)). Qed.
Lemma lem2608417 (n : nat) : (term847 n) = (term828 n).
Proof. exact (SYM (@lem2608416 n)). Qed.
Lemma lem2608419 (p : Prop) (q : Prop) : term712 p q.
Proof. exact (@lem2607682 p q (@lem2607674 p q)). Qed.
Lemma lem2608420 (n : nat) : term848 n.
Proof. exact (@lem2608419 (term838 n) (term846 n)). Qed.
Lemma lem2608432 (P : int -> Prop) : (term699 P) = (term700 P).
Proof. exact (EQ_MP (@lem2607573 P) (@lem2607572 P)). Qed.
Lemma lem2608433 (n' : nat) (n : nat) : (term849 n' n) = (term850 n' n).
Proof. exact (@lem2608432 (term851 n' n)). Qed.
Lemma lem2608434 (n' : nat) (n : nat) (c : int) : (term852 n' n c) = ((term853 n' n c) = (term854 n' n c)).
Proof. exact (eq_refl (term852 n' n c)). Qed.
Lemma lem2608435 (n' : nat) (n : nat) : (term855 n' n) = (term851 n' n).
Proof. exact (fun_ext (fun c : int => @lem2608434 n' n c)). Qed.
Lemma lem2608436 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2608437 (n' : nat) (n : nat) : (term849 n' n) = (term834 n' n).
Proof. exact (MK_COMB (@lem2608436) (@lem2608435 n' n)). Qed.
Lemma lem2608438 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2608439 (n' : nat) (n : nat) : (term856 n' n) = (term857 n' n).
Proof. exact (MK_COMB (@lem2608438) (@lem2608437 n' n)). Qed.
Lemma lem2608440 (n' : nat) (n : nat) (n'' : nat) : (term858 n' n n'') = ((term859 n' n n'') = (term860 n' n n'')).
Proof. exact (eq_refl (term858 n' n n'')). Qed.
Lemma lem2608441 (n' : nat) (n : nat) : (term861 n' n) = (term862 n' n).
Proof. exact (fun_ext (fun n'' : nat => @lem2608440 n' n n'')). Qed.
Lemma lem2608442 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2608443 (n' : nat) (n : nat) : (term863 n' n) = (term864 n' n).
Proof. exact (MK_COMB (@lem2608442) (@lem2608441 n' n)). Qed.
Lemma lem2608444 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2608445 (n' : nat) (n : nat) : (term865 n' n) = (term866 n' n).
Proof. exact (MK_COMB (@lem2608444) (@lem2608443 n' n)). Qed.
Lemma lem2608446 (n' : nat) (n : nat) (n'' : nat) : (term867 n' n n'') = ((term868 n' n n'') = (term869 n' n n'')).
Proof. exact (eq_refl (term867 n' n n'')). Qed.
Lemma lem2608447 (n' : nat) (n : nat) : (term870 n' n) = (term871 n' n).
Proof. exact (fun_ext (fun n'' : nat => @lem2608446 n' n n'')). Qed.
Lemma lem2608448 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2608449 (n' : nat) (n : nat) : (term872 n' n) = (term873 n' n).
Proof. exact (MK_COMB (@lem2608448) (@lem2608447 n' n)). Qed.
Lemma lem2608450 (n' : nat) (n : nat) : (term850 n' n) = (term874 n' n).
Proof. exact (MK_COMB (@lem2608445 n' n) (@lem2608449 n' n)). Qed.
Lemma lem2608451 (n' : nat) (n : nat) : ((term849 n' n) = (term850 n' n)) = ((term834 n' n) = (term874 n' n)).
Proof. exact (MK_COMB (@lem2608439 n' n) (@lem2608450 n' n)). Qed.
Lemma lem2608452 (n' : nat) (n : nat) : (term834 n' n) = (term874 n' n).
Proof. exact (EQ_MP (@lem2608451 n' n) (@lem2608433 n' n)). Qed.
Lemma lem2608464 (m : nat) (n : nat) : (term598 m n) = (term704 m n).
Proof. exact (EQ_MP (@lem2607579 m n) (@lem2607578 m n)). Qed.
Lemma lem2608465 (n' : nat) (n : nat) : (term598 n' n) = (term704 n' n).
Proof. exact (@lem2608464 n' n). Qed.
Lemma lem2608466 : int_lt = int_lt.
Proof. exact (eq_refl int_lt). Qed.
Lemma lem2608467 (n' : nat) (n : nat) : (term875 n' n) = (term876 n' n).
Proof. exact (MK_COMB (@lem2608466) (@lem2608465 n' n)). Qed.
Lemma lem2608468 (n'' : nat) : (int_of_num n'') = (int_of_num n'').
Proof. exact (eq_refl (int_of_num n'')). Qed.
Lemma lem2608469 (n' : nat) (n : nat) (n'' : nat) : (term859 n' n n'') = (term877 n' n n'').
Proof. exact (MK_COMB (@lem2608467 n' n) (@lem2608468 n'')). Qed.
Lemma lem2608470 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2608471 (n' : nat) (n : nat) (n'' : nat) : (term878 n' n n'') = (term879 n' n n'').
Proof. exact (MK_COMB (@lem2608470) (@lem2608469 n' n n'')). Qed.
Lemma lem2608472 (n' : nat) (n : nat) (n'' : nat) : (term860 n' n n'') = (term860 n' n n'').
Proof. exact (eq_refl (term860 n' n n'')). Qed.
Lemma lem2608473 (n' : nat) (n : nat) (n'' : nat) : ((term859 n' n n'') = (term860 n' n n'')) = ((term877 n' n n'') = (term860 n' n n'')).
Proof. exact (MK_COMB (@lem2608471 n' n n'') (@lem2608472 n' n n'')). Qed.
Lemma lem2608476 (n' : nat) (n : nat) : (term862 n' n) = (term880 n' n).
Proof. exact (fun_ext (fun n'' : nat => @lem2608473 n' n n'')). Qed.
Lemma lem2608477 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2608478 (n' : nat) (n : nat) : (term864 n' n) = (term881 n' n).
Proof. exact (MK_COMB (@lem2608477) (@lem2608476 n' n)). Qed.
Lemma lem2608485 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2608486 (n' : nat) (n : nat) : (term866 n' n) = (term882 n' n).
Proof. exact (MK_COMB (@lem2608485) (@lem2608478 n' n)). Qed.
Lemma lem2608496 (m : nat) (n : nat) : (term598 m n) = (term704 m n).
Proof. exact (EQ_MP (@lem2607579 m n) (@lem2607578 m n)). Qed.
Lemma lem2608497 (n' : nat) (n : nat) : (term598 n' n) = (term704 n' n).
Proof. exact (@lem2608496 n' n). Qed.
Lemma lem2608498 : int_lt = int_lt.
Proof. exact (eq_refl int_lt). Qed.
Lemma lem2608499 (n' : nat) (n : nat) : (term875 n' n) = (term876 n' n).
Proof. exact (MK_COMB (@lem2608498) (@lem2608497 n' n)). Qed.
Lemma lem2608500 (n'' : nat) : (term618 n'') = (term618 n'').
Proof. exact (eq_refl (term618 n'')). Qed.
Lemma lem2608501 (n' : nat) (n : nat) (n'' : nat) : (term868 n' n n'') = (term883 n' n n'').
Proof. exact (MK_COMB (@lem2608499 n' n) (@lem2608500 n'')). Qed.
Lemma lem2608502 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2608503 (n' : nat) (n : nat) (n'' : nat) : (term884 n' n n'') = (term885 n' n n'').
Proof. exact (MK_COMB (@lem2608502) (@lem2608501 n' n n'')). Qed.
Lemma lem2608504 (n' : nat) (n : nat) (n'' : nat) : (term869 n' n n'') = (term869 n' n n'').
Proof. exact (eq_refl (term869 n' n n'')). Qed.
Lemma lem2608505 (n' : nat) (n : nat) (n'' : nat) : ((term868 n' n n'') = (term869 n' n n'')) = ((term883 n' n n'') = (term869 n' n n'')).
Proof. exact (MK_COMB (@lem2608503 n' n n'') (@lem2608504 n' n n'')). Qed.
Lemma lem2608508 (n' : nat) (n : nat) : (term871 n' n) = (term886 n' n).
Proof. exact (fun_ext (fun n'' : nat => @lem2608505 n' n n'')). Qed.
Lemma lem2608509 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2608510 (n' : nat) (n : nat) : (term873 n' n) = (term887 n' n).
Proof. exact (MK_COMB (@lem2608509) (@lem2608508 n' n)). Qed.
Lemma lem2608517 (n' : nat) (n : nat) : (term874 n' n) = (term888 n' n).
Proof. exact (MK_COMB (@lem2608486 n' n) (@lem2608510 n' n)). Qed.
Lemma lem2608520 (n' : nat) (n : nat) : (term834 n' n) = (term888 n' n).
Proof. exact (TRANS (@lem2608452 n' n) (@lem2608517 n' n)). Qed.
Lemma lem2608521 (n : nat) : (term836 n) = (term889 n).
Proof. exact (fun_ext (fun n' : nat => @lem2608520 n' n)). Qed.
Lemma lem2608522 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2608523 (n : nat) : (term838 n) = (term890 n).
Proof. exact (MK_COMB (@lem2608522) (@lem2608521 n)). Qed.
Lemma lem2608530 (n : nat) : (term890 n) = (term838 n).
Proof. exact (SYM (@lem2608523 n)). Qed.
Lemma lem2608544 (m : nat) (n : nat) : (term692 m n) = (term693 m n).
Proof. exact (EQ_MP (@lem2607564 m n) (@lem2607563 m n)). Qed.
Lemma lem2608545 (n : nat) (n'' : nat) : (term692 n n'') = (term693 n n'').
Proof. exact (@lem2608544 n n''). Qed.
Lemma lem2608546 (n' : nat) : (term891 n') = (term891 n').
Proof. exact (eq_refl (term891 n')). Qed.
Lemma lem2608547 (n' : nat) (n : nat) (n'' : nat) : (term860 n' n n'') = (term892 n' n n'').
Proof. exact (MK_COMB (@lem2608546 n') (@lem2608545 n n'')). Qed.
Lemma lem2608548 (n' : nat) (n : nat) (n'' : nat) : (term879 n' n n'') = (term879 n' n n'').
Proof. exact (eq_refl (term879 n' n n'')). Qed.
Lemma lem2608549 (n' : nat) (n : nat) (n'' : nat) : ((term877 n' n n'') = (term860 n' n n'')) = ((term877 n' n n'') = (term892 n' n n'')).
Proof. exact (MK_COMB (@lem2608548 n' n n'') (@lem2608547 n' n n'')). Qed.
Lemma lem2608552 (n' : nat) (n : nat) : (term880 n' n) = (term893 n' n).
Proof. exact (fun_ext (fun n'' : nat => @lem2608549 n' n n'')). Qed.
Lemma lem2608553 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2608554 (n' : nat) (n : nat) : (term881 n' n) = (term894 n' n).
Proof. exact (MK_COMB (@lem2608553) (@lem2608552 n' n)). Qed.
Lemma lem2608559 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2608560 (n' : nat) (n : nat) : (term882 n' n) = (term895 n' n).
Proof. exact (MK_COMB (@lem2608559) (@lem2608554 n' n)). Qed.
Lemma lem2608568 (x : int) (y : int) : (term21 x y) = (term697 x y).
Proof. exact (EQ_MP (@lem2607570 x y) (@lem2607569 x y)). Qed.
Lemma lem2608569 (n : nat) (n'' : nat) : (term896 n n'') = (term897 n n'').
Proof. exact (@lem2608568 (int_of_num n) (int_of_num n'')). Qed.
Lemma lem2608571 (m : nat) (n : nat) : (term692 m n) = (term693 m n).
Proof. exact (EQ_MP (@lem2607564 m n) (@lem2607563 m n)). Qed.
Lemma lem2608572 (n : nat) (n'' : nat) : (term692 n n'') = (term693 n n'').
Proof. exact (@lem2608571 n n''). Qed.
Lemma lem2608573 : int_neg = int_neg.
Proof. exact (eq_refl int_neg). Qed.
Lemma lem2608574 (n : nat) (n'' : nat) : (term897 n n'') = (term898 n n'').
Proof. exact (MK_COMB (@lem2608573) (@lem2608572 n n'')). Qed.
Lemma lem2608575 (n : nat) (n'' : nat) : (term896 n n'') = (term898 n n'').
Proof. exact (TRANS (@lem2608569 n n'') (@lem2608574 n n'')). Qed.
Lemma lem2608576 (n' : nat) : (term891 n') = (term891 n').
Proof. exact (eq_refl (term891 n')). Qed.
Lemma lem2608577 (n' : nat) (n : nat) (n'' : nat) : (term869 n' n n'') = (term899 n' n n'').
Proof. exact (MK_COMB (@lem2608576 n') (@lem2608575 n n'')). Qed.
Lemma lem2608578 (n' : nat) (n : nat) (n'' : nat) : (term885 n' n n'') = (term885 n' n n'').
Proof. exact (eq_refl (term885 n' n n'')). Qed.
Lemma lem2608579 (n' : nat) (n : nat) (n'' : nat) : ((term883 n' n n'') = (term869 n' n n'')) = ((term883 n' n n'') = (term899 n' n n'')).
Proof. exact (MK_COMB (@lem2608578 n' n n'') (@lem2608577 n' n n'')). Qed.
Lemma lem2608582 (n' : nat) (n : nat) : (term886 n' n) = (term900 n' n).
Proof. exact (fun_ext (fun n'' : nat => @lem2608579 n' n n'')). Qed.
Lemma lem2608583 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2608584 (n' : nat) (n : nat) : (term887 n' n) = (term901 n' n).
Proof. exact (MK_COMB (@lem2608583) (@lem2608582 n' n)). Qed.
Lemma lem2608589 (n' : nat) (n : nat) : (term888 n' n) = (term902 n' n).
Proof. exact (MK_COMB (@lem2608560 n' n) (@lem2608584 n' n)). Qed.
Lemma lem2608592 (n : nat) : (term889 n) = (term903 n).
Proof. exact (fun_ext (fun n' : nat => @lem2608589 n' n)). Qed.
Lemma lem2608593 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2608594 (n : nat) : (term890 n) = (term904 n).
Proof. exact (MK_COMB (@lem2608593) (@lem2608592 n)). Qed.
Lemma lem2608599 (n : nat) : (term904 n) = (term890 n).
Proof. exact (SYM (@lem2608594 n)). Qed.
Lemma lem2608613 (m : nat) (n : nat) : (term688 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem2607558 m n) (@lem2607557 m n)). Qed.
Lemma lem2608614 (n' : nat) (n : nat) (n'' : nat) : (term877 n' n n'') = (term905 n' n n'').
Proof. exact (@lem2608613 (Nat.div n' n) n''). Qed.
Lemma lem2608615 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2608616 (n' : nat) (n : nat) (n'' : nat) : (term879 n' n n'') = (term906 n' n n'').
Proof. exact (MK_COMB (@lem2608615) (@lem2608614 n' n n'')). Qed.
Lemma lem2608618 (m : nat) (n : nat) : (term688 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem2607558 m n) (@lem2607557 m n)). Qed.
Lemma lem2608619 (n' : nat) (n : nat) (n'' : nat) : (term892 n' n n'') = (term907 n' n n'').
Proof. exact (@lem2608618 n' (Nat.mul n n'')). Qed.
Lemma lem2608620 (n' : nat) (n : nat) (n'' : nat) : ((term877 n' n n'') = (term892 n' n n'')) = ((term905 n' n n'') = (term907 n' n n'')).
Proof. exact (MK_COMB (@lem2608616 n' n n'') (@lem2608619 n' n n'')). Qed.
Lemma lem2608623 (n' : nat) (n : nat) : (term893 n' n) = (term908 n' n).
Proof. exact (fun_ext (fun n'' : nat => @lem2608620 n' n n'')). Qed.
Lemma lem2608624 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2608625 (n' : nat) (n : nat) : (term894 n' n) = (term909 n' n).
Proof. exact (MK_COMB (@lem2608624) (@lem2608623 n' n)). Qed.
Lemma lem2608630 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2608631 (n' : nat) (n : nat) : (term895 n' n) = (term910 n' n).
Proof. exact (MK_COMB (@lem2608630) (@lem2608625 n' n)). Qed.
Lemma lem2608639 (m : nat) (n : nat) : (term616 m n) = False.
Proof. exact (@lem2607552 m n (@lem2607551 m n)). Qed.
Lemma lem2608640 (n' : nat) (n : nat) (n'' : nat) : (term883 n' n n'') = False.
Proof. exact (@lem2608639 (Nat.div n' n) n''). Qed.
Lemma lem2608641 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2608642 (n' : nat) (n : nat) (n'' : nat) : (term885 n' n n'') = (@eq Prop False).
Proof. exact (MK_COMB (@lem2608641) (@lem2608640 n' n n'')). Qed.
Lemma lem2608644 (m : nat) (n : nat) : (term616 m n) = False.
Proof. exact (@lem2607552 m n (@lem2607551 m n)). Qed.
Lemma lem2608645 (n' : nat) (n : nat) (n'' : nat) : (term899 n' n n'') = False.
Proof. exact (@lem2608644 n' (Nat.mul n n'')). Qed.
Lemma lem2608646 (n' : nat) (n : nat) (n'' : nat) : ((term883 n' n n'') = (term899 n' n n'')) = (False = False).
Proof. exact (MK_COMB (@lem2608642 n' n n'') (@lem2608645 n' n n'')). Qed.
Lemma lem2608648 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem2608649 : (False = False) = (~ False).
Proof. exact (@lem2608648 False). Qed.
Lemma lem2608651 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2608652 : (False = False) = True.
Proof. exact (TRANS (@lem2608649) (@lem2608651)). Qed.
Lemma lem2608653 (n' : nat) (n : nat) (n'' : nat) : ((term883 n' n n'') = (term899 n' n n'')) = True.
Proof. exact (TRANS (@lem2608646 n' n n'') (@lem2608652)). Qed.
Lemma lem2608654 (n' : nat) (n : nat) : (term900 n' n) = term787.
Proof. exact (fun_ext (fun n'' : nat => @lem2608653 n' n n'')). Qed.
Lemma lem2608655 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2608656 (n' : nat) (n : nat) : (term901 n' n) = term788.
Proof. exact (MK_COMB (@lem2608655) (@lem2608654 n' n)). Qed.
Lemma lem2608658 {A : Type'} (t : Prop) : (term784 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2608659 (t : Prop) : (term789 t) = t.
Proof. exact (@lem2608658 nat t). Qed.
Lemma lem2608660 : term788 = True.
Proof. exact (@lem2608659 True). Qed.
Lemma lem2608661 (n' : nat) (n : nat) : (term901 n' n) = True.
Proof. exact (TRANS (@lem2608656 n' n) (@lem2608660)). Qed.
Lemma lem2608662 (n' : nat) (n : nat) : (term902 n' n) = (term911 n' n).
Proof. exact (MK_COMB (@lem2608631 n' n) (@lem2608661 n' n)). Qed.
Lemma lem2608664 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem2608665 (n' : nat) (n : nat) : (term911 n' n) = (term909 n' n).
Proof. exact (@lem2608664 (term909 n' n)). Qed.
Lemma lem2608672 (n' : nat) (n : nat) : (term902 n' n) = (term909 n' n).
Proof. exact (TRANS (@lem2608662 n' n) (@lem2608665 n' n)). Qed.
Lemma lem2608673 (n : nat) : (term903 n) = (term912 n).
Proof. exact (fun_ext (fun n' : nat => @lem2608672 n' n)). Qed.
Lemma lem2608674 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2608675 (n : nat) : (term904 n) = (term913 n).
Proof. exact (MK_COMB (@lem2608674) (@lem2608673 n)). Qed.
Lemma lem2608680 (n : nat) : (term913 n) = (term904 n).
Proof. exact (SYM (@lem2608675 n)). Qed.
Lemma lem2608681 : term914.
Proof. exact (proj2 (@lem99082)). Qed.
Lemma lem2608682 : term915.
Proof. exact (proj2 (@lem2608681)). Qed.
Lemma lem2608683 : term916.
Proof. exact (proj2 (@lem2608682)). Qed.
Lemma lem2608684 : term917.
Proof. exact (proj2 (@lem2608683)). Qed.
Lemma lem2608685 : term918.
Proof. exact (proj2 (@lem2608684)). Qed.
Lemma lem2608686 (n : nat) : term919 n.
Proof. exact (@lem2608685 n). Qed.
Lemma lem2608687 (n : nat) : (term919 n) = (term920 n).
Proof. exact (eq_refl (term919 n)). Qed.
Lemma lem2608688 (n : nat) : term920 n.
Proof. exact (EQ_MP (@lem2608687 n) (@lem2608686 n)). Qed.
Lemma lem2608689 (n : nat) (h1 : term921 n) : term921 n.
Proof. exact (h1). Qed.
Lemma lem2608690 (n : nat) (h1 : term921 n) : term922 n.
Proof. exact (@lem2608688 n (@lem2608689 n h1)). Qed.
Lemma lem2608691 (n : nat) : term923 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem2608692 (n : nat) (h1 : term921 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem2608691 n (@lem2608690 n h1)). Qed.
Lemma lem2608727 : term924.
Proof. exact (proj1 (@lem2608683)). Qed.
Lemma lem2608728 (n : nat) : term925 n.
Proof. exact (@lem2608727 n). Qed.
Lemma lem2608729 (n : nat) : (term925 n) = (term926 n).
Proof. exact (eq_refl (term925 n)). Qed.
Lemma lem2608730 (n : nat) : term926 n.
Proof. exact (EQ_MP (@lem2608729 n) (@lem2608728 n)). Qed.
Lemma lem2608731 (n : nat) (h1 : term812 n) : term812 n.
Proof. exact (h1). Qed.
Lemma lem2608732 (n : nat) (h1 : term812 n) : term921 n.
Proof. exact (@lem2608730 n (@lem2608731 n h1)). Qed.
Lemma lem2608733 (n : nat) : (term921 n) = ((term921 n) = True).
Proof. exact (@lem7 (term921 n)). Qed.
Lemma lem2608734 (n : nat) (h1 : term812 n) : (term921 n) = True.
Proof. exact (EQ_MP (@lem2608733 n) (@lem2608732 n h1)). Qed.
Lemma lem2608795 (a : nat) : term927 a.
Proof. exact (@lem188986 a). Qed.
Lemma lem2608796 (a : nat) : (term927 a) = (term928 a).
Proof. exact (eq_refl (term927 a)). Qed.
Lemma lem2608797 (a : nat) : term928 a.
Proof. exact (EQ_MP (@lem2608796 a) (@lem2608795 a)). Qed.
Lemma lem2608798 (a : nat) (b : nat) : term929 a b.
Proof. exact (@lem2608797 a b). Qed.
Lemma lem2608799 (b : nat) (a : nat) : (term929 a b) = (term930 b a).
Proof. exact (eq_refl (term929 a b)). Qed.
Lemma lem2608800 (b : nat) (a : nat) : term930 b a.
Proof. exact (EQ_MP (@lem2608799 b a) (@lem2608798 a b)). Qed.
Lemma lem2608801 (b : nat) (a : nat) (n : nat) : term931 b a n.
Proof. exact (@lem2608800 b a n). Qed.
Lemma lem2608802 (b : nat) (a : nat) (n : nat) : (term931 b a n) = (term932 b a n).
Proof. exact (eq_refl (term931 b a n)). Qed.
Lemma lem2608803 (b : nat) (a : nat) (n : nat) : term932 b a n.
Proof. exact (EQ_MP (@lem2608802 b a n) (@lem2608801 b a n)). Qed.
Lemma lem2608804 (a : nat) (h1 : term922 a) : term922 a.
Proof. exact (h1). Qed.
Lemma lem2608805 (b : nat) (n : nat) (a : nat) (h1 : term922 a) : (term905 b a n) = (term907 b a n).
Proof. exact (@lem2608803 b a n (@lem2608804 a h1)). Qed.
Lemma lem2608811 (n : nat) : (term812 n) = ((term812 n) = True).
Proof. exact (@lem7 (term812 n)). Qed.
Lemma lem2608824 (b : nat) (a : nat) (n : nat) : term932 b a n.
Proof. exact (fun h0 : term922 a => @lem2608805 b n a h0). Qed.
Lemma lem2608825 (n' : nat) (n : nat) (n'' : nat) : term932 n' n n''.
Proof. exact (@lem2608824 n' n n''). Qed.
Lemma lem2608827 (n : nat) : term933 n.
Proof. exact (fun h0 : term921 n => @lem2608692 n h0). Qed.
Lemma lem2608829 (n : nat) : term934 n.
Proof. exact (fun h0 : term812 n => @lem2608734 n h0). Qed.
Lemma lem2608831 (n : nat) (h1 : term812 n) : (term812 n) = True.
Proof. exact (EQ_MP (@lem2608811 n) (@lem2608394 n h1)). Qed.
Lemma lem2608832 (n : nat) (h1 : term812 n) : True = (term812 n).
Proof. exact (SYM (@lem2608831 n h1)). Qed.
Lemma lem2608833 (n : nat) (h1 : term812 n) : term812 n.
Proof. exact (EQ_MP (@lem2608832 n h1) (@lem0)). Qed.
Lemma lem2608834 (n : nat) (h1 : term812 n) : (term921 n) = True.
Proof. exact (@lem2608829 n (@lem2608833 n h1)). Qed.
Lemma lem2608835 (n : nat) (h1 : term812 n) : True = (term921 n).
Proof. exact (SYM (@lem2608834 n h1)). Qed.
Lemma lem2608836 (n : nat) (h1 : term812 n) : term921 n.
Proof. exact (EQ_MP (@lem2608835 n h1) (@lem0)). Qed.
Lemma lem2608837 (n : nat) (h1 : term812 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem2608827 n (@lem2608836 n h1)). Qed.
Lemma lem2608838 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2608839 (n : nat) (h1 : term812 n) : (term922 n) = (~ False).
Proof. exact (MK_COMB (@lem2608838) (@lem2608837 n h1)). Qed.
Lemma lem2608841 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2608842 (n : nat) (h1 : term812 n) : (term922 n) = True.
Proof. exact (TRANS (@lem2608839 n h1) (@lem2608841)). Qed.
Lemma lem2608843 (n : nat) (h1 : term812 n) : True = (term922 n).
Proof. exact (SYM (@lem2608842 n h1)). Qed.
Lemma lem2608844 (n : nat) (h1 : term812 n) : term922 n.
Proof. exact (EQ_MP (@lem2608843 n h1) (@lem0)). Qed.
Lemma lem2608845 (n' : nat) (n'' : nat) (n : nat) (h1 : term812 n) : (term905 n' n n'') = (term907 n' n n'').
Proof. exact (@lem2608825 n' n n'' (@lem2608844 n h1)). Qed.
Lemma lem2608846 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2608847 (n' : nat) (n'' : nat) (n : nat) (h1 : term812 n) : (term906 n' n n'') = (term935 n' n n'').
Proof. exact (MK_COMB (@lem2608846) (@lem2608845 n' n'' n h1)). Qed.
Lemma lem2608848 (n' : nat) (n : nat) (n'' : nat) : (term907 n' n n'') = (term907 n' n n'').
Proof. exact (eq_refl (term907 n' n n'')). Qed.
Lemma lem2608849 (n' : nat) (n'' : nat) (n : nat) (h1 : term812 n) : ((term905 n' n n'') = (term907 n' n n'')) = ((term907 n' n n'') = (term907 n' n n'')).
Proof. exact (MK_COMB (@lem2608847 n' n'' n h1) (@lem2608848 n' n n'')). Qed.
Lemma lem2608851 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2608852 (x : Prop) : (x = x) = True.
Proof. exact (@lem2608851 Prop x). Qed.
Lemma lem2608853 (n' : nat) (n : nat) (n'' : nat) : ((term907 n' n n'') = (term907 n' n n'')) = True.
Proof. exact (@lem2608852 (term907 n' n n'')). Qed.
Lemma lem2608854 (n' : nat) (n'' : nat) (n : nat) (h1 : term812 n) : ((term905 n' n n'') = (term907 n' n n'')) = True.
Proof. exact (TRANS (@lem2608849 n' n'' n h1) (@lem2608853 n' n n'')). Qed.
Lemma lem2608855 (n' : nat) (n : nat) (h1 : term812 n) : (term908 n' n) = term787.
Proof. exact (fun_ext (fun n'' : nat => @lem2608854 n' n'' n h1)). Qed.
Lemma lem2608856 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2608857 (n' : nat) (n : nat) (h1 : term812 n) : (term909 n' n) = term788.
Proof. exact (MK_COMB (@lem2608856) (@lem2608855 n' n h1)). Qed.
Lemma lem2608859 {A : Type'} (t : Prop) : (term784 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2608860 (t : Prop) : (term789 t) = t.
Proof. exact (@lem2608859 nat t). Qed.
Lemma lem2608861 : term788 = True.
Proof. exact (@lem2608860 True). Qed.
Lemma lem2608862 (n' : nat) (n : nat) (h1 : term812 n) : (term909 n' n) = True.
Proof. exact (TRANS (@lem2608857 n' n h1) (@lem2608861)). Qed.
Lemma lem2608863 (n : nat) (h1 : term812 n) : (term912 n) = term787.
Proof. exact (fun_ext (fun n' : nat => @lem2608862 n' n h1)). Qed.
Lemma lem2608864 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2608865 (n : nat) (h1 : term812 n) : (term913 n) = term788.
Proof. exact (MK_COMB (@lem2608864) (@lem2608863 n h1)). Qed.
Lemma lem2608867 {A : Type'} (t : Prop) : (term784 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2608868 (t : Prop) : (term789 t) = t.
Proof. exact (@lem2608867 nat t). Qed.
Lemma lem2608869 : term788 = True.
Proof. exact (@lem2608868 True). Qed.
Lemma lem2608870 (n : nat) (h1 : term812 n) : (term913 n) = True.
Proof. exact (TRANS (@lem2608865 n h1) (@lem2608869)). Qed.
Lemma lem2608871 (n : nat) (h1 : term812 n) : True = (term913 n).
Proof. exact (SYM (@lem2608870 n h1)). Qed.
Lemma lem2608872 (n : nat) (h1 : term812 n) : term913 n.
Proof. exact (EQ_MP (@lem2608871 n h1) (@lem0)). Qed.
Lemma lem2608873 (n : nat) (h1 : term812 n) : term904 n.
Proof. exact (EQ_MP (@lem2608680 n) (@lem2608872 n h1)). Qed.
Lemma lem2608874 (n : nat) (h1 : term812 n) : term890 n.
Proof. exact (EQ_MP (@lem2608599 n) (@lem2608873 n h1)). Qed.
Lemma lem2608875 (n : nat) (h1 : term812 n) : term838 n.
Proof. exact (EQ_MP (@lem2608530 n) (@lem2608874 n h1)). Qed.
Lemma lem2608876 (n : nat) (h1 : term838 n) : term838 n.
Proof. exact (h1). Qed.
Lemma lem2608884 (m : int) (n : int) : (term611 m n) = (term612 m n).
Proof. exact (EQ_MP (@lem2606766 m n) (@lem2606765 m n)). Qed.
Lemma lem2608885 (m : nat) (n : nat) : (term936 m n) = (term937 m n).
Proof. exact (@lem2608884 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2608890 : int_lt = int_lt.
Proof. exact (eq_refl int_lt). Qed.
Lemma lem2608891 (m : nat) (n : nat) : (term938 m n) = (term939 m n).
Proof. exact (MK_COMB (@lem2608890) (@lem2608885 m n)). Qed.
Lemma lem2608892 (c : int) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem2608893 (m : nat) (n : nat) (c : int) : (term940 m n c) = (term941 m n c).
Proof. exact (MK_COMB (@lem2608891 m n) (@lem2608892 c)). Qed.
Lemma lem2608894 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2608895 (m : nat) (n : nat) (c : int) : (term942 m n c) = (term943 m n c).
Proof. exact (MK_COMB (@lem2608894) (@lem2608893 m n c)). Qed.
Lemma lem2608896 (m : nat) (n : nat) (c : int) : (term944 m n c) = (term944 m n c).
Proof. exact (eq_refl (term944 m n c)). Qed.
Lemma lem2608897 (m : nat) (n : nat) (c : int) : ((term940 m n c) = (term944 m n c)) = ((term941 m n c) = (term944 m n c)).
Proof. exact (MK_COMB (@lem2608895 m n c) (@lem2608896 m n c)). Qed.
Lemma lem2608900 (m : nat) (n : nat) : (term945 m n) = (term946 m n).
Proof. exact (fun_ext (fun c : int => @lem2608897 m n c)). Qed.
Lemma lem2608901 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2608902 (m : nat) (n : nat) : (term842 m n) = (term947 m n).
Proof. exact (MK_COMB (@lem2608901) (@lem2608900 m n)). Qed.
Lemma lem2608907 (m : nat) (n : nat) : (term947 m n) = (term842 m n).
Proof. exact (SYM (@lem2608902 m n)). Qed.
Lemma lem2608908 (_474 : int) (_475 : Prop) (_476 : int -> Prop) (_477 : int) : (term948 _476 _475 _474 _477) = (term949 _474 _475 _476 _477).
Proof. exact (@lem13473 int _474 _475 _476 _477). Qed.
Lemma lem2608909 (_474 : int) (_475 : Prop) (m : nat) (n : nat) (_477 : int) : (term950 m n _475 _474 _477) = (term951 _474 _475 m n _477).
Proof. exact (@lem2608908 _474 _475 (term952 m n) _477). Qed.
Lemma lem2608910 (m : nat) (n : nat) : (term953 m n) = (term954 m n).
Proof. exact (@lem2608909 (term955 m n) ((term601 m n) = term527) m n (term956 m n)). Qed.
Lemma lem2608911 (m : nat) (n : nat) : (term957 m n) = (term958 m n).
Proof. exact (eq_refl (term957 m n)). Qed.
Lemma lem2608912 (m : nat) (n : nat) : (term959 m n) = (term959 m n).
Proof. exact (eq_refl (term959 m n)). Qed.
Lemma lem2608913 (m : nat) (n : nat) : (term960 m n) = (term961 m n).
Proof. exact (MK_COMB (@lem2608912 m n) (@lem2608911 m n)). Qed.
Lemma lem2608914 (m : nat) (n : nat) : (term962 m n) = (term963 m n).
Proof. exact (eq_refl (term962 m n)). Qed.
Lemma lem2608915 (m : nat) (n : nat) : (term964 m n) = (term964 m n).
Proof. exact (eq_refl (term964 m n)). Qed.
Lemma lem2608916 (m : nat) (n : nat) : (term965 m n) = (term966 m n).
Proof. exact (MK_COMB (@lem2608915 m n) (@lem2608914 m n)). Qed.
Lemma lem2608917 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2608918 (m : nat) (n : nat) : (term967 m n) = (term968 m n).
Proof. exact (MK_COMB (@lem2608917) (@lem2608916 m n)). Qed.
Lemma lem2608919 (m : nat) (n : nat) : (term954 m n) = (term969 m n).
Proof. exact (MK_COMB (@lem2608918 m n) (@lem2608913 m n)). Qed.
Lemma lem2608920 (m : nat) (n : nat) : (term953 m n) = (term947 m n).
Proof. exact (eq_refl (term953 m n)). Qed.
Lemma lem2608921 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2608922 (m : nat) (n : nat) : (term970 m n) = (term971 m n).
Proof. exact (MK_COMB (@lem2608921) (@lem2608920 m n)). Qed.
Lemma lem2608923 (m : nat) (n : nat) : ((term953 m n) = (term954 m n)) = ((term947 m n) = (term969 m n)).
Proof. exact (MK_COMB (@lem2608922 m n) (@lem2608919 m n)). Qed.
Lemma lem2608924 (m : nat) (n : nat) : (term947 m n) = (term969 m n).
Proof. exact (EQ_MP (@lem2608923 m n) (@lem2608910 m n)). Qed.
Lemma lem2608925 (m : nat) (n : nat) : (term969 m n) = (term947 m n).
Proof. exact (SYM (@lem2608924 m n)). Qed.
Lemma lem2608926 (m : nat) (n : nat) (h1 : (term601 m n) = term527) : (term601 m n) = term527.
Proof. exact (h1). Qed.
Lemma lem2608943 (m : nat) (n : nat) (h1 : term972 m n) : term972 m n.
Proof. exact (h1). Qed.
Lemma lem2608962 (n : nat) (h1 : term812 n) : term812 n.
Proof. exact (h1). Qed.
Lemma lem2608966 (m : nat) (n : nat) (h1 : (term601 m n) = term527) : (term601 m n) = term527.
Proof. exact (h1). Qed.
Lemma lem2608968 (m : nat) (n : nat) (q : int) (h1 : (term598 m n) = q) : (term598 m n) = q.
Proof. exact (h1). Qed.
Lemma lem2608969 : int_mul = int_mul.
Proof. exact (eq_refl int_mul). Qed.
Lemma lem2608970 (m : nat) (n : nat) (q : int) (h1 : (term598 m n) = q) : (term973 m n) = (int_mul q).
Proof. exact (MK_COMB (@lem2608969) (@lem2608968 m n q h1)). Qed.
Lemma lem2608971 (n : nat) : (int_of_num n) = (int_of_num n).
Proof. exact (eq_refl (int_of_num n)). Qed.
Lemma lem2608972 (m : nat) (n : nat) (q : int) (h1 : (term598 m n) = q) : (term974 m n) = (term526 q n).
Proof. exact (MK_COMB (@lem2608970 m n q h1) (@lem2608971 n)). Qed.
Lemma lem2608973 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2608974 (m : nat) (n : nat) (q : int) (h1 : (term598 m n) = q) : (term975 m n) = (term976 q n).
Proof. exact (MK_COMB (@lem2608973) (@lem2608972 m n q h1)). Qed.
Lemma lem2608975 (m : nat) (n : nat) : (term601 m n) = (term601 m n).
Proof. exact (eq_refl (term601 m n)). Qed.
Lemma lem2608976 (m : nat) (n : nat) (q : int) (h1 : (term598 m n) = q) : (term977 m n) = (term978 q m n).
Proof. exact (MK_COMB (@lem2608974 m n q h1) (@lem2608975 m n)). Qed.
Lemma lem2608977 (m : nat) : (term979 m) = (term979 m).
Proof. exact (eq_refl (term979 m)). Qed.
Lemma lem2608978 (m : nat) (n : nat) (q : int) (h1 : (term598 m n) = q) : ((int_of_num m) = (term977 m n)) = ((int_of_num m) = (term978 q m n)).
Proof. exact (MK_COMB (@lem2608977 m) (@lem2608976 m n q h1)). Qed.
Lemma lem2608979 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2608980 (m : nat) (n : nat) (q : int) (h1 : (term598 m n) = q) : (term980 m n) = (term981 q m n).
Proof. exact (MK_COMB (@lem2608979) (@lem2608978 m n q h1)). Qed.
Lemma lem2608981 (m : nat) (n : nat) : (term982 m n) = (term982 m n).
Proof. exact (eq_refl (term982 m n)). Qed.
Lemma lem2608982 (m : nat) (n : nat) (q : int) (h1 : (term598 m n) = q) : (term983 m n) = (term984 q m n).
Proof. exact (MK_COMB (@lem2608980 m n q h1) (@lem2608981 m n)). Qed.
Lemma lem2608983 (n : nat) : (term985 n) = (term985 n).
Proof. exact (eq_refl (term985 n)). Qed.
Lemma lem2608984 (m : nat) (n : nat) (q : int) (h1 : (term598 m n) = q) : (term607 m n) = (term986 q m n).
Proof. exact (MK_COMB (@lem2608983 n) (@lem2608982 m n q h1)). Qed.
Lemma lem2608985 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2608986 (m : nat) (n : nat) (q : int) (h1 : (term598 m n) = q) : (term987 m n) = (term988 q m n).
Proof. exact (MK_COMB (@lem2608985) (@lem2608984 m n q h1)). Qed.
Lemma lem2608988 (m : nat) (n : nat) (q : int) (h1 : (term598 m n) = q) : (term598 m n) = q.
Proof. exact (h1). Qed.
Lemma lem2608989 : int_neg = int_neg.
Proof. exact (eq_refl int_neg). Qed.
Lemma lem2608990 (m : nat) (n : nat) (q : int) (h1 : (term598 m n) = q) : (term955 m n) = (int_neg q).
Proof. exact (MK_COMB (@lem2608989) (@lem2608988 m n q h1)). Qed.
Lemma lem2608991 : int_lt = int_lt.
Proof. exact (eq_refl int_lt). Qed.
Lemma lem2608992 (m : nat) (n : nat) (q : int) (h1 : (term598 m n) = q) : (term989 m n) = (term990 q).
Proof. exact (MK_COMB (@lem2608991) (@lem2608990 m n q h1)). Qed.
Lemma lem2608993 (c : int) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem2608994 (c : int) (m : nat) (n : nat) (q : int) (h1 : (term598 m n) = q) : (term991 m n c) = (term992 q c).
Proof. exact (MK_COMB (@lem2608992 m n q h1) (@lem2608993 c)). Qed.
Lemma lem2608995 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2608996 (c : int) (m : nat) (n : nat) (q : int) (h1 : (term598 m n) = q) : (term993 m n c) = (term994 q c).
Proof. exact (MK_COMB (@lem2608995) (@lem2608994 c m n q h1)). Qed.
Lemma lem2608997 (m : nat) (n : nat) (c : int) : (term944 m n c) = (term944 m n c).
Proof. exact (eq_refl (term944 m n c)). Qed.
Lemma lem2608998 (c : int) (m : nat) (n : nat) (q : int) (h1 : (term598 m n) = q) : ((term991 m n c) = (term944 m n c)) = ((term992 q c) = (term944 m n c)).
Proof. exact (MK_COMB (@lem2608996 c m n q h1) (@lem2608997 m n c)). Qed.
Lemma lem2608999 (m : nat) (n : nat) (q : int) (h1 : (term598 m n) = q) : (term995 m n) = (term996 q m n).
Proof. exact (fun_ext (fun c : int => @lem2608998 c m n q h1)). Qed.
Lemma lem2609000 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2609001 (m : nat) (n : nat) (q : int) (h1 : (term598 m n) = q) : (term963 m n) = (term997 q m n).
Proof. exact (MK_COMB (@lem2609000) (@lem2608999 m n q h1)). Qed.
Lemma lem2609002 (m : nat) (n : nat) (q : int) (h1 : (term598 m n) = q) : (term998 m n) = (term999 q m n).
Proof. exact (MK_COMB (@lem2608986 m n q h1) (@lem2609001 m n q h1)). Qed.
Lemma lem2609003 (m : nat) (n : nat) (q : int) (h1 : (term598 m n) = q) : (term999 q m n) = (term998 m n).
Proof. exact (SYM (@lem2609002 m n q h1)). Qed.
Lemma lem2609004 (m : nat) (n : nat) (r : int) (h1 : (term601 m n) = r) : (term601 m n) = r.
Proof. exact (h1). Qed.
Lemma lem2609006 (n : nat) (h1 : term812 n) : term812 n.
Proof. exact (h1). Qed.
Lemma lem2609010 (m : nat) (n : nat) (r : int) (h1 : (term601 m n) = r) : (term601 m n) = r.
Proof. exact (h1). Qed.
Lemma lem2609011 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2609012 (m : nat) (n : nat) (r : int) (h1 : (term601 m n) = r) : (term1000 m n) = (@eq int r).
Proof. exact (MK_COMB (@lem2609011) (@lem2609010 m n r h1)). Qed.
Lemma lem2609013 : term527 = term527.
Proof. exact (eq_refl term527). Qed.
Lemma lem2609014 (m : nat) (n : nat) (r : int) (h1 : (term601 m n) = r) : ((term601 m n) = term527) = (r = term527).
Proof. exact (MK_COMB (@lem2609012 m n r h1) (@lem2609013)). Qed.
Lemma lem2609019 (m : nat) (n : nat) (r : int) (h1 : (term601 m n) = r) : (term601 m n) = r.
Proof. exact (h1). Qed.
Lemma lem2609020 (q : int) (n : nat) : (term976 q n) = (term976 q n).
Proof. exact (eq_refl (term976 q n)). Qed.
Lemma lem2609021 (q : int) (m : nat) (n : nat) (r : int) (h1 : (term601 m n) = r) : (term978 q m n) = (term1001 q n r).
Proof. exact (MK_COMB (@lem2609020 q n) (@lem2609019 m n r h1)). Qed.
Lemma lem2609022 (m : nat) : (term979 m) = (term979 m).
Proof. exact (eq_refl (term979 m)). Qed.
Lemma lem2609023 (q : int) (m : nat) (n : nat) (r : int) (h1 : (term601 m n) = r) : ((int_of_num m) = (term978 q m n)) = ((int_of_num m) = (term1001 q n r)).
Proof. exact (MK_COMB (@lem2609022 m) (@lem2609021 q m n r h1)). Qed.
Lemma lem2609024 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2609025 (q : int) (m : nat) (n : nat) (r : int) (h1 : (term601 m n) = r) : (term981 q m n) = (term1002 m q n r).
Proof. exact (MK_COMB (@lem2609024) (@lem2609023 q m n r h1)). Qed.
Lemma lem2609027 (m : nat) (n : nat) (r : int) (h1 : (term601 m n) = r) : (term601 m n) = r.
Proof. exact (h1). Qed.
Lemma lem2609028 : term1003 = term1003.
Proof. exact (eq_refl term1003). Qed.
Lemma lem2609029 (m : nat) (n : nat) (r : int) (h1 : (term601 m n) = r) : (term1004 m n) = (term1005 r).
Proof. exact (MK_COMB (@lem2609028) (@lem2609027 m n r h1)). Qed.
Lemma lem2609030 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2609031 (m : nat) (n : nat) (r : int) (h1 : (term601 m n) = r) : (term1006 m n) = (term1007 r).
Proof. exact (MK_COMB (@lem2609030) (@lem2609029 m n r h1)). Qed.
Lemma lem2609033 (m : nat) (n : nat) (r : int) (h1 : (term601 m n) = r) : (term601 m n) = r.
Proof. exact (h1). Qed.
Lemma lem2609034 : int_lt = int_lt.
Proof. exact (eq_refl int_lt). Qed.
Lemma lem2609035 (m : nat) (n : nat) (r : int) (h1 : (term601 m n) = r) : (term1008 m n) = (int_lt r).
Proof. exact (MK_COMB (@lem2609034) (@lem2609033 m n r h1)). Qed.
Lemma lem2609036 (n : nat) : (term1009 n) = (term1009 n).
Proof. exact (eq_refl (term1009 n)). Qed.
Lemma lem2609037 (m : nat) (n : nat) (r : int) (h1 : (term601 m n) = r) : (term1010 m n) = (term1011 r n).
Proof. exact (MK_COMB (@lem2609035 m n r h1) (@lem2609036 n)). Qed.
Lemma lem2609038 (m : nat) (n : nat) (r : int) (h1 : (term601 m n) = r) : (term982 m n) = (term1012 r n).
Proof. exact (MK_COMB (@lem2609031 m n r h1) (@lem2609037 m n r h1)). Qed.
Lemma lem2609039 (q : int) (m : nat) (n : nat) (r : int) (h1 : (term601 m n) = r) : (term984 q m n) = (term1013 m q r n).
Proof. exact (MK_COMB (@lem2609025 q m n r h1) (@lem2609038 m n r h1)). Qed.
Lemma lem2609040 (n : nat) : (term985 n) = (term985 n).
Proof. exact (eq_refl (term985 n)). Qed.
Lemma lem2609041 (q : int) (m : nat) (n : nat) (r : int) (h1 : (term601 m n) = r) : (term986 q m n) = (term1014 m q r n).
Proof. exact (MK_COMB (@lem2609040 n) (@lem2609039 q m n r h1)). Qed.
Lemma lem2609042 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2609043 (q : int) (m : nat) (n : nat) (r : int) (h1 : (term601 m n) = r) : (term988 q m n) = (term1015 m q r n).
Proof. exact (MK_COMB (@lem2609042) (@lem2609041 q m n r h1)). Qed.
Lemma lem2609044 (q : int) (m : nat) (n : nat) : (term997 q m n) = (term997 q m n).
Proof. exact (eq_refl (term997 q m n)). Qed.
Lemma lem2609045 (q : int) (m : nat) (n : nat) (r : int) (h1 : (term601 m n) = r) : (term999 q m n) = (term1016 r q m n).
Proof. exact (MK_COMB (@lem2609043 q m n r h1) (@lem2609044 q m n)). Qed.
Lemma lem2609046 (q : int) (m : nat) (n : nat) (r : int) (h1 : (term601 m n) = r) : (term1016 r q m n) = (term999 q m n).
Proof. exact (SYM (@lem2609045 q m n r h1)). Qed.
Lemma lem2609047 : term914.
Proof. exact (proj2 (@lem99082)). Qed.
Lemma lem2609048 : term915.
Proof. exact (proj2 (@lem2609047)). Qed.
Lemma lem2609049 : term916.
Proof. exact (proj2 (@lem2609048)). Qed.
Lemma lem2609050 : term917.
Proof. exact (proj2 (@lem2609049)). Qed.
Lemma lem2609051 : term918.
Proof. exact (proj2 (@lem2609050)). Qed.
Lemma lem2609052 (n : nat) : term919 n.
Proof. exact (@lem2609051 n). Qed.
Lemma lem2609053 (n : nat) : (term919 n) = (term920 n).
Proof. exact (eq_refl (term919 n)). Qed.
Lemma lem2609054 (n : nat) : term920 n.
Proof. exact (EQ_MP (@lem2609053 n) (@lem2609052 n)). Qed.
Lemma lem2609055 (n : nat) (h1 : term921 n) : term921 n.
Proof. exact (h1). Qed.
Lemma lem2609056 (n : nat) (h1 : term921 n) : term922 n.
Proof. exact (@lem2609054 n (@lem2609055 n h1)). Qed.
Lemma lem2609057 (n : nat) : term923 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem2609058 (n : nat) (h1 : term921 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem2609057 n (@lem2609056 n h1)). Qed.
Lemma lem2609093 : term924.
Proof. exact (proj1 (@lem2609049)). Qed.
Lemma lem2609094 (n : nat) : term925 n.
Proof. exact (@lem2609093 n). Qed.
Lemma lem2609095 (n : nat) : (term925 n) = (term926 n).
Proof. exact (eq_refl (term925 n)). Qed.
Lemma lem2609096 (n : nat) : term926 n.
Proof. exact (EQ_MP (@lem2609095 n) (@lem2609094 n)). Qed.
Lemma lem2609097 (n : nat) (h1 : term812 n) : term812 n.
Proof. exact (h1). Qed.
Lemma lem2609098 (n : nat) (h1 : term812 n) : term921 n.
Proof. exact (@lem2609096 n (@lem2609097 n h1)). Qed.
Lemma lem2609099 (n : nat) : (term921 n) = ((term921 n) = True).
Proof. exact (@lem7 (term921 n)). Qed.
Lemma lem2609100 (n : nat) (h1 : term812 n) : (term921 n) = True.
Proof. exact (EQ_MP (@lem2609099 n) (@lem2609098 n h1)). Qed.
Lemma lem2609161 (m : nat) : term1017 m.
Proof. exact (@lem2307147 m). Qed.
Lemma lem2609162 (m : nat) : (term1017 m) = (term1018 m).
Proof. exact (eq_refl (term1017 m)). Qed.
Lemma lem2609163 (m : nat) : term1018 m.
Proof. exact (EQ_MP (@lem2609162 m) (@lem2609161 m)). Qed.
Lemma lem2609164 (m : nat) (n : nat) : term1019 m n.
Proof. exact (@lem2609163 m n). Qed.
Lemma lem2609165 (m : nat) (n : nat) : (term1019 m n) = (((int_of_num m) = (int_of_num n)) = (m = n)).
Proof. exact (eq_refl (term1019 m n)). Qed.
Lemma lem2609167 (n : nat) : (term812 n) = ((term812 n) = True).
Proof. exact (@lem7 (term812 n)). Qed.
Lemma lem2609178 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term1020 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem2609179 (p : Prop) (q : Prop) (p' : Prop) : term1021 p q p'.
Proof. exact (fun q' : Prop => @lem2609178 p q p' q'). Qed.
Lemma lem2609180 (p : Prop) (q : Prop) : term1022 p q.
Proof. exact (fun p' : Prop => @lem2609179 p q p'). Qed.
Lemma lem2609181 (r : int) (q : int) (m : nat) (n : nat) : term1023 r q m n.
Proof. exact (@lem2609180 (term1014 m q r n) (term997 q m n)). Qed.
Lemma lem2609182 (r : int) (q : int) (m : nat) (n : nat) (p' : Prop) : term1024 r q m n p'.
Proof. exact (@lem2609181 r q m n p'). Qed.
Lemma lem2609183 (r : int) (q : int) (m : nat) (n : nat) (p' : Prop) : (term1024 r q m n p') = (term1025 r q m n p').
Proof. exact (eq_refl (term1024 r q m n p')). Qed.
Lemma lem2609184 (r : int) (q : int) (m : nat) (n : nat) (p' : Prop) : term1025 r q m n p'.
Proof. exact (EQ_MP (@lem2609183 r q m n p') (@lem2609182 r q m n p')). Qed.
Lemma lem2609185 (r : int) (q : int) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term1026 r q m n p' q'.
Proof. exact (@lem2609184 r q m n p' q'). Qed.
Lemma lem2609186 (r : int) (q : int) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : (term1026 r q m n p' q') = (term1027 r q m n p' q').
Proof. exact (eq_refl (term1026 r q m n p' q')). Qed.
Lemma lem2609187 (r : int) (q : int) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term1027 r q m n p' q'.
Proof. exact (EQ_MP (@lem2609186 r q m n p' q') (@lem2609185 r q m n p' q')). Qed.
Lemma lem2609191 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term1020 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem2609192 (p : Prop) (q : Prop) (p' : Prop) : term1021 p q p'.
Proof. exact (fun q' : Prop => @lem2609191 p q p' q'). Qed.
Lemma lem2609193 (p : Prop) (q : Prop) : term1022 p q.
Proof. exact (fun p' : Prop => @lem2609192 p q p'). Qed.
Lemma lem2609194 (m : nat) (q : int) (r : int) (n : nat) : term1028 m q r n.
Proof. exact (@lem2609193 (term1029 n) (term1013 m q r n)). Qed.
Lemma lem2609195 (m : nat) (q : int) (r : int) (n : nat) (p' : Prop) : term1030 m q r n p'.
Proof. exact (@lem2609194 m q r n p'). Qed.
Lemma lem2609196 (m : nat) (q : int) (r : int) (n : nat) (p' : Prop) : (term1030 m q r n p') = (term1031 m q r n p').
Proof. exact (eq_refl (term1030 m q r n p')). Qed.
Lemma lem2609197 (m : nat) (q : int) (r : int) (n : nat) (p' : Prop) : term1031 m q r n p'.
Proof. exact (EQ_MP (@lem2609196 m q r n p') (@lem2609195 m q r n p')). Qed.
Lemma lem2609198 (m : nat) (q : int) (r : int) (n : nat) (p' : Prop) (q' : Prop) : term1032 m q r n p' q'.
Proof. exact (@lem2609197 m q r n p' q'). Qed.
Lemma lem2609199 (m : nat) (q : int) (r : int) (n : nat) (p' : Prop) (q' : Prop) : (term1032 m q r n p' q') = (term1033 m q r n p' q').
Proof. exact (eq_refl (term1032 m q r n p' q')). Qed.
Lemma lem2609200 (m : nat) (q : int) (r : int) (n : nat) (p' : Prop) (q' : Prop) : term1033 m q r n p' q'.
Proof. exact (EQ_MP (@lem2609199 m q r n p' q') (@lem2609198 m q r n p' q')). Qed.
Lemma lem2609202 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem2609165 m n) (@lem2609164 m n)). Qed.
Lemma lem2609203 (n : nat) : ((int_of_num n) = term527) = (n = (NUMERAL 0)).
Proof. exact (@lem2609202 n (NUMERAL 0)). Qed.
Lemma lem2609205 (n : nat) : term933 n.
Proof. exact (fun h0 : term921 n => @lem2609058 n h0). Qed.
Lemma lem2609207 (n : nat) : term934 n.
Proof. exact (fun h0 : term812 n => @lem2609100 n h0). Qed.
Lemma lem2609209 (n : nat) (h1 : term812 n) : (term812 n) = True.
Proof. exact (EQ_MP (@lem2609167 n) (@lem2609006 n h1)). Qed.
Lemma lem2609210 (n : nat) (h1 : term812 n) : True = (term812 n).
Proof. exact (SYM (@lem2609209 n h1)). Qed.
Lemma lem2609211 (n : nat) (h1 : term812 n) : term812 n.
Proof. exact (EQ_MP (@lem2609210 n h1) (@lem0)). Qed.
Lemma lem2609212 (n : nat) (h1 : term812 n) : (term921 n) = True.
Proof. exact (@lem2609207 n (@lem2609211 n h1)). Qed.
Lemma lem2609213 (n : nat) (h1 : term812 n) : True = (term921 n).
Proof. exact (SYM (@lem2609212 n h1)). Qed.
Lemma lem2609214 (n : nat) (h1 : term812 n) : term921 n.
Proof. exact (EQ_MP (@lem2609213 n h1) (@lem0)). Qed.
Lemma lem2609215 (n : nat) (h1 : term812 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem2609205 n (@lem2609214 n h1)). Qed.
Lemma lem2609216 (n : nat) (h1 : term812 n) : ((int_of_num n) = term527) = False.
Proof. exact (TRANS (@lem2609203 n) (@lem2609215 n h1)). Qed.
Lemma lem2609217 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2609218 (n : nat) (h1 : term812 n) : (term1029 n) = (~ False).
Proof. exact (MK_COMB (@lem2609217) (@lem2609216 n h1)). Qed.
Lemma lem2609220 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2609221 (n : nat) (h1 : term812 n) : (term1029 n) = True.
Proof. exact (TRANS (@lem2609218 n h1) (@lem2609220)). Qed.
Lemma lem2609222 (m : nat) (q : int) (r : int) (n : nat) (q' : Prop) : term1034 m q r n q'.
Proof. exact (@lem2609200 m q r n True q'). Qed.
Lemma lem2609223 (m : nat) (q : int) (r : int) (q' : Prop) (n : nat) (h1 : term812 n) : term1035 m q r n q'.
Proof. exact (@lem2609222 m q r n q' (@lem2609221 n h1)). Qed.
Lemma lem2609234 (r : int) (m : nat) (n : nat) (h1 : (term601 m n) = r) (h2 : (term601 m n) = term527) : r = term527.
Proof. exact (EQ_MP (@lem2609014 m n r h1) (@lem2608966 m n h2)). Qed.
Lemma lem2609235 (q : int) (n : nat) : (term976 q n) = (term976 q n).
Proof. exact (eq_refl (term976 q n)). Qed.
Lemma lem2609236 (q : int) (r : int) (m : nat) (n : nat) (h1 : (term601 m n) = r) (h2 : (term601 m n) = term527) : (term1001 q n r) = (term523 q n).
Proof. exact (MK_COMB (@lem2609235 q n) (@lem2609234 r m n h1 h2)). Qed.
Lemma lem2609237 (m : nat) : (term979 m) = (term979 m).
Proof. exact (eq_refl (term979 m)). Qed.
Lemma lem2609238 (q : int) (r : int) (m : nat) (n : nat) (h1 : (term601 m n) = r) (h2 : (term601 m n) = term527) : ((int_of_num m) = (term1001 q n r)) = ((int_of_num m) = (term523 q n)).
Proof. exact (MK_COMB (@lem2609237 m) (@lem2609236 q r m n h1 h2)). Qed.
Lemma lem2609241 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2609242 (q : int) (r : int) (m : nat) (n : nat) (h1 : (term601 m n) = r) (h2 : (term601 m n) = term527) : (term1002 m q n r) = (term1036 m q n).
Proof. exact (MK_COMB (@lem2609241) (@lem2609238 q r m n h1 h2)). Qed.
Lemma lem2609248 (r : int) (m : nat) (n : nat) (h1 : (term601 m n) = r) (h2 : (term601 m n) = term527) : r = term527.
Proof. exact (EQ_MP (@lem2609014 m n r h1) (@lem2608966 m n h2)). Qed.
Lemma lem2609249 : term1003 = term1003.
Proof. exact (eq_refl term1003). Qed.
Lemma lem2609250 (r : int) (m : nat) (n : nat) (h1 : (term601 m n) = r) (h2 : (term601 m n) = term527) : (term1005 r) = term1037.
Proof. exact (MK_COMB (@lem2609249) (@lem2609248 r m n h1 h2)). Qed.
Lemma lem2609251 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2609252 (r : int) (m : nat) (n : nat) (h1 : (term601 m n) = r) (h2 : (term601 m n) = term527) : (term1007 r) = term1038.
Proof. exact (MK_COMB (@lem2609251) (@lem2609250 r m n h1 h2)). Qed.
Lemma lem2609254 (r : int) (m : nat) (n : nat) (h1 : (term601 m n) = r) (h2 : (term601 m n) = term527) : r = term527.
Proof. exact (EQ_MP (@lem2609014 m n r h1) (@lem2608966 m n h2)). Qed.
Lemma lem2609255 : int_lt = int_lt.
Proof. exact (eq_refl int_lt). Qed.
Lemma lem2609256 (r : int) (m : nat) (n : nat) (h1 : (term601 m n) = r) (h2 : (term601 m n) = term527) : (int_lt r) = term1039.
Proof. exact (MK_COMB (@lem2609255) (@lem2609254 r m n h1 h2)). Qed.
Lemma lem2609257 (n : nat) : (term1009 n) = (term1009 n).
Proof. exact (eq_refl (term1009 n)). Qed.
Lemma lem2609258 (r : int) (m : nat) (n : nat) (h1 : (term601 m n) = r) (h2 : (term601 m n) = term527) : (term1011 r n) = (term1040 n).
Proof. exact (MK_COMB (@lem2609256 r m n h1 h2) (@lem2609257 n)). Qed.
Lemma lem2609259 (r : int) (m : nat) (n : nat) (h1 : (term601 m n) = r) (h2 : (term601 m n) = term527) : (term1012 r n) = (term1041 n).
Proof. exact (MK_COMB (@lem2609252 r m n h1 h2) (@lem2609258 r m n h1 h2)). Qed.
Lemma lem2609262 (q : int) (r : int) (m : nat) (n : nat) (h1 : (term601 m n) = r) (h2 : (term601 m n) = term527) : (term1013 m q r n) = (term1042 m q n).
Proof. exact (MK_COMB (@lem2609242 q r m n h1 h2) (@lem2609259 r m n h1 h2)). Qed.
Lemma lem2609269 (q : int) (r : int) (m : nat) (n : nat) (h1 : (term601 m n) = r) (h2 : (term601 m n) = term527) : term1043 r m q n.
Proof. exact (fun h0 : True => @lem2609262 q r m n h1 h2). Qed.
Lemma lem2609270 (r : int) (m : nat) (q : int) (n : nat) (h1 : term812 n) : term1044 r m q n.
Proof. exact (@lem2609223 m q r (term1042 m q n) n h1). Qed.
Lemma lem2609271 (q : int) (r : int) (m : nat) (n : nat) (h1 : term812 n) (h2 : (term601 m n) = r) (h3 : (term601 m n) = term527) : (term1014 m q r n) = (term1045 m q n).
Proof. exact (@lem2609270 r m q n h1 (@lem2609269 q r m n h2 h3)). Qed.
Lemma lem2609273 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem2609274 (m : nat) (q : int) (n : nat) : (term1045 m q n) = (term1042 m q n).
Proof. exact (@lem2609273 (term1042 m q n)). Qed.
Lemma lem2609281 (q : int) (r : int) (m : nat) (n : nat) (h1 : term812 n) (h2 : (term601 m n) = r) (h3 : (term601 m n) = term527) : (term1014 m q r n) = (term1042 m q n).
Proof. exact (TRANS (@lem2609271 q r m n h1 h2 h3) (@lem2609274 m q n)). Qed.
Lemma lem2609282 (r : int) (m : nat) (q : int) (n : nat) (q' : Prop) : term1046 r m q n q'.
Proof. exact (@lem2609187 r q m n (term1042 m q n) q'). Qed.
Lemma lem2609283 (q : int) (q' : Prop) (r : int) (m : nat) (n : nat) (h1 : term812 n) (h2 : (term601 m n) = r) (h3 : (term601 m n) = term527) : term1047 r m q n q'.
Proof. exact (@lem2609282 r m q n q' (@lem2609281 q r m n h1 h2 h3)). Qed.
Lemma lem2609284 (m : nat) (q : int) (n : nat) (h1 : term1042 m q n) : term1042 m q n.
Proof. exact (h1). Qed.
Lemma lem2609300 (m : nat) (q : int) (n : nat) (h1 : term1042 m q n) : (int_of_num m) = (term523 q n).
Proof. exact (proj1 (@lem2609284 m q n h1)). Qed.
Lemma lem2609301 : int_neg = int_neg.
Proof. exact (eq_refl int_neg). Qed.
Lemma lem2609302 (m : nat) (q : int) (n : nat) (h1 : term1042 m q n) : (term618 m) = (term512 q n).
Proof. exact (MK_COMB (@lem2609301) (@lem2609300 m q n h1)). Qed.
Lemma lem2609303 : int_lt = int_lt.
Proof. exact (eq_refl int_lt). Qed.
Lemma lem2609304 (m : nat) (q : int) (n : nat) (h1 : term1042 m q n) : (term1048 m) = (term1049 q n).
Proof. exact (MK_COMB (@lem2609303) (@lem2609302 m q n h1)). Qed.
Lemma lem2609305 (n : nat) (c : int) : (term1050 n c) = (term1050 n c).
Proof. exact (eq_refl (term1050 n c)). Qed.
Lemma lem2609306 (c : int) (m : nat) (q : int) (n : nat) (h1 : term1042 m q n) : (term944 m n c) = (term1051 q n c).
Proof. exact (MK_COMB (@lem2609304 m q n h1) (@lem2609305 n c)). Qed.
Lemma lem2609307 (q : int) (c : int) : (term994 q c) = (term994 q c).
Proof. exact (eq_refl (term994 q c)). Qed.
Lemma lem2609308 (c : int) (m : nat) (q : int) (n : nat) (h1 : term1042 m q n) : ((term992 q c) = (term944 m n c)) = ((term992 q c) = (term1051 q n c)).
Proof. exact (MK_COMB (@lem2609307 q c) (@lem2609306 c m q n h1)). Qed.
Lemma lem2609311 (m : nat) (q : int) (n : nat) (h1 : term1042 m q n) : (term996 q m n) = (term1052 q n).
Proof. exact (fun_ext (fun c : int => @lem2609308 c m q n h1)). Qed.
Lemma lem2609314 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2609315 (m : nat) (q : int) (n : nat) (h1 : term1042 m q n) : (term997 q m n) = (term1053 q n).
Proof. exact (MK_COMB (@lem2609314) (@lem2609311 m q n h1)). Qed.
Lemma lem2609322 (m : nat) (q : int) (n : nat) : term1054 m q n.
Proof. exact (fun h0 : term1042 m q n => @lem2609315 m q n h0). Qed.
Lemma lem2609323 (q : int) (r : int) (m : nat) (n : nat) (h1 : term812 n) (h2 : (term601 m n) = r) (h3 : (term601 m n) = term527) : term1055 r m q n.
Proof. exact (@lem2609283 q (term1053 q n) r m n h1 h2 h3). Qed.
Lemma lem2609324 (q : int) (r : int) (m : nat) (n : nat) (h1 : term812 n) (h2 : (term601 m n) = r) (h3 : (term601 m n) = term527) : (term1016 r q m n) = (term1056 m q n).
Proof. exact (@lem2609323 q r m n h1 h2 h3 (@lem2609322 m q n)). Qed.
Lemma lem2609378 (q : int) (r : int) (m : nat) (n : nat) (h1 : term812 n) (h2 : (term601 m n) = r) (h3 : (term601 m n) = term527) : (term1056 m q n) = (term1016 r q m n).
Proof. exact (SYM (@lem2609324 q r m n h1 h2 h3)). Qed.
Lemma lem2609387 (n : nat) (q : int) : (term512 q n) = (term513 n q).
Proof. exact (EQ_MP (@lem2605893 n q) (@lem2606738 n q)). Qed.
Lemma lem2609388 : int_lt = int_lt.
Proof. exact (eq_refl int_lt). Qed.
Lemma lem2609389 (n : nat) (q : int) : (term1049 q n) = (term1057 n q).
Proof. exact (MK_COMB (@lem2609388) (@lem2609387 n q)). Qed.
Lemma lem2609390 (n : nat) (c : int) : (term1050 n c) = (term1050 n c).
Proof. exact (eq_refl (term1050 n c)). Qed.
Lemma lem2609391 (q : int) (n : nat) (c : int) : (term1051 q n c) = (term1058 q n c).
Proof. exact (MK_COMB (@lem2609389 n q) (@lem2609390 n c)). Qed.
Lemma lem2609392 (q : int) (c : int) : (term994 q c) = (term994 q c).
Proof. exact (eq_refl (term994 q c)). Qed.
Lemma lem2609393 (q : int) (n : nat) (c : int) : ((term992 q c) = (term1051 q n c)) = ((term992 q c) = (term1058 q n c)).
Proof. exact (MK_COMB (@lem2609392 q c) (@lem2609391 q n c)). Qed.
Lemma lem2609396 (q : int) (n : nat) : (term1052 q n) = (term1059 q n).
Proof. exact (fun_ext (fun c : int => @lem2609393 q n c)). Qed.
Lemma lem2609397 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2609398 (q : int) (n : nat) : (term1053 q n) = (term1060 q n).
Proof. exact (MK_COMB (@lem2609397) (@lem2609396 q n)). Qed.
Lemma lem2609403 (q : int) (n : nat) : (term1060 q n) = (term1053 q n).
Proof. exact (SYM (@lem2609398 q n)). Qed.
Lemma lem2609404 (m : nat) : term685 m.
Proof. exact (@lem2307247 m). Qed.
Lemma lem2609405 (m : nat) : (term685 m) = (term686 m).
Proof. exact (eq_refl (term685 m)). Qed.
Lemma lem2609406 (m : nat) : term686 m.
Proof. exact (EQ_MP (@lem2609405 m) (@lem2609404 m)). Qed.
Lemma lem2609407 (m : nat) (n : nat) : term687 m n.
Proof. exact (@lem2609406 m n). Qed.
Lemma lem2609408 (m : nat) (n : nat) : (term687 m n) = ((term688 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term687 m n)). Qed.
Lemma lem2609410 (x : int) : term1061 x.
Proof. exact (@lem2304244 x). Qed.
Lemma lem2609411 (x : int) : (term1061 x) = (term1062 x).
Proof. exact (eq_refl (term1061 x)). Qed.
Lemma lem2609412 (x : int) : term1062 x.
Proof. exact (EQ_MP (@lem2609411 x) (@lem2609410 x)). Qed.
Lemma lem2609413 (x : int) (y : int) : term1063 x y.
Proof. exact (@lem2609412 x y). Qed.
Lemma lem2609414 (x : int) (y : int) : (term1063 x y) = (term1064 x y).
Proof. exact (eq_refl (term1063 x y)). Qed.
Lemma lem2609415 (x : int) (y : int) : term1064 x y.
Proof. exact (EQ_MP (@lem2609414 x y) (@lem2609413 x y)). Qed.
Lemma lem2609416 (x : int) (y : int) (z : int) : term1065 x y z.
Proof. exact (@lem2609415 x y z). Qed.
Lemma lem2609417 (z : int) (x : int) (y : int) : (term1065 x y z) = (term1066 z x y).
Proof. exact (eq_refl (term1065 x y z)). Qed.
Lemma lem2609418 (z : int) (x : int) (y : int) : term1066 z x y.
Proof. exact (EQ_MP (@lem2609417 z x y) (@lem2609416 x y z)). Qed.
Lemma lem2609419 (z : int) (h1 : term1067 z) : term1067 z.
Proof. exact (h1). Qed.
Lemma lem2609420 (x : int) (y : int) (z : int) (h1 : term1067 z) : (term1068 x z y) = (int_lt x y).
Proof. exact (@lem2609418 z x y (@lem2609419 z h1)). Qed.
Lemma lem2609426 (n : nat) : (term812 n) = ((term812 n) = True).
Proof. exact (@lem7 (term812 n)). Qed.
Lemma lem2609449 (z : int) (x : int) (y : int) : term1066 z x y.
Proof. exact (fun h0 : term1067 z => @lem2609420 x y z h0). Qed.
Lemma lem2609450 (n : nat) (q : int) (c : int) : term1069 n q c.
Proof. exact (@lem2609449 (int_of_num n) (int_neg q) c). Qed.
Lemma lem2609452 (m : nat) (n : nat) : (term688 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem2609408 m n) (@lem2609407 m n)). Qed.
Lemma lem2609453 (n : nat) : (term795 n) = (term812 n).
Proof. exact (@lem2609452 (NUMERAL 0) n). Qed.
Lemma lem2609455 (n : nat) (h1 : term812 n) : (term812 n) = True.
Proof. exact (EQ_MP (@lem2609426 n) (@lem2609006 n h1)). Qed.
Lemma lem2609456 (n : nat) (h1 : term812 n) : (term795 n) = True.
Proof. exact (TRANS (@lem2609453 n) (@lem2609455 n h1)). Qed.
Lemma lem2609457 (n : nat) (h1 : term812 n) : True = (term795 n).
Proof. exact (SYM (@lem2609456 n h1)). Qed.
Lemma lem2609458 (n : nat) (h1 : term812 n) : term795 n.
Proof. exact (EQ_MP (@lem2609457 n h1) (@lem0)). Qed.
Lemma lem2609459 (q : int) (c : int) (n : nat) (h1 : term812 n) : (term1058 q n c) = (term992 q c).
Proof. exact (@lem2609450 n q c (@lem2609458 n h1)). Qed.
Lemma lem2609460 (q : int) (c : int) : (term994 q c) = (term994 q c).
Proof. exact (eq_refl (term994 q c)). Qed.
Lemma lem2609461 (q : int) (c : int) (n : nat) (h1 : term812 n) : ((term992 q c) = (term1058 q n c)) = ((term992 q c) = (term992 q c)).
Proof. exact (MK_COMB (@lem2609460 q c) (@lem2609459 q c n h1)). Qed.
Lemma lem2609463 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2609464 (x : Prop) : (x = x) = True.
Proof. exact (@lem2609463 Prop x). Qed.
Lemma lem2609465 (q : int) (c : int) : ((term992 q c) = (term992 q c)) = True.
Proof. exact (@lem2609464 (term992 q c)). Qed.
Lemma lem2609466 (q : int) (c : int) (n : nat) (h1 : term812 n) : ((term992 q c) = (term1058 q n c)) = True.
Proof. exact (TRANS (@lem2609461 q c n h1) (@lem2609465 q c)). Qed.
Lemma lem2609467 (q : int) (n : nat) (h1 : term812 n) : (term1059 q n) = term781.
Proof. exact (fun_ext (fun c : int => @lem2609466 q c n h1)). Qed.
Lemma lem2609468 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2609469 (q : int) (n : nat) (h1 : term812 n) : (term1060 q n) = term783.
Proof. exact (MK_COMB (@lem2609468) (@lem2609467 q n h1)). Qed.
Lemma lem2609471 {A : Type'} (t : Prop) : (term784 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2609472 (t : Prop) : (term785 t) = t.
Proof. exact (@lem2609471 int t). Qed.
Lemma lem2609473 : term783 = True.
Proof. exact (@lem2609472 True). Qed.
Lemma lem2609474 (q : int) (n : nat) (h1 : term812 n) : (term1060 q n) = True.
Proof. exact (TRANS (@lem2609469 q n h1) (@lem2609473)). Qed.
Lemma lem2609475 (q : int) (n : nat) (h1 : term812 n) : True = (term1060 q n).
Proof. exact (SYM (@lem2609474 q n h1)). Qed.
Lemma lem2609476 (q : int) (n : nat) (h1 : term812 n) : term1060 q n.
Proof. exact (EQ_MP (@lem2609475 q n h1) (@lem0)). Qed.
Lemma lem2609477 (q : int) (n : nat) (h1 : term812 n) : term1053 q n.
Proof. exact (EQ_MP (@lem2609403 q n) (@lem2609476 q n h1)). Qed.
Lemma lem2609478 (m : nat) (q : int) (n : nat) (h1 : term812 n) : term1056 m q n.
Proof. exact (fun h0 : term1042 m q n => @lem2609477 q n h1). Qed.
Lemma lem2609479 (q : int) (r : int) (m : nat) (n : nat) (h1 : term812 n) (h2 : (term601 m n) = r) (h3 : (term601 m n) = term527) : term1016 r q m n.
Proof. exact (EQ_MP (@lem2609378 q r m n h1 h2 h3) (@lem2609478 m q n h1)). Qed.
Lemma lem2609480 (q : int) (r : int) (m : nat) (n : nat) (h1 : term812 n) (h2 : (term601 m n) = r) (h3 : (term601 m n) = term527) : ((term601 m n) = r) = (term1016 r q m n).
Proof. exact (prop_ext (fun h4 : (term601 m n) = r => @lem2609479 q r m n h1 h2 h3) (fun h4 : term1016 r q m n => @lem2609004 m n r h2)). Qed.
Lemma lem2609481 (q : int) (r : int) (m : nat) (n : nat) (h1 : term812 n) (h2 : (term601 m n) = r) (h3 : (term601 m n) = term527) : term1016 r q m n.
Proof. exact (EQ_MP (@lem2609480 q r m n h1 h2 h3) (@lem2609004 m n r h2)). Qed.
Lemma lem2609482 (q : int) (r : int) (m : nat) (n : nat) (h1 : term812 n) (h2 : (term601 m n) = r) (h3 : (term601 m n) = term527) : term999 q m n.
Proof. exact (EQ_MP (@lem2609046 q m n r h2) (@lem2609481 q r m n h1 h2 h3)). Qed.
Lemma lem2609483 (q : int) (r : int) (m : nat) (n : nat) (h1 : term812 n) (h2 : (term601 m n) = r) (h3 : (term601 m n) = term527) : (term812 n) = (term999 q m n).
Proof. exact (prop_ext (fun h4 : term812 n => @lem2609482 q r m n h1 h2 h3) (fun h4 : term999 q m n => @lem2609006 n h1)). Qed.
Lemma lem2609484 (q : int) (r : int) (m : nat) (n : nat) (h1 : term812 n) (h2 : (term601 m n) = r) (h3 : (term601 m n) = term527) : term999 q m n.
Proof. exact (EQ_MP (@lem2609483 q r m n h1 h2 h3) (@lem2609006 n h1)). Qed.
Lemma lem2609485 (q : int) (m : nat) (n : nat) (h1 : term812 n) (h2 : (term601 m n) = term527) : term999 q m n.
Proof. exact (ex_elim (@lem2606755 m n) (fun r : int => fun h0 : term603 m n r => @lem2609484 q r m n h1 h0 h2)). Qed.
Lemma lem2609486 (q : int) (m : nat) (n : nat) (h1 : term812 n) (h2 : (term598 m n) = q) (h3 : (term601 m n) = term527) : term998 m n.
Proof. exact (EQ_MP (@lem2609003 m n q h2) (@lem2609485 q m n h1 h3)). Qed.
Lemma lem2609487 (q : int) (m : nat) (n : nat) (h1 : term812 n) (h2 : (term598 m n) = q) (h3 : (term601 m n) = term527) : ((term601 m n) = term527) = (term998 m n).
Proof. exact (prop_ext (fun h4 : (term601 m n) = term527 => @lem2609486 q m n h1 h2 h3) (fun h4 : term998 m n => @lem2608966 m n h3)). Qed.
Lemma lem2609488 (q : int) (m : nat) (n : nat) (h1 : term812 n) (h2 : (term598 m n) = q) (h3 : (term601 m n) = term527) : term998 m n.
Proof. exact (EQ_MP (@lem2609487 q m n h1 h2 h3) (@lem2608966 m n h3)). Qed.
Lemma lem2609489 (q : int) (m : nat) (n : nat) (h1 : term812 n) (h2 : (term598 m n) = q) (h3 : (term601 m n) = term527) : (term812 n) = (term998 m n).
Proof. exact (prop_ext (fun h4 : term812 n => @lem2609488 q m n h1 h2 h3) (fun h4 : term998 m n => @lem2608962 n h1)). Qed.
Lemma lem2609490 (q : int) (m : nat) (n : nat) (h1 : term812 n) (h2 : (term598 m n) = q) (h3 : (term601 m n) = term527) : term998 m n.
Proof. exact (EQ_MP (@lem2609489 q m n h1 h2 h3) (@lem2608962 n h1)). Qed.
Lemma lem2609491 (m : nat) (n : nat) (h1 : term812 n) (h2 : (term601 m n) = term527) : term998 m n.
Proof. exact (ex_elim (@lem2606747 m n) (fun q : int => fun h0 : term600 m n q => @lem2609490 q m n h1 h0 h2)). Qed.
Lemma lem2609607 (m : nat) : term685 m.
Proof. exact (@lem2307247 m). Qed.
Lemma lem2609608 (m : nat) : (term685 m) = (term686 m).
Proof. exact (eq_refl (term685 m)). Qed.
Lemma lem2609609 (m : nat) : term686 m.
Proof. exact (EQ_MP (@lem2609608 m) (@lem2609607 m)). Qed.
Lemma lem2609610 (m : nat) (n : nat) : term687 m n.
Proof. exact (@lem2609609 m n). Qed.
Lemma lem2609611 (m : nat) (n : nat) : (term687 m n) = ((term688 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term687 m n)). Qed.
Lemma lem2609613 (x : int) : term1070 x.
Proof. exact (@lem2309043 x). Qed.
Lemma lem2609614 (x : int) : (term1070 x) = ((int_sgn x) = (term1071 x)).
Proof. exact (eq_refl (term1070 x)). Qed.
Lemma lem2609616 (n : nat) : (term812 n) = ((term812 n) = True).
Proof. exact (@lem7 (term812 n)). Qed.
Lemma lem2609644 (x : int) : (int_sgn x) = (term1071 x).
Proof. exact (EQ_MP (@lem2609614 x) (@lem2609613 x)). Qed.
Lemma lem2609645 (n : nat) : (term1072 n) = (term1073 n).
Proof. exact (@lem2609644 (int_of_num n)). Qed.
Lemma lem2609647 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term1074 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem2609648 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term1075 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem2609647 _2963 g t e g' t' e'). Qed.
Lemma lem2609649 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term1076 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem2609648 _2963 g t e g' t'). Qed.
Lemma lem2609650 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term1077 _2963 g t e.
Proof. exact (fun g' : Prop => @lem2609649 _2963 g t e g'). Qed.
Lemma lem2609651 (g : Prop) (t : int) (e : int) : term1078 g t e.
Proof. exact (@lem2609650 int g t e). Qed.
Lemma lem2609652 (n : nat) : term1079 n.
Proof. exact (@lem2609651 (term795 n) term58 (term1080 n)). Qed.
Lemma lem2609653 (n : nat) (g' : Prop) : term1081 n g'.
Proof. exact (@lem2609652 n g'). Qed.
Lemma lem2609654 (n : nat) (g' : Prop) : (term1081 n g') = (term1082 n g').
Proof. exact (eq_refl (term1081 n g')). Qed.
Lemma lem2609655 (n : nat) (g' : Prop) : term1082 n g'.
Proof. exact (EQ_MP (@lem2609654 n g') (@lem2609653 n g')). Qed.
Lemma lem2609656 (n : nat) (g' : Prop) (t' : int) : term1083 n g' t'.
Proof. exact (@lem2609655 n g' t'). Qed.
Lemma lem2609657 (n : nat) (g' : Prop) (t' : int) : (term1083 n g' t') = (term1084 n g' t').
Proof. exact (eq_refl (term1083 n g' t')). Qed.
Lemma lem2609658 (n : nat) (g' : Prop) (t' : int) : term1084 n g' t'.
Proof. exact (EQ_MP (@lem2609657 n g' t') (@lem2609656 n g' t')). Qed.
Lemma lem2609659 (n : nat) (g' : Prop) (t' : int) (e' : int) : term1085 n g' t' e'.
Proof. exact (@lem2609658 n g' t' e'). Qed.
Lemma lem2609660 (n : nat) (g' : Prop) (t' : int) (e' : int) : (term1085 n g' t' e') = (term1086 n g' t' e').
Proof. exact (eq_refl (term1085 n g' t' e')). Qed.
Lemma lem2609661 (n : nat) (g' : Prop) (t' : int) (e' : int) : term1086 n g' t' e'.
Proof. exact (EQ_MP (@lem2609660 n g' t' e') (@lem2609659 n g' t' e')). Qed.
Lemma lem2609663 (m : nat) (n : nat) : (term688 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem2609611 m n) (@lem2609610 m n)). Qed.
Lemma lem2609664 (n : nat) : (term795 n) = (term812 n).
Proof. exact (@lem2609663 (NUMERAL 0) n). Qed.
Lemma lem2609666 (n : nat) (h1 : term812 n) : (term812 n) = True.
Proof. exact (EQ_MP (@lem2609616 n) (@lem2608394 n h1)). Qed.
Lemma lem2609667 (n : nat) (h1 : term812 n) : (term795 n) = True.
Proof. exact (TRANS (@lem2609664 n) (@lem2609666 n h1)). Qed.
Lemma lem2609668 (n : nat) (t' : int) (e' : int) : term1087 n t' e'.
Proof. exact (@lem2609661 n True t' e'). Qed.
Lemma lem2609669 (t' : int) (e' : int) (n : nat) (h1 : term812 n) : term1088 n t' e'.
Proof. exact (@lem2609668 n t' e' (@lem2609667 n h1)). Qed.
Lemma lem2609675 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem2609676 : term1089.
Proof. exact (fun h0 : True => @lem2609675). Qed.
Lemma lem2609677 (e' : int) (n : nat) (h1 : term812 n) : term1090 n e'.
Proof. exact (@lem2609669 term58 e' n h1). Qed.
Lemma lem2609678 (e' : int) (n : nat) (h1 : term812 n) : term1091 n e'.
Proof. exact (@lem2609677 e' n h1 (@lem2609676)). Qed.
Lemma lem2609683 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term1074 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem2609684 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term1075 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem2609683 _2963 g t e g' t' e'). Qed.
Lemma lem2609685 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term1076 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem2609684 _2963 g t e g' t'). Qed.
Lemma lem2609686 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term1077 _2963 g t e.
Proof. exact (fun g' : Prop => @lem2609685 _2963 g t e g'). Qed.
Lemma lem2609687 (g : Prop) (t : int) (e : int) : term1078 g t e.
Proof. exact (@lem2609686 int g t e). Qed.
Lemma lem2609688 (n : nat) : term1092 n.
Proof. exact (@lem2609687 (term1093 n) term1094 term527). Qed.
Lemma lem2609689 (n : nat) (g' : Prop) : term1095 n g'.
Proof. exact (@lem2609688 n g'). Qed.
Lemma lem2609690 (n : nat) (g' : Prop) : (term1095 n g') = (term1096 n g').
Proof. exact (eq_refl (term1095 n g')). Qed.
Lemma lem2609691 (n : nat) (g' : Prop) : term1096 n g'.
Proof. exact (EQ_MP (@lem2609690 n g') (@lem2609689 n g')). Qed.
Lemma lem2609692 (n : nat) (g' : Prop) (t' : int) : term1097 n g' t'.
Proof. exact (@lem2609691 n g' t'). Qed.
Lemma lem2609693 (n : nat) (g' : Prop) (t' : int) : (term1097 n g' t') = (term1098 n g' t').
Proof. exact (eq_refl (term1097 n g' t')). Qed.
Lemma lem2609694 (n : nat) (g' : Prop) (t' : int) : term1098 n g' t'.
Proof. exact (EQ_MP (@lem2609693 n g' t') (@lem2609692 n g' t')). Qed.
Lemma lem2609695 (n : nat) (g' : Prop) (t' : int) (e' : int) : term1099 n g' t' e'.
Proof. exact (@lem2609694 n g' t' e'). Qed.
Lemma lem2609696 (n : nat) (g' : Prop) (t' : int) (e' : int) : (term1099 n g' t' e') = (term1100 n g' t' e').
Proof. exact (eq_refl (term1099 n g' t' e')). Qed.
Lemma lem2609697 (n : nat) (g' : Prop) (t' : int) (e' : int) : term1100 n g' t' e'.
Proof. exact (EQ_MP (@lem2609696 n g' t' e') (@lem2609695 n g' t' e')). Qed.
Lemma lem2609699 (m : nat) (n : nat) : (term688 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem2609611 m n) (@lem2609610 m n)). Qed.
Lemma lem2609700 (n : nat) : (term1093 n) = (term1101 n).
Proof. exact (@lem2609699 n (NUMERAL 0)). Qed.
Lemma lem2609701 (n : nat) (t' : int) (e' : int) : term1102 n t' e'.
Proof. exact (@lem2609697 n (term1101 n) t' e'). Qed.
Lemma lem2609702 (n : nat) (t' : int) (e' : int) : term1103 n t' e'.
Proof. exact (@lem2609701 n t' e' (@lem2609700 n)). Qed.
Lemma lem2609706 : term1094 = term1094.
Proof. exact (eq_refl term1094). Qed.
Lemma lem2609707 (n : nat) : term1104 n.
Proof. exact (fun h0 : term1101 n => @lem2609706). Qed.
Lemma lem2609708 (n : nat) (e' : int) : term1105 n e'.
Proof. exact (@lem2609702 n term1094 e'). Qed.
Lemma lem2609709 (n : nat) (e' : int) : term1106 n e'.
Proof. exact (@lem2609708 n e' (@lem2609707 n)). Qed.
Lemma lem2609713 : term527 = term527.
Proof. exact (eq_refl term527). Qed.
Lemma lem2609714 (n : nat) : term1107 n.
Proof. exact (fun h0 : term1108 n => @lem2609713). Qed.
Lemma lem2609715 (n : nat) : term1109 n.
Proof. exact (@lem2609709 n term527). Qed.
Lemma lem2609716 (n : nat) : (term1080 n) = (term1110 n).
Proof. exact (@lem2609715 n (@lem2609714 n)). Qed.
Lemma lem2609750 (n : nat) : term1111 n.
Proof. exact (fun h0 : ~ True => @lem2609716 n). Qed.
Lemma lem2609751 (n : nat) (h1 : term812 n) : term1112 n.
Proof. exact (@lem2609678 (term1110 n) n h1). Qed.
Lemma lem2609752 (n : nat) (h1 : term812 n) : (term1073 n) = (term1113 n).
Proof. exact (@lem2609751 n h1 (@lem2609750 n)). Qed.
Lemma lem2609754 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem2609755 (t2 : int) (t1 : int) : (@COND int True t1 t2) = t1.
Proof. exact (@lem2609754 int t2 t1). Qed.
Lemma lem2609756 (n : nat) : (term1113 n) = term58.
Proof. exact (@lem2609755 (term1110 n) term58). Qed.
Lemma lem2609757 (n : nat) (h1 : term812 n) : (term1073 n) = term58.
Proof. exact (TRANS (@lem2609752 n h1) (@lem2609756 n)). Qed.
Lemma lem2609758 (n : nat) (h1 : term812 n) : (term1072 n) = term58.
Proof. exact (TRANS (@lem2609645 n) (@lem2609757 n h1)). Qed.
Lemma lem2609759 (m : nat) (n : nat) : (term1114 m n) = (term1114 m n).
Proof. exact (eq_refl (term1114 m n)). Qed.
Lemma lem2609760 (m : nat) (n : nat) (h1 : term812 n) : (term956 m n) = (term1115 m n).
Proof. exact (MK_COMB (@lem2609759 m n) (@lem2609758 n h1)). Qed.
Lemma lem2609761 : int_lt = int_lt.
Proof. exact (eq_refl int_lt). Qed.
Lemma lem2609762 (m : nat) (n : nat) (h1 : term812 n) : (term1116 m n) = (term1117 m n).
Proof. exact (MK_COMB (@lem2609761) (@lem2609760 m n h1)). Qed.
Lemma lem2609763 (c : int) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem2609764 (m : nat) (c : int) (n : nat) (h1 : term812 n) : (term1118 m n c) = (term1119 m n c).
Proof. exact (MK_COMB (@lem2609762 m n h1) (@lem2609763 c)). Qed.
Lemma lem2609765 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2609766 (m : nat) (c : int) (n : nat) (h1 : term812 n) : (term1120 m n c) = (term1121 m n c).
Proof. exact (MK_COMB (@lem2609765) (@lem2609764 m c n h1)). Qed.
Lemma lem2609767 (m : nat) (n : nat) (c : int) : (term944 m n c) = (term944 m n c).
Proof. exact (eq_refl (term944 m n c)). Qed.
Lemma lem2609768 (m : nat) (c : int) (n : nat) (h1 : term812 n) : ((term1118 m n c) = (term944 m n c)) = ((term1119 m n c) = (term944 m n c)).
Proof. exact (MK_COMB (@lem2609766 m c n h1) (@lem2609767 m n c)). Qed.
Lemma lem2609771 (m : nat) (n : nat) (h1 : term812 n) : (term1122 m n) = (term1123 m n).
Proof. exact (fun_ext (fun c : int => @lem2609768 m c n h1)). Qed.
Lemma lem2609774 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2609775 (m : nat) (n : nat) (h1 : term812 n) : (term958 m n) = (term1124 m n).
Proof. exact (MK_COMB (@lem2609774) (@lem2609771 m n h1)). Qed.
Lemma lem2609782 (m : nat) (n : nat) (h1 : term812 n) : (term1124 m n) = (term958 m n).
Proof. exact (SYM (@lem2609775 m n h1)). Qed.
Lemma lem2609790 (x : int) (z : int) (y : int) : (term509 x y z) = (term510 x z y).
Proof. exact (EQ_MP (@lem2605891 x z y) (@lem2605890 x y z)). Qed.
Lemma lem2609791 (m : nat) (n : nat) (c : int) : (term1119 m n c) = (term1125 m n c).
Proof. exact (@lem2609790 (term955 m n) c term58). Qed.
Lemma lem2609793 (x : int) (y : int) : (term493 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2605882 x y) (@lem2605881 x y)). Qed.
Lemma lem2609794 (m : nat) (n : nat) (c : int) : (term1125 m n c) = (term1126 m n c).
Proof. exact (@lem2609793 (term955 m n) c). Qed.
Lemma lem2609795 (m : nat) (n : nat) (c : int) : (term1119 m n c) = (term1126 m n c).
Proof. exact (TRANS (@lem2609791 m n c) (@lem2609794 m n c)). Qed.
Lemma lem2609796 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2609797 (m : nat) (n : nat) (c : int) : (term1121 m n c) = (term1127 m n c).
Proof. exact (MK_COMB (@lem2609796) (@lem2609795 m n c)). Qed.
Lemma lem2609798 (m : nat) (n : nat) (c : int) : (term944 m n c) = (term944 m n c).
Proof. exact (eq_refl (term944 m n c)). Qed.
Lemma lem2609799 (m : nat) (n : nat) (c : int) : ((term1119 m n c) = (term944 m n c)) = ((term1126 m n c) = (term944 m n c)).
Proof. exact (MK_COMB (@lem2609797 m n c) (@lem2609798 m n c)). Qed.
Lemma lem2609802 (m : nat) (n : nat) : (term1123 m n) = (term1128 m n).
Proof. exact (fun_ext (fun c : int => @lem2609799 m n c)). Qed.
Lemma lem2609803 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2609804 (m : nat) (n : nat) : (term1124 m n) = (term1129 m n).
Proof. exact (MK_COMB (@lem2609803) (@lem2609802 m n)). Qed.
Lemma lem2609809 (m : nat) (n : nat) : (term1129 m n) = (term1124 m n).
Proof. exact (SYM (@lem2609804 m n)). Qed.
Lemma lem2609812 (n' : nat) (n : nat) (h1 : term838 n) : term1130 n n'.
Proof. exact (@lem2608876 n h1 n'). Qed.
Lemma lem2609813 (n' : nat) (n : nat) : (term1130 n n') = (term834 n' n).
Proof. exact (eq_refl (term1130 n n')). Qed.
Lemma lem2609814 (n' : nat) (n : nat) (h1 : term838 n) : term834 n' n.
Proof. exact (EQ_MP (@lem2609813 n' n) (@lem2609812 n' n h1)). Qed.
Lemma lem2609815 (n' : nat) (c : int) (n : nat) (h1 : term838 n) : term852 n' n c.
Proof. exact (@lem2609814 n' n h1 c). Qed.
Lemma lem2609816 (n' : nat) (n : nat) (c : int) : (term852 n' n c) = ((term853 n' n c) = (term854 n' n c)).
Proof. exact (eq_refl (term852 n' n c)). Qed.
Lemma lem2609838 (a : int) (b : int) : (term424 a b) = (term425 a b).
Proof. exact (EQ_MP (@lem2604433 a b) (@lem2605862 a b)). Qed.
Lemma lem2609839 (m : nat) (n : nat) (c : int) : (term1126 m n c) = (term1131 m n c).
Proof. exact (@lem2609838 (term598 m n) c). Qed.
Lemma lem2609841 (n' : nat) (c : int) (n : nat) (h1 : term838 n) : (term853 n' n c) = (term854 n' n c).
Proof. exact (EQ_MP (@lem2609816 n' n c) (@lem2609815 n' c n h1)). Qed.
Lemma lem2609842 (m : nat) (c : int) (n : nat) (h1 : term838 n) : (term1132 m n c) = (term1133 m n c).
Proof. exact (@lem2609841 m (int_neg c) n h1). Qed.
Lemma lem2609843 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2609844 (m : nat) (c : int) (n : nat) (h1 : term838 n) : (term1131 m n c) = (term1134 m n c).
Proof. exact (MK_COMB (@lem2609843) (@lem2609842 m c n h1)). Qed.
Lemma lem2609845 (m : nat) (c : int) (n : nat) (h1 : term838 n) : (term1126 m n c) = (term1134 m n c).
Proof. exact (TRANS (@lem2609839 m n c) (@lem2609844 m c n h1)). Qed.
Lemma lem2609846 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2609847 (m : nat) (c : int) (n : nat) (h1 : term838 n) : (term1127 m n c) = (term1135 m n c).
Proof. exact (MK_COMB (@lem2609846) (@lem2609845 m c n h1)). Qed.
Lemma lem2609848 (m : nat) (n : nat) (c : int) : (term944 m n c) = (term944 m n c).
Proof. exact (eq_refl (term944 m n c)). Qed.
Lemma lem2609849 (m : nat) (c : int) (n : nat) (h1 : term838 n) : ((term1126 m n c) = (term944 m n c)) = ((term1134 m n c) = (term944 m n c)).
Proof. exact (MK_COMB (@lem2609847 m c n h1) (@lem2609848 m n c)). Qed.
Lemma lem2609852 (m : nat) (n : nat) (h1 : term838 n) : (term1128 m n) = (term1136 m n).
Proof. exact (fun_ext (fun c : int => @lem2609849 m c n h1)). Qed.
Lemma lem2609853 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2609854 (m : nat) (n : nat) (h1 : term838 n) : (term1129 m n) = (term1137 m n).
Proof. exact (MK_COMB (@lem2609853) (@lem2609852 m n h1)). Qed.
Lemma lem2609859 (m : nat) (n : nat) (h1 : term838 n) : (term1137 m n) = (term1129 m n).
Proof. exact (SYM (@lem2609854 m n h1)). Qed.
Lemma lem2609865 (m : int) (n : int) (c : int) : ((term1 m n c) = (term2 m n c)) = (term3 m n c).
Proof. exact (EQ_MP (@lem2599948 m n c) (@lem2604431 m n c)). Qed.
Lemma lem2609866 (m : nat) (n : nat) (c : int) : ((term1134 m n c) = (term944 m n c)) = (term1138 m n c).
Proof. exact (@lem2609865 (int_of_num m) (int_of_num n) c). Qed.
Lemma lem2609869 (m : nat) (n : nat) : (term1136 m n) = (term1139 m n).
Proof. exact (fun_ext (fun c : int => @lem2609866 m n c)). Qed.
Lemma lem2609870 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2609871 (m : nat) (n : nat) : (term1137 m n) = (term1140 m n).
Proof. exact (MK_COMB (@lem2609870) (@lem2609869 m n)). Qed.
Lemma lem2609876 (m : nat) (n : nat) : (term1140 m n) = (term1137 m n).
Proof. exact (SYM (@lem2609871 m n)). Qed.
Lemma lem2609878 (p : Prop) : p = (term1141 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2609879 (m : nat) (n : nat) : (term1140 m n) = (term1142 m n).
Proof. exact (@lem2609878 (term1140 m n)). Qed.
Lemma lem2609880 (m : nat) (n : nat) : (term1142 m n) = (term1140 m n).
Proof. exact (SYM (@lem2609879 m n)). Qed.
Lemma lem2609881 (m : nat) (n : nat) (h1 : term1143 m n) : term1143 m n.
Proof. exact (h1). Qed.
Lemma lem2609884 (m : nat) (n : nat) (h1 : term1144 m n) : term1144 m n.
Proof. exact (h1). Qed.
Lemma lem2609885 (m : nat) (n : nat) : term1145 m n.
Proof. exact (fun h0 : term1144 m n => @lem2609884 m n h0). Qed.
Lemma lem2609886 (m : nat) (n : nat) (h1 : term1145 m n) : term1145 m n.
Proof. exact (h1). Qed.
Lemma lem2609887 (m : nat) (n : nat) (h1 : term1144 m n) : term1144 m n.
Proof. exact (h1). Qed.
Lemma lem2609888 (m : nat) (n : nat) (h1 : term1144 m n) (h2 : term1145 m n) : term1144 m n.
Proof. exact (@lem2609886 m n h2 (@lem2609887 m n h1)). Qed.
Lemma lem2609889 (m : nat) (n : nat) (h1 : term1144 m n) : term1146 m n.
Proof. exact (fun h0 : term1145 m n => @lem2609888 m n h1 h0). Qed.
Lemma lem2609890 (m : nat) (n : nat) (h1 : term1145 m n) : term1145 m n.
Proof. exact (h1). Qed.
Lemma lem2609891 (m : nat) (n : nat) (h1 : term1144 m n) (h2 : term1145 m n) : term1144 m n.
Proof. exact (@lem2609889 m n h1 (@lem2609890 m n h2)). Qed.
Lemma lem2609892 (m : nat) (n : nat) (h1 : term1145 m n) : term1145 m n.
Proof. exact (fun h0 : term1144 m n => @lem2609891 m n h0 h1). Qed.
Lemma lem2609893 (m : nat) (n : nat) : term1147 m n.
Proof. exact (fun h0 : term1145 m n => @lem2609892 m n h0). Qed.
Lemma lem2609896 (m : nat) (n : nat) : term1145 m n.
Proof. exact (@lem2609893 m n (@lem2609885 m n)). Qed.
Lemma lem2609926 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem2609927 : term1148 = term1149.
Proof. exact (@lem2609926 term1150). Qed.
Lemma lem2609946 (m : nat) (n : nat) : (term1151 m n) = (term1151 m n).
Proof. exact (eq_refl (term1151 m n)). Qed.
Lemma lem2609947 (m : nat) (n : nat) : (term1152 m n) = (term1153 m n).
Proof. exact (MK_COMB (@lem2609946 m n) (@lem2609927)). Qed.
Lemma lem2609950 (m : nat) (n : nat) : (term959 m n) = (term959 m n).
Proof. exact (eq_refl (term959 m n)). Qed.
Lemma lem2609951 (m : nat) (n : nat) : (term1154 m n) = (term1155 m n).
Proof. exact (MK_COMB (@lem2609950 m n) (@lem2609947 m n)). Qed.
Lemma lem2609954 (n : nat) : (term1156 n) = (term1156 n).
Proof. exact (eq_refl (term1156 n)). Qed.
Lemma lem2609955 (m : nat) (n : nat) : (term1157 m n) = (term1158 m n).
Proof. exact (MK_COMB (@lem2609954 n) (@lem2609951 m n)). Qed.
Lemma lem2609958 (n : nat) : (term813 n) = (term813 n).
Proof. exact (eq_refl (term813 n)). Qed.
Lemma lem2609959 (m : nat) (n : nat) : (term1144 m n) = (term1159 m n).
Proof. exact (MK_COMB (@lem2609958 n) (@lem2609955 m n)). Qed.
Lemma lem2609962 (n : nat) : (term1160 n) = (term1161 n).
Proof. exact (fun_ext (fun m : nat => @lem2609959 m n)). Qed.
Lemma lem2609963 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2609964 (n : nat) : (term1162 n) = (term1163 n).
Proof. exact (MK_COMB (@lem2609963) (@lem2609962 n)). Qed.
Lemma lem2609969 : term1164 = term1165.
Proof. exact (fun_ext (fun n : nat => @lem2609964 n)). Qed.
Lemma lem2609970 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2609979 : term1166 = term1167.
Proof. exact (MK_COMB (@lem2609970) (@lem2609969)). Qed.
Lemma lem2609980 (n : int) (m : int) : ((term1168 n m) = term527) = ((term1168 n m) = term527).
Proof. exact (eq_refl ((term1168 n m) = term527)). Qed.
Lemma lem2609981 (m : int) : (term1169 m) = (term1169 m).
Proof. exact (fun_ext (fun n : int => @lem2609980 n m)). Qed.
Lemma lem2609982 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2609983 (m : int) : (term1170 m) = (term1170 m).
Proof. exact (MK_COMB (@lem2609982) (@lem2609981 m)). Qed.
Lemma lem2609984 : term1171 = term1171.
Proof. exact (fun_ext (fun m : int => @lem2609983 m)). Qed.
Lemma lem2609985 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2609986 : term1172 = term1172.
Proof. exact (MK_COMB (@lem2609985) (@lem2609984)). Qed.
Lemma lem2609987 (m : int) (n : int) : ((term1173 m n) = term527) = ((term1173 m n) = term527).
Proof. exact (eq_refl ((term1173 m n) = term527)). Qed.
Lemma lem2609988 (m : int) : (term1174 m) = (term1174 m).
Proof. exact (fun_ext (fun n : int => @lem2609987 m n)). Qed.
Lemma lem2609989 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2609990 (m : int) : (term1175 m) = (term1175 m).
Proof. exact (MK_COMB (@lem2609989) (@lem2609988 m)). Qed.
Lemma lem2609991 : term1176 = term1176.
Proof. exact (fun_ext (fun m : int => @lem2609990 m)). Qed.
Lemma lem2609992 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2609993 : term1177 = term1177.
Proof. exact (MK_COMB (@lem2609992) (@lem2609991)). Qed.
Lemma lem2609994 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2609995 : term1178 = term1178.
Proof. exact (MK_COMB (@lem2609994) (@lem2609993)). Qed.
Lemma lem2609996 : term1150 = term1150.
Proof. exact (MK_COMB (@lem2609995) (@lem2609986)). Qed.
Lemma lem2609997 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2609998 : term1149 = term1149.
Proof. exact (MK_COMB (@lem2609997) (@lem2609996)). Qed.
Lemma lem2610001 (m : nat) (n : nat) (c : int) : (term1138 m n c) = (term1138 m n c).
Proof. exact (eq_refl (term1138 m n c)). Qed.
Lemma lem2610002 (m : nat) (n : nat) : (term1139 m n) = (term1139 m n).
Proof. exact (fun_ext (fun c : int => @lem2610001 m n c)). Qed.
Lemma lem2610003 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2610004 (m : nat) (n : nat) : (term1140 m n) = (term1140 m n).
Proof. exact (MK_COMB (@lem2610003) (@lem2610002 m n)). Qed.
Lemma lem2610005 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2610006 (m : nat) (n : nat) : (term1143 m n) = (term1143 m n).
Proof. exact (MK_COMB (@lem2610005) (@lem2610004 m n)). Qed.
Lemma lem2610007 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2610008 (m : nat) (n : nat) : (term1151 m n) = (term1151 m n).
Proof. exact (MK_COMB (@lem2610007) (@lem2610006 m n)). Qed.
Lemma lem2610009 (m : nat) (n : nat) : (term1153 m n) = (term1153 m n).
Proof. exact (MK_COMB (@lem2610008 m n) (@lem2609998)). Qed.
Lemma lem2610014 (m : nat) (n : nat) : (term959 m n) = (term959 m n).
Proof. exact (eq_refl (term959 m n)). Qed.
Lemma lem2610015 (m : nat) (n : nat) : (term1155 m n) = (term1155 m n).
Proof. exact (MK_COMB (@lem2610014 m n) (@lem2610009 m n)). Qed.
Lemma lem2610020 (n' : nat) (n : nat) (c : int) : ((term853 n' n c) = (term854 n' n c)) = ((term853 n' n c) = (term854 n' n c)).
Proof. exact (eq_refl ((term853 n' n c) = (term854 n' n c))). Qed.
Lemma lem2610021 (n' : nat) (n : nat) : (term851 n' n) = (term851 n' n).
Proof. exact (fun_ext (fun c : int => @lem2610020 n' n c)). Qed.
Lemma lem2610022 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2610023 (n' : nat) (n : nat) : (term834 n' n) = (term834 n' n).
Proof. exact (MK_COMB (@lem2610022) (@lem2610021 n' n)). Qed.
Lemma lem2610024 (n : nat) : (term836 n) = (term836 n).
Proof. exact (fun_ext (fun n' : nat => @lem2610023 n' n)). Qed.
Lemma lem2610025 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2610026 (n : nat) : (term838 n) = (term838 n).
Proof. exact (MK_COMB (@lem2610025) (@lem2610024 n)). Qed.
Lemma lem2610027 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2610028 (n : nat) : (term1156 n) = (term1156 n).
Proof. exact (MK_COMB (@lem2610027) (@lem2610026 n)). Qed.
Lemma lem2610029 (m : nat) (n : nat) : (term1158 m n) = (term1158 m n).
Proof. exact (MK_COMB (@lem2610028 n) (@lem2610015 m n)). Qed.
Lemma lem2610032 (n : nat) : (term813 n) = (term813 n).
Proof. exact (eq_refl (term813 n)). Qed.
Lemma lem2610033 (m : nat) (n : nat) : (term1159 m n) = (term1159 m n).
Proof. exact (MK_COMB (@lem2610032 n) (@lem2610029 m n)). Qed.
Lemma lem2610034 (n : nat) : (term1161 n) = (term1161 n).
Proof. exact (fun_ext (fun m : nat => @lem2610033 m n)). Qed.
Lemma lem2610035 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2610036 (n : nat) : (term1163 n) = (term1163 n).
Proof. exact (MK_COMB (@lem2610035) (@lem2610034 n)). Qed.
Lemma lem2610037 : term1165 = term1165.
Proof. exact (fun_ext (fun n : nat => @lem2610036 n)). Qed.
Lemma lem2610038 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2610039 : term1167 = term1167.
Proof. exact (MK_COMB (@lem2610038) (@lem2610037)). Qed.
Lemma lem2610106 : term1166 = term1167.
Proof. exact (TRANS (@lem2609979) (@lem2610039)). Qed.
Lemma lem2610107 : term1167 = term1166.
Proof. exact (SYM (@lem2610106)). Qed.
Lemma lem2610111 (m : nat) (n : nat) (h1 : term1143 m n) : term1143 m n.
Proof. exact (h1). Qed.
Lemma lem2610112 (h1 : term1150) : term1150.
Proof. exact (h1). Qed.
Lemma lem2610411 (m : nat) (n : nat) (h1 : term972 m n) : term972 m n.
Proof. exact (h1). Qed.
Lemma lem2610414 (m : nat) (n : nat) (c : int) : (term1179 m n c) = ((int_of_num m) = (term513 n c)).
Proof. exact (@lem16933 ((int_of_num m) = (term513 n c))). Qed.
Lemma lem2610415 (P : int -> Prop) : (term1180 P) = (term1181 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2610416 (m : nat) (n : nat) : (term1143 m n) = (term1182 m n).
Proof. exact (@lem2610415 (term1139 m n)). Qed.
Lemma lem2610417 (m : nat) (n : nat) (c : int) : (term1183 m n c) = (term1138 m n c).
Proof. exact (eq_refl (term1183 m n c)). Qed.
Lemma lem2610418 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2610419 (m : nat) (n : nat) (c : int) : (term1184 m n c) = (term1179 m n c).
Proof. exact (MK_COMB (@lem2610418) (@lem2610417 m n c)). Qed.
Lemma lem2610420 (m : nat) (n : nat) (c : int) : (term1184 m n c) = ((int_of_num m) = (term513 n c)).
Proof. exact (TRANS (@lem2610419 m n c) (@lem2610414 m n c)). Qed.
Lemma lem2610421 (m : nat) (n : nat) : (term1185 m n) = (term1186 m n).
Proof. exact (fun_ext (fun c : int => @lem2610420 m n c)). Qed.
Lemma lem2610422 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2610423 (m : nat) (n : nat) : (term1182 m n) = (term1187 m n).
Proof. exact (MK_COMB (@lem2610422) (@lem2610421 m n)). Qed.
Lemma lem2610432 (m : nat) (n : nat) : (term1143 m n) = (term1187 m n).
Proof. exact (TRANS (@lem2610416 m n) (@lem2610423 m n)). Qed.
Lemma lem2610433 (m : nat) (n : nat) (h1 : term1143 m n) : term1187 m n.
Proof. exact (EQ_MP (@lem2610432 m n) (@lem2610111 m n h1)). Qed.
Lemma lem2610434 (m : int) (n : int) : ((term1173 m n) = term527) = ((term1173 m n) = term527).
Proof. exact (eq_refl ((term1173 m n) = term527)). Qed.
Lemma lem2610435 (m : int) : (term1174 m) = (term1174 m).
Proof. exact (fun_ext (fun n : int => @lem2610434 m n)). Qed.
Lemma lem2610436 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2610437 (m : int) : (term1175 m) = (term1175 m).
Proof. exact (MK_COMB (@lem2610436) (@lem2610435 m)). Qed.
Lemma lem2610438 : term1176 = term1176.
Proof. exact (fun_ext (fun m : int => @lem2610437 m)). Qed.
Lemma lem2610439 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2610440 : term1177 = term1177.
Proof. exact (MK_COMB (@lem2610439) (@lem2610438)). Qed.
Lemma lem2610441 (n : int) (m : int) : ((term1168 n m) = term527) = ((term1168 n m) = term527).
Proof. exact (eq_refl ((term1168 n m) = term527)). Qed.
Lemma lem2610442 (m : int) : (term1169 m) = (term1169 m).
Proof. exact (fun_ext (fun n : int => @lem2610441 n m)). Qed.
Lemma lem2610443 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2610444 (m : int) : (term1170 m) = (term1170 m).
Proof. exact (MK_COMB (@lem2610443) (@lem2610442 m)). Qed.
Lemma lem2610445 : term1171 = term1171.
Proof. exact (fun_ext (fun m : int => @lem2610444 m)). Qed.
Lemma lem2610446 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2610447 : term1172 = term1172.
Proof. exact (MK_COMB (@lem2610446) (@lem2610445)). Qed.
Lemma lem2610448 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2610449 : term1178 = term1178.
Proof. exact (MK_COMB (@lem2610448) (@lem2610440)). Qed.
Lemma lem2610470 : term1150 = term1150.
Proof. exact (MK_COMB (@lem2610449) (@lem2610447)). Qed.
Lemma lem2610471 (h1 : term1150) : term1150.
Proof. exact (EQ_MP (@lem2610470) (@lem2610112 h1)). Qed.
Lemma lem2610578 (m : nat) (n : nat) (h1 : term972 m n) : term972 m n.
Proof. exact (h1). Qed.
Lemma lem2610595 (n : int) (m : int) : ((term1168 n m) = term527) = ((term1168 n m) = term527).
Proof. exact (eq_refl ((term1168 n m) = term527)). Qed.
Lemma lem2610596 (m : int) : (term1169 m) = (term1169 m).
Proof. exact (fun_ext (fun n : int => @lem2610595 n m)). Qed.
Lemma lem2610597 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2610598 (m : int) : (term1170 m) = (term1170 m).
Proof. exact (MK_COMB (@lem2610597) (@lem2610596 m)). Qed.
Lemma lem2610599 : term1171 = term1171.
Proof. exact (fun_ext (fun m : int => @lem2610598 m)). Qed.
Lemma lem2610600 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2610601 : term1172 = term1172.
Proof. exact (MK_COMB (@lem2610600) (@lem2610599)). Qed.
Lemma lem2610618 (m : int) (n : int) : ((term1173 m n) = term527) = ((term1173 m n) = term527).
Proof. exact (eq_refl ((term1173 m n) = term527)). Qed.
Lemma lem2610619 (m : int) : (term1174 m) = (term1174 m).
Proof. exact (fun_ext (fun n : int => @lem2610618 m n)). Qed.
Lemma lem2610620 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2610621 (m : int) : (term1175 m) = (term1175 m).
Proof. exact (MK_COMB (@lem2610620) (@lem2610619 m)). Qed.
Lemma lem2610622 : term1176 = term1176.
Proof. exact (fun_ext (fun m : int => @lem2610621 m)). Qed.
Lemma lem2610623 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2610624 : term1177 = term1177.
Proof. exact (MK_COMB (@lem2610623) (@lem2610622)). Qed.
Lemma lem2610625 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2610626 : term1178 = term1178.
Proof. exact (MK_COMB (@lem2610625) (@lem2610624)). Qed.
Lemma lem2610627 : term1150 = term1150.
Proof. exact (MK_COMB (@lem2610626) (@lem2610601)). Qed.
Lemma lem2610628 (h1 : term1150) : term1150.
Proof. exact (EQ_MP (@lem2610627) (@lem2610471 h1)). Qed.
Lemma lem2610644 (m : nat) (n : nat) (c : int) (h1 : (int_of_num m) = (term513 n c)) : (int_of_num m) = (term513 n c).
Proof. exact (h1). Qed.
Lemma lem2610645 (h1 : term1150) : term1172.
Proof. exact (proj2 (@lem2610628 h1)). Qed.
Lemma lem2610656 (m : nat) (n : nat) (h1 : term972 m n) : term972 m n.
Proof. exact (h1). Qed.
Lemma lem2610660 (m : nat) (n : nat) (c : int) (h1 : (int_of_num m) = (term513 n c)) : (int_of_num m) = (term513 n c).
Proof. exact (h1). Qed.
Lemma lem2610672 (n : int) (m : int) : ((term1168 n m) = term527) = ((term1168 n m) = term527).
Proof. exact (eq_refl ((term1168 n m) = term527)). Qed.
Lemma lem2610673 (m : int) : (term1169 m) = (term1169 m).
Proof. exact (fun_ext (fun n : int => @lem2610672 n m)). Qed.
Lemma lem2610674 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2610675 (m : int) : (term1170 m) = (term1170 m).
Proof. exact (MK_COMB (@lem2610674) (@lem2610673 m)). Qed.
Lemma lem2610676 : term1171 = term1171.
Proof. exact (fun_ext (fun m : int => @lem2610675 m)). Qed.
Lemma lem2610677 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2610679 : term1172 = term1172.
Proof. exact (MK_COMB (@lem2610677) (@lem2610676)). Qed.
Lemma lem2610680 (h1 : term1150) : term1172.
Proof. exact (EQ_MP (@lem2610679) (@lem2610645 h1)). Qed.
Lemma lem2610719 (_30037 : int) (h1 : term1150) : term1188 _30037.
Proof. exact (@lem2610680 h1 _30037). Qed.
Lemma lem2610720 (_30037 : int) : (term1188 _30037) = (term1170 _30037).
Proof. exact (eq_refl (term1188 _30037)). Qed.
Lemma lem2610721 (_30037 : int) (h1 : term1150) : term1170 _30037.
Proof. exact (EQ_MP (@lem2610720 _30037) (@lem2610719 _30037 h1)). Qed.
Lemma lem2610722 (_30037 : int) (_30038 : int) (h1 : term1150) : term1189 _30037 _30038.
Proof. exact (@lem2610721 _30037 h1 _30038). Qed.
Lemma lem2610723 (_30038 : int) (_30037 : int) : (term1189 _30037 _30038) = ((term1168 _30038 _30037) = term527).
Proof. exact (eq_refl (term1189 _30037 _30038)). Qed.
Lemma lem2610740 (m : nat) (n : nat) (h1 : term972 m n) : term972 m n.
Proof. exact (h1). Qed.
Lemma lem2610742 (m : nat) (n : nat) (c : int) (h1 : (int_of_num m) = (term513 n c)) : (int_of_num m) = (term513 n c).
Proof. exact (h1). Qed.
Lemma lem2610835 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2610836 (_30061 : int) (_30063 : int) (h1 : _30061 = _30063) : _30061 = _30063.
Proof. exact (h1). Qed.
Lemma lem2610837 (_30062 : int) (_30064 : int) (h1 : _30062 = _30064) : _30062 = _30064.
Proof. exact (h1). Qed.
Lemma lem2610838 (_30061 : int) (_30063 : int) (h1 : _30061 = _30063) : (rem _30061) = (rem _30063).
Proof. exact (MK_COMB (@lem2610835) (@lem2610836 _30061 _30063 h1)). Qed.
Lemma lem2610839 (_30061 : int) (_30063 : int) (_30062 : int) (_30064 : int) (h1 : _30061 = _30063) (h2 : _30062 = _30064) : (rem _30061 _30062) = (rem _30063 _30064).
Proof. exact (MK_COMB (@lem2610838 _30061 _30063 h1) (@lem2610837 _30062 _30064 h2)). Qed.
Lemma lem2610840 (_30062 : int) (_30064 : int) (_30061 : int) (_30063 : int) (h1 : _30061 = _30063) : term1190 _30061 _30062 _30063 _30064.
Proof. exact (fun h0 : _30062 = _30064 => @lem2610839 _30061 _30063 _30062 _30064 h1 h0). Qed.
Lemma lem2610842 (a : Prop) (b : Prop) : (a -> b) = (term1191 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem2610843 (_30061 : int) (_30062 : int) (_30063 : int) (_30064 : int) : (term1190 _30061 _30062 _30063 _30064) = (term1192 _30061 _30062 _30063 _30064).
Proof. exact (@lem2610842 (_30062 = _30064) ((rem _30061 _30062) = (rem _30063 _30064))). Qed.
Lemma lem2610844 (_30062 : int) (_30064 : int) (_30061 : int) (_30063 : int) (h1 : _30061 = _30063) : term1192 _30061 _30062 _30063 _30064.
Proof. exact (EQ_MP (@lem2610843 _30061 _30062 _30063 _30064) (@lem2610840 _30062 _30064 _30061 _30063 h1)). Qed.
Lemma lem2610845 (_30061 : int) (_30062 : int) (_30063 : int) (_30064 : int) : term1193 _30061 _30062 _30063 _30064.
Proof. exact (fun h0 : _30061 = _30063 => @lem2610844 _30062 _30064 _30061 _30063 h0). Qed.
Lemma lem2610847 (a : Prop) (b : Prop) : (a -> b) = (term1191 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem2610848 (_30061 : int) (_30062 : int) (_30063 : int) (_30064 : int) : (term1193 _30061 _30062 _30063 _30064) = (term1194 _30061 _30062 _30063 _30064).
Proof. exact (@lem2610847 (_30061 = _30063) (term1192 _30061 _30062 _30063 _30064)). Qed.
Lemma lem2610849 (_30061 : int) (_30062 : int) (_30063 : int) (_30064 : int) : term1194 _30061 _30062 _30063 _30064.
Proof. exact (EQ_MP (@lem2610848 _30061 _30062 _30063 _30064) (@lem2610845 _30061 _30062 _30063 _30064)). Qed.
Lemma lem2610869 (x : int) (y : int) (z : int) : term1195 x y z.
Proof. exact (@lem21385 int x y z). Qed.
Lemma lem2610871 (m : nat) (n : nat) (c : int) (h1 : (int_of_num m) = (term513 n c)) : (int_of_num m) = (term513 n c).
Proof. exact (h1). Qed.
Lemma lem2610872 (m : nat) (n : nat) (c : int) (h1 : (int_of_num m) = (term513 n c)) : term1196 m n c.
Proof. exact (fun h0 : term1138 m n c => @lem2610871 m n c h1). Qed.
Lemma lem2610874 (p : Prop) : (term1197 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2610875 (m : nat) (n : nat) (c : int) : (term1196 m n c) = ((int_of_num m) = (term513 n c)).
Proof. exact (@lem2610874 ((int_of_num m) = (term513 n c))). Qed.
Lemma lem2610876 (m : nat) (n : nat) (c : int) (h1 : (int_of_num m) = (term513 n c)) : (int_of_num m) = (term513 n c).
Proof. exact (EQ_MP (@lem2610875 m n c) (@lem2610872 m n c h1)). Qed.
Lemma lem2610878 (x : int) : x = x.
Proof. exact (@lem21386 int x). Qed.
Lemma lem2610879 (n : nat) : (int_of_num n) = (int_of_num n).
Proof. exact (@lem2610878 (int_of_num n)). Qed.
Lemma lem2610880 (n : nat) : term1198 n.
Proof. exact (fun h0 : term1199 n => @lem2610879 n). Qed.
Lemma lem2610882 (p : Prop) : (term1197 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2610883 (n : nat) : (term1198 n) = ((int_of_num n) = (int_of_num n)).
Proof. exact (@lem2610882 ((int_of_num n) = (int_of_num n))). Qed.
Lemma lem2610884 (n : nat) : (int_of_num n) = (int_of_num n).
Proof. exact (EQ_MP (@lem2610883 n) (@lem2610880 n)). Qed.
Lemma lem2610902 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2610903 (_30061 : int) (_30063 : int) (_30062 : int) (_30064 : int) : (term1192 _30061 _30062 _30063 _30064) = (term1200 _30061 _30063 _30062 _30064).
Proof. exact (@lem2610902 ((rem _30061 _30062) = (rem _30063 _30064)) (term100 _30062 _30064)). Qed.
Lemma lem2610913 (_30061 : int) (_30063 : int) : (term1201 _30061 _30063) = (term1201 _30061 _30063).
Proof. exact (eq_refl (term1201 _30061 _30063)). Qed.
Lemma lem2610914 (_30061 : int) (_30063 : int) (_30062 : int) (_30064 : int) : (term1194 _30061 _30062 _30063 _30064) = (term1202 _30061 _30063 _30062 _30064).
Proof. exact (MK_COMB (@lem2610913 _30061 _30063) (@lem2610903 _30061 _30063 _30062 _30064)). Qed.
Lemma lem2610918 (q : Prop) (p : Prop) (r : Prop) : (term1203 p q r) = (term1203 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2610919 (_30061 : int) (_30063 : int) (_30062 : int) (_30064 : int) : (term1202 _30061 _30063 _30062 _30064) = (term1204 _30061 _30063 _30062 _30064).
Proof. exact (@lem2610918 ((rem _30061 _30062) = (rem _30063 _30064)) (term100 _30061 _30063) (term100 _30062 _30064)). Qed.
Lemma lem2610941 (_30061 : int) (_30063 : int) (_30062 : int) (_30064 : int) : (term1194 _30061 _30062 _30063 _30064) = (term1204 _30061 _30063 _30062 _30064).
Proof. exact (TRANS (@lem2610914 _30061 _30063 _30062 _30064) (@lem2610919 _30061 _30063 _30062 _30064)). Qed.
Lemma lem2610942 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2610943 (_30061 : int) (_30063 : int) (_30062 : int) (_30064 : int) : (term1205 _30061 _30062 _30063 _30064) = (term1206 _30061 _30063 _30062 _30064).
Proof. exact (MK_COMB (@lem2610942) (@lem2610941 _30061 _30063 _30062 _30064)). Qed.
Lemma lem2610965 (_30061 : int) (_30063 : int) (_30062 : int) (_30064 : int) : (term1204 _30061 _30063 _30062 _30064) = (term1204 _30061 _30063 _30062 _30064).
Proof. exact (eq_refl (term1204 _30061 _30063 _30062 _30064)). Qed.
Lemma lem2610966 (_30061 : int) (_30063 : int) (_30062 : int) (_30064 : int) : ((term1194 _30061 _30062 _30063 _30064) = (term1204 _30061 _30063 _30062 _30064)) = ((term1204 _30061 _30063 _30062 _30064) = (term1204 _30061 _30063 _30062 _30064)).
Proof. exact (MK_COMB (@lem2610943 _30061 _30063 _30062 _30064) (@lem2610965 _30061 _30063 _30062 _30064)). Qed.
Lemma lem2610968 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2610969 (x : Prop) : (x = x) = True.
Proof. exact (@lem2610968 Prop x). Qed.
Lemma lem2610970 (_30061 : int) (_30063 : int) (_30062 : int) (_30064 : int) : ((term1204 _30061 _30063 _30062 _30064) = (term1204 _30061 _30063 _30062 _30064)) = True.
Proof. exact (@lem2610969 (term1204 _30061 _30063 _30062 _30064)). Qed.
Lemma lem2610971 (_30061 : int) (_30063 : int) (_30062 : int) (_30064 : int) : ((term1194 _30061 _30062 _30063 _30064) = (term1204 _30061 _30063 _30062 _30064)) = True.
Proof. exact (TRANS (@lem2610966 _30061 _30063 _30062 _30064) (@lem2610970 _30061 _30063 _30062 _30064)). Qed.
Lemma lem2610972 (_30061 : int) (_30063 : int) (_30062 : int) (_30064 : int) : True = ((term1194 _30061 _30062 _30063 _30064) = (term1204 _30061 _30063 _30062 _30064)).
Proof. exact (SYM (@lem2610971 _30061 _30063 _30062 _30064)). Qed.
Lemma lem2610973 (_30061 : int) (_30063 : int) (_30062 : int) (_30064 : int) : (term1194 _30061 _30062 _30063 _30064) = (term1204 _30061 _30063 _30062 _30064).
Proof. exact (EQ_MP (@lem2610972 _30061 _30063 _30062 _30064) (@lem0)). Qed.
Lemma lem2610974 (_30061 : int) (_30063 : int) (_30062 : int) (_30064 : int) : term1204 _30061 _30063 _30062 _30064.
Proof. exact (EQ_MP (@lem2610973 _30061 _30063 _30062 _30064) (@lem2610849 _30061 _30062 _30063 _30064)). Qed.
Lemma lem2610976 (b : Prop) (a : Prop) : (a \/ b) = (term1207 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2610977 (_30061 : int) (_30062 : int) (_30063 : int) (_30064 : int) : (term1204 _30061 _30063 _30062 _30064) = (term1208 _30061 _30062 _30063 _30064).
Proof. exact (@lem2610976 (term1209 _30061 _30063 _30062 _30064) ((rem _30061 _30062) = (rem _30063 _30064))). Qed.
Lemma lem2610979 (a : Prop) (b : Prop) : (term1210 a b) = (term1211 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem2610980 (_30061 : int) (_30063 : int) (_30062 : int) (_30064 : int) : (term1212 _30061 _30063 _30062 _30064) = (term1213 _30061 _30063 _30062 _30064).
Proof. exact (@lem2610979 (term100 _30061 _30063) (term100 _30062 _30064)). Qed.
Lemma lem2610982 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2610983 (_30061 : int) (_30063 : int) : (term1214 _30061 _30063) = (_30061 = _30063).
Proof. exact (@lem2610982 (_30061 = _30063)). Qed.
Lemma lem2610984 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2610985 (_30061 : int) (_30063 : int) : (term1215 _30061 _30063) = (term1216 _30061 _30063).
Proof. exact (MK_COMB (@lem2610984) (@lem2610983 _30061 _30063)). Qed.
Lemma lem2610987 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2610988 (_30062 : int) (_30064 : int) : (term1214 _30062 _30064) = (_30062 = _30064).
Proof. exact (@lem2610987 (_30062 = _30064)). Qed.
Lemma lem2610989 (_30061 : int) (_30063 : int) (_30062 : int) (_30064 : int) : (term1213 _30061 _30063 _30062 _30064) = (term1217 _30061 _30063 _30062 _30064).
Proof. exact (MK_COMB (@lem2610985 _30061 _30063) (@lem2610988 _30062 _30064)). Qed.
Lemma lem2610990 (_30061 : int) (_30063 : int) (_30062 : int) (_30064 : int) : (term1212 _30061 _30063 _30062 _30064) = (term1217 _30061 _30063 _30062 _30064).
Proof. exact (TRANS (@lem2610980 _30061 _30063 _30062 _30064) (@lem2610989 _30061 _30063 _30062 _30064)). Qed.
Lemma lem2610991 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2610992 (_30061 : int) (_30063 : int) (_30062 : int) (_30064 : int) : (term1218 _30061 _30063 _30062 _30064) = (term1219 _30061 _30063 _30062 _30064).
Proof. exact (MK_COMB (@lem2610991) (@lem2610990 _30061 _30063 _30062 _30064)). Qed.
Lemma lem2610993 (_30061 : int) (_30062 : int) (_30063 : int) (_30064 : int) : ((rem _30061 _30062) = (rem _30063 _30064)) = ((rem _30061 _30062) = (rem _30063 _30064)).
Proof. exact (eq_refl ((rem _30061 _30062) = (rem _30063 _30064))). Qed.
Lemma lem2610994 (_30061 : int) (_30062 : int) (_30063 : int) (_30064 : int) : (term1208 _30061 _30062 _30063 _30064) = (term1220 _30061 _30062 _30063 _30064).
Proof. exact (MK_COMB (@lem2610992 _30061 _30063 _30062 _30064) (@lem2610993 _30061 _30062 _30063 _30064)). Qed.
Lemma lem2610995 (_30061 : int) (_30062 : int) (_30063 : int) (_30064 : int) : (term1204 _30061 _30063 _30062 _30064) = (term1220 _30061 _30062 _30063 _30064).
Proof. exact (TRANS (@lem2610977 _30061 _30062 _30063 _30064) (@lem2610994 _30061 _30062 _30063 _30064)). Qed.
Lemma lem2610997 (m : nat) (n : nat) (c : int) (h1 : (int_of_num m) = (term513 n c)) : term1221 m c n.
Proof. exact (conj (@lem2610876 m n c h1) (@lem2610884 n)). Qed.
Lemma lem2610999 (_30061 : int) (_30062 : int) (_30063 : int) (_30064 : int) : term1220 _30061 _30062 _30063 _30064.
Proof. exact (EQ_MP (@lem2610995 _30061 _30062 _30063 _30064) (@lem2610974 _30061 _30063 _30062 _30064)). Qed.
Lemma lem2611000 (m : nat) (c : int) (n : nat) : term1222 m c n.
Proof. exact (@lem2610999 (int_of_num m) (int_of_num n) (term513 n c) (int_of_num n)). Qed.
Lemma lem2611003 (m : nat) (n : nat) (c : int) (h1 : (int_of_num m) = (term513 n c)) : (term601 m n) = (term1223 c n).
Proof. exact (@lem2611000 m c n (@lem2610997 m n c h1)). Qed.
Lemma lem2611004 (m : nat) (n : nat) (c : int) (h1 : (int_of_num m) = (term513 n c)) : term1224 m c n.
Proof. exact (fun h0 : term1225 m c n => @lem2611003 m n c h1). Qed.
Lemma lem2611006 (p : Prop) : (term1197 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2611007 (m : nat) (c : int) (n : nat) : (term1224 m c n) = ((term601 m n) = (term1223 c n)).
Proof. exact (@lem2611006 ((term601 m n) = (term1223 c n))). Qed.
Lemma lem2611008 (m : nat) (n : nat) (c : int) (h1 : (int_of_num m) = (term513 n c)) : (term601 m n) = (term1223 c n).
Proof. exact (EQ_MP (@lem2611007 m c n) (@lem2611004 m n c h1)). Qed.
Lemma lem2611010 (x : int) : x = x.
Proof. exact (@lem21386 int x). Qed.
Lemma lem2611011 (m : nat) (n : nat) : (term601 m n) = (term601 m n).
Proof. exact (@lem2611010 (term601 m n)). Qed.
Lemma lem2611012 (m : nat) (n : nat) : term1226 m n.
Proof. exact (fun h0 : term1227 m n => @lem2611011 m n). Qed.
Lemma lem2611014 (p : Prop) : (term1197 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2611015 (m : nat) (n : nat) : (term1226 m n) = ((term601 m n) = (term601 m n)).
Proof. exact (@lem2611014 ((term601 m n) = (term601 m n))). Qed.
Lemma lem2611016 (m : nat) (n : nat) : (term601 m n) = (term601 m n).
Proof. exact (EQ_MP (@lem2611015 m n) (@lem2611012 m n)). Qed.
Lemma lem2611034 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2611035 (y : int) (x : int) (z : int) : (term1228 x y z) = (term1229 y x z).
Proof. exact (@lem2611034 (y = z) (term100 x z)). Qed.
Lemma lem2611045 (x : int) (y : int) : (term1201 x y) = (term1201 x y).
Proof. exact (eq_refl (term1201 x y)). Qed.
Lemma lem2611046 (y : int) (x : int) (z : int) : (term1195 x y z) = (term1230 y x z).
Proof. exact (MK_COMB (@lem2611045 x y) (@lem2611035 y x z)). Qed.
Lemma lem2611050 (q : Prop) (p : Prop) (r : Prop) : (term1203 p q r) = (term1203 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2611051 (y : int) (x : int) (z : int) : (term1230 y x z) = (term1231 y x z).
Proof. exact (@lem2611050 (y = z) (term100 x y) (term100 x z)). Qed.
Lemma lem2611073 (y : int) (x : int) (z : int) : (term1195 x y z) = (term1231 y x z).
Proof. exact (TRANS (@lem2611046 y x z) (@lem2611051 y x z)). Qed.
Lemma lem2611074 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2611075 (y : int) (x : int) (z : int) : (term1232 x y z) = (term1233 y x z).
Proof. exact (MK_COMB (@lem2611074) (@lem2611073 y x z)). Qed.
Lemma lem2611097 (y : int) (x : int) (z : int) : (term1231 y x z) = (term1231 y x z).
Proof. exact (eq_refl (term1231 y x z)). Qed.
Lemma lem2611098 (y : int) (x : int) (z : int) : ((term1195 x y z) = (term1231 y x z)) = ((term1231 y x z) = (term1231 y x z)).
Proof. exact (MK_COMB (@lem2611075 y x z) (@lem2611097 y x z)). Qed.
Lemma lem2611100 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2611101 (x : Prop) : (x = x) = True.
Proof. exact (@lem2611100 Prop x). Qed.
Lemma lem2611102 (y : int) (x : int) (z : int) : ((term1231 y x z) = (term1231 y x z)) = True.
Proof. exact (@lem2611101 (term1231 y x z)). Qed.
Lemma lem2611103 (y : int) (x : int) (z : int) : ((term1195 x y z) = (term1231 y x z)) = True.
Proof. exact (TRANS (@lem2611098 y x z) (@lem2611102 y x z)). Qed.
Lemma lem2611104 (y : int) (x : int) (z : int) : True = ((term1195 x y z) = (term1231 y x z)).
Proof. exact (SYM (@lem2611103 y x z)). Qed.
Lemma lem2611105 (y : int) (x : int) (z : int) : (term1195 x y z) = (term1231 y x z).
Proof. exact (EQ_MP (@lem2611104 y x z) (@lem0)). Qed.
Lemma lem2611106 (y : int) (x : int) (z : int) : term1231 y x z.
Proof. exact (EQ_MP (@lem2611105 y x z) (@lem2610869 x y z)). Qed.
Lemma lem2611108 (b : Prop) (a : Prop) : (a \/ b) = (term1207 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2611109 (x : int) (y : int) (z : int) : (term1231 y x z) = (term1234 x y z).
Proof. exact (@lem2611108 (term1235 y x z) (y = z)). Qed.
Lemma lem2611111 (a : Prop) (b : Prop) : (term1210 a b) = (term1211 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem2611112 (y : int) (x : int) (z : int) : (term1236 y x z) = (term1237 y x z).
Proof. exact (@lem2611111 (term100 x y) (term100 x z)). Qed.
Lemma lem2611114 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2611115 (x : int) (y : int) : (term1214 x y) = (x = y).
Proof. exact (@lem2611114 (x = y)). Qed.
Lemma lem2611116 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2611117 (x : int) (y : int) : (term1215 x y) = (term1216 x y).
Proof. exact (MK_COMB (@lem2611116) (@lem2611115 x y)). Qed.
Lemma lem2611119 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2611120 (x : int) (z : int) : (term1214 x z) = (x = z).
Proof. exact (@lem2611119 (x = z)). Qed.
Lemma lem2611121 (y : int) (x : int) (z : int) : (term1237 y x z) = (term1238 y x z).
Proof. exact (MK_COMB (@lem2611117 x y) (@lem2611120 x z)). Qed.
Lemma lem2611122 (y : int) (x : int) (z : int) : (term1236 y x z) = (term1238 y x z).
Proof. exact (TRANS (@lem2611112 y x z) (@lem2611121 y x z)). Qed.
Lemma lem2611123 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2611124 (y : int) (x : int) (z : int) : (term1239 y x z) = (term1240 y x z).
Proof. exact (MK_COMB (@lem2611123) (@lem2611122 y x z)). Qed.
Lemma lem2611125 (y : int) (z : int) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem2611126 (x : int) (y : int) (z : int) : (term1234 x y z) = (term1241 x y z).
Proof. exact (MK_COMB (@lem2611124 y x z) (@lem2611125 y z)). Qed.
Lemma lem2611127 (x : int) (y : int) (z : int) : (term1231 y x z) = (term1241 x y z).
Proof. exact (TRANS (@lem2611109 x y z) (@lem2611126 x y z)). Qed.
Lemma lem2611129 (m : nat) (n : nat) (c : int) (h1 : (int_of_num m) = (term513 n c)) : term1242 c m n.
Proof. exact (conj (@lem2611008 m n c h1) (@lem2611016 m n)). Qed.
Lemma lem2611131 (x : int) (y : int) (z : int) : term1241 x y z.
Proof. exact (EQ_MP (@lem2611127 x y z) (@lem2611106 y x z)). Qed.
Lemma lem2611132 (c : int) (m : nat) (n : nat) : term1243 c m n.
Proof. exact (@lem2611131 (term601 m n) (term1223 c n) (term601 m n)). Qed.
Lemma lem2611135 (m : nat) (n : nat) (c : int) (h1 : (int_of_num m) = (term513 n c)) : (term1223 c n) = (term601 m n).
Proof. exact (@lem2611132 c m n (@lem2611129 m n c h1)). Qed.
Lemma lem2611136 (m : nat) (n : nat) (c : int) (h1 : (int_of_num m) = (term513 n c)) : term1244 c m n.
Proof. exact (fun h0 : term1245 c m n => @lem2611135 m n c h1). Qed.
Lemma lem2611138 (p : Prop) : (term1197 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2611139 (c : int) (m : nat) (n : nat) : (term1244 c m n) = ((term1223 c n) = (term601 m n)).
Proof. exact (@lem2611138 ((term1223 c n) = (term601 m n))). Qed.
Lemma lem2611140 (m : nat) (n : nat) (c : int) (h1 : (int_of_num m) = (term513 n c)) : (term1223 c n) = (term601 m n).
Proof. exact (EQ_MP (@lem2611139 c m n) (@lem2611136 m n c h1)). Qed.
Lemma lem2611142 (_30038 : int) (_30037 : int) (h1 : term1150) : (term1168 _30038 _30037) = term527.
Proof. exact (EQ_MP (@lem2610723 _30038 _30037) (@lem2610722 _30037 _30038 h1)). Qed.
Lemma lem2611143 (c : int) (n : nat) (h1 : term1150) : (term1223 c n) = term527.
Proof. exact (@lem2611142 (int_neg c) (int_of_num n) h1). Qed.
Lemma lem2611144 (c : int) (n : nat) (h1 : term1150) : term1246 c n.
Proof. exact (fun h0 : term1247 c n => @lem2611143 c n h1). Qed.
Lemma lem2611146 (p : Prop) : (term1197 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2611147 (c : int) (n : nat) : (term1246 c n) = ((term1223 c n) = term527).
Proof. exact (@lem2611146 ((term1223 c n) = term527)). Qed.
Lemma lem2611148 (c : int) (n : nat) (h1 : term1150) : (term1223 c n) = term527.
Proof. exact (EQ_MP (@lem2611147 c n) (@lem2611144 c n h1)). Qed.
Lemma lem2611149 (m : nat) (n : nat) (c : int) (h1 : term1150) (h2 : (int_of_num m) = (term513 n c)) : term1248 m c n.
Proof. exact (conj (@lem2611140 m n c h2) (@lem2611148 c n h1)). Qed.
Lemma lem2611151 (x : int) (y : int) (z : int) : term1241 x y z.
Proof. exact (EQ_MP (@lem2611127 x y z) (@lem2611106 y x z)). Qed.
Lemma lem2611152 (c : int) (m : nat) (n : nat) : term1249 c m n.
Proof. exact (@lem2611151 (term1223 c n) (term601 m n) term527). Qed.
Lemma lem2611155 (m : nat) (n : nat) (c : int) (h1 : term1150) (h2 : (int_of_num m) = (term513 n c)) : (term601 m n) = term527.
Proof. exact (@lem2611152 c m n (@lem2611149 m n c h1 h2)). Qed.
Lemma lem2611156 (m : nat) (n : nat) (c : int) (h1 : term1150) (h2 : (int_of_num m) = (term513 n c)) : term1250 m n.
Proof. exact (fun h0 : term972 m n => @lem2611155 m n c h1 h2). Qed.
Lemma lem2611158 (p : Prop) : (term1197 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2611159 (m : nat) (n : nat) : (term1250 m n) = ((term601 m n) = term527).
Proof. exact (@lem2611158 ((term601 m n) = term527)). Qed.
Lemma lem2611160 (m : nat) (n : nat) (c : int) (h1 : term1150) (h2 : (int_of_num m) = (term513 n c)) : (term601 m n) = term527.
Proof. exact (EQ_MP (@lem2611159 m n) (@lem2611156 m n c h1 h2)). Qed.
Lemma lem2611163 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2611165 (m : nat) (n : nat) : (term972 m n) = (term1251 m n).
Proof. exact (@lem2611163 ((term601 m n) = term527)). Qed.
Lemma lem2611168 (m : nat) (n : nat) (h1 : term972 m n) : term1251 m n.
Proof. exact (EQ_MP (@lem2611165 m n) (@lem2610740 m n h1)). Qed.
Lemma lem2611171 (m : nat) (n : nat) (c : int) (h1 : term972 m n) (h2 : term1150) (h3 : (int_of_num m) = (term513 n c)) : False.
Proof. exact (@lem2611168 m n h1 (@lem2611160 m n c h2 h3)). Qed.
Lemma lem2611172 (m : nat) (n : nat) (c : int) (h1 : term972 m n) (h2 : term1150) (h3 : (int_of_num m) = (term513 n c)) : term1252.
Proof. exact (fun h0 : ~ False => @lem2611171 m n c h1 h2 h3). Qed.
Lemma lem2611174 (p : Prop) : (term1197 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2611175 : term1252 = False.
Proof. exact (@lem2611174 False). Qed.
Lemma lem2611176 (m : nat) (n : nat) (c : int) (h1 : term972 m n) (h2 : term1150) (h3 : (int_of_num m) = (term513 n c)) : False.
Proof. exact (EQ_MP (@lem2611175) (@lem2611172 m n c h1 h2 h3)). Qed.
Lemma lem2611177 (m : nat) (n : nat) (c : int) (h1 : term972 m n) (h2 : term1150) (h3 : (int_of_num m) = (term513 n c)) : ((int_of_num m) = (term513 n c)) = False.
Proof. exact (prop_ext (fun h4 : (int_of_num m) = (term513 n c) => @lem2611176 m n c h1 h2 h3) (fun h4 : False => @lem2610742 m n c h3)). Qed.
Lemma lem2611178 (m : nat) (n : nat) (c : int) (h1 : term972 m n) (h2 : term1150) (h3 : (int_of_num m) = (term513 n c)) : False.
Proof. exact (EQ_MP (@lem2611177 m n c h1 h2 h3) (@lem2610742 m n c h3)). Qed.
Lemma lem2611179 (m : nat) (n : nat) (c : int) (h1 : term972 m n) (h2 : term1150) (h3 : (int_of_num m) = (term513 n c)) : (term972 m n) = False.
Proof. exact (prop_ext (fun h4 : term972 m n => @lem2611178 m n c h1 h2 h3) (fun h4 : False => @lem2610740 m n h1)). Qed.
Lemma lem2611180 (m : nat) (n : nat) (c : int) (h1 : term972 m n) (h2 : term1150) (h3 : (int_of_num m) = (term513 n c)) : False.
Proof. exact (EQ_MP (@lem2611179 m n c h1 h2 h3) (@lem2610740 m n h1)). Qed.
Lemma lem2611181 (m : nat) (n : nat) (c : int) (h1 : term972 m n) (h2 : term1150) (h3 : (int_of_num m) = (term513 n c)) : ((int_of_num m) = (term513 n c)) = False.
Proof. exact (prop_ext (fun h4 : (int_of_num m) = (term513 n c) => @lem2611180 m n c h1 h2 h3) (fun h4 : False => @lem2610660 m n c h3)). Qed.
Lemma lem2611182 (m : nat) (n : nat) (c : int) (h1 : term972 m n) (h2 : term1150) (h3 : (int_of_num m) = (term513 n c)) : False.
Proof. exact (EQ_MP (@lem2611181 m n c h1 h2 h3) (@lem2610660 m n c h3)). Qed.
Lemma lem2611183 (m : nat) (n : nat) (c : int) (h1 : term972 m n) (h2 : term1150) (h3 : (int_of_num m) = (term513 n c)) : (term972 m n) = False.
Proof. exact (prop_ext (fun h4 : term972 m n => @lem2611182 m n c h1 h2 h3) (fun h4 : False => @lem2610656 m n h1)). Qed.
Lemma lem2611184 (m : nat) (n : nat) (c : int) (h1 : term972 m n) (h2 : term1150) (h3 : (int_of_num m) = (term513 n c)) : False.
Proof. exact (EQ_MP (@lem2611183 m n c h1 h2 h3) (@lem2610656 m n h1)). Qed.
Lemma lem2611185 (m : nat) (n : nat) (c : int) (h1 : term972 m n) (h2 : term1150) (h3 : (int_of_num m) = (term513 n c)) : ((int_of_num m) = (term513 n c)) = False.
Proof. exact (prop_ext (fun h4 : (int_of_num m) = (term513 n c) => @lem2611184 m n c h1 h2 h3) (fun h4 : False => @lem2610660 m n c h3)). Qed.
Lemma lem2611186 (m : nat) (n : nat) (c : int) (h1 : term972 m n) (h2 : term1150) (h3 : (int_of_num m) = (term513 n c)) : False.
Proof. exact (EQ_MP (@lem2611185 m n c h1 h2 h3) (@lem2610660 m n c h3)). Qed.
Lemma lem2611187 (m : nat) (n : nat) (c : int) (h1 : term972 m n) (h2 : term1150) (h3 : (int_of_num m) = (term513 n c)) : (term972 m n) = False.
Proof. exact (prop_ext (fun h4 : term972 m n => @lem2611186 m n c h1 h2 h3) (fun h4 : False => @lem2610656 m n h1)). Qed.
Lemma lem2611188 (m : nat) (n : nat) (c : int) (h1 : term972 m n) (h2 : term1150) (h3 : (int_of_num m) = (term513 n c)) : False.
Proof. exact (EQ_MP (@lem2611187 m n c h1 h2 h3) (@lem2610656 m n h1)). Qed.
Lemma lem2611189 (m : nat) (n : nat) (c : int) (h1 : term972 m n) (h2 : term1150) (h3 : (int_of_num m) = (term513 n c)) : ((int_of_num m) = (term513 n c)) = False.
Proof. exact (prop_ext (fun h4 : (int_of_num m) = (term513 n c) => @lem2611188 m n c h1 h2 h3) (fun h4 : False => @lem2610644 m n c h3)). Qed.
Lemma lem2611190 (m : nat) (n : nat) (c : int) (h1 : term972 m n) (h2 : term1150) (h3 : (int_of_num m) = (term513 n c)) : False.
Proof. exact (EQ_MP (@lem2611189 m n c h1 h2 h3) (@lem2610644 m n c h3)). Qed.
Lemma lem2611191 (m : nat) (n : nat) (c : int) (h1 : term972 m n) (h2 : term1150) (h3 : (int_of_num m) = (term513 n c)) : term1150 = False.
Proof. exact (prop_ext (fun h4 : term1150 => @lem2611190 m n c h1 h2 h3) (fun h4 : False => @lem2610628 h2)). Qed.
Lemma lem2611192 (m : nat) (n : nat) (c : int) (h1 : term972 m n) (h2 : term1150) (h3 : (int_of_num m) = (term513 n c)) : False.
Proof. exact (EQ_MP (@lem2611191 m n c h1 h2 h3) (@lem2610628 h2)). Qed.
Lemma lem2611193 (m : nat) (n : nat) (c : int) (h1 : term972 m n) (h2 : term1150) (h3 : (int_of_num m) = (term513 n c)) : (term972 m n) = False.
Proof. exact (prop_ext (fun h4 : term972 m n => @lem2611192 m n c h1 h2 h3) (fun h4 : False => @lem2610578 m n h1)). Qed.
Lemma lem2611194 (m : nat) (n : nat) (c : int) (h1 : term972 m n) (h2 : term1150) (h3 : (int_of_num m) = (term513 n c)) : False.
Proof. exact (EQ_MP (@lem2611193 m n c h1 h2 h3) (@lem2610578 m n h1)). Qed.
Lemma lem2611195 (m : nat) (n : nat) (h1 : term1143 m n) (h2 : term972 m n) (h3 : term1150) : False.
Proof. exact (ex_elim (@lem2610433 m n h1) (fun c : int => fun h0 : term1186 m n c => @lem2611194 m n c h2 h3 h0)). Qed.
Lemma lem2611196 (m : nat) (n : nat) (h1 : term1143 m n) (h2 : term972 m n) (h3 : term1150) : term1150 = False.
Proof. exact (prop_ext (fun h4 : term1150 => @lem2611195 m n h1 h2 h3) (fun h4 : False => @lem2610471 h3)). Qed.
Lemma lem2611197 (m : nat) (n : nat) (h1 : term1143 m n) (h2 : term972 m n) (h3 : term1150) : False.
Proof. exact (EQ_MP (@lem2611196 m n h1 h2 h3) (@lem2610471 h3)). Qed.
Lemma lem2611198 (m : nat) (n : nat) (h1 : term1143 m n) (h2 : term972 m n) (h3 : term1150) : (term972 m n) = False.
Proof. exact (prop_ext (fun h4 : term972 m n => @lem2611197 m n h1 h2 h3) (fun h4 : False => @lem2610411 m n h2)). Qed.
Lemma lem2611199 (m : nat) (n : nat) (h1 : term1143 m n) (h2 : term972 m n) (h3 : term1150) : False.
Proof. exact (EQ_MP (@lem2611198 m n h1 h2 h3) (@lem2610411 m n h2)). Qed.
Lemma lem2611200 (m : nat) (n : nat) (h1 : term1143 m n) (h2 : term972 m n) : term1148.
Proof. exact (fun h0 : term1150 => @lem2611199 m n h1 h2 h0). Qed.
Lemma lem2611201 : term1148 = term1149.
Proof. exact (@lem69 term1150). Qed.
Lemma lem2611202 (m : nat) (n : nat) (h1 : term1143 m n) (h2 : term972 m n) : term1149.
Proof. exact (EQ_MP (@lem2611201) (@lem2611200 m n h1 h2)). Qed.
Lemma lem2611203 (m : nat) (n : nat) (h1 : term972 m n) : term1153 m n.
Proof. exact (fun h0 : term1143 m n => @lem2611202 m n h0 h1). Qed.
Lemma lem2611204 (m : nat) (n : nat) : term1155 m n.
Proof. exact (fun h0 : term972 m n => @lem2611203 m n h0). Qed.
Lemma lem2611205 (m : nat) (n : nat) : term1158 m n.
Proof. exact (fun h0 : term838 n => @lem2611204 m n). Qed.
Lemma lem2611206 (m : nat) (n : nat) : term1159 m n.
Proof. exact (fun h0 : term812 n => @lem2611205 m n). Qed.
Lemma lem2611211 (n : nat) : term1163 n.
Proof. exact (fun m : nat => @lem2611206 m n). Qed.
Lemma lem2611216 : term1167.
Proof. exact (fun n : nat => @lem2611211 n). Qed.
Lemma lem2611217 : term1166.
Proof. exact (EQ_MP (@lem2610107) (@lem2611216)). Qed.
Lemma lem2611218 (n : nat) : term1253 n.
Proof. exact (@lem2611217 n). Qed.
Lemma lem2611219 (n : nat) : (term1253 n) = (term1162 n).
Proof. exact (eq_refl (term1253 n)). Qed.
Lemma lem2611220 (n : nat) : term1162 n.
Proof. exact (EQ_MP (@lem2611219 n) (@lem2611218 n)). Qed.
Lemma lem2611221 (n : nat) (m : nat) : term1254 n m.
Proof. exact (@lem2611220 n m). Qed.
Lemma lem2611222 (m : nat) (n : nat) : (term1254 n m) = (term1144 m n).
Proof. exact (eq_refl (term1254 n m)). Qed.
Lemma lem2611223 (m : nat) (n : nat) : term1144 m n.
Proof. exact (EQ_MP (@lem2611222 m n) (@lem2611221 n m)). Qed.
Lemma lem2611225 (m : nat) (n : nat) : term1144 m n.
Proof. exact (@lem2609896 m n (@lem2611223 m n)). Qed.
Lemma lem2611226 (m : nat) (n : nat) (h1 : term812 n) : term1157 m n.
Proof. exact (@lem2611225 m n (@lem2608394 n h1)). Qed.
Lemma lem2611227 (m : nat) (n : nat) (h1 : term838 n) (h2 : term812 n) : term1154 m n.
Proof. exact (@lem2611226 m n h2 (@lem2608876 n h1)). Qed.
Lemma lem2611228 (m : nat) (n : nat) (h1 : term838 n) (h2 : term972 m n) (h3 : term812 n) : term1152 m n.
Proof. exact (@lem2611227 m n h1 h3 (@lem2608943 m n h2)). Qed.
Lemma lem2611229 (m : nat) (n : nat) (h1 : term838 n) (h2 : term1143 m n) (h3 : term972 m n) (h4 : term812 n) : term1148.
Proof. exact (@lem2611228 m n h1 h3 h4 (@lem2609881 m n h2)). Qed.
Lemma lem2611230 (m : nat) (n : nat) (h1 : term838 n) (h2 : term1143 m n) (h3 : term972 m n) (h4 : term812 n) : False.
Proof. exact (@lem2611229 m n h1 h2 h3 h4 (@lem2599936)). Qed.
Lemma lem2611231 (m : nat) (n : nat) (h1 : term838 n) (h2 : term1143 m n) (h3 : term972 m n) (h4 : term812 n) : (term1143 m n) = False.
Proof. exact (prop_ext (fun h5 : term1143 m n => @lem2611230 m n h1 h2 h3 h4) (fun h5 : False => @lem2609881 m n h2)). Qed.
Lemma lem2611232 (m : nat) (n : nat) (h1 : term838 n) (h2 : term1143 m n) (h3 : term972 m n) (h4 : term812 n) : False.
Proof. exact (EQ_MP (@lem2611231 m n h1 h2 h3 h4) (@lem2609881 m n h2)). Qed.
Lemma lem2611233 (m : nat) (n : nat) (h1 : term838 n) (h2 : term972 m n) (h3 : term812 n) : term1142 m n.
Proof. exact (fun h0 : term1143 m n => @lem2611232 m n h1 h0 h2 h3). Qed.
Lemma lem2611234 (m : nat) (n : nat) (h1 : term838 n) (h2 : term972 m n) (h3 : term812 n) : term1140 m n.
Proof. exact (EQ_MP (@lem2609880 m n) (@lem2611233 m n h1 h2 h3)). Qed.
Lemma lem2611235 (m : nat) (n : nat) (h1 : term838 n) (h2 : term972 m n) (h3 : term812 n) : term1137 m n.
Proof. exact (EQ_MP (@lem2609876 m n) (@lem2611234 m n h1 h2 h3)). Qed.
Lemma lem2611236 (m : nat) (n : nat) (h1 : term838 n) (h2 : term972 m n) (h3 : term812 n) : term1129 m n.
Proof. exact (EQ_MP (@lem2609859 m n h1) (@lem2611235 m n h1 h2 h3)). Qed.
Lemma lem2611237 (m : nat) (n : nat) (h1 : term838 n) (h2 : term972 m n) (h3 : term812 n) : term1124 m n.
Proof. exact (EQ_MP (@lem2609809 m n) (@lem2611236 m n h1 h2 h3)). Qed.
Lemma lem2611239 (m : nat) (n : nat) (h1 : term838 n) (h2 : term972 m n) (h3 : term812 n) : term958 m n.
Proof. exact (EQ_MP (@lem2609782 m n h3) (@lem2611237 m n h1 h2 h3)). Qed.
Lemma lem2611240 (m : nat) (n : nat) (h1 : term838 n) (h2 : term972 m n) (h3 : term812 n) : (term972 m n) = (term958 m n).
Proof. exact (prop_ext (fun h4 : term972 m n => @lem2611239 m n h1 h2 h3) (fun h4 : term958 m n => @lem2608943 m n h2)). Qed.
Lemma lem2611241 (m : nat) (n : nat) (h1 : term838 n) (h2 : term972 m n) (h3 : term812 n) : term958 m n.
Proof. exact (EQ_MP (@lem2611240 m n h1 h2 h3) (@lem2608943 m n h2)). Qed.
Lemma lem2611242 (m : nat) (n : nat) (h1 : term838 n) (h2 : term812 n) : term961 m n.
Proof. exact (fun h0 : term972 m n => @lem2611241 m n h1 h0 h2). Qed.
Lemma lem2611243 (m : nat) (n : nat) (h1 : term812 n) (h2 : (term601 m n) = term527) : term963 m n.
Proof. exact (@lem2609491 m n h1 h2 (@lem2606761 m n)). Qed.
Lemma lem2611244 (m : nat) (n : nat) (h1 : term812 n) (h2 : (term601 m n) = term527) : ((term601 m n) = term527) = (term963 m n).
Proof. exact (prop_ext (fun h3 : (term601 m n) = term527 => @lem2611243 m n h1 h2) (fun h3 : term963 m n => @lem2608926 m n h2)). Qed.
Lemma lem2611245 (m : nat) (n : nat) (h1 : term812 n) (h2 : (term601 m n) = term527) : term963 m n.
Proof. exact (EQ_MP (@lem2611244 m n h1 h2) (@lem2608926 m n h2)). Qed.
Lemma lem2611246 (m : nat) (n : nat) (h1 : term812 n) : term966 m n.
Proof. exact (fun h0 : (term601 m n) = term527 => @lem2611245 m n h1 h0). Qed.
Lemma lem2611247 (m : nat) (n : nat) (h1 : term838 n) (h2 : term812 n) : term969 m n.
Proof. exact (conj (@lem2611246 m n h2) (@lem2611242 m n h1 h2)). Qed.
Lemma lem2611248 (m : nat) (n : nat) (h1 : term838 n) (h2 : term812 n) : term947 m n.
Proof. exact (EQ_MP (@lem2608925 m n) (@lem2611247 m n h1 h2)). Qed.
Lemma lem2611249 (m : nat) (n : nat) (h1 : term838 n) (h2 : term812 n) : term842 m n.
Proof. exact (EQ_MP (@lem2608907 m n) (@lem2611248 m n h1 h2)). Qed.
Lemma lem2611254 (n : nat) (h1 : term838 n) (h2 : term812 n) : term846 n.
Proof. exact (fun m : nat => @lem2611249 m n h1 h2). Qed.
Lemma lem2611255 (n : nat) (h1 : term812 n) : term1255 n.
Proof. exact (fun h0 : term838 n => @lem2611254 n h0 h1). Qed.
Lemma lem2611256 (n : nat) (h1 : term812 n) : term1256 n.
Proof. exact (conj (@lem2608875 n h1) (@lem2611255 n h1)). Qed.
Lemma lem2611257 (n : nat) (h1 : term812 n) : term847 n.
Proof. exact (@lem2608420 n (@lem2611256 n h1)). Qed.
Lemma lem2611258 (n : nat) (h1 : term812 n) : term828 n.
Proof. exact (EQ_MP (@lem2608417 n) (@lem2611257 n h1)). Qed.
Lemma lem2611259 (n : nat) : term829 n.
Proof. exact (fun h0 : term812 n => @lem2611258 n h0). Qed.
Lemma lem2611260 (n : nat) : term761 n.
Proof. exact (EQ_MP (@lem2608393 n) (@lem2611259 n)). Qed.
Lemma lem2611265 : term765.
Proof. exact (fun n : nat => @lem2611260 n). Qed.
Lemma lem2611266 : term774.
Proof. exact (EQ_MP (@lem2608314) (@lem2611265)). Qed.
Lemma lem2611267 : term757.
Proof. exact (EQ_MP (@lem2608223) (@lem2611266)). Qed.
