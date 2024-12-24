Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_SET_OF_LIST_term_abbrevs.
Require Import ALL_MEM_spec.
Require Import CARD_CLAUSES_spec.
Require Import CARD_SET_OF_LIST_LE_spec.
Require Import DISJ_ACI_spec.
Require Import FINITE_SET_OF_LIST_spec.
Require Import HAS_SIZE_spec.
Require Import INT_POS_spec.
Require Import IN_SET_OF_LIST_spec.
Require Import SUC_INJ_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097080_spec.
Require Import thm1110672_spec.
Require Import thm1110673_spec.
Require Import thm1110681_spec.
Require Import thm1110682_spec.
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
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17500_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19792_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm20230_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm2841416_spec.
Require Import thm2841417_spec.
Require Import thm4211_spec.
Require Import thm4785464_spec.
Require Import thm4785470_spec.
Require Import thm4785471_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem4897963 (m : nat) : (S m) = (term0 m).
Proof. exact (EQ_MP (@lem2841417 m) (@lem2841416 m)). Qed.
Lemma lem4897964 (n : nat) : (S n) = (term0 n).
Proof. exact (@lem4897963 n). Qed.
Lemma lem4897965 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem4897966 (n : nat) : (term1 n) = (term2 n).
Proof. exact (MK_COMB (@lem4897965) (@lem4897964 n)). Qed.
Lemma lem4897967 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4897968 (n : nat) : (term3 n) = (term4 n).
Proof. exact (MK_COMB (@lem4897966 n) (@lem4897967 n)). Qed.
Lemma lem4897969 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4897987 (n : nat) : (term5 n) = (term6 n).
Proof. exact (MK_COMB (@lem4897969) (@lem4897968 n)). Qed.
Lemma lem4897989 (m : nat) (n : nat) : (Peano.le m n) = (term7 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem4897990 (n : nat) : (term4 n) = (term8 n).
Proof. exact (@lem4897989 (term0 n) n). Qed.
Lemma lem4897992 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem4897993 (n : nat) : (term11 n) = (term12 n).
Proof. exact (@lem4897992 n term13). Qed.
Lemma lem4897994 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem4897995 (n : nat) : (term14 n) = (term15 n).
Proof. exact (MK_COMB (@lem4897994) (@lem4897993 n)). Qed.
Lemma lem4897996 (n : nat) : (int_of_num n) = (int_of_num n).
Proof. exact (eq_refl (int_of_num n)). Qed.
Lemma lem4897997 (n : nat) : (term8 n) = (term16 n).
Proof. exact (MK_COMB (@lem4897995 n) (@lem4897996 n)). Qed.
Lemma lem4897998 (n : nat) : (term4 n) = (term16 n).
Proof. exact (TRANS (@lem4897990 n) (@lem4897997 n)). Qed.
Lemma lem4897999 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4898000 (n : nat) : (term6 n) = (term17 n).
Proof. exact (MK_COMB (@lem4897999) (@lem4897998 n)). Qed.
Lemma lem4898001 (n : nat) : (term5 n) = (term17 n).
Proof. exact (TRANS (@lem4897987 n) (@lem4898000 n)). Qed.
Lemma lem4898002 (n : nat) : term18 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem4898003 (n : nat) : (term18 n) = (term19 n).
Proof. exact (eq_refl (term18 n)). Qed.
Lemma lem4898004 (n : nat) : term19 n.
Proof. exact (EQ_MP (@lem4898003 n) (@lem4898002 n)). Qed.
Lemma lem4898005 (_60489 : int) : (term20 _60489) = (term21 _60489).
Proof. exact (@lem2318604 (term21 _60489)). Qed.
Lemma lem4898016 (_60489 : int) : (term22 _60489) = (term23 _60489).
Proof. exact (@lem16933 (term23 _60489)). Qed.
Lemma lem4898018 (_60489 : int) : (term24 _60489) = (term24 _60489).
Proof. exact (eq_refl (term24 _60489)). Qed.
Lemma lem4898019 (_60489 : int) : (term25 _60489) = (term26 _60489).
Proof. exact (MK_COMB (@lem4898018 _60489) (@lem4898016 _60489)). Qed.
Lemma lem4898020 (_60489 : int) : (term27 _60489) = (term25 _60489).
Proof. exact (@lem17362 (term28 _60489) (term29 _60489)). Qed.
Lemma lem4898028 (_60489 : int) : (term27 _60489) = (term26 _60489).
Proof. exact (TRANS (@lem4898020 _60489) (@lem4898019 _60489)). Qed.
Lemma lem4898031 (x : int) (y : int) : (int_le x y) = (term30 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4898032 (_60489 : int) : (term28 _60489) = (term31 _60489).
Proof. exact (@lem4898031 term32 _60489). Qed.
Lemma lem4898034 (n : nat) : (term33 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4898035 : term34 = term35.
Proof. exact (@lem4898034 (NUMERAL 0)). Qed.
Lemma lem4898036 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4898037 : term36 = term37.
Proof. exact (MK_COMB (@lem4898036) (@lem4898035)). Qed.
Lemma lem4898038 (_60489 : int) : (real_of_int _60489) = (real_of_int _60489).
Proof. exact (eq_refl (real_of_int _60489)). Qed.
Lemma lem4898039 (_60489 : int) : (term31 _60489) = (term38 _60489).
Proof. exact (MK_COMB (@lem4898037) (@lem4898038 _60489)). Qed.
Lemma lem4898041 (_60489 : int) : (term28 _60489) = (term38 _60489).
Proof. exact (TRANS (@lem4898032 _60489) (@lem4898039 _60489)). Qed.
Lemma lem4898044 (x : int) (y : int) : (int_le x y) = (term30 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4898045 (_60489 : int) : (term23 _60489) = (term39 _60489).
Proof. exact (@lem4898044 (term40 _60489) _60489). Qed.
Lemma lem4898047 (x : int) (y : int) : (term41 x y) = (term42 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem4898048 (_60489 : int) : (term43 _60489) = (term44 _60489).
Proof. exact (@lem4898047 _60489 term45). Qed.
Lemma lem4898050 (n : nat) : (term33 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4898051 : term46 = term47.
Proof. exact (@lem4898050 term13). Qed.
Lemma lem4898052 (_60489 : int) : (term48 _60489) = (term48 _60489).
Proof. exact (eq_refl (term48 _60489)). Qed.
Lemma lem4898053 (_60489 : int) : (term44 _60489) = (term49 _60489).
Proof. exact (MK_COMB (@lem4898052 _60489) (@lem4898051)). Qed.
Lemma lem4898054 (_60489 : int) : (term43 _60489) = (term49 _60489).
Proof. exact (TRANS (@lem4898048 _60489) (@lem4898053 _60489)). Qed.
Lemma lem4898055 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4898056 (_60489 : int) : (term50 _60489) = (term51 _60489).
Proof. exact (MK_COMB (@lem4898055) (@lem4898054 _60489)). Qed.
Lemma lem4898057 (_60489 : int) : (real_of_int _60489) = (real_of_int _60489).
Proof. exact (eq_refl (real_of_int _60489)). Qed.
Lemma lem4898058 (_60489 : int) : (term39 _60489) = (term52 _60489).
Proof. exact (MK_COMB (@lem4898056 _60489) (@lem4898057 _60489)). Qed.
Lemma lem4898060 (_60489 : int) : (term23 _60489) = (term52 _60489).
Proof. exact (TRANS (@lem4898045 _60489) (@lem4898058 _60489)). Qed.
Lemma lem4898061 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4898062 (_60489 : int) : (term24 _60489) = (term53 _60489).
Proof. exact (MK_COMB (@lem4898061) (@lem4898041 _60489)). Qed.
Lemma lem4898063 (_60489 : int) : (term26 _60489) = (term54 _60489).
Proof. exact (MK_COMB (@lem4898062 _60489) (@lem4898060 _60489)). Qed.
Lemma lem4898064 (_60489 : int) : (term27 _60489) = (term54 _60489).
Proof. exact (TRANS (@lem4898028 _60489) (@lem4898063 _60489)). Qed.
Lemma lem4898068 (t : Prop) : (term55 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4898084 (_60489 : int) : (term56 _60489) = (term54 _60489).
Proof. exact (@lem4898068 (term54 _60489)). Qed.
Lemma lem4898085 (_60489 : int) : (term38 _60489) = (term57 _60489).
Proof. exact (@lem1988287 (real_of_int _60489) term35). Qed.
Lemma lem4898091 (_60489 : int) : (term58 _60489) = (term59 _60489).
Proof. exact (@lem1982792 (real_of_int _60489) term35). Qed.
Lemma lem4898093 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4898094 : term35 = term61.
Proof. exact (@lem4898093 (NUMERAL 0)). Qed.
Lemma lem4898096 (x : nat) : (term62 x) = (term63 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4898097 : term64 = term65.
Proof. exact (@lem4898096 term13). Qed.
Lemma lem4898098 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4898099 : term66 = term67.
Proof. exact (MK_COMB (@lem4898098) (@lem4898097)). Qed.
Lemma lem4898100 : term68 = term69.
Proof. exact (MK_COMB (@lem4898099) (@lem4898094)). Qed.
Lemma lem4898101 : term69 = term70.
Proof. exact (@lem1981613 term64 term35 term47 term47). Qed.
Lemma lem4898103 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4898104 : term73 = term74.
Proof. exact (@lem4898103 term13 term13). Qed.
Lemma lem4898105 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4898106 : term76 = term13.
Proof. exact (EQ_MP (@lem4898105) (@lem940073)). Qed.
Lemma lem4898107 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4898108 : term74 = term47.
Proof. exact (MK_COMB (@lem4898107) (@lem4898106)). Qed.
Lemma lem4898109 : term73 = term47.
Proof. exact (TRANS (@lem4898104) (@lem4898108)). Qed.
Lemma lem4898111 (x : nat) : (term77 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem4898112 : term68 = term35.
Proof. exact (@lem4898111 term13). Qed.
Lemma lem4898113 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4898114 : term78 = term79.
Proof. exact (MK_COMB (@lem4898113) (@lem4898112)). Qed.
Lemma lem4898115 : term70 = term61.
Proof. exact (MK_COMB (@lem4898114) (@lem4898109)). Qed.
Lemma lem4898116 : term69 = term61.
Proof. exact (TRANS (@lem4898101) (@lem4898115)). Qed.
Lemma lem4898117 : term68 = term61.
Proof. exact (TRANS (@lem4898100) (@lem4898116)). Qed.
Lemma lem4898119 (x : real) : (term80 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4898120 : term61 = term35.
Proof. exact (@lem4898119 term35). Qed.
Lemma lem4898121 : term68 = term35.
Proof. exact (TRANS (@lem4898117) (@lem4898120)). Qed.
Lemma lem4898122 (_60489 : int) : (term48 _60489) = (term48 _60489).
Proof. exact (eq_refl (term48 _60489)). Qed.
Lemma lem4898123 (_60489 : int) : (term59 _60489) = (term81 _60489).
Proof. exact (MK_COMB (@lem4898122 _60489) (@lem4898121)). Qed.
Lemma lem4898124 (_60489 : int) : (term81 _60489) = (real_of_int _60489).
Proof. exact (@lem1982723 (real_of_int _60489)). Qed.
Lemma lem4898125 (_60489 : int) : (term59 _60489) = (real_of_int _60489).
Proof. exact (TRANS (@lem4898123 _60489) (@lem4898124 _60489)). Qed.
Lemma lem4898127 (_60489 : int) : (term58 _60489) = (real_of_int _60489).
Proof. exact (TRANS (@lem4898091 _60489) (@lem4898125 _60489)). Qed.
Lemma lem4898128 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4898129 (_60489 : int) : (term82 _60489) = (term83 _60489).
Proof. exact (MK_COMB (@lem4898128) (@lem4898127 _60489)). Qed.
Lemma lem4898130 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem4898131 (_60489 : int) : (term57 _60489) = (term84 _60489).
Proof. exact (MK_COMB (@lem4898129 _60489) (@lem4898130)). Qed.
Lemma lem4898132 (_60489 : int) : (term38 _60489) = (term84 _60489).
Proof. exact (TRANS (@lem4898085 _60489) (@lem4898131 _60489)). Qed.
Lemma lem4898133 (_60489 : int) : (term52 _60489) = (term85 _60489).
Proof. exact (@lem1988287 (real_of_int _60489) (term49 _60489)). Qed.
Lemma lem4898145 (_60489 : int) : (term86 _60489) = (term87 _60489).
Proof. exact (@lem1982792 (real_of_int _60489) (term49 _60489)). Qed.
Lemma lem4898146 (_60489 : int) : (term88 _60489) = (term89 _60489).
Proof. exact (@lem1982781 (real_of_int _60489) term64 term47). Qed.
Lemma lem4898148 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4898149 : term47 = term90.
Proof. exact (@lem4898148 term13). Qed.
Lemma lem4898151 (x : nat) : (term62 x) = (term63 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4898152 : term64 = term65.
Proof. exact (@lem4898151 term13). Qed.
Lemma lem4898153 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4898154 : term66 = term67.
Proof. exact (MK_COMB (@lem4898153) (@lem4898152)). Qed.
Lemma lem4898155 : term91 = term92.
Proof. exact (MK_COMB (@lem4898154) (@lem4898149)). Qed.
Lemma lem4898156 : term92 = term93.
Proof. exact (@lem1981613 term64 term47 term47 term47). Qed.
Lemma lem4898158 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4898159 : term73 = term74.
Proof. exact (@lem4898158 term13 term13). Qed.
Lemma lem4898160 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4898161 : term76 = term13.
Proof. exact (EQ_MP (@lem4898160) (@lem940073)). Qed.
Lemma lem4898162 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4898163 : term74 = term47.
Proof. exact (MK_COMB (@lem4898162) (@lem4898161)). Qed.
Lemma lem4898164 : term73 = term47.
Proof. exact (TRANS (@lem4898159) (@lem4898163)). Qed.
Lemma lem4898166 (m : nat) (n : nat) : (term94 m n) = (term95 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4898167 : term91 = term96.
Proof. exact (@lem4898166 term13 term13). Qed.
Lemma lem4898168 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4898169 : term76 = term13.
Proof. exact (EQ_MP (@lem4898168) (@lem940073)). Qed.
Lemma lem4898170 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4898171 : term74 = term47.
Proof. exact (MK_COMB (@lem4898170) (@lem4898169)). Qed.
Lemma lem4898172 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4898173 : term96 = term64.
Proof. exact (MK_COMB (@lem4898172) (@lem4898171)). Qed.
Lemma lem4898174 : term91 = term64.
Proof. exact (TRANS (@lem4898167) (@lem4898173)). Qed.
Lemma lem4898175 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4898176 : term97 = term98.
Proof. exact (MK_COMB (@lem4898175) (@lem4898174)). Qed.
Lemma lem4898177 : term93 = term65.
Proof. exact (MK_COMB (@lem4898176) (@lem4898164)). Qed.
Lemma lem4898178 : term92 = term65.
Proof. exact (TRANS (@lem4898156) (@lem4898177)). Qed.
Lemma lem4898179 : term91 = term65.
Proof. exact (TRANS (@lem4898155) (@lem4898178)). Qed.
Lemma lem4898181 (x : real) : (term80 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4898182 : term65 = term64.
Proof. exact (@lem4898181 term64). Qed.
Lemma lem4898183 : term91 = term64.
Proof. exact (TRANS (@lem4898179) (@lem4898182)). Qed.
Lemma lem4898186 (_60489 : int) : (term99 _60489) = (term99 _60489).
Proof. exact (eq_refl (term99 _60489)). Qed.
Lemma lem4898187 (_60489 : int) : (term89 _60489) = (term100 _60489).
Proof. exact (MK_COMB (@lem4898186 _60489) (@lem4898183)). Qed.
Lemma lem4898188 (_60489 : int) : (term88 _60489) = (term100 _60489).
Proof. exact (TRANS (@lem4898146 _60489) (@lem4898187 _60489)). Qed.
Lemma lem4898189 (_60489 : int) : (term48 _60489) = (term48 _60489).
Proof. exact (eq_refl (term48 _60489)). Qed.
Lemma lem4898190 (_60489 : int) : (term87 _60489) = (term101 _60489).
Proof. exact (MK_COMB (@lem4898189 _60489) (@lem4898188 _60489)). Qed.
Lemma lem4898191 (_60489 : int) : (term101 _60489) = (term102 _60489).
Proof. exact (@lem1982763 (real_of_int _60489) (term103 _60489) term64). Qed.
Lemma lem4898192 (_60489 : int) : (term104 _60489) = (term105 _60489).
Proof. exact (@lem1982715 term64 (real_of_int _60489)). Qed.
Lemma lem4898194 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4898195 : term47 = term90.
Proof. exact (@lem4898194 term13). Qed.
Lemma lem4898197 (x : nat) : (term62 x) = (term63 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4898198 : term64 = term65.
Proof. exact (@lem4898197 term13). Qed.
Lemma lem4898199 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4898200 : term106 = term107.
Proof. exact (MK_COMB (@lem4898199) (@lem4898198)). Qed.
Lemma lem4898201 : term108 = term109.
Proof. exact (MK_COMB (@lem4898200) (@lem4898195)). Qed.
Lemma lem4898202 : term110.
Proof. exact (@lem1981473 term64 term47 term47 term47 term35 term47). Qed.
Lemma lem4898204 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4898205 : term112 = term113.
Proof. exact (@lem4898204 (NUMERAL 0) term13). Qed.
Lemma lem4898206 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4898207 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4898208 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem4898207 h1) (fun h1 : term113 = True => @lem4898206)). Qed.
Lemma lem4898209 : term113 = True.
Proof. exact (EQ_MP (@lem4898208) (@lem4898206)). Qed.
Lemma lem4898210 : term112 = True.
Proof. exact (TRANS (@lem4898205) (@lem4898209)). Qed.
Lemma lem4898211 : True = term112.
Proof. exact (SYM (@lem4898210)). Qed.
Lemma lem4898212 : term112.
Proof. exact (EQ_MP (@lem4898211) (@lem0)). Qed.
Lemma lem4898213 : term115.
Proof. exact (@lem4898202 (@lem4898212)). Qed.
Lemma lem4898215 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4898216 : term112 = term113.
Proof. exact (@lem4898215 (NUMERAL 0) term13). Qed.
Lemma lem4898217 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4898218 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4898219 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem4898218 h1) (fun h1 : term113 = True => @lem4898217)). Qed.
Lemma lem4898220 : term113 = True.
Proof. exact (EQ_MP (@lem4898219) (@lem4898217)). Qed.
Lemma lem4898221 : term112 = True.
Proof. exact (TRANS (@lem4898216) (@lem4898220)). Qed.
Lemma lem4898222 : True = term112.
Proof. exact (SYM (@lem4898221)). Qed.
Lemma lem4898223 : term112.
Proof. exact (EQ_MP (@lem4898222) (@lem0)). Qed.
Lemma lem4898224 : term116.
Proof. exact (@lem4898213 (@lem4898223)). Qed.
Lemma lem4898226 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4898227 : term112 = term113.
Proof. exact (@lem4898226 (NUMERAL 0) term13). Qed.
Lemma lem4898228 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4898229 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4898230 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem4898229 h1) (fun h1 : term113 = True => @lem4898228)). Qed.
Lemma lem4898231 : term113 = True.
Proof. exact (EQ_MP (@lem4898230) (@lem4898228)). Qed.
Lemma lem4898232 : term112 = True.
Proof. exact (TRANS (@lem4898227) (@lem4898231)). Qed.
Lemma lem4898233 : True = term112.
Proof. exact (SYM (@lem4898232)). Qed.
Lemma lem4898234 : term112.
Proof. exact (EQ_MP (@lem4898233) (@lem0)). Qed.
Lemma lem4898235 : term117.
Proof. exact (@lem4898224 (@lem4898234)). Qed.
Lemma lem4898237 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4898238 : term73 = term74.
Proof. exact (@lem4898237 term13 term13). Qed.
Lemma lem4898239 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4898240 : term76 = term13.
Proof. exact (EQ_MP (@lem4898239) (@lem940073)). Qed.
Lemma lem4898241 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4898242 : term74 = term47.
Proof. exact (MK_COMB (@lem4898241) (@lem4898240)). Qed.
Lemma lem4898243 : term73 = term47.
Proof. exact (TRANS (@lem4898238) (@lem4898242)). Qed.
Lemma lem4898245 (m : nat) (n : nat) : (term94 m n) = (term95 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4898246 : term91 = term96.
Proof. exact (@lem4898245 term13 term13). Qed.
Lemma lem4898247 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4898248 : term76 = term13.
Proof. exact (EQ_MP (@lem4898247) (@lem940073)). Qed.
Lemma lem4898249 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4898250 : term74 = term47.
Proof. exact (MK_COMB (@lem4898249) (@lem4898248)). Qed.
Lemma lem4898251 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4898252 : term96 = term64.
Proof. exact (MK_COMB (@lem4898251) (@lem4898250)). Qed.
Lemma lem4898253 : term91 = term64.
Proof. exact (TRANS (@lem4898246) (@lem4898252)). Qed.
Lemma lem4898254 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4898255 : term118 = term106.
Proof. exact (MK_COMB (@lem4898254) (@lem4898253)). Qed.
Lemma lem4898256 : term119 = term108.
Proof. exact (MK_COMB (@lem4898255) (@lem4898243)). Qed.
Lemma lem4898258 (m : nat) : (term120 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4898259 : term108 = term35.
Proof. exact (@lem4898258 term13). Qed.
Lemma lem4898260 : term119 = term35.
Proof. exact (TRANS (@lem4898256) (@lem4898259)). Qed.
Lemma lem4898261 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4898262 : term121 = term122.
Proof. exact (MK_COMB (@lem4898261) (@lem4898260)). Qed.
Lemma lem4898263 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem4898264 : term123 = term124.
Proof. exact (MK_COMB (@lem4898262) (@lem4898263)). Qed.
Lemma lem4898266 (x : nat) : (term125 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4898267 : term124 = term35.
Proof. exact (@lem4898266 term13). Qed.
Lemma lem4898268 : term123 = term35.
Proof. exact (TRANS (@lem4898264) (@lem4898267)). Qed.
Lemma lem4898270 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4898271 : term73 = term74.
Proof. exact (@lem4898270 term13 term13). Qed.
Lemma lem4898272 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4898273 : term76 = term13.
Proof. exact (EQ_MP (@lem4898272) (@lem940073)). Qed.
Lemma lem4898274 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4898275 : term74 = term47.
Proof. exact (MK_COMB (@lem4898274) (@lem4898273)). Qed.
Lemma lem4898276 : term73 = term47.
Proof. exact (TRANS (@lem4898271) (@lem4898275)). Qed.
Lemma lem4898277 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem4898278 : term126 = term124.
Proof. exact (MK_COMB (@lem4898277) (@lem4898276)). Qed.
Lemma lem4898280 (x : nat) : (term125 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4898281 : term124 = term35.
Proof. exact (@lem4898280 term13). Qed.
Lemma lem4898282 : term126 = term35.
Proof. exact (TRANS (@lem4898278) (@lem4898281)). Qed.
Lemma lem4898283 : term35 = term126.
Proof. exact (SYM (@lem4898282)). Qed.
Lemma lem4898284 : term123 = term126.
Proof. exact (TRANS (@lem4898268) (@lem4898283)). Qed.
Lemma lem4898285 : term109 = term61.
Proof. exact (@lem4898235 (@lem4898284)). Qed.
Lemma lem4898286 : term108 = term61.
Proof. exact (TRANS (@lem4898201) (@lem4898285)). Qed.
Lemma lem4898288 (x : real) : (term80 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4898289 : term61 = term35.
Proof. exact (@lem4898288 term35). Qed.
Lemma lem4898290 : term108 = term35.
Proof. exact (TRANS (@lem4898286) (@lem4898289)). Qed.
Lemma lem4898291 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4898292 : term127 = term122.
Proof. exact (MK_COMB (@lem4898291) (@lem4898290)). Qed.
Lemma lem4898293 (_60489 : int) : (real_of_int _60489) = (real_of_int _60489).
Proof. exact (eq_refl (real_of_int _60489)). Qed.
Lemma lem4898294 (_60489 : int) : (term105 _60489) = (term128 _60489).
Proof. exact (MK_COMB (@lem4898292) (@lem4898293 _60489)). Qed.
Lemma lem4898295 (_60489 : int) : (term104 _60489) = (term128 _60489).
Proof. exact (TRANS (@lem4898192 _60489) (@lem4898294 _60489)). Qed.
Lemma lem4898296 (_60489 : int) : (term128 _60489) = term35.
Proof. exact (@lem1982719 (real_of_int _60489)). Qed.
Lemma lem4898297 (_60489 : int) : (term104 _60489) = term35.
Proof. exact (TRANS (@lem4898295 _60489) (@lem4898296 _60489)). Qed.
Lemma lem4898298 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4898299 (_60489 : int) : (term129 _60489) = term130.
Proof. exact (MK_COMB (@lem4898298) (@lem4898297 _60489)). Qed.
Lemma lem4898300 : term64 = term64.
Proof. exact (eq_refl term64). Qed.
Lemma lem4898301 (_60489 : int) : (term102 _60489) = term131.
Proof. exact (MK_COMB (@lem4898299 _60489) (@lem4898300)). Qed.
Lemma lem4898302 (_60489 : int) : (term101 _60489) = term131.
Proof. exact (TRANS (@lem4898191 _60489) (@lem4898301 _60489)). Qed.
Lemma lem4898303 : term131 = term64.
Proof. exact (@lem1982721 term64). Qed.
Lemma lem4898304 (_60489 : int) : (term101 _60489) = term64.
Proof. exact (TRANS (@lem4898302 _60489) (@lem4898303)). Qed.
Lemma lem4898305 (_60489 : int) : (term87 _60489) = term64.
Proof. exact (TRANS (@lem4898190 _60489) (@lem4898304 _60489)). Qed.
Lemma lem4898307 (_60489 : int) : (term86 _60489) = term64.
Proof. exact (TRANS (@lem4898145 _60489) (@lem4898305 _60489)). Qed.
Lemma lem4898308 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4898309 (_60489 : int) : (term132 _60489) = term133.
Proof. exact (MK_COMB (@lem4898308) (@lem4898307 _60489)). Qed.
Lemma lem4898310 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem4898311 (_60489 : int) : (term85 _60489) = term134.
Proof. exact (MK_COMB (@lem4898309 _60489) (@lem4898310)). Qed.
Lemma lem4898312 (_60489 : int) : (term52 _60489) = term134.
Proof. exact (TRANS (@lem4898133 _60489) (@lem4898311 _60489)). Qed.
Lemma lem4898313 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4898314 (_60489 : int) : (term53 _60489) = (term135 _60489).
Proof. exact (MK_COMB (@lem4898313) (@lem4898132 _60489)). Qed.
Lemma lem4898315 (_60489 : int) : (term54 _60489) = (term136 _60489).
Proof. exact (MK_COMB (@lem4898314 _60489) (@lem4898312 _60489)). Qed.
Lemma lem4898330 (_60489 : int) : (term56 _60489) = (term136 _60489).
Proof. exact (TRANS (@lem4898084 _60489) (@lem4898315 _60489)). Qed.
Lemma lem4898334 (_60489 : int) (h1 : term136 _60489) : term136 _60489.
Proof. exact (h1). Qed.
Lemma lem4898335 (_60489 : int) (h1 : term136 _60489) : term134.
Proof. exact (proj2 (@lem4898334 _60489 h1)). Qed.
Lemma lem4898338 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem4898339 : term134 = term137.
Proof. exact (@lem4898338 term35 term64). Qed.
Lemma lem4898341 (x : nat) : (term62 x) = (term63 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4898342 : term64 = term65.
Proof. exact (@lem4898341 term13). Qed.
Lemma lem4898344 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4898345 : term35 = term61.
Proof. exact (@lem4898344 (NUMERAL 0)). Qed.
Lemma lem4898346 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4898347 : term37 = term138.
Proof. exact (MK_COMB (@lem4898346) (@lem4898345)). Qed.
Lemma lem4898348 : term137 = term139.
Proof. exact (MK_COMB (@lem4898347) (@lem4898342)). Qed.
Lemma lem4898349 : term140.
Proof. exact (@lem1980026 term35 term47 term64 term47). Qed.
Lemma lem4898351 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4898352 : term112 = term113.
Proof. exact (@lem4898351 (NUMERAL 0) term13). Qed.
Lemma lem4898353 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4898354 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4898355 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem4898354 h1) (fun h1 : term113 = True => @lem4898353)). Qed.
Lemma lem4898356 : term113 = True.
Proof. exact (EQ_MP (@lem4898355) (@lem4898353)). Qed.
Lemma lem4898357 : term112 = True.
Proof. exact (TRANS (@lem4898352) (@lem4898356)). Qed.
Lemma lem4898358 : True = term112.
Proof. exact (SYM (@lem4898357)). Qed.
Lemma lem4898359 : term112.
Proof. exact (EQ_MP (@lem4898358) (@lem0)). Qed.
Lemma lem4898360 : term141.
Proof. exact (@lem4898349 (@lem4898359)). Qed.
Lemma lem4898362 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4898363 : term112 = term113.
Proof. exact (@lem4898362 (NUMERAL 0) term13). Qed.
Lemma lem4898364 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4898365 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4898366 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem4898365 h1) (fun h1 : term113 = True => @lem4898364)). Qed.
Lemma lem4898367 : term113 = True.
Proof. exact (EQ_MP (@lem4898366) (@lem4898364)). Qed.
Lemma lem4898368 : term112 = True.
Proof. exact (TRANS (@lem4898363) (@lem4898367)). Qed.
Lemma lem4898369 : True = term112.
Proof. exact (SYM (@lem4898368)). Qed.
Lemma lem4898370 : term112.
Proof. exact (EQ_MP (@lem4898369) (@lem0)). Qed.
Lemma lem4898371 : term139 = term142.
Proof. exact (@lem4898360 (@lem4898370)). Qed.
Lemma lem4898373 (m : nat) (n : nat) : (term94 m n) = (term95 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4898374 : term91 = term96.
Proof. exact (@lem4898373 term13 term13). Qed.
Lemma lem4898375 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4898376 : term76 = term13.
Proof. exact (EQ_MP (@lem4898375) (@lem940073)). Qed.
Lemma lem4898377 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4898378 : term74 = term47.
Proof. exact (MK_COMB (@lem4898377) (@lem4898376)). Qed.
Lemma lem4898379 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4898380 : term96 = term64.
Proof. exact (MK_COMB (@lem4898379) (@lem4898378)). Qed.
Lemma lem4898381 : term91 = term64.
Proof. exact (TRANS (@lem4898374) (@lem4898380)). Qed.
Lemma lem4898383 (x : nat) : (term125 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4898384 : term124 = term35.
Proof. exact (@lem4898383 term13). Qed.
Lemma lem4898385 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4898386 : term143 = term37.
Proof. exact (MK_COMB (@lem4898385) (@lem4898384)). Qed.
Lemma lem4898387 : term142 = term137.
Proof. exact (MK_COMB (@lem4898386) (@lem4898381)). Qed.
Lemma lem4898389 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem4898390 : term137 = term146.
Proof. exact (@lem4898389 (NUMERAL 0) term13). Qed.
Lemma lem4898391 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4898392 (h1 : term114 = (BIT1 0)) : (term13 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem4898393 : (term114 = (BIT1 0)) = ((term13 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem4898392 h1) (fun h1 : (term13 = (NUMERAL 0)) = False => @lem4898391)). Qed.
Lemma lem4898394 : (term13 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem4898393) (@lem4898391)). Qed.
Lemma lem4898395 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem4898396 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4898397 : term147 = (and True).
Proof. exact (MK_COMB (@lem4898396) (@lem4898395)). Qed.
Lemma lem4898398 : term146 = (True /\ False).
Proof. exact (MK_COMB (@lem4898397) (@lem4898394)). Qed.
Lemma lem4898400 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem4898401 : term146 = False.
Proof. exact (TRANS (@lem4898398) (@lem4898400)). Qed.
Lemma lem4898402 : term137 = False.
Proof. exact (TRANS (@lem4898390) (@lem4898401)). Qed.
Lemma lem4898403 : term142 = False.
Proof. exact (TRANS (@lem4898387) (@lem4898402)). Qed.
Lemma lem4898404 : term139 = False.
Proof. exact (TRANS (@lem4898371) (@lem4898403)). Qed.
Lemma lem4898405 : term137 = False.
Proof. exact (TRANS (@lem4898348) (@lem4898404)). Qed.
Lemma lem4898406 : term134 = False.
Proof. exact (TRANS (@lem4898339) (@lem4898405)). Qed.
Lemma lem4898407 (_60489 : int) (h1 : term136 _60489) : False.
Proof. exact (EQ_MP (@lem4898406) (@lem4898335 _60489 h1)). Qed.
Lemma lem4898409 (_60489 : int) (h1 : term136 _60489) : term136 _60489.
Proof. exact (h1). Qed.
Lemma lem4898410 (_60489 : int) (h1 : term136 _60489) : (term136 _60489) = False.
Proof. exact (prop_ext (fun h2 : term136 _60489 => @lem4898407 _60489 h1) (fun h2 : False => @lem4898409 _60489 h1)). Qed.
Lemma lem4898411 (_60489 : int) (h1 : term136 _60489) : False.
Proof. exact (EQ_MP (@lem4898410 _60489 h1) (@lem4898409 _60489 h1)). Qed.
Lemma lem4898412 (_60489 : int) (h1 : term56 _60489) : term56 _60489.
Proof. exact (h1). Qed.
Lemma lem4898413 (_60489 : int) (h1 : term56 _60489) : term136 _60489.
Proof. exact (EQ_MP (@lem4898330 _60489) (@lem4898412 _60489 h1)). Qed.
Lemma lem4898414 (_60489 : int) (h1 : term56 _60489) : (term136 _60489) = False.
Proof. exact (prop_ext (fun h2 : term136 _60489 => @lem4898411 _60489 h2) (fun h2 : False => @lem4898413 _60489 h1)). Qed.
Lemma lem4898415 (_60489 : int) (h1 : term56 _60489) : False.
Proof. exact (EQ_MP (@lem4898414 _60489 h1) (@lem4898413 _60489 h1)). Qed.
Lemma lem4898416 (_60489 : int) : term148 _60489.
Proof. exact (fun h0 : term56 _60489 => @lem4898415 _60489 h0). Qed.
Lemma lem4898417 (_60489 : int) : term149 _60489.
Proof. exact (@lem1386578 (term150 _60489)). Qed.
Lemma lem4898420 (_60489 : int) : term150 _60489.
Proof. exact (@lem4898417 _60489 (@lem4898416 _60489)). Qed.
Lemma lem4898421 (_60489 : int) : (term54 _60489) = (term27 _60489).
Proof. exact (SYM (@lem4898064 _60489)). Qed.
Lemma lem4898422 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4898423 (_60489 : int) : (term150 _60489) = (term20 _60489).
Proof. exact (MK_COMB (@lem4898422) (@lem4898421 _60489)). Qed.
Lemma lem4898424 (_60489 : int) : term20 _60489.
Proof. exact (EQ_MP (@lem4898423 _60489) (@lem4898420 _60489)). Qed.
Lemma lem4898425 (_60489 : int) : term21 _60489.
Proof. exact (EQ_MP (@lem4898005 _60489) (@lem4898424 _60489)). Qed.
Lemma lem4898426 (n : nat) : term151 n.
Proof. exact (@lem4898425 (int_of_num n)). Qed.
Lemma lem4898427 (n : nat) : term17 n.
Proof. exact (@lem4898426 n (@lem4898004 n)). Qed.
Lemma lem4898428 (n : nat) : (term17 n) = (term5 n).
Proof. exact (SYM (@lem4898001 n)). Qed.
Lemma lem4898429 (n : nat) : term5 n.
Proof. exact (EQ_MP (@lem4898428 n) (@lem4898427 n)). Qed.
Lemma lem4898440 : term152.
Proof. exact (fun n : nat => @lem4898429 n). Qed.
Lemma lem4898443 {_26777 : Type'} (P : _26777 -> Prop) (l : list _26777) (h1 : (term153 _26777 l P) = (@List.Forall _26777 P l)) : (term153 _26777 l P) = (@List.Forall _26777 P l).
Proof. exact (h1). Qed.
Lemma lem4898444 {_26777 : Type'} (P : _26777 -> Prop) (l : list _26777) (h1 : (term153 _26777 l P) = (@List.Forall _26777 P l)) : (@List.Forall _26777 P l) = (term153 _26777 l P).
Proof. exact (SYM (@lem4898443 _26777 P l h1)). Qed.
Lemma lem4898445 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) (h1 : (@List.Forall _26777 P l) = (term153 _26777 l P)) : (@List.Forall _26777 P l) = (term153 _26777 l P).
Proof. exact (h1). Qed.
Lemma lem4898446 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) (h1 : (@List.Forall _26777 P l) = (term153 _26777 l P)) : (term153 _26777 l P) = (@List.Forall _26777 P l).
Proof. exact (SYM (@lem4898445 _26777 l P h1)). Qed.
Lemma lem4898447 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) : ((term153 _26777 l P) = (@List.Forall _26777 P l)) = ((@List.Forall _26777 P l) = (term153 _26777 l P)).
Proof. exact (prop_ext (fun h1 : (term153 _26777 l P) = (@List.Forall _26777 P l) => @lem4898444 _26777 P l h1) (fun h1 : (@List.Forall _26777 P l) = (term153 _26777 l P) => @lem4898446 _26777 l P h1)). Qed.
Lemma lem4898448 {_26777 : Type'} (P : _26777 -> Prop) : (term154 _26777 P) = (term155 _26777 P).
Proof. exact (fun_ext (fun l : list _26777 => @lem4898447 _26777 l P)). Qed.
Lemma lem4898449 {_26777 : Type'} : (@all (list _26777)) = (@all (list _26777)).
Proof. exact (eq_refl (@all (list _26777))). Qed.
Lemma lem4898450 {_26777 : Type'} (P : _26777 -> Prop) : (term156 _26777 P) = (term157 _26777 P).
Proof. exact (MK_COMB (@lem4898449 _26777) (@lem4898448 _26777 P)). Qed.
Lemma lem4898451 {_26777 : Type'} : (term158 _26777) = (term159 _26777).
Proof. exact (fun_ext (fun P : _26777 -> Prop => @lem4898450 _26777 P)). Qed.
Lemma lem4898452 {_26777 : Type'} : (@all (_26777 -> Prop)) = (@all (_26777 -> Prop)).
Proof. exact (eq_refl (@all (_26777 -> Prop))). Qed.
Lemma lem4898453 {_26777 : Type'} : (term160 _26777) = (term161 _26777).
Proof. exact (MK_COMB (@lem4898452 _26777) (@lem4898451 _26777)). Qed.
Lemma lem4898454 {_26777 : Type'} : term161 _26777.
Proof. exact (EQ_MP (@lem4898453 _26777) (@lem1138070 _26777)). Qed.
Lemma lem4898455 {_110366 : Type'} (l : list _110366) : term162 _110366 l.
Proof. exact (@lem4788499 _110366 l). Qed.
Lemma lem4898456 {_110366 : Type'} (l : list _110366) : (term162 _110366 l) = (term163 _110366 l).
Proof. exact (eq_refl (term162 _110366 l)). Qed.
Lemma lem4898457 {_110366 : Type'} (l : list _110366) : term163 _110366 l.
Proof. exact (EQ_MP (@lem4898456 _110366 l) (@lem4898455 _110366 l)). Qed.
Lemma lem4898458 {_110366 : Type'} (l : list _110366) : (term163 _110366 l) = ((term163 _110366 l) = True).
Proof. exact (@lem7 (term163 _110366 l)). Qed.
Lemma lem4898460 {_100044 : Type'} (s : _100044 -> Prop) : term164 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem4898461 {_100044 : Type'} (s : _100044 -> Prop) : (term164 _100044 s) = (term165 _100044 s).
Proof. exact (eq_refl (term164 _100044 s)). Qed.
Lemma lem4898462 {_100044 : Type'} (s : _100044 -> Prop) : term165 _100044 s.
Proof. exact (EQ_MP (@lem4898461 _100044 s) (@lem4898460 _100044 s)). Qed.
Lemma lem4898463 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term166 _100044 s n.
Proof. exact (@lem4898462 _100044 s n). Qed.
Lemma lem4898464 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term166 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term167 _100044 s n)).
Proof. exact (eq_refl (term166 _100044 s n)). Qed.
Lemma lem4898473 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term167 _100044 s n).
Proof. exact (EQ_MP (@lem4898464 _100044 s n) (@lem4898463 _100044 s n)). Qed.
Lemma lem4898474 {_112866 : Type'} (s : _112866 -> Prop) (n : nat) : (@HAS_SIZE _112866 s n) = (term167 _112866 s n).
Proof. exact (@lem4898473 _112866 s n). Qed.
Lemma lem4898475 {_112866 : Type'} (l : list _112866) : (term168 _112866 l) = (term169 _112866 l).
Proof. exact (@lem4898474 _112866 (@set_of_list _112866 l) (@List.length _112866 l)). Qed.
Lemma lem4898479 {_110366 : Type'} (l : list _110366) : (term163 _110366 l) = True.
Proof. exact (EQ_MP (@lem4898458 _110366 l) (@lem4898457 _110366 l)). Qed.
Lemma lem4898480 {_112866 : Type'} (l : list _112866) : (term163 _112866 l) = True.
Proof. exact (@lem4898479 _112866 l). Qed.
Lemma lem4898481 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4898482 {_112866 : Type'} (l : list _112866) : (term170 _112866 l) = (and True).
Proof. exact (MK_COMB (@lem4898481) (@lem4898480 _112866 l)). Qed.
Lemma lem4898485 {_112866 : Type'} (l : list _112866) : ((term171 _112866 l) = (@List.length _112866 l)) = ((term171 _112866 l) = (@List.length _112866 l)).
Proof. exact (eq_refl ((term171 _112866 l) = (@List.length _112866 l))). Qed.
Lemma lem4898486 {_112866 : Type'} (l : list _112866) : (term169 _112866 l) = (term172 _112866 l).
Proof. exact (MK_COMB (@lem4898482 _112866 l) (@lem4898485 _112866 l)). Qed.
Lemma lem4898488 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4898489 {_112866 : Type'} (l : list _112866) : (term172 _112866 l) = ((term171 _112866 l) = (@List.length _112866 l)).
Proof. exact (@lem4898488 ((term171 _112866 l) = (@List.length _112866 l))). Qed.
Lemma lem4898492 {_112866 : Type'} (l : list _112866) : (term169 _112866 l) = ((term171 _112866 l) = (@List.length _112866 l)).
Proof. exact (TRANS (@lem4898486 _112866 l) (@lem4898489 _112866 l)). Qed.
Lemma lem4898493 {_112866 : Type'} (l : list _112866) : (term168 _112866 l) = ((term171 _112866 l) = (@List.length _112866 l)).
Proof. exact (TRANS (@lem4898475 _112866 l) (@lem4898492 _112866 l)). Qed.
Lemma lem4898494 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4898495 {_112866 : Type'} (l : list _112866) : (term173 _112866 l) = (term174 _112866 l).
Proof. exact (MK_COMB (@lem4898494) (@lem4898493 _112866 l)). Qed.
Lemma lem4898498 {_112866 : Type'} (l : list _112866) : (term175 _112866 l) = (term175 _112866 l).
Proof. exact (eq_refl (term175 _112866 l)). Qed.
Lemma lem4898499 {_112866 : Type'} (l : list _112866) : ((term168 _112866 l) = (term175 _112866 l)) = (((term171 _112866 l) = (@List.length _112866 l)) = (term175 _112866 l)).
Proof. exact (MK_COMB (@lem4898495 _112866 l) (@lem4898498 _112866 l)). Qed.
Lemma lem4898502 {_112866 : Type'} : (term176 _112866) = (term177 _112866).
Proof. exact (fun_ext (fun l : list _112866 => @lem4898499 _112866 l)). Qed.
Lemma lem4898503 {_112866 : Type'} : (@all (list _112866)) = (@all (list _112866)).
Proof. exact (eq_refl (@all (list _112866))). Qed.
Lemma lem4898504 {_112866 : Type'} : (term178 _112866) = (term179 _112866).
Proof. exact (MK_COMB (@lem4898503 _112866) (@lem4898502 _112866)). Qed.
Lemma lem4898509 {_112866 : Type'} : (term179 _112866) = (term178 _112866).
Proof. exact (SYM (@lem4898504 _112866)). Qed.
Lemma lem4898511 {A : Type'} (P : type1143 A) : term180 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem4898512 {_112866 : Type'} (P : type1143 _112866) : term180 _112866 P.
Proof. exact (@lem4898511 _112866 P). Qed.
Lemma lem4898513 {_112866 : Type'} : term181 _112866.
Proof. exact (@lem4898512 _112866 (term177 _112866)). Qed.
Lemma lem4898514 {_112866 : Type'} : (term182 _112866) = (((term183 _112866) = (@List.length _112866 (@nil _112866))) = (term184 _112866)).
Proof. exact (eq_refl (term182 _112866)). Qed.
Lemma lem4898515 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4898516 {_112866 : Type'} : (term185 _112866) = (term186 _112866).
Proof. exact (MK_COMB (@lem4898515) (@lem4898514 _112866)). Qed.
Lemma lem4898517 {_112866 : Type'} (t : list _112866) : (term187 _112866 t) = (((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)).
Proof. exact (eq_refl (term187 _112866 t)). Qed.
Lemma lem4898518 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4898519 {_112866 : Type'} (t : list _112866) : (term188 _112866 t) = (term189 _112866 t).
Proof. exact (MK_COMB (@lem4898518) (@lem4898517 _112866 t)). Qed.
Lemma lem4898520 {_112866 : Type'} (h : _112866) (t : list _112866) : (term190 _112866 h t) = (((term191 _112866 h t) = (term192 _112866 h t)) = (term193 _112866 h t)).
Proof. exact (eq_refl (term190 _112866 h t)). Qed.
Lemma lem4898521 {_112866 : Type'} (h : _112866) (t : list _112866) : (term194 _112866 h t) = (term195 _112866 h t).
Proof. exact (MK_COMB (@lem4898519 _112866 t) (@lem4898520 _112866 h t)). Qed.
Lemma lem4898522 {_112866 : Type'} (h : _112866) : (term196 _112866 h) = (term197 _112866 h).
Proof. exact (fun_ext (fun t : list _112866 => @lem4898521 _112866 h t)). Qed.
Lemma lem4898523 {_112866 : Type'} : (@all (list _112866)) = (@all (list _112866)).
Proof. exact (eq_refl (@all (list _112866))). Qed.
Lemma lem4898524 {_112866 : Type'} (h : _112866) : (term198 _112866 h) = (term199 _112866 h).
Proof. exact (MK_COMB (@lem4898523 _112866) (@lem4898522 _112866 h)). Qed.
Lemma lem4898525 {_112866 : Type'} : (term200 _112866) = (term201 _112866).
Proof. exact (fun_ext (fun h : _112866 => @lem4898524 _112866 h)). Qed.
Lemma lem4898526 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4898527 {_112866 : Type'} : (term202 _112866) = (term203 _112866).
Proof. exact (MK_COMB (@lem4898526 _112866) (@lem4898525 _112866)). Qed.
Lemma lem4898528 {_112866 : Type'} : (term204 _112866) = (term205 _112866).
Proof. exact (MK_COMB (@lem4898516 _112866) (@lem4898527 _112866)). Qed.
Lemma lem4898529 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4898530 {_112866 : Type'} : (term206 _112866) = (term207 _112866).
Proof. exact (MK_COMB (@lem4898529) (@lem4898528 _112866)). Qed.
Lemma lem4898531 {_112866 : Type'} (l : list _112866) : (term187 _112866 l) = (((term171 _112866 l) = (@List.length _112866 l)) = (term175 _112866 l)).
Proof. exact (eq_refl (term187 _112866 l)). Qed.
Lemma lem4898532 {_112866 : Type'} : (term208 _112866) = (term177 _112866).
Proof. exact (fun_ext (fun l : list _112866 => @lem4898531 _112866 l)). Qed.
Lemma lem4898533 {_112866 : Type'} : (@all (list _112866)) = (@all (list _112866)).
Proof. exact (eq_refl (@all (list _112866))). Qed.
Lemma lem4898534 {_112866 : Type'} : (term209 _112866) = (term179 _112866).
Proof. exact (MK_COMB (@lem4898533 _112866) (@lem4898532 _112866)). Qed.
Lemma lem4898535 {_112866 : Type'} : (term181 _112866) = (term210 _112866).
Proof. exact (MK_COMB (@lem4898530 _112866) (@lem4898534 _112866)). Qed.
Lemma lem4898536 {_112866 : Type'} : term210 _112866.
Proof. exact (EQ_MP (@lem4898535 _112866) (@lem4898513 _112866)). Qed.
Lemma lem4898537 {_112866 : Type'} (t : list _112866) (h1 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t).
Proof. exact (h1). Qed.
Lemma lem4898589 {A : Type'} : (@set_of_list A (@nil A)) = (@EMPTY A).
Proof. exact (proj1 (@lem4785464 A)). Qed.
Lemma lem4898590 {_112866 : Type'} : (@set_of_list _112866 (@nil _112866)) = (@EMPTY _112866).
Proof. exact (@lem4898589 _112866). Qed.
Lemma lem4898591 {_112866 : Type'} : (@CARD _112866) = (@CARD _112866).
Proof. exact (eq_refl (@CARD _112866)). Qed.
Lemma lem4898592 {_112866 : Type'} : (term183 _112866) = (@CARD _112866 (@EMPTY _112866)).
Proof. exact (MK_COMB (@lem4898591 _112866) (@lem4898590 _112866)). Qed.
Lemma lem4898594 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem4898595 {_112866 : Type'} : (@CARD _112866 (@EMPTY _112866)) = (NUMERAL 0).
Proof. exact (@lem4898594 _112866). Qed.
Lemma lem4898596 {_112866 : Type'} : (term183 _112866) = (NUMERAL 0).
Proof. exact (TRANS (@lem4898592 _112866) (@lem4898595 _112866)). Qed.
Lemma lem4898597 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4898598 {_112866 : Type'} : (term211 _112866) = term212.
Proof. exact (MK_COMB (@lem4898597) (@lem4898596 _112866)). Qed.
Lemma lem4898600 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem4898601 {_112866 : Type'} : (@List.length _112866 (@nil _112866)) = (NUMERAL 0).
Proof. exact (@lem4898600 _112866). Qed.
Lemma lem4898602 {_112866 : Type'} : ((term183 _112866) = (@List.length _112866 (@nil _112866))) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem4898598 _112866) (@lem4898601 _112866)). Qed.
Lemma lem4898604 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4898605 (x : nat) : (x = x) = True.
Proof. exact (@lem4898604 nat x). Qed.
Lemma lem4898606 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem4898605 (NUMERAL 0)). Qed.
Lemma lem4898607 {_112866 : Type'} : ((term183 _112866) = (@List.length _112866 (@nil _112866))) = True.
Proof. exact (TRANS (@lem4898602 _112866) (@lem4898606)). Qed.
Lemma lem4898608 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4898609 {_112866 : Type'} : (term213 _112866) = (@eq Prop True).
Proof. exact (MK_COMB (@lem4898608) (@lem4898607 _112866)). Qed.
Lemma lem4898611 {A : Type'} (r : type1402 A) : (@List.ForallOrdPairs A r (@nil A)) = True.
Proof. exact (EQ_MP (@lem1110673 A r) (@lem1110672 A r)). Qed.
Lemma lem4898612 {_112866 : Type'} (r : type1402 _112866) : (@List.ForallOrdPairs _112866 r (@nil _112866)) = True.
Proof. exact (@lem4898611 _112866 r). Qed.
Lemma lem4898613 {_112866 : Type'} : (term184 _112866) = True.
Proof. exact (@lem4898612 _112866 (term214 _112866)). Qed.
Lemma lem4898614 {_112866 : Type'} : (((term183 _112866) = (@List.length _112866 (@nil _112866))) = (term184 _112866)) = (True = True).
Proof. exact (MK_COMB (@lem4898609 _112866) (@lem4898613 _112866)). Qed.
Lemma lem4898616 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem4898617 : (True = True) = True.
Proof. exact (@lem4898616 True). Qed.
Lemma lem4898618 {_112866 : Type'} : (((term183 _112866) = (@List.length _112866 (@nil _112866))) = (term184 _112866)) = True.
Proof. exact (TRANS (@lem4898614 _112866) (@lem4898617)). Qed.
Lemma lem4898619 {_112866 : Type'} : True = (((term183 _112866) = (@List.length _112866 (@nil _112866))) = (term184 _112866)).
Proof. exact (SYM (@lem4898618 _112866)). Qed.
Lemma lem4898620 {_112866 : Type'} : ((term183 _112866) = (@List.length _112866 (@nil _112866))) = (term184 _112866).
Proof. exact (EQ_MP (@lem4898619 _112866) (@lem0)). Qed.
Lemma lem4898621 {_110384 : Type'} (x : _110384) : term215 _110384 x.
Proof. exact (@lem4790171 _110384 x). Qed.
Lemma lem4898622 {_110384 : Type'} (x : _110384) : (term215 _110384 x) = (term216 _110384 x).
Proof. exact (eq_refl (term215 _110384 x)). Qed.
Lemma lem4898623 {_110384 : Type'} (x : _110384) : term216 _110384 x.
Proof. exact (EQ_MP (@lem4898622 _110384 x) (@lem4898621 _110384 x)). Qed.
Lemma lem4898624 {_110384 : Type'} (x : _110384) (l : list _110384) : term217 _110384 x l.
Proof. exact (@lem4898623 _110384 x l). Qed.
Lemma lem4898625 {_110384 : Type'} (x : _110384) (l : list _110384) : (term217 _110384 x l) = ((term218 _110384 x l) = (@List.In _110384 x l)).
Proof. exact (eq_refl (term217 _110384 x l)). Qed.
Lemma lem4898627 {_26777 : Type'} (P : _26777 -> Prop) : term219 _26777 P.
Proof. exact (@lem4898454 _26777 P). Qed.
Lemma lem4898628 {_26777 : Type'} (P : _26777 -> Prop) : (term219 _26777 P) = (term157 _26777 P).
Proof. exact (eq_refl (term219 _26777 P)). Qed.
Lemma lem4898629 {_26777 : Type'} (P : _26777 -> Prop) : term157 _26777 P.
Proof. exact (EQ_MP (@lem4898628 _26777 P) (@lem4898627 _26777 P)). Qed.
Lemma lem4898630 {_26777 : Type'} (P : _26777 -> Prop) (l : list _26777) : term220 _26777 P l.
Proof. exact (@lem4898629 _26777 P l). Qed.
Lemma lem4898631 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) : (term220 _26777 P l) = ((@List.Forall _26777 P l) = (term153 _26777 l P)).
Proof. exact (eq_refl (term220 _26777 P l)). Qed.
Lemma lem4898633 {_110366 : Type'} (l : list _110366) : term162 _110366 l.
Proof. exact (@lem4788499 _110366 l). Qed.
Lemma lem4898634 {_110366 : Type'} (l : list _110366) : (term162 _110366 l) = (term163 _110366 l).
Proof. exact (eq_refl (term162 _110366 l)). Qed.
Lemma lem4898635 {_110366 : Type'} (l : list _110366) : term163 _110366 l.
Proof. exact (EQ_MP (@lem4898634 _110366 l) (@lem4898633 _110366 l)). Qed.
Lemma lem4898636 {_110366 : Type'} (l : list _110366) : (term163 _110366 l) = ((term163 _110366 l) = True).
Proof. exact (@lem7 (term163 _110366 l)). Qed.
Lemma lem4898644 {A : Type'} : term221 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem4898645 {A : Type'} (h : A) : term222 A h.
Proof. exact (@lem4898644 A h). Qed.
Lemma lem4898646 {A : Type'} (h : A) : (term222 A h) = (term223 A h).
Proof. exact (eq_refl (term222 A h)). Qed.
Lemma lem4898647 {A : Type'} (h : A) : term223 A h.
Proof. exact (EQ_MP (@lem4898646 A h) (@lem4898645 A h)). Qed.
Lemma lem4898648 {A : Type'} (h : A) (t : list A) : term224 A h t.
Proof. exact (@lem4898647 A h t). Qed.
Lemma lem4898649 {A : Type'} (h : A) (t : list A) : (term224 A h t) = ((term192 A h t) = (term225 A t)).
Proof. exact (eq_refl (term224 A h t)). Qed.
Lemma lem4898652 {A : Type'} : term226 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem4898653 {A : Type'} (x : A) : term227 A x.
Proof. exact (@lem4898652 A x). Qed.
Lemma lem4898654 {A : Type'} (x : A) : (term227 A x) = (term228 A x).
Proof. exact (eq_refl (term227 A x)). Qed.
Lemma lem4898655 {A : Type'} (x : A) : term228 A x.
Proof. exact (EQ_MP (@lem4898654 A x) (@lem4898653 A x)). Qed.
Lemma lem4898656 {A : Type'} (x : A) (s : A -> Prop) : term229 A x s.
Proof. exact (@lem4898655 A x s). Qed.
Lemma lem4898657 {A : Type'} (x : A) (s : A -> Prop) : (term229 A x s) = (term230 A x s).
Proof. exact (eq_refl (term229 A x s)). Qed.
Lemma lem4898658 {A : Type'} (x : A) (s : A -> Prop) : term230 A x s.
Proof. exact (EQ_MP (@lem4898657 A x s) (@lem4898656 A x s)). Qed.
Lemma lem4898659 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4898660 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term231 A x s) = (term232 A x s).
Proof. exact (@lem4898658 A x s (@lem4898659 A s h1)). Qed.
Lemma lem4898672 {A : Type'} (h : A) (t : list A) : (term233 A h t) = (term234 A h t).
Proof. exact (EQ_MP (@lem4785471 A h t) (@lem4785470 A h t)). Qed.
Lemma lem4898673 {_112866 : Type'} (h : _112866) (t : list _112866) : (term233 _112866 h t) = (term234 _112866 h t).
Proof. exact (@lem4898672 _112866 h t). Qed.
Lemma lem4898674 {_112866 : Type'} : (@CARD _112866) = (@CARD _112866).
Proof. exact (eq_refl (@CARD _112866)). Qed.
Lemma lem4898675 {_112866 : Type'} (h : _112866) (t : list _112866) : (term191 _112866 h t) = (term235 _112866 h t).
Proof. exact (MK_COMB (@lem4898674 _112866) (@lem4898673 _112866 h t)). Qed.
Lemma lem4898677 {A : Type'} (x : A) (s : A -> Prop) : term230 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem4898660 A x s h0). Qed.
Lemma lem4898678 {_112866 : Type'} (x : _112866) (s : _112866 -> Prop) : term230 _112866 x s.
Proof. exact (@lem4898677 _112866 x s). Qed.
Lemma lem4898679 {_112866 : Type'} (h : _112866) (t : list _112866) : term236 _112866 h t.
Proof. exact (@lem4898678 _112866 h (@set_of_list _112866 t)). Qed.
Lemma lem4898681 {_110366 : Type'} (l : list _110366) : (term163 _110366 l) = True.
Proof. exact (EQ_MP (@lem4898636 _110366 l) (@lem4898635 _110366 l)). Qed.
Lemma lem4898682 {_112866 : Type'} (l : list _112866) : (term163 _112866 l) = True.
Proof. exact (@lem4898681 _112866 l). Qed.
Lemma lem4898683 {_112866 : Type'} (t : list _112866) : (term163 _112866 t) = True.
Proof. exact (@lem4898682 _112866 t). Qed.
Lemma lem4898684 {_112866 : Type'} (t : list _112866) : True = (term163 _112866 t).
Proof. exact (SYM (@lem4898683 _112866 t)). Qed.
Lemma lem4898685 {_112866 : Type'} (t : list _112866) : term163 _112866 t.
Proof. exact (EQ_MP (@lem4898684 _112866 t) (@lem0)). Qed.
Lemma lem4898686 {_112866 : Type'} (h : _112866) (t : list _112866) : (term235 _112866 h t) = (term237 _112866 h t).
Proof. exact (@lem4898679 _112866 h t (@lem4898685 _112866 t)). Qed.
Lemma lem4898688 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term238 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4898689 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term239 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4898688 _2963 g t e g' t' e'). Qed.
Lemma lem4898690 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term240 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4898689 _2963 g t e g' t'). Qed.
Lemma lem4898691 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term241 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4898690 _2963 g t e g'). Qed.
Lemma lem4898692 (g : Prop) (t : nat) (e : nat) : term242 g t e.
Proof. exact (@lem4898691 nat g t e). Qed.
Lemma lem4898693 {_112866 : Type'} (h : _112866) (t : list _112866) : term243 _112866 h t.
Proof. exact (@lem4898692 (term218 _112866 h t) (term171 _112866 t) (term244 _112866 t)). Qed.
Lemma lem4898694 {_112866 : Type'} (h : _112866) (t : list _112866) (g' : Prop) : term245 _112866 h t g'.
Proof. exact (@lem4898693 _112866 h t g'). Qed.
Lemma lem4898695 {_112866 : Type'} (h : _112866) (t : list _112866) (g' : Prop) : (term245 _112866 h t g') = (term246 _112866 h t g').
Proof. exact (eq_refl (term245 _112866 h t g')). Qed.
Lemma lem4898696 {_112866 : Type'} (h : _112866) (t : list _112866) (g' : Prop) : term246 _112866 h t g'.
Proof. exact (EQ_MP (@lem4898695 _112866 h t g') (@lem4898694 _112866 h t g')). Qed.
Lemma lem4898697 {_112866 : Type'} (h : _112866) (t : list _112866) (g' : Prop) (t' : nat) : term247 _112866 h t g' t'.
Proof. exact (@lem4898696 _112866 h t g' t'). Qed.
Lemma lem4898698 {_112866 : Type'} (h : _112866) (t : list _112866) (g' : Prop) (t' : nat) : (term247 _112866 h t g' t') = (term248 _112866 h t g' t').
Proof. exact (eq_refl (term247 _112866 h t g' t')). Qed.
Lemma lem4898699 {_112866 : Type'} (h : _112866) (t : list _112866) (g' : Prop) (t' : nat) : term248 _112866 h t g' t'.
Proof. exact (EQ_MP (@lem4898698 _112866 h t g' t') (@lem4898697 _112866 h t g' t')). Qed.
Lemma lem4898700 {_112866 : Type'} (h : _112866) (t : list _112866) (g' : Prop) (t' : nat) (e' : nat) : term249 _112866 h t g' t' e'.
Proof. exact (@lem4898699 _112866 h t g' t' e'). Qed.
Lemma lem4898701 {_112866 : Type'} (h : _112866) (t : list _112866) (g' : Prop) (t' : nat) (e' : nat) : (term249 _112866 h t g' t' e') = (term250 _112866 h t g' t' e').
Proof. exact (eq_refl (term249 _112866 h t g' t' e')). Qed.
Lemma lem4898702 {_112866 : Type'} (h : _112866) (t : list _112866) (g' : Prop) (t' : nat) (e' : nat) : term250 _112866 h t g' t' e'.
Proof. exact (EQ_MP (@lem4898701 _112866 h t g' t' e') (@lem4898700 _112866 h t g' t' e')). Qed.
Lemma lem4898704 {_110384 : Type'} (x : _110384) (l : list _110384) : (term218 _110384 x l) = (@List.In _110384 x l).
Proof. exact (EQ_MP (@lem4898625 _110384 x l) (@lem4898624 _110384 x l)). Qed.
Lemma lem4898705 {_112866 : Type'} (x : _112866) (l : list _112866) : (term218 _112866 x l) = (@List.In _112866 x l).
Proof. exact (@lem4898704 _112866 x l). Qed.
Lemma lem4898706 {_112866 : Type'} (h : _112866) (t : list _112866) : (term218 _112866 h t) = (@List.In _112866 h t).
Proof. exact (@lem4898705 _112866 h t). Qed.
Lemma lem4898707 {_112866 : Type'} (h : _112866) (t : list _112866) (t' : nat) (e' : nat) : term251 _112866 h t t' e'.
Proof. exact (@lem4898702 _112866 h t (@List.In _112866 h t) t' e'). Qed.
Lemma lem4898708 {_112866 : Type'} (h : _112866) (t : list _112866) (t' : nat) (e' : nat) : term252 _112866 h t t' e'.
Proof. exact (@lem4898707 _112866 h t t' e' (@lem4898706 _112866 h t)). Qed.
Lemma lem4898712 {_112866 : Type'} (t : list _112866) : (term171 _112866 t) = (term171 _112866 t).
Proof. exact (eq_refl (term171 _112866 t)). Qed.
Lemma lem4898713 {_112866 : Type'} (h : _112866) (t : list _112866) : term253 _112866 h t.
Proof. exact (fun h0 : @List.In _112866 h t => @lem4898712 _112866 t). Qed.
Lemma lem4898714 {_112866 : Type'} (h : _112866) (t : list _112866) (e' : nat) : term254 _112866 h t e'.
Proof. exact (@lem4898708 _112866 h t (term171 _112866 t) e'). Qed.
Lemma lem4898715 {_112866 : Type'} (h : _112866) (t : list _112866) (e' : nat) : term255 _112866 h t e'.
Proof. exact (@lem4898714 _112866 h t e' (@lem4898713 _112866 h t)). Qed.
Lemma lem4898719 {_112866 : Type'} (t : list _112866) : (term244 _112866 t) = (term244 _112866 t).
Proof. exact (eq_refl (term244 _112866 t)). Qed.
Lemma lem4898720 {_112866 : Type'} (h : _112866) (t : list _112866) : term256 _112866 h t.
Proof. exact (fun h0 : term257 _112866 h t => @lem4898719 _112866 t). Qed.
Lemma lem4898721 {_112866 : Type'} (h : _112866) (t : list _112866) : term258 _112866 h t.
Proof. exact (@lem4898715 _112866 h t (term244 _112866 t)). Qed.
Lemma lem4898722 {_112866 : Type'} (h : _112866) (t : list _112866) : (term237 _112866 h t) = (term259 _112866 h t).
Proof. exact (@lem4898721 _112866 h t (@lem4898720 _112866 h t)). Qed.
Lemma lem4898756 {_112866 : Type'} (h : _112866) (t : list _112866) : (term235 _112866 h t) = (term259 _112866 h t).
Proof. exact (TRANS (@lem4898686 _112866 h t) (@lem4898722 _112866 h t)). Qed.
Lemma lem4898757 {_112866 : Type'} (h : _112866) (t : list _112866) : (term191 _112866 h t) = (term259 _112866 h t).
Proof. exact (TRANS (@lem4898675 _112866 h t) (@lem4898756 _112866 h t)). Qed.
Lemma lem4898758 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4898759 {_112866 : Type'} (h : _112866) (t : list _112866) : (term260 _112866 h t) = (term261 _112866 h t).
Proof. exact (MK_COMB (@lem4898758) (@lem4898757 _112866 h t)). Qed.
Lemma lem4898794 {A : Type'} (h : A) (t : list A) : (term192 A h t) = (term225 A t).
Proof. exact (EQ_MP (@lem4898649 A h t) (@lem4898648 A h t)). Qed.
Lemma lem4898795 {_112866 : Type'} (h : _112866) (t : list _112866) : (term192 _112866 h t) = (term225 _112866 t).
Proof. exact (@lem4898794 _112866 h t). Qed.
Lemma lem4898796 {_112866 : Type'} (h : _112866) (t : list _112866) : ((term191 _112866 h t) = (term192 _112866 h t)) = ((term259 _112866 h t) = (term225 _112866 t)).
Proof. exact (MK_COMB (@lem4898759 _112866 h t) (@lem4898795 _112866 h t)). Qed.
Lemma lem4898832 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4898833 {_112866 : Type'} (h : _112866) (t : list _112866) : (term262 _112866 h t) = (term263 _112866 h t).
Proof. exact (MK_COMB (@lem4898832) (@lem4898796 _112866 h t)). Qed.
Lemma lem4898870 {A : Type'} (h : A) (r : type1402 A) (t : list A) : (term264 A r h t) = (term265 A h r t).
Proof. exact (EQ_MP (@lem1110682 A h r t) (@lem1110681 A h r t)). Qed.
Lemma lem4898871 {_112866 : Type'} (h : _112866) (r : type1402 _112866) (t : list _112866) : (term264 _112866 r h t) = (term265 _112866 h r t).
Proof. exact (@lem4898870 _112866 h r t). Qed.
Lemma lem4898872 {_112866 : Type'} (h : _112866) (t : list _112866) : (term193 _112866 h t) = (term266 _112866 h t).
Proof. exact (@lem4898871 _112866 h (term214 _112866) t). Qed.
Lemma lem4898876 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) : (@List.Forall _26777 P l) = (term153 _26777 l P).
Proof. exact (EQ_MP (@lem4898631 _26777 l P) (@lem4898630 _26777 P l)). Qed.
Lemma lem4898877 {_112866 : Type'} (l : list _112866) (P : _112866 -> Prop) : (@List.Forall _112866 P l) = (term153 _112866 l P).
Proof. exact (@lem4898876 _112866 l P). Qed.
Lemma lem4898878 {_112866 : Type'} (t : list _112866) (h : _112866) : (term267 _112866 h t) = (term268 _112866 t h).
Proof. exact (@lem4898877 _112866 t (term269 _112866 h)). Qed.
Lemma lem4898886 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term270 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4898887 (p : Prop) (q : Prop) (p' : Prop) : term271 p q p'.
Proof. exact (fun q' : Prop => @lem4898886 p q p' q'). Qed.
Lemma lem4898888 (p : Prop) (q : Prop) : term272 p q.
Proof. exact (fun p' : Prop => @lem4898887 p q p'). Qed.
Lemma lem4898889 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : term273 _112866 t h x.
Proof. exact (@lem4898888 (@List.In _112866 x t) (term274 _112866 h x)). Qed.
Lemma lem4898890 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) (p' : Prop) : term275 _112866 t h x p'.
Proof. exact (@lem4898889 _112866 t h x p'). Qed.
Lemma lem4898891 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) (p' : Prop) : (term275 _112866 t h x p') = (term276 _112866 t h x p').
Proof. exact (eq_refl (term275 _112866 t h x p')). Qed.
Lemma lem4898892 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) (p' : Prop) : term276 _112866 t h x p'.
Proof. exact (EQ_MP (@lem4898891 _112866 t h x p') (@lem4898890 _112866 t h x p')). Qed.
Lemma lem4898893 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) (p' : Prop) (q' : Prop) : term277 _112866 t h x p' q'.
Proof. exact (@lem4898892 _112866 t h x p' q'). Qed.
Lemma lem4898894 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) (p' : Prop) (q' : Prop) : (term277 _112866 t h x p' q') = (term278 _112866 t h x p' q').
Proof. exact (eq_refl (term277 _112866 t h x p' q')). Qed.
Lemma lem4898895 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) (p' : Prop) (q' : Prop) : term278 _112866 t h x p' q'.
Proof. exact (EQ_MP (@lem4898894 _112866 t h x p' q') (@lem4898893 _112866 t h x p' q')). Qed.
Lemma lem4898896 {_112866 : Type'} (x : _112866) (t : list _112866) : (@List.In _112866 x t) = (@List.In _112866 x t).
Proof. exact (eq_refl (@List.In _112866 x t)). Qed.
Lemma lem4898897 {_112866 : Type'} (h : _112866) (x : _112866) (t : list _112866) (q' : Prop) : term279 _112866 h x t q'.
Proof. exact (@lem4898895 _112866 t h x (@List.In _112866 x t) q'). Qed.
Lemma lem4898898 {_112866 : Type'} (h : _112866) (x : _112866) (t : list _112866) (q' : Prop) : term280 _112866 h x t q'.
Proof. exact (@lem4898897 _112866 h x t q' (@lem4898896 _112866 x t)). Qed.
Lemma lem4898903 {A B : Type'} (f : A -> B) (y : A) : (term281 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4898904 {_112866 : Type'} (f : type1402 _112866) (y : _112866) : (term282 _112866 f y) = (f y).
Proof. exact (@lem4898903 _112866 (_112866 -> Prop) f y). Qed.
Lemma lem4898905 {_112866 : Type'} (h : _112866) : (term283 _112866 h) = (term269 _112866 h).
Proof. exact (@lem4898904 _112866 (term214 _112866) h). Qed.
Lemma lem4898906 {_112866 : Type'} (x : _112866) : (term269 _112866 x) = (term284 _112866 x).
Proof. exact (eq_refl (term269 _112866 x)). Qed.
Lemma lem4898907 {_112866 : Type'} : (term285 _112866) = (term214 _112866).
Proof. exact (fun_ext (fun x : _112866 => @lem4898906 _112866 x)). Qed.
Lemma lem4898908 {_112866 : Type'} (h : _112866) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem4898909 {_112866 : Type'} (h : _112866) : (term283 _112866 h) = (term269 _112866 h).
Proof. exact (MK_COMB (@lem4898907 _112866) (@lem4898908 _112866 h)). Qed.
Lemma lem4898910 {_112866 : Type'} : (@eq (_112866 -> Prop)) = (@eq (_112866 -> Prop)).
Proof. exact (eq_refl (@eq (_112866 -> Prop))). Qed.
Lemma lem4898911 {_112866 : Type'} (h : _112866) : (term286 _112866 h) = (term287 _112866 h).
Proof. exact (MK_COMB (@lem4898910 _112866) (@lem4898909 _112866 h)). Qed.
Lemma lem4898912 {_112866 : Type'} (h : _112866) : (term269 _112866 h) = (term284 _112866 h).
Proof. exact (eq_refl (term269 _112866 h)). Qed.
Lemma lem4898913 {_112866 : Type'} (h : _112866) : ((term283 _112866 h) = (term269 _112866 h)) = ((term269 _112866 h) = (term284 _112866 h)).
Proof. exact (MK_COMB (@lem4898911 _112866 h) (@lem4898912 _112866 h)). Qed.
Lemma lem4898914 {_112866 : Type'} (h : _112866) : (term269 _112866 h) = (term284 _112866 h).
Proof. exact (EQ_MP (@lem4898913 _112866 h) (@lem4898905 _112866 h)). Qed.
Lemma lem4898917 {_112866 : Type'} (x : _112866) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4898918 {_112866 : Type'} (h : _112866) (x : _112866) : (term274 _112866 h x) = (term288 _112866 h x).
Proof. exact (MK_COMB (@lem4898914 _112866 h) (@lem4898917 _112866 x)). Qed.
Lemma lem4898920 {A B : Type'} (f : A -> B) (y : A) : (term281 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4898921 {_112866 : Type'} (f : _112866 -> Prop) (y : _112866) : (term289 _112866 f y) = (f y).
Proof. exact (@lem4898920 _112866 Prop f y). Qed.
Lemma lem4898922 {_112866 : Type'} (h : _112866) (x : _112866) : (term290 _112866 h x) = (term288 _112866 h x).
Proof. exact (@lem4898921 _112866 (term284 _112866 h) x). Qed.
Lemma lem4898923 {_112866 : Type'} (h : _112866) (y : _112866) : (term288 _112866 h y) = (term291 _112866 h y).
Proof. exact (eq_refl (term288 _112866 h y)). Qed.
Lemma lem4898924 {_112866 : Type'} (h : _112866) : (term292 _112866 h) = (term284 _112866 h).
Proof. exact (fun_ext (fun y : _112866 => @lem4898923 _112866 h y)). Qed.
Lemma lem4898925 {_112866 : Type'} (x : _112866) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4898926 {_112866 : Type'} (h : _112866) (x : _112866) : (term290 _112866 h x) = (term288 _112866 h x).
Proof. exact (MK_COMB (@lem4898924 _112866 h) (@lem4898925 _112866 x)). Qed.
Lemma lem4898927 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4898928 {_112866 : Type'} (h : _112866) (x : _112866) : (term293 _112866 h x) = (term294 _112866 h x).
Proof. exact (MK_COMB (@lem4898927) (@lem4898926 _112866 h x)). Qed.
Lemma lem4898929 {_112866 : Type'} (h : _112866) (x : _112866) : (term288 _112866 h x) = (term291 _112866 h x).
Proof. exact (eq_refl (term288 _112866 h x)). Qed.
Lemma lem4898930 {_112866 : Type'} (h : _112866) (x : _112866) : ((term290 _112866 h x) = (term288 _112866 h x)) = ((term288 _112866 h x) = (term291 _112866 h x)).
Proof. exact (MK_COMB (@lem4898928 _112866 h x) (@lem4898929 _112866 h x)). Qed.
Lemma lem4898931 {_112866 : Type'} (h : _112866) (x : _112866) : (term288 _112866 h x) = (term291 _112866 h x).
Proof. exact (EQ_MP (@lem4898930 _112866 h x) (@lem4898922 _112866 h x)). Qed.
Lemma lem4898934 {_112866 : Type'} (h : _112866) (x : _112866) : (term274 _112866 h x) = (term291 _112866 h x).
Proof. exact (TRANS (@lem4898918 _112866 h x) (@lem4898931 _112866 h x)). Qed.
Lemma lem4898935 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : term295 _112866 t h x.
Proof. exact (fun h0 : @List.In _112866 x t => @lem4898934 _112866 h x). Qed.
Lemma lem4898936 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : term296 _112866 t h x.
Proof. exact (@lem4898898 _112866 h x t (term291 _112866 h x)). Qed.
Lemma lem4898937 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term297 _112866 t h x) = (term298 _112866 t h x).
Proof. exact (@lem4898936 _112866 t h x (@lem4898935 _112866 t h x)). Qed.
Lemma lem4898965 {_112866 : Type'} (t : list _112866) (h : _112866) : (term299 _112866 t h) = (term300 _112866 t h).
Proof. exact (fun_ext (fun x : _112866 => @lem4898937 _112866 t h x)). Qed.
Lemma lem4898993 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4898994 {_112866 : Type'} (t : list _112866) (h : _112866) : (term268 _112866 t h) = (term301 _112866 t h).
Proof. exact (MK_COMB (@lem4898993 _112866) (@lem4898965 _112866 t h)). Qed.
Lemma lem4899026 {_112866 : Type'} (t : list _112866) (h : _112866) : (term267 _112866 h t) = (term301 _112866 t h).
Proof. exact (TRANS (@lem4898878 _112866 t h) (@lem4898994 _112866 t h)). Qed.
Lemma lem4899027 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4899028 {_112866 : Type'} (t : list _112866) (h : _112866) : (term302 _112866 h t) = (term303 _112866 t h).
Proof. exact (MK_COMB (@lem4899027) (@lem4899026 _112866 t h)). Qed.
Lemma lem4899062 {_112866 : Type'} (t : list _112866) : (term175 _112866 t) = (term175 _112866 t).
Proof. exact (eq_refl (term175 _112866 t)). Qed.
Lemma lem4899063 {_112866 : Type'} (h : _112866) (t : list _112866) : (term266 _112866 h t) = (term304 _112866 h t).
Proof. exact (MK_COMB (@lem4899028 _112866 t h) (@lem4899062 _112866 t)). Qed.
Lemma lem4899099 {_112866 : Type'} (h : _112866) (t : list _112866) : (term193 _112866 h t) = (term304 _112866 h t).
Proof. exact (TRANS (@lem4898872 _112866 h t) (@lem4899063 _112866 h t)). Qed.
Lemma lem4899100 {_112866 : Type'} (h : _112866) (t : list _112866) : (((term191 _112866 h t) = (term192 _112866 h t)) = (term193 _112866 h t)) = (((term259 _112866 h t) = (term225 _112866 t)) = (term304 _112866 h t)).
Proof. exact (MK_COMB (@lem4898833 _112866 h t) (@lem4899099 _112866 h t)). Qed.
Lemma lem4899173 {_112866 : Type'} (h : _112866) (t : list _112866) : (((term259 _112866 h t) = (term225 _112866 t)) = (term304 _112866 h t)) = (((term191 _112866 h t) = (term192 _112866 h t)) = (term193 _112866 h t)).
Proof. exact (SYM (@lem4899100 _112866 h t)). Qed.
Lemma lem4899174 (_474 : nat) (_475 : Prop) (_476 : nat -> Prop) (_477 : nat) : (term305 _476 _475 _474 _477) = (term306 _474 _475 _476 _477).
Proof. exact (@lem13473 nat _474 _475 _476 _477). Qed.
Lemma lem4899175 {_112866 : Type'} (_474 : nat) (_475 : Prop) (h : _112866) (t : list _112866) (_477 : nat) : (term307 _112866 h t _475 _474 _477) = (term308 _112866 _474 _475 h t _477).
Proof. exact (@lem4899174 _474 _475 (term309 _112866 h t) _477). Qed.
Lemma lem4899176 {_112866 : Type'} (h : _112866) (t : list _112866) : (term310 _112866 h t) = (term311 _112866 h t).
Proof. exact (@lem4899175 _112866 (term171 _112866 t) (@List.In _112866 h t) h t (term244 _112866 t)). Qed.
Lemma lem4899177 {_112866 : Type'} (h : _112866) (t : list _112866) : (term312 _112866 h t) = (((term244 _112866 t) = (term225 _112866 t)) = (term304 _112866 h t)).
Proof. exact (eq_refl (term312 _112866 h t)). Qed.
Lemma lem4899178 {_112866 : Type'} (h : _112866) (t : list _112866) : (term313 _112866 h t) = (term313 _112866 h t).
Proof. exact (eq_refl (term313 _112866 h t)). Qed.
Lemma lem4899179 {_112866 : Type'} (h : _112866) (t : list _112866) : (term314 _112866 h t) = (term315 _112866 h t).
Proof. exact (MK_COMB (@lem4899178 _112866 h t) (@lem4899177 _112866 h t)). Qed.
Lemma lem4899180 {_112866 : Type'} (h : _112866) (t : list _112866) : (term316 _112866 h t) = (((term171 _112866 t) = (term225 _112866 t)) = (term304 _112866 h t)).
Proof. exact (eq_refl (term316 _112866 h t)). Qed.
Lemma lem4899181 {_112866 : Type'} (h : _112866) (t : list _112866) : (term317 _112866 h t) = (term317 _112866 h t).
Proof. exact (eq_refl (term317 _112866 h t)). Qed.
Lemma lem4899182 {_112866 : Type'} (h : _112866) (t : list _112866) : (term318 _112866 h t) = (term319 _112866 h t).
Proof. exact (MK_COMB (@lem4899181 _112866 h t) (@lem4899180 _112866 h t)). Qed.
Lemma lem4899183 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4899184 {_112866 : Type'} (h : _112866) (t : list _112866) : (term320 _112866 h t) = (term321 _112866 h t).
Proof. exact (MK_COMB (@lem4899183) (@lem4899182 _112866 h t)). Qed.
Lemma lem4899185 {_112866 : Type'} (h : _112866) (t : list _112866) : (term311 _112866 h t) = (term322 _112866 h t).
Proof. exact (MK_COMB (@lem4899184 _112866 h t) (@lem4899179 _112866 h t)). Qed.
Lemma lem4899186 {_112866 : Type'} (h : _112866) (t : list _112866) : (term310 _112866 h t) = (((term259 _112866 h t) = (term225 _112866 t)) = (term304 _112866 h t)).
Proof. exact (eq_refl (term310 _112866 h t)). Qed.
Lemma lem4899187 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4899188 {_112866 : Type'} (h : _112866) (t : list _112866) : (term323 _112866 h t) = (term324 _112866 h t).
Proof. exact (MK_COMB (@lem4899187) (@lem4899186 _112866 h t)). Qed.
Lemma lem4899189 {_112866 : Type'} (h : _112866) (t : list _112866) : ((term310 _112866 h t) = (term311 _112866 h t)) = ((((term259 _112866 h t) = (term225 _112866 t)) = (term304 _112866 h t)) = (term322 _112866 h t)).
Proof. exact (MK_COMB (@lem4899188 _112866 h t) (@lem4899185 _112866 h t)). Qed.
Lemma lem4899190 {_112866 : Type'} (h : _112866) (t : list _112866) : (((term259 _112866 h t) = (term225 _112866 t)) = (term304 _112866 h t)) = (term322 _112866 h t).
Proof. exact (EQ_MP (@lem4899189 _112866 h t) (@lem4899176 _112866 h t)). Qed.
Lemma lem4899191 {_112866 : Type'} (h : _112866) (t : list _112866) : (term322 _112866 h t) = (((term259 _112866 h t) = (term225 _112866 t)) = (term304 _112866 h t)).
Proof. exact (SYM (@lem4899190 _112866 h t)). Qed.
Lemma lem4899192 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : @List.In _112866 h t) : @List.In _112866 h t.
Proof. exact (h1). Qed.
Lemma lem4899209 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term257 _112866 h t) : term257 _112866 h t.
Proof. exact (h1). Qed.
Lemma lem4899252 (m : nat) : term325 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem4899253 (m : nat) : (term325 m) = (term326 m).
Proof. exact (eq_refl (term325 m)). Qed.
Lemma lem4899254 (m : nat) : term326 m.
Proof. exact (EQ_MP (@lem4899253 m) (@lem4899252 m)). Qed.
Lemma lem4899255 (m : nat) (n : nat) : term327 m n.
Proof. exact (@lem4899254 m n). Qed.
Lemma lem4899256 (m : nat) (n : nat) : (term327 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term327 m n)). Qed.
Lemma lem4899263 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem4899256 m n) (@lem4899255 m n)). Qed.
Lemma lem4899264 {_112866 : Type'} (t : list _112866) : ((term244 _112866 t) = (term225 _112866 t)) = ((term171 _112866 t) = (@List.length _112866 t)).
Proof. exact (@lem4899263 (term171 _112866 t) (@List.length _112866 t)). Qed.
Lemma lem4899266 {_112866 : Type'} (t : list _112866) (h1 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t).
Proof. exact (h1). Qed.
Lemma lem4899267 {_112866 : Type'} (t : list _112866) (h1 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) : ((term244 _112866 t) = (term225 _112866 t)) = (term175 _112866 t).
Proof. exact (TRANS (@lem4899264 _112866 t) (@lem4899266 _112866 t h1)). Qed.
Lemma lem4899270 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4899271 {_112866 : Type'} (t : list _112866) (h1 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) : (term328 _112866 t) = (term329 _112866 t).
Proof. exact (MK_COMB (@lem4899270) (@lem4899267 _112866 t h1)). Qed.
Lemma lem4899284 {_112866 : Type'} (h : _112866) (t : list _112866) : (term304 _112866 h t) = (term304 _112866 h t).
Proof. exact (eq_refl (term304 _112866 h t)). Qed.
Lemma lem4899285 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) : (((term244 _112866 t) = (term225 _112866 t)) = (term304 _112866 h t)) = ((term175 _112866 t) = (term304 _112866 h t)).
Proof. exact (MK_COMB (@lem4899271 _112866 t h1) (@lem4899284 _112866 h t)). Qed.
Lemma lem4899288 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) : ((term175 _112866 t) = (term304 _112866 h t)) = (((term244 _112866 t) = (term225 _112866 t)) = (term304 _112866 h t)).
Proof. exact (SYM (@lem4899285 _112866 h t h1)). Qed.
Lemma lem4899290 (p : Prop) : p = (term330 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4899291 {_112866 : Type'} (h : _112866) (t : list _112866) : (((term171 _112866 t) = (term225 _112866 t)) = (term304 _112866 h t)) = (term331 _112866 h t).
Proof. exact (@lem4899290 (((term171 _112866 t) = (term225 _112866 t)) = (term304 _112866 h t))). Qed.
Lemma lem4899292 {_112866 : Type'} (h : _112866) (t : list _112866) : (term331 _112866 h t) = (((term171 _112866 t) = (term225 _112866 t)) = (term304 _112866 h t)).
Proof. exact (SYM (@lem4899291 _112866 h t)). Qed.
Lemma lem4899293 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term332 _112866 h t) : term332 _112866 h t.
Proof. exact (h1). Qed.
Lemma lem4899294 {_112866 : Type'} : term333 _112866.
Proof. exact (@lem4897948 _112866). Qed.
Lemma lem4899299 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term334 _112866 h t) : term334 _112866 h t.
Proof. exact (h1). Qed.
Lemma lem4899300 {_112866 : Type'} (h : _112866) (t : list _112866) : term335 _112866 h t.
Proof. exact (fun h0 : term334 _112866 h t => @lem4899299 _112866 h t h0). Qed.
Lemma lem4899301 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term335 _112866 h t) : term335 _112866 h t.
Proof. exact (h1). Qed.
Lemma lem4899302 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term334 _112866 h t) : term334 _112866 h t.
Proof. exact (h1). Qed.
Lemma lem4899303 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term334 _112866 h t) (h2 : term335 _112866 h t) : term334 _112866 h t.
Proof. exact (@lem4899301 _112866 h t h2 (@lem4899302 _112866 h t h1)). Qed.
Lemma lem4899304 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term334 _112866 h t) : term336 _112866 h t.
Proof. exact (fun h0 : term335 _112866 h t => @lem4899303 _112866 h t h1 h0). Qed.
Lemma lem4899305 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term335 _112866 h t) : term335 _112866 h t.
Proof. exact (h1). Qed.
Lemma lem4899306 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term334 _112866 h t) (h2 : term335 _112866 h t) : term334 _112866 h t.
Proof. exact (@lem4899304 _112866 h t h1 (@lem4899305 _112866 h t h2)). Qed.
Lemma lem4899307 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term335 _112866 h t) : term335 _112866 h t.
Proof. exact (fun h0 : term334 _112866 h t => @lem4899306 _112866 h t h0 h1). Qed.
Lemma lem4899308 {_112866 : Type'} (h : _112866) (t : list _112866) : term337 _112866 h t.
Proof. exact (fun h0 : term335 _112866 h t => @lem4899307 _112866 h t h0). Qed.
Lemma lem4899311 {_112866 : Type'} (h : _112866) (t : list _112866) : term335 _112866 h t.
Proof. exact (@lem4899308 _112866 h t (@lem4899300 _112866 h t)). Qed.
Lemma lem4899312 {_112866 : Type'} (h : _112866) (t : list _112866) : term335 _112866 h t.
Proof. exact (@lem4899311 _112866 h t). Qed.
Lemma lem4899342 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4899343 {_112866 : Type'} : (term338 _112866) = (term339 _112866).
Proof. exact (@lem4899342 (term333 _112866)). Qed.
Lemma lem4899348 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem4899349 {_112866 : Type'} : (term341 _112866) = (term342 _112866).
Proof. exact (MK_COMB (@lem4899348) (@lem4899343 _112866)). Qed.
Lemma lem4899352 {_112866 : Type'} (h : _112866) (t : list _112866) : (term343 _112866 h t) = (term343 _112866 h t).
Proof. exact (eq_refl (term343 _112866 h t)). Qed.
Lemma lem4899353 {_112866 : Type'} (h : _112866) (t : list _112866) : (term344 _112866 h t) = (term345 _112866 h t).
Proof. exact (MK_COMB (@lem4899352 _112866 h t) (@lem4899349 _112866)). Qed.
Lemma lem4899356 {_112866 : Type'} (h : _112866) (t : list _112866) : (term317 _112866 h t) = (term317 _112866 h t).
Proof. exact (eq_refl (term317 _112866 h t)). Qed.
Lemma lem4899357 {_112866 : Type'} (h : _112866) (t : list _112866) : (term346 _112866 h t) = (term347 _112866 h t).
Proof. exact (MK_COMB (@lem4899356 _112866 h t) (@lem4899353 _112866 h t)). Qed.
Lemma lem4899360 {_112866 : Type'} (t : list _112866) : (term189 _112866 t) = (term189 _112866 t).
Proof. exact (eq_refl (term189 _112866 t)). Qed.
Lemma lem4899361 {_112866 : Type'} (h : _112866) (t : list _112866) : (term334 _112866 h t) = (term348 _112866 h t).
Proof. exact (MK_COMB (@lem4899360 _112866 t) (@lem4899357 _112866 h t)). Qed.
Lemma lem4899364 {_112866 : Type'} (t : list _112866) : (term349 _112866 t) = (term350 _112866 t).
Proof. exact (fun_ext (fun h : _112866 => @lem4899361 _112866 h t)). Qed.
Lemma lem4899365 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4899366 {_112866 : Type'} (t : list _112866) : (term351 _112866 t) = (term352 _112866 t).
Proof. exact (MK_COMB (@lem4899365 _112866) (@lem4899364 _112866 t)). Qed.
Lemma lem4899371 {_112866 : Type'} : (term353 _112866) = (term354 _112866).
Proof. exact (fun_ext (fun t : list _112866 => @lem4899366 _112866 t)). Qed.
Lemma lem4899372 {_112866 : Type'} : (@all (list _112866)) = (@all (list _112866)).
Proof. exact (eq_refl (@all (list _112866))). Qed.
Lemma lem4899379 {_112866 : Type'} : (term355 _112866) = (term356 _112866).
Proof. exact (MK_COMB (@lem4899372 _112866) (@lem4899371 _112866)). Qed.
Lemma lem4899380 {_112866 : Type'} (_60497 : type1402 _112866) (h1 : _60497 = (term214 _112866)) : _60497 = (term214 _112866).
Proof. exact (h1). Qed.
Lemma lem4899392 {_112866 : Type'} (l : list _112866) : (term357 _112866 l) = (term357 _112866 l).
Proof. exact (eq_refl (term357 _112866 l)). Qed.
Lemma lem4899393 {_112866 : Type'} : (term358 _112866) = (term358 _112866).
Proof. exact (fun_ext (fun l : list _112866 => @lem4899392 _112866 l)). Qed.
Lemma lem4899394 {_112866 : Type'} : (@all (list _112866)) = (@all (list _112866)).
Proof. exact (eq_refl (@all (list _112866))). Qed.
Lemma lem4899395 {_112866 : Type'} : (term333 _112866) = (term333 _112866).
Proof. exact (MK_COMB (@lem4899394 _112866) (@lem4899393 _112866)). Qed.
Lemma lem4899396 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4899397 {_112866 : Type'} : (term339 _112866) = (term339 _112866).
Proof. exact (MK_COMB (@lem4899396) (@lem4899395 _112866)). Qed.
Lemma lem4899406 (n : nat) : (term5 n) = (term5 n).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem4899407 : term359 = term359.
Proof. exact (fun_ext (fun n : nat => @lem4899406 n)). Qed.
Lemma lem4899408 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4899409 : term152 = term152.
Proof. exact (MK_COMB (@lem4899408) (@lem4899407)). Qed.
Lemma lem4899410 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4899411 : term340 = term340.
Proof. exact (MK_COMB (@lem4899410) (@lem4899409)). Qed.
Lemma lem4899412 {_112866 : Type'} : (term342 _112866) = (term342 _112866).
Proof. exact (MK_COMB (@lem4899411) (@lem4899397 _112866)). Qed.
Lemma lem4899413 {_112866 : Type'} (t : list _112866) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4899415 {_112866 : Type'} (_60497 : type1402 _112866) (h1 : _60497 = (term214 _112866)) : (term214 _112866) = _60497.
Proof. exact (SYM (@lem4899380 _112866 _60497 h1)). Qed.
Lemma lem4899416 {_112866 : Type'} (_60497 : type1402 _112866) (h1 : _60497 = (term214 _112866)) : (term214 _112866) = _60497.
Proof. exact (@lem4899415 _112866 _60497 h1). Qed.
Lemma lem4899417 {_112866 : Type'} : (@List.ForallOrdPairs _112866) = (@List.ForallOrdPairs _112866).
Proof. exact (eq_refl (@List.ForallOrdPairs _112866)). Qed.
Lemma lem4899418 {_112866 : Type'} (_60497 : type1402 _112866) (h1 : _60497 = (term214 _112866)) : (term360 _112866) = (@List.ForallOrdPairs _112866 _60497).
Proof. exact (MK_COMB (@lem4899417 _112866) (@lem4899416 _112866 _60497 h1)). Qed.
Lemma lem4899419 {_112866 : Type'} (t : list _112866) (_60497 : type1402 _112866) (h1 : _60497 = (term214 _112866)) : (term175 _112866 t) = (@List.ForallOrdPairs _112866 _60497 t).
Proof. exact (MK_COMB (@lem4899418 _112866 _60497 h1) (@lem4899413 _112866 t)). Qed.
Lemma lem4899434 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term298 _112866 t h x) = (term298 _112866 t h x).
Proof. exact (eq_refl (term298 _112866 t h x)). Qed.
Lemma lem4899435 {_112866 : Type'} (t : list _112866) (h : _112866) : (term300 _112866 t h) = (term300 _112866 t h).
Proof. exact (fun_ext (fun x : _112866 => @lem4899434 _112866 t h x)). Qed.
Lemma lem4899436 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4899437 {_112866 : Type'} (t : list _112866) (h : _112866) : (term301 _112866 t h) = (term301 _112866 t h).
Proof. exact (MK_COMB (@lem4899436 _112866) (@lem4899435 _112866 t h)). Qed.
Lemma lem4899438 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4899439 {_112866 : Type'} (t : list _112866) (h : _112866) : (term303 _112866 t h) = (term303 _112866 t h).
Proof. exact (MK_COMB (@lem4899438) (@lem4899437 _112866 t h)). Qed.
Lemma lem4899440 {_112866 : Type'} (h : _112866) (t : list _112866) (_60497 : type1402 _112866) (h1 : _60497 = (term214 _112866)) : (term304 _112866 h t) = (term361 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4899439 _112866 t h) (@lem4899419 _112866 t _60497 h1)). Qed.
Lemma lem4899455 {_112866 : Type'} (t : list _112866) : (term362 _112866 t) = (term362 _112866 t).
Proof. exact (eq_refl (term362 _112866 t)). Qed.
Lemma lem4899456 {_112866 : Type'} (h : _112866) (t : list _112866) (_60497 : type1402 _112866) (h1 : _60497 = (term214 _112866)) : (((term171 _112866 t) = (term225 _112866 t)) = (term304 _112866 h t)) = (((term171 _112866 t) = (term225 _112866 t)) = (term361 _112866 h _60497 t)).
Proof. exact (MK_COMB (@lem4899455 _112866 t) (@lem4899440 _112866 h t _60497 h1)). Qed.
Lemma lem4899457 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4899458 {_112866 : Type'} (h : _112866) (t : list _112866) (_60497 : type1402 _112866) (h1 : _60497 = (term214 _112866)) : (term332 _112866 h t) = (term363 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4899457) (@lem4899456 _112866 h t _60497 h1)). Qed.
Lemma lem4899459 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4899460 {_112866 : Type'} (h : _112866) (t : list _112866) (_60497 : type1402 _112866) (h1 : _60497 = (term214 _112866)) : (term343 _112866 h t) = (term364 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4899459) (@lem4899458 _112866 h t _60497 h1)). Qed.
Lemma lem4899461 {_112866 : Type'} (h : _112866) (t : list _112866) (_60497 : type1402 _112866) (h1 : _60497 = (term214 _112866)) : (term345 _112866 h t) = (term365 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4899460 _112866 h t _60497 h1) (@lem4899412 _112866)). Qed.
Lemma lem4899468 {_112866 : Type'} (h : _112866) (t : list _112866) : (term317 _112866 h t) = (term317 _112866 h t).
Proof. exact (eq_refl (term317 _112866 h t)). Qed.
Lemma lem4899469 {_112866 : Type'} (h : _112866) (t : list _112866) (_60497 : type1402 _112866) (h1 : _60497 = (term214 _112866)) : (term347 _112866 h t) = (term366 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4899468 _112866 h t) (@lem4899461 _112866 h t _60497 h1)). Qed.
Lemma lem4899470 {_112866 : Type'} (t : list _112866) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4899472 {_112866 : Type'} (_60497 : type1402 _112866) (h1 : _60497 = (term214 _112866)) : (term214 _112866) = _60497.
Proof. exact (SYM (@lem4899380 _112866 _60497 h1)). Qed.
Lemma lem4899473 {_112866 : Type'} (_60497 : type1402 _112866) (h1 : _60497 = (term214 _112866)) : (term214 _112866) = _60497.
Proof. exact (@lem4899472 _112866 _60497 h1). Qed.
Lemma lem4899474 {_112866 : Type'} : (@List.ForallOrdPairs _112866) = (@List.ForallOrdPairs _112866).
Proof. exact (eq_refl (@List.ForallOrdPairs _112866)). Qed.
Lemma lem4899475 {_112866 : Type'} (_60497 : type1402 _112866) (h1 : _60497 = (term214 _112866)) : (term360 _112866) = (@List.ForallOrdPairs _112866 _60497).
Proof. exact (MK_COMB (@lem4899474 _112866) (@lem4899473 _112866 _60497 h1)). Qed.
Lemma lem4899476 {_112866 : Type'} (t : list _112866) (_60497 : type1402 _112866) (h1 : _60497 = (term214 _112866)) : (term175 _112866 t) = (@List.ForallOrdPairs _112866 _60497 t).
Proof. exact (MK_COMB (@lem4899475 _112866 _60497 h1) (@lem4899470 _112866 t)). Qed.
Lemma lem4899489 {_112866 : Type'} (t : list _112866) : (term174 _112866 t) = (term174 _112866 t).
Proof. exact (eq_refl (term174 _112866 t)). Qed.
Lemma lem4899490 {_112866 : Type'} (t : list _112866) (_60497 : type1402 _112866) (h1 : _60497 = (term214 _112866)) : (((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) = (((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)).
Proof. exact (MK_COMB (@lem4899489 _112866 t) (@lem4899476 _112866 t _60497 h1)). Qed.
Lemma lem4899491 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4899492 {_112866 : Type'} (t : list _112866) (_60497 : type1402 _112866) (h1 : _60497 = (term214 _112866)) : (term189 _112866 t) = (term367 _112866 _60497 t).
Proof. exact (MK_COMB (@lem4899491) (@lem4899490 _112866 t _60497 h1)). Qed.
Lemma lem4899493 {_112866 : Type'} (h : _112866) (t : list _112866) (_60497 : type1402 _112866) (h1 : _60497 = (term214 _112866)) : (term348 _112866 h t) = (term368 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4899492 _112866 t _60497 h1) (@lem4899469 _112866 h t _60497 h1)). Qed.
Lemma lem4899494 {_112866 : Type'} (t : list _112866) (_60497 : type1402 _112866) (h1 : _60497 = (term214 _112866)) : (term350 _112866 t) = (term369 _112866 _60497 t).
Proof. exact (fun_ext (fun h : _112866 => @lem4899493 _112866 h t _60497 h1)). Qed.
Lemma lem4899495 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4899496 {_112866 : Type'} (t : list _112866) (_60497 : type1402 _112866) (h1 : _60497 = (term214 _112866)) : (term352 _112866 t) = (term370 _112866 _60497 t).
Proof. exact (MK_COMB (@lem4899495 _112866) (@lem4899494 _112866 t _60497 h1)). Qed.
Lemma lem4899497 {_112866 : Type'} (_60497 : type1402 _112866) (h1 : _60497 = (term214 _112866)) : (term354 _112866) = (term371 _112866 _60497).
Proof. exact (fun_ext (fun t : list _112866 => @lem4899496 _112866 t _60497 h1)). Qed.
Lemma lem4899498 {_112866 : Type'} : (@all (list _112866)) = (@all (list _112866)).
Proof. exact (eq_refl (@all (list _112866))). Qed.
Lemma lem4899499 {_112866 : Type'} (_60497 : type1402 _112866) (h1 : _60497 = (term214 _112866)) : (term356 _112866) = (term372 _112866 _60497).
Proof. exact (MK_COMB (@lem4899498 _112866) (@lem4899497 _112866 _60497 h1)). Qed.
Lemma lem4899500 {_112866 : Type'} (_60497 : type1402 _112866) : term373 _112866 _60497.
Proof. exact (fun h0 : _60497 = (term214 _112866) => @lem4899499 _112866 _60497 h0). Qed.
Lemma lem4899501 {_112866 : Type'} : term374 _112866.
Proof. exact (fun _60497 : type1402 _112866 => @lem4899500 _112866 _60497). Qed.
Lemma lem4899503 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term375 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem4899504 {_112866 : Type'} (P : Prop) (c : type1402 _112866) (Q : type421 _112866) : term376 _112866 P c Q.
Proof. exact (@lem4899503 (type1402 _112866) P c Q). Qed.
Lemma lem4899505 {_112866 : Type'} : term377 _112866.
Proof. exact (@lem4899504 _112866 (term356 _112866) (term214 _112866) (term378 _112866)). Qed.
Lemma lem4899506 {_112866 : Type'} (_60497 : type1402 _112866) : (term379 _112866 _60497) = (term372 _112866 _60497).
Proof. exact (eq_refl (term379 _112866 _60497)). Qed.
Lemma lem4899507 {_112866 : Type'} : (term380 _112866) = (term380 _112866).
Proof. exact (eq_refl (term380 _112866)). Qed.
Lemma lem4899508 {_112866 : Type'} (_60497 : type1402 _112866) : ((term356 _112866) = (term379 _112866 _60497)) = ((term356 _112866) = (term372 _112866 _60497)).
Proof. exact (MK_COMB (@lem4899507 _112866) (@lem4899506 _112866 _60497)). Qed.
Lemma lem4899509 {_112866 : Type'} (_60497 : type1402 _112866) : (term381 _112866 _60497) = (term381 _112866 _60497).
Proof. exact (eq_refl (term381 _112866 _60497)). Qed.
Lemma lem4899510 {_112866 : Type'} (_60497 : type1402 _112866) : (term382 _112866 _60497) = (term373 _112866 _60497).
Proof. exact (MK_COMB (@lem4899509 _112866 _60497) (@lem4899508 _112866 _60497)). Qed.
Lemma lem4899511 {_112866 : Type'} : (term383 _112866) = (term384 _112866).
Proof. exact (fun_ext (fun _60497 : type1402 _112866 => @lem4899510 _112866 _60497)). Qed.
Lemma lem4899512 {_112866 : Type'} : (@all (_112866 -> _112866 -> Prop)) = (@all (_112866 -> _112866 -> Prop)).
Proof. exact (eq_refl (@all (_112866 -> _112866 -> Prop))). Qed.
Lemma lem4899513 {_112866 : Type'} : (term385 _112866) = (term374 _112866).
Proof. exact (MK_COMB (@lem4899512 _112866) (@lem4899511 _112866)). Qed.
Lemma lem4899514 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4899515 {_112866 : Type'} : (term386 _112866) = (term387 _112866).
Proof. exact (MK_COMB (@lem4899514) (@lem4899513 _112866)). Qed.
Lemma lem4899516 {_112866 : Type'} (_60497 : type1402 _112866) : (term379 _112866 _60497) = (term372 _112866 _60497).
Proof. exact (eq_refl (term379 _112866 _60497)). Qed.
Lemma lem4899517 {_112866 : Type'} (_60497 : type1402 _112866) : (term381 _112866 _60497) = (term381 _112866 _60497).
Proof. exact (eq_refl (term381 _112866 _60497)). Qed.
Lemma lem4899518 {_112866 : Type'} (_60497 : type1402 _112866) : (term388 _112866 _60497) = (term389 _112866 _60497).
Proof. exact (MK_COMB (@lem4899517 _112866 _60497) (@lem4899516 _112866 _60497)). Qed.
Lemma lem4899519 {_112866 : Type'} : (term390 _112866) = (term391 _112866).
Proof. exact (fun_ext (fun _60497 : type1402 _112866 => @lem4899518 _112866 _60497)). Qed.
Lemma lem4899520 {_112866 : Type'} : (@all (_112866 -> _112866 -> Prop)) = (@all (_112866 -> _112866 -> Prop)).
Proof. exact (eq_refl (@all (_112866 -> _112866 -> Prop))). Qed.
Lemma lem4899521 {_112866 : Type'} : (term392 _112866) = (term393 _112866).
Proof. exact (MK_COMB (@lem4899520 _112866) (@lem4899519 _112866)). Qed.
Lemma lem4899522 {_112866 : Type'} : (term380 _112866) = (term380 _112866).
Proof. exact (eq_refl (term380 _112866)). Qed.
Lemma lem4899523 {_112866 : Type'} : ((term356 _112866) = (term392 _112866)) = ((term356 _112866) = (term393 _112866)).
Proof. exact (MK_COMB (@lem4899522 _112866) (@lem4899521 _112866)). Qed.
Lemma lem4899524 {_112866 : Type'} : (term377 _112866) = (term394 _112866).
Proof. exact (MK_COMB (@lem4899515 _112866) (@lem4899523 _112866)). Qed.
Lemma lem4899525 {_112866 : Type'} : term394 _112866.
Proof. exact (EQ_MP (@lem4899524 _112866) (@lem4899505 _112866)). Qed.
Lemma lem4899526 {_112866 : Type'} : (term356 _112866) = (term393 _112866).
Proof. exact (@lem4899525 _112866 (@lem4899501 _112866)). Qed.
Lemma lem4899528 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term395 _3571 _3575 t)) = (term396 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem4899529 {_112866 : Type'} (s : type1402 _112866) (t : type1402 _112866) : (s = (term397 _112866 t)) = (term398 _112866 s t).
Proof. exact (@lem4899528 (_112866 -> Prop) _112866 s t). Qed.
Lemma lem4899530 {_112866 : Type'} (_60497 : type1402 _112866) : (_60497 = (term285 _112866)) = (term399 _112866 _60497).
Proof. exact (@lem4899529 _112866 _60497 (term214 _112866)). Qed.
Lemma lem4899531 {_112866 : Type'} (x : _112866) : (term269 _112866 x) = (term284 _112866 x).
Proof. exact (eq_refl (term269 _112866 x)). Qed.
Lemma lem4899532 {_112866 : Type'} : (term285 _112866) = (term214 _112866).
Proof. exact (fun_ext (fun x : _112866 => @lem4899531 _112866 x)). Qed.
Lemma lem4899533 {_112866 : Type'} (_60497 : type1402 _112866) : (@eq (_112866 -> _112866 -> Prop) _60497) = (@eq (_112866 -> _112866 -> Prop) _60497).
Proof. exact (eq_refl (@eq (_112866 -> _112866 -> Prop) _60497)). Qed.
Lemma lem4899534 {_112866 : Type'} (_60497 : type1402 _112866) : (_60497 = (term285 _112866)) = (_60497 = (term214 _112866)).
Proof. exact (MK_COMB (@lem4899533 _112866 _60497) (@lem4899532 _112866)). Qed.
Lemma lem4899535 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4899536 {_112866 : Type'} (_60497 : type1402 _112866) : (term400 _112866 _60497) = (term401 _112866 _60497).
Proof. exact (MK_COMB (@lem4899535) (@lem4899534 _112866 _60497)). Qed.
Lemma lem4899537 {_112866 : Type'} (x : _112866) : (term269 _112866 x) = (term284 _112866 x).
Proof. exact (eq_refl (term269 _112866 x)). Qed.
Lemma lem4899538 {_112866 : Type'} (_60497 : type1402 _112866) (x : _112866) : (term402 _112866 _60497 x) = (term402 _112866 _60497 x).
Proof. exact (eq_refl (term402 _112866 _60497 x)). Qed.
Lemma lem4899539 {_112866 : Type'} (_60497 : type1402 _112866) (x : _112866) : ((_60497 x) = (term269 _112866 x)) = ((_60497 x) = (term284 _112866 x)).
Proof. exact (MK_COMB (@lem4899538 _112866 _60497 x) (@lem4899537 _112866 x)). Qed.
Lemma lem4899540 {_112866 : Type'} (_60497 : type1402 _112866) : (term403 _112866 _60497) = (term404 _112866 _60497).
Proof. exact (fun_ext (fun x : _112866 => @lem4899539 _112866 _60497 x)). Qed.
Lemma lem4899541 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4899542 {_112866 : Type'} (_60497 : type1402 _112866) : (term399 _112866 _60497) = (term405 _112866 _60497).
Proof. exact (MK_COMB (@lem4899541 _112866) (@lem4899540 _112866 _60497)). Qed.
Lemma lem4899543 {_112866 : Type'} (_60497 : type1402 _112866) : ((_60497 = (term285 _112866)) = (term399 _112866 _60497)) = ((_60497 = (term214 _112866)) = (term405 _112866 _60497)).
Proof. exact (MK_COMB (@lem4899536 _112866 _60497) (@lem4899542 _112866 _60497)). Qed.
Lemma lem4899544 {_112866 : Type'} (_60497 : type1402 _112866) : (_60497 = (term214 _112866)) = (term405 _112866 _60497).
Proof. exact (EQ_MP (@lem4899543 _112866 _60497) (@lem4899530 _112866 _60497)). Qed.
Lemma lem4899545 {_112866 : Type'} (_60497 : type1402 _112866) (x : _112866) : ((_60497 x) = (term284 _112866 x)) = ((_60497 x) = (term284 _112866 x)).
Proof. exact (eq_refl ((_60497 x) = (term284 _112866 x))). Qed.
Lemma lem4899546 {_112866 : Type'} (_60497 : type1402 _112866) : (term404 _112866 _60497) = (term404 _112866 _60497).
Proof. exact (fun_ext (fun x : _112866 => @lem4899545 _112866 _60497 x)). Qed.
Lemma lem4899547 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4899548 {_112866 : Type'} (_60497 : type1402 _112866) : (term405 _112866 _60497) = (term405 _112866 _60497).
Proof. exact (MK_COMB (@lem4899547 _112866) (@lem4899546 _112866 _60497)). Qed.
Lemma lem4899549 {_112866 : Type'} (_60497 : type1402 _112866) : (_60497 = (term214 _112866)) = (term405 _112866 _60497).
Proof. exact (TRANS (@lem4899544 _112866 _60497) (@lem4899548 _112866 _60497)). Qed.
Lemma lem4899550 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4899551 {_112866 : Type'} (_60497 : type1402 _112866) : (term381 _112866 _60497) = (term406 _112866 _60497).
Proof. exact (MK_COMB (@lem4899550) (@lem4899549 _112866 _60497)). Qed.
Lemma lem4899552 {_112866 : Type'} (_60497 : type1402 _112866) : (term372 _112866 _60497) = (term372 _112866 _60497).
Proof. exact (eq_refl (term372 _112866 _60497)). Qed.
Lemma lem4899553 {_112866 : Type'} (_60497 : type1402 _112866) : (term389 _112866 _60497) = (term407 _112866 _60497).
Proof. exact (MK_COMB (@lem4899551 _112866 _60497) (@lem4899552 _112866 _60497)). Qed.
Lemma lem4899554 {_112866 : Type'} : (term391 _112866) = (term408 _112866).
Proof. exact (fun_ext (fun _60497 : type1402 _112866 => @lem4899553 _112866 _60497)). Qed.
Lemma lem4899555 {_112866 : Type'} : (@all (_112866 -> _112866 -> Prop)) = (@all (_112866 -> _112866 -> Prop)).
Proof. exact (eq_refl (@all (_112866 -> _112866 -> Prop))). Qed.
Lemma lem4899556 {_112866 : Type'} : (term393 _112866) = (term409 _112866).
Proof. exact (MK_COMB (@lem4899555 _112866) (@lem4899554 _112866)). Qed.
Lemma lem4899557 {_112866 : Type'} : (term380 _112866) = (term380 _112866).
Proof. exact (eq_refl (term380 _112866)). Qed.
Lemma lem4899558 {_112866 : Type'} : ((term356 _112866) = (term393 _112866)) = ((term356 _112866) = (term409 _112866)).
Proof. exact (MK_COMB (@lem4899557 _112866) (@lem4899556 _112866)). Qed.
Lemma lem4899559 {_112866 : Type'} : (term356 _112866) = (term409 _112866).
Proof. exact (EQ_MP (@lem4899558 _112866) (@lem4899526 _112866)). Qed.
Lemma lem4899560 {_112866 : Type'} (_60498 : type1402 _112866) (h1 : _60498 = (term214 _112866)) : _60498 = (term214 _112866).
Proof. exact (h1). Qed.
Lemma lem4899561 {_112866 : Type'} (x : _112866) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4899562 {_112866 : Type'} (x : _112866) (_60498 : type1402 _112866) (h1 : _60498 = (term214 _112866)) : (_60498 x) = (term269 _112866 x).
Proof. exact (MK_COMB (@lem4899560 _112866 _60498 h1) (@lem4899561 _112866 x)). Qed.
Lemma lem4899563 {_112866 : Type'} (x : _112866) : (term269 _112866 x) = (term284 _112866 x).
Proof. exact (eq_refl (term269 _112866 x)). Qed.
Lemma lem4899564 {_112866 : Type'} (_60498 : type1402 _112866) (x : _112866) : (term402 _112866 _60498 x) = (term402 _112866 _60498 x).
Proof. exact (eq_refl (term402 _112866 _60498 x)). Qed.
Lemma lem4899565 {_112866 : Type'} (_60498 : type1402 _112866) (x : _112866) : ((_60498 x) = (term269 _112866 x)) = ((_60498 x) = (term284 _112866 x)).
Proof. exact (MK_COMB (@lem4899564 _112866 _60498 x) (@lem4899563 _112866 x)). Qed.
Lemma lem4899566 {_112866 : Type'} (x : _112866) (_60498 : type1402 _112866) (h1 : _60498 = (term214 _112866)) : (_60498 x) = (term284 _112866 x).
Proof. exact (EQ_MP (@lem4899565 _112866 _60498 x) (@lem4899562 _112866 x _60498 h1)). Qed.
Lemma lem4899578 {_112866 : Type'} (l : list _112866) : (term357 _112866 l) = (term357 _112866 l).
Proof. exact (eq_refl (term357 _112866 l)). Qed.
Lemma lem4899579 {_112866 : Type'} : (term358 _112866) = (term358 _112866).
Proof. exact (fun_ext (fun l : list _112866 => @lem4899578 _112866 l)). Qed.
Lemma lem4899580 {_112866 : Type'} : (@all (list _112866)) = (@all (list _112866)).
Proof. exact (eq_refl (@all (list _112866))). Qed.
Lemma lem4899581 {_112866 : Type'} : (term333 _112866) = (term333 _112866).
Proof. exact (MK_COMB (@lem4899580 _112866) (@lem4899579 _112866)). Qed.
Lemma lem4899582 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4899583 {_112866 : Type'} : (term339 _112866) = (term339 _112866).
Proof. exact (MK_COMB (@lem4899582) (@lem4899581 _112866)). Qed.
Lemma lem4899592 (n : nat) : (term5 n) = (term5 n).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem4899593 : term359 = term359.
Proof. exact (fun_ext (fun n : nat => @lem4899592 n)). Qed.
Lemma lem4899594 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4899595 : term152 = term152.
Proof. exact (MK_COMB (@lem4899594) (@lem4899593)). Qed.
Lemma lem4899596 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4899597 : term340 = term340.
Proof. exact (MK_COMB (@lem4899596) (@lem4899595)). Qed.
Lemma lem4899598 {_112866 : Type'} : (term342 _112866) = (term342 _112866).
Proof. exact (MK_COMB (@lem4899597) (@lem4899583 _112866)). Qed.
Lemma lem4899603 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) : (@List.ForallOrdPairs _112866 _60497 t) = (@List.ForallOrdPairs _112866 _60497 t).
Proof. exact (eq_refl (@List.ForallOrdPairs _112866 _60497 t)). Qed.
Lemma lem4899618 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term298 _112866 t h x) = (term298 _112866 t h x).
Proof. exact (eq_refl (term298 _112866 t h x)). Qed.
Lemma lem4899619 {_112866 : Type'} (t : list _112866) (h : _112866) : (term300 _112866 t h) = (term300 _112866 t h).
Proof. exact (fun_ext (fun x : _112866 => @lem4899618 _112866 t h x)). Qed.
Lemma lem4899620 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4899621 {_112866 : Type'} (t : list _112866) (h : _112866) : (term301 _112866 t h) = (term301 _112866 t h).
Proof. exact (MK_COMB (@lem4899620 _112866) (@lem4899619 _112866 t h)). Qed.
Lemma lem4899622 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4899623 {_112866 : Type'} (t : list _112866) (h : _112866) : (term303 _112866 t h) = (term303 _112866 t h).
Proof. exact (MK_COMB (@lem4899622) (@lem4899621 _112866 t h)). Qed.
Lemma lem4899624 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term361 _112866 h _60497 t) = (term361 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4899623 _112866 t h) (@lem4899603 _112866 _60497 t)). Qed.
Lemma lem4899639 {_112866 : Type'} (t : list _112866) : (term362 _112866 t) = (term362 _112866 t).
Proof. exact (eq_refl (term362 _112866 t)). Qed.
Lemma lem4899640 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (((term171 _112866 t) = (term225 _112866 t)) = (term361 _112866 h _60497 t)) = (((term171 _112866 t) = (term225 _112866 t)) = (term361 _112866 h _60497 t)).
Proof. exact (MK_COMB (@lem4899639 _112866 t) (@lem4899624 _112866 h _60497 t)). Qed.
Lemma lem4899641 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4899642 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term363 _112866 h _60497 t) = (term363 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4899641) (@lem4899640 _112866 h _60497 t)). Qed.
Lemma lem4899643 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4899644 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term364 _112866 h _60497 t) = (term364 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4899643) (@lem4899642 _112866 h _60497 t)). Qed.
Lemma lem4899645 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term365 _112866 h _60497 t) = (term365 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4899644 _112866 h _60497 t) (@lem4899598 _112866)). Qed.
Lemma lem4899652 {_112866 : Type'} (h : _112866) (t : list _112866) : (term317 _112866 h t) = (term317 _112866 h t).
Proof. exact (eq_refl (term317 _112866 h t)). Qed.
Lemma lem4899653 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term366 _112866 h _60497 t) = (term366 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4899652 _112866 h t) (@lem4899645 _112866 h _60497 t)). Qed.
Lemma lem4899674 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) : (term367 _112866 _60497 t) = (term367 _112866 _60497 t).
Proof. exact (eq_refl (term367 _112866 _60497 t)). Qed.
Lemma lem4899675 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term368 _112866 h _60497 t) = (term368 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4899674 _112866 _60497 t) (@lem4899653 _112866 h _60497 t)). Qed.
Lemma lem4899676 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) : (term369 _112866 _60497 t) = (term369 _112866 _60497 t).
Proof. exact (fun_ext (fun h : _112866 => @lem4899675 _112866 h _60497 t)). Qed.
Lemma lem4899677 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4899678 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) : (term370 _112866 _60497 t) = (term370 _112866 _60497 t).
Proof. exact (MK_COMB (@lem4899677 _112866) (@lem4899676 _112866 _60497 t)). Qed.
Lemma lem4899679 {_112866 : Type'} (_60497 : type1402 _112866) : (term371 _112866 _60497) = (term371 _112866 _60497).
Proof. exact (fun_ext (fun t : list _112866 => @lem4899678 _112866 _60497 t)). Qed.
Lemma lem4899680 {_112866 : Type'} : (@all (list _112866)) = (@all (list _112866)).
Proof. exact (eq_refl (@all (list _112866))). Qed.
Lemma lem4899681 {_112866 : Type'} (_60497 : type1402 _112866) : (term372 _112866 _60497) = (term372 _112866 _60497).
Proof. exact (MK_COMB (@lem4899680 _112866) (@lem4899679 _112866 _60497)). Qed.
Lemma lem4899683 {_112866 : Type'} (x : _112866) (_60498 : type1402 _112866) (h1 : _60498 = (term214 _112866)) : (term284 _112866 x) = (_60498 x).
Proof. exact (SYM (@lem4899566 _112866 x _60498 h1)). Qed.
Lemma lem4899684 {_112866 : Type'} (x : _112866) (_60498 : type1402 _112866) (h1 : _60498 = (term214 _112866)) : (term284 _112866 x) = (_60498 x).
Proof. exact (@lem4899683 _112866 x _60498 h1). Qed.
Lemma lem4899689 {_112866 : Type'} (_60497 : type1402 _112866) (x : _112866) : (term402 _112866 _60497 x) = (term402 _112866 _60497 x).
Proof. exact (eq_refl (term402 _112866 _60497 x)). Qed.
Lemma lem4899690 {_112866 : Type'} (_60497 : type1402 _112866) (x : _112866) (_60498 : type1402 _112866) (h1 : _60498 = (term214 _112866)) : ((_60497 x) = (term284 _112866 x)) = ((_60497 x) = (_60498 x)).
Proof. exact (MK_COMB (@lem4899689 _112866 _60497 x) (@lem4899684 _112866 x _60498 h1)). Qed.
Lemma lem4899691 {_112866 : Type'} (_60497 : type1402 _112866) (_60498 : type1402 _112866) (h1 : _60498 = (term214 _112866)) : (term404 _112866 _60497) = (term410 _112866 _60497 _60498).
Proof. exact (fun_ext (fun x : _112866 => @lem4899690 _112866 _60497 x _60498 h1)). Qed.
Lemma lem4899692 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4899693 {_112866 : Type'} (_60497 : type1402 _112866) (_60498 : type1402 _112866) (h1 : _60498 = (term214 _112866)) : (term405 _112866 _60497) = (term398 _112866 _60497 _60498).
Proof. exact (MK_COMB (@lem4899692 _112866) (@lem4899691 _112866 _60497 _60498 h1)). Qed.
Lemma lem4899694 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4899695 {_112866 : Type'} (_60497 : type1402 _112866) (_60498 : type1402 _112866) (h1 : _60498 = (term214 _112866)) : (term406 _112866 _60497) = (term411 _112866 _60497 _60498).
Proof. exact (MK_COMB (@lem4899694) (@lem4899693 _112866 _60497 _60498 h1)). Qed.
Lemma lem4899696 {_112866 : Type'} (_60497 : type1402 _112866) (_60498 : type1402 _112866) (h1 : _60498 = (term214 _112866)) : (term407 _112866 _60497) = (term412 _112866 _60498 _60497).
Proof. exact (MK_COMB (@lem4899695 _112866 _60497 _60498 h1) (@lem4899681 _112866 _60497)). Qed.
Lemma lem4899697 {_112866 : Type'} (_60498 : type1402 _112866) (h1 : _60498 = (term214 _112866)) : (term408 _112866) = (term413 _112866 _60498).
Proof. exact (fun_ext (fun _60497 : type1402 _112866 => @lem4899696 _112866 _60497 _60498 h1)). Qed.
Lemma lem4899698 {_112866 : Type'} : (@all (_112866 -> _112866 -> Prop)) = (@all (_112866 -> _112866 -> Prop)).
Proof. exact (eq_refl (@all (_112866 -> _112866 -> Prop))). Qed.
Lemma lem4899699 {_112866 : Type'} (_60498 : type1402 _112866) (h1 : _60498 = (term214 _112866)) : (term409 _112866) = (term414 _112866 _60498).
Proof. exact (MK_COMB (@lem4899698 _112866) (@lem4899697 _112866 _60498 h1)). Qed.
Lemma lem4899700 {_112866 : Type'} (_60498 : type1402 _112866) : term415 _112866 _60498.
Proof. exact (fun h0 : _60498 = (term214 _112866) => @lem4899699 _112866 _60498 h0). Qed.
Lemma lem4899701 {_112866 : Type'} : term416 _112866.
Proof. exact (fun _60498 : type1402 _112866 => @lem4899700 _112866 _60498). Qed.
Lemma lem4899703 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term375 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem4899704 {_112866 : Type'} (P : Prop) (c : type1402 _112866) (Q : type421 _112866) : term376 _112866 P c Q.
Proof. exact (@lem4899703 (type1402 _112866) P c Q). Qed.
Lemma lem4899705 {_112866 : Type'} : term417 _112866.
Proof. exact (@lem4899704 _112866 (term409 _112866) (term214 _112866) (term418 _112866)). Qed.
Lemma lem4899706 {_112866 : Type'} (_60498 : type1402 _112866) : (term419 _112866 _60498) = (term414 _112866 _60498).
Proof. exact (eq_refl (term419 _112866 _60498)). Qed.
Lemma lem4899707 {_112866 : Type'} : (term420 _112866) = (term420 _112866).
Proof. exact (eq_refl (term420 _112866)). Qed.
Lemma lem4899708 {_112866 : Type'} (_60498 : type1402 _112866) : ((term409 _112866) = (term419 _112866 _60498)) = ((term409 _112866) = (term414 _112866 _60498)).
Proof. exact (MK_COMB (@lem4899707 _112866) (@lem4899706 _112866 _60498)). Qed.
Lemma lem4899709 {_112866 : Type'} (_60498 : type1402 _112866) : (term381 _112866 _60498) = (term381 _112866 _60498).
Proof. exact (eq_refl (term381 _112866 _60498)). Qed.
Lemma lem4899710 {_112866 : Type'} (_60498 : type1402 _112866) : (term421 _112866 _60498) = (term415 _112866 _60498).
Proof. exact (MK_COMB (@lem4899709 _112866 _60498) (@lem4899708 _112866 _60498)). Qed.
Lemma lem4899711 {_112866 : Type'} : (term422 _112866) = (term423 _112866).
Proof. exact (fun_ext (fun _60498 : type1402 _112866 => @lem4899710 _112866 _60498)). Qed.
Lemma lem4899712 {_112866 : Type'} : (@all (_112866 -> _112866 -> Prop)) = (@all (_112866 -> _112866 -> Prop)).
Proof. exact (eq_refl (@all (_112866 -> _112866 -> Prop))). Qed.
Lemma lem4899713 {_112866 : Type'} : (term424 _112866) = (term416 _112866).
Proof. exact (MK_COMB (@lem4899712 _112866) (@lem4899711 _112866)). Qed.
Lemma lem4899714 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4899715 {_112866 : Type'} : (term425 _112866) = (term426 _112866).
Proof. exact (MK_COMB (@lem4899714) (@lem4899713 _112866)). Qed.
Lemma lem4899716 {_112866 : Type'} (_60498 : type1402 _112866) : (term419 _112866 _60498) = (term414 _112866 _60498).
Proof. exact (eq_refl (term419 _112866 _60498)). Qed.
Lemma lem4899717 {_112866 : Type'} (_60498 : type1402 _112866) : (term381 _112866 _60498) = (term381 _112866 _60498).
Proof. exact (eq_refl (term381 _112866 _60498)). Qed.
Lemma lem4899718 {_112866 : Type'} (_60498 : type1402 _112866) : (term427 _112866 _60498) = (term428 _112866 _60498).
Proof. exact (MK_COMB (@lem4899717 _112866 _60498) (@lem4899716 _112866 _60498)). Qed.
Lemma lem4899719 {_112866 : Type'} : (term429 _112866) = (term430 _112866).
Proof. exact (fun_ext (fun _60498 : type1402 _112866 => @lem4899718 _112866 _60498)). Qed.
Lemma lem4899720 {_112866 : Type'} : (@all (_112866 -> _112866 -> Prop)) = (@all (_112866 -> _112866 -> Prop)).
Proof. exact (eq_refl (@all (_112866 -> _112866 -> Prop))). Qed.
Lemma lem4899721 {_112866 : Type'} : (term431 _112866) = (term432 _112866).
Proof. exact (MK_COMB (@lem4899720 _112866) (@lem4899719 _112866)). Qed.
Lemma lem4899722 {_112866 : Type'} : (term420 _112866) = (term420 _112866).
Proof. exact (eq_refl (term420 _112866)). Qed.
Lemma lem4899723 {_112866 : Type'} : ((term409 _112866) = (term431 _112866)) = ((term409 _112866) = (term432 _112866)).
Proof. exact (MK_COMB (@lem4899722 _112866) (@lem4899721 _112866)). Qed.
Lemma lem4899724 {_112866 : Type'} : (term417 _112866) = (term433 _112866).
Proof. exact (MK_COMB (@lem4899715 _112866) (@lem4899723 _112866)). Qed.
Lemma lem4899725 {_112866 : Type'} : term433 _112866.
Proof. exact (EQ_MP (@lem4899724 _112866) (@lem4899705 _112866)). Qed.
Lemma lem4899726 {_112866 : Type'} : (term409 _112866) = (term432 _112866).
Proof. exact (@lem4899725 _112866 (@lem4899701 _112866)). Qed.
Lemma lem4899728 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term395 _3571 _3575 t)) = (term396 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem4899729 {_112866 : Type'} (s : type1402 _112866) (t : type1402 _112866) : (s = (term397 _112866 t)) = (term398 _112866 s t).
Proof. exact (@lem4899728 (_112866 -> Prop) _112866 s t). Qed.
Lemma lem4899730 {_112866 : Type'} (_60498 : type1402 _112866) : (_60498 = (term285 _112866)) = (term399 _112866 _60498).
Proof. exact (@lem4899729 _112866 _60498 (term214 _112866)). Qed.
Lemma lem4899731 {_112866 : Type'} (x : _112866) : (term269 _112866 x) = (term284 _112866 x).
Proof. exact (eq_refl (term269 _112866 x)). Qed.
Lemma lem4899732 {_112866 : Type'} : (term285 _112866) = (term214 _112866).
Proof. exact (fun_ext (fun x : _112866 => @lem4899731 _112866 x)). Qed.
Lemma lem4899733 {_112866 : Type'} (_60498 : type1402 _112866) : (@eq (_112866 -> _112866 -> Prop) _60498) = (@eq (_112866 -> _112866 -> Prop) _60498).
Proof. exact (eq_refl (@eq (_112866 -> _112866 -> Prop) _60498)). Qed.
Lemma lem4899734 {_112866 : Type'} (_60498 : type1402 _112866) : (_60498 = (term285 _112866)) = (_60498 = (term214 _112866)).
Proof. exact (MK_COMB (@lem4899733 _112866 _60498) (@lem4899732 _112866)). Qed.
Lemma lem4899735 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4899736 {_112866 : Type'} (_60498 : type1402 _112866) : (term400 _112866 _60498) = (term401 _112866 _60498).
Proof. exact (MK_COMB (@lem4899735) (@lem4899734 _112866 _60498)). Qed.
Lemma lem4899737 {_112866 : Type'} (x : _112866) : (term269 _112866 x) = (term284 _112866 x).
Proof. exact (eq_refl (term269 _112866 x)). Qed.
Lemma lem4899738 {_112866 : Type'} (_60498 : type1402 _112866) (x : _112866) : (term402 _112866 _60498 x) = (term402 _112866 _60498 x).
Proof. exact (eq_refl (term402 _112866 _60498 x)). Qed.
Lemma lem4899739 {_112866 : Type'} (_60498 : type1402 _112866) (x : _112866) : ((_60498 x) = (term269 _112866 x)) = ((_60498 x) = (term284 _112866 x)).
Proof. exact (MK_COMB (@lem4899738 _112866 _60498 x) (@lem4899737 _112866 x)). Qed.
Lemma lem4899740 {_112866 : Type'} (_60498 : type1402 _112866) : (term403 _112866 _60498) = (term404 _112866 _60498).
Proof. exact (fun_ext (fun x : _112866 => @lem4899739 _112866 _60498 x)). Qed.
Lemma lem4899741 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4899742 {_112866 : Type'} (_60498 : type1402 _112866) : (term399 _112866 _60498) = (term405 _112866 _60498).
Proof. exact (MK_COMB (@lem4899741 _112866) (@lem4899740 _112866 _60498)). Qed.
Lemma lem4899743 {_112866 : Type'} (_60498 : type1402 _112866) : ((_60498 = (term285 _112866)) = (term399 _112866 _60498)) = ((_60498 = (term214 _112866)) = (term405 _112866 _60498)).
Proof. exact (MK_COMB (@lem4899736 _112866 _60498) (@lem4899742 _112866 _60498)). Qed.
Lemma lem4899744 {_112866 : Type'} (_60498 : type1402 _112866) : (_60498 = (term214 _112866)) = (term405 _112866 _60498).
Proof. exact (EQ_MP (@lem4899743 _112866 _60498) (@lem4899730 _112866 _60498)). Qed.
Lemma lem4899746 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term395 _3571 _3575 t)) = (term396 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem4899747 {_112866 : Type'} (s : _112866 -> Prop) (t : _112866 -> Prop) : (s = (term434 _112866 t)) = (term435 _112866 s t).
Proof. exact (@lem4899746 Prop _112866 s t). Qed.
Lemma lem4899748 {_112866 : Type'} (_60498 : type1402 _112866) (x : _112866) : ((_60498 x) = (term292 _112866 x)) = (term436 _112866 _60498 x).
Proof. exact (@lem4899747 _112866 (_60498 x) (term284 _112866 x)). Qed.
Lemma lem4899749 {_112866 : Type'} (x : _112866) (y : _112866) : (term288 _112866 x y) = (term291 _112866 x y).
Proof. exact (eq_refl (term288 _112866 x y)). Qed.
Lemma lem4899750 {_112866 : Type'} (x : _112866) : (term292 _112866 x) = (term284 _112866 x).
Proof. exact (fun_ext (fun y : _112866 => @lem4899749 _112866 x y)). Qed.
Lemma lem4899751 {_112866 : Type'} (_60498 : type1402 _112866) (x : _112866) : (term402 _112866 _60498 x) = (term402 _112866 _60498 x).
Proof. exact (eq_refl (term402 _112866 _60498 x)). Qed.
Lemma lem4899752 {_112866 : Type'} (_60498 : type1402 _112866) (x : _112866) : ((_60498 x) = (term292 _112866 x)) = ((_60498 x) = (term284 _112866 x)).
Proof. exact (MK_COMB (@lem4899751 _112866 _60498 x) (@lem4899750 _112866 x)). Qed.
Lemma lem4899753 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4899754 {_112866 : Type'} (_60498 : type1402 _112866) (x : _112866) : (term437 _112866 _60498 x) = (term438 _112866 _60498 x).
Proof. exact (MK_COMB (@lem4899753) (@lem4899752 _112866 _60498 x)). Qed.
Lemma lem4899755 {_112866 : Type'} (x : _112866) (y : _112866) : (term288 _112866 x y) = (term291 _112866 x y).
Proof. exact (eq_refl (term288 _112866 x y)). Qed.
Lemma lem4899756 {_112866 : Type'} (_60498 : type1402 _112866) (x : _112866) (y : _112866) : (term439 _112866 _60498 x y) = (term439 _112866 _60498 x y).
Proof. exact (eq_refl (term439 _112866 _60498 x y)). Qed.
Lemma lem4899757 {_112866 : Type'} (_60498 : type1402 _112866) (x : _112866) (y : _112866) : ((_60498 x y) = (term288 _112866 x y)) = ((_60498 x y) = (term291 _112866 x y)).
Proof. exact (MK_COMB (@lem4899756 _112866 _60498 x y) (@lem4899755 _112866 x y)). Qed.
Lemma lem4899758 {_112866 : Type'} (_60498 : type1402 _112866) (x : _112866) : (term440 _112866 _60498 x) = (term441 _112866 _60498 x).
Proof. exact (fun_ext (fun y : _112866 => @lem4899757 _112866 _60498 x y)). Qed.
Lemma lem4899759 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4899760 {_112866 : Type'} (_60498 : type1402 _112866) (x : _112866) : (term436 _112866 _60498 x) = (term442 _112866 _60498 x).
Proof. exact (MK_COMB (@lem4899759 _112866) (@lem4899758 _112866 _60498 x)). Qed.
Lemma lem4899761 {_112866 : Type'} (_60498 : type1402 _112866) (x : _112866) : (((_60498 x) = (term292 _112866 x)) = (term436 _112866 _60498 x)) = (((_60498 x) = (term284 _112866 x)) = (term442 _112866 _60498 x)).
Proof. exact (MK_COMB (@lem4899754 _112866 _60498 x) (@lem4899760 _112866 _60498 x)). Qed.
Lemma lem4899762 {_112866 : Type'} (_60498 : type1402 _112866) (x : _112866) : ((_60498 x) = (term284 _112866 x)) = (term442 _112866 _60498 x).
Proof. exact (EQ_MP (@lem4899761 _112866 _60498 x) (@lem4899748 _112866 _60498 x)). Qed.
Lemma lem4899763 {_112866 : Type'} (_60498 : type1402 _112866) (x : _112866) (y : _112866) : ((_60498 x y) = (term291 _112866 x y)) = ((_60498 x y) = (term291 _112866 x y)).
Proof. exact (eq_refl ((_60498 x y) = (term291 _112866 x y))). Qed.
Lemma lem4899764 {_112866 : Type'} (_60498 : type1402 _112866) (x : _112866) : (term441 _112866 _60498 x) = (term441 _112866 _60498 x).
Proof. exact (fun_ext (fun y : _112866 => @lem4899763 _112866 _60498 x y)). Qed.
Lemma lem4899765 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4899766 {_112866 : Type'} (_60498 : type1402 _112866) (x : _112866) : (term442 _112866 _60498 x) = (term442 _112866 _60498 x).
Proof. exact (MK_COMB (@lem4899765 _112866) (@lem4899764 _112866 _60498 x)). Qed.
Lemma lem4899767 {_112866 : Type'} (_60498 : type1402 _112866) (x : _112866) : ((_60498 x) = (term284 _112866 x)) = (term442 _112866 _60498 x).
Proof. exact (TRANS (@lem4899762 _112866 _60498 x) (@lem4899766 _112866 _60498 x)). Qed.
Lemma lem4899768 {_112866 : Type'} (_60498 : type1402 _112866) : (term404 _112866 _60498) = (term443 _112866 _60498).
Proof. exact (fun_ext (fun x : _112866 => @lem4899767 _112866 _60498 x)). Qed.
Lemma lem4899769 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4899770 {_112866 : Type'} (_60498 : type1402 _112866) : (term405 _112866 _60498) = (term444 _112866 _60498).
Proof. exact (MK_COMB (@lem4899769 _112866) (@lem4899768 _112866 _60498)). Qed.
Lemma lem4899771 {_112866 : Type'} (_60498 : type1402 _112866) : (_60498 = (term214 _112866)) = (term444 _112866 _60498).
Proof. exact (TRANS (@lem4899744 _112866 _60498) (@lem4899770 _112866 _60498)). Qed.
Lemma lem4899772 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4899773 {_112866 : Type'} (_60498 : type1402 _112866) : (term381 _112866 _60498) = (term445 _112866 _60498).
Proof. exact (MK_COMB (@lem4899772) (@lem4899771 _112866 _60498)). Qed.
Lemma lem4899774 {_112866 : Type'} (_60498 : type1402 _112866) : (term414 _112866 _60498) = (term414 _112866 _60498).
Proof. exact (eq_refl (term414 _112866 _60498)). Qed.
Lemma lem4899775 {_112866 : Type'} (_60498 : type1402 _112866) : (term428 _112866 _60498) = (term446 _112866 _60498).
Proof. exact (MK_COMB (@lem4899773 _112866 _60498) (@lem4899774 _112866 _60498)). Qed.
Lemma lem4899776 {_112866 : Type'} : (term430 _112866) = (term447 _112866).
Proof. exact (fun_ext (fun _60498 : type1402 _112866 => @lem4899775 _112866 _60498)). Qed.
Lemma lem4899777 {_112866 : Type'} : (@all (_112866 -> _112866 -> Prop)) = (@all (_112866 -> _112866 -> Prop)).
Proof. exact (eq_refl (@all (_112866 -> _112866 -> Prop))). Qed.
Lemma lem4899778 {_112866 : Type'} : (term432 _112866) = (term448 _112866).
Proof. exact (MK_COMB (@lem4899777 _112866) (@lem4899776 _112866)). Qed.
Lemma lem4899779 {_112866 : Type'} : (term420 _112866) = (term420 _112866).
Proof. exact (eq_refl (term420 _112866)). Qed.
Lemma lem4899780 {_112866 : Type'} : ((term409 _112866) = (term432 _112866)) = ((term409 _112866) = (term448 _112866)).
Proof. exact (MK_COMB (@lem4899779 _112866) (@lem4899778 _112866)). Qed.
Lemma lem4899783 {_112866 : Type'} : (term409 _112866) = (term448 _112866).
Proof. exact (EQ_MP (@lem4899780 _112866) (@lem4899726 _112866)). Qed.
Lemma lem4899784 {_112866 : Type'} : (term356 _112866) = (term448 _112866).
Proof. exact (TRANS (@lem4899559 _112866) (@lem4899783 _112866)). Qed.
Lemma lem4899785 {_112866 : Type'} : (term355 _112866) = (term448 _112866).
Proof. exact (TRANS (@lem4899379 _112866) (@lem4899784 _112866)). Qed.
Lemma lem4899786 {_112866 : Type'} (l : list _112866) : (term357 _112866 l) = (term357 _112866 l).
Proof. exact (eq_refl (term357 _112866 l)). Qed.
Lemma lem4899787 {_112866 : Type'} : (term358 _112866) = (term358 _112866).
Proof. exact (fun_ext (fun l : list _112866 => @lem4899786 _112866 l)). Qed.
Lemma lem4899788 {_112866 : Type'} : (@all (list _112866)) = (@all (list _112866)).
Proof. exact (eq_refl (@all (list _112866))). Qed.
Lemma lem4899789 {_112866 : Type'} : (term333 _112866) = (term333 _112866).
Proof. exact (MK_COMB (@lem4899788 _112866) (@lem4899787 _112866)). Qed.
Lemma lem4899790 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4899791 {_112866 : Type'} : (term339 _112866) = (term339 _112866).
Proof. exact (MK_COMB (@lem4899790) (@lem4899789 _112866)). Qed.
Lemma lem4899794 (n : nat) : (term5 n) = (term5 n).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem4899795 : term359 = term359.
Proof. exact (fun_ext (fun n : nat => @lem4899794 n)). Qed.
Lemma lem4899796 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4899797 : term152 = term152.
Proof. exact (MK_COMB (@lem4899796) (@lem4899795)). Qed.
Lemma lem4899798 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4899799 : term340 = term340.
Proof. exact (MK_COMB (@lem4899798) (@lem4899797)). Qed.
Lemma lem4899800 {_112866 : Type'} : (term342 _112866) = (term342 _112866).
Proof. exact (MK_COMB (@lem4899799) (@lem4899791 _112866)). Qed.
Lemma lem4899801 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) : (@List.ForallOrdPairs _112866 _60497 t) = (@List.ForallOrdPairs _112866 _60497 t).
Proof. exact (eq_refl (@List.ForallOrdPairs _112866 _60497 t)). Qed.
Lemma lem4899808 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term298 _112866 t h x) = (term298 _112866 t h x).
Proof. exact (eq_refl (term298 _112866 t h x)). Qed.
Lemma lem4899809 {_112866 : Type'} (t : list _112866) (h : _112866) : (term300 _112866 t h) = (term300 _112866 t h).
Proof. exact (fun_ext (fun x : _112866 => @lem4899808 _112866 t h x)). Qed.
Lemma lem4899810 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4899811 {_112866 : Type'} (t : list _112866) (h : _112866) : (term301 _112866 t h) = (term301 _112866 t h).
Proof. exact (MK_COMB (@lem4899810 _112866) (@lem4899809 _112866 t h)). Qed.
Lemma lem4899812 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4899813 {_112866 : Type'} (t : list _112866) (h : _112866) : (term303 _112866 t h) = (term303 _112866 t h).
Proof. exact (MK_COMB (@lem4899812) (@lem4899811 _112866 t h)). Qed.
Lemma lem4899814 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term361 _112866 h _60497 t) = (term361 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4899813 _112866 t h) (@lem4899801 _112866 _60497 t)). Qed.
Lemma lem4899817 {_112866 : Type'} (t : list _112866) : (term362 _112866 t) = (term362 _112866 t).
Proof. exact (eq_refl (term362 _112866 t)). Qed.
Lemma lem4899818 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (((term171 _112866 t) = (term225 _112866 t)) = (term361 _112866 h _60497 t)) = (((term171 _112866 t) = (term225 _112866 t)) = (term361 _112866 h _60497 t)).
Proof. exact (MK_COMB (@lem4899817 _112866 t) (@lem4899814 _112866 h _60497 t)). Qed.
Lemma lem4899819 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4899820 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term363 _112866 h _60497 t) = (term363 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4899819) (@lem4899818 _112866 h _60497 t)). Qed.
Lemma lem4899821 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4899822 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term364 _112866 h _60497 t) = (term364 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4899821) (@lem4899820 _112866 h _60497 t)). Qed.
Lemma lem4899823 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term365 _112866 h _60497 t) = (term365 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4899822 _112866 h _60497 t) (@lem4899800 _112866)). Qed.
Lemma lem4899826 {_112866 : Type'} (h : _112866) (t : list _112866) : (term317 _112866 h t) = (term317 _112866 h t).
Proof. exact (eq_refl (term317 _112866 h t)). Qed.
Lemma lem4899827 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term366 _112866 h _60497 t) = (term366 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4899826 _112866 h t) (@lem4899823 _112866 h _60497 t)). Qed.
Lemma lem4899834 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) : (term367 _112866 _60497 t) = (term367 _112866 _60497 t).
Proof. exact (eq_refl (term367 _112866 _60497 t)). Qed.
Lemma lem4899835 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term368 _112866 h _60497 t) = (term368 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4899834 _112866 _60497 t) (@lem4899827 _112866 h _60497 t)). Qed.
Lemma lem4899836 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) : (term369 _112866 _60497 t) = (term369 _112866 _60497 t).
Proof. exact (fun_ext (fun h : _112866 => @lem4899835 _112866 h _60497 t)). Qed.
Lemma lem4899837 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4899838 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) : (term370 _112866 _60497 t) = (term370 _112866 _60497 t).
Proof. exact (MK_COMB (@lem4899837 _112866) (@lem4899836 _112866 _60497 t)). Qed.
Lemma lem4899839 {_112866 : Type'} (_60497 : type1402 _112866) : (term371 _112866 _60497) = (term371 _112866 _60497).
Proof. exact (fun_ext (fun t : list _112866 => @lem4899838 _112866 _60497 t)). Qed.
Lemma lem4899840 {_112866 : Type'} : (@all (list _112866)) = (@all (list _112866)).
Proof. exact (eq_refl (@all (list _112866))). Qed.
Lemma lem4899841 {_112866 : Type'} (_60497 : type1402 _112866) : (term372 _112866 _60497) = (term372 _112866 _60497).
Proof. exact (MK_COMB (@lem4899840 _112866) (@lem4899839 _112866 _60497)). Qed.
Lemma lem4899842 {_112866 : Type'} (_60497 : type1402 _112866) (_60498 : type1402 _112866) (x : _112866) : ((_60497 x) = (_60498 x)) = ((_60497 x) = (_60498 x)).
Proof. exact (eq_refl ((_60497 x) = (_60498 x))). Qed.
Lemma lem4899843 {_112866 : Type'} (_60497 : type1402 _112866) (_60498 : type1402 _112866) : (term410 _112866 _60497 _60498) = (term410 _112866 _60497 _60498).
Proof. exact (fun_ext (fun x : _112866 => @lem4899842 _112866 _60497 _60498 x)). Qed.
Lemma lem4899844 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4899845 {_112866 : Type'} (_60497 : type1402 _112866) (_60498 : type1402 _112866) : (term398 _112866 _60497 _60498) = (term398 _112866 _60497 _60498).
Proof. exact (MK_COMB (@lem4899844 _112866) (@lem4899843 _112866 _60497 _60498)). Qed.
Lemma lem4899846 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4899847 {_112866 : Type'} (_60497 : type1402 _112866) (_60498 : type1402 _112866) : (term411 _112866 _60497 _60498) = (term411 _112866 _60497 _60498).
Proof. exact (MK_COMB (@lem4899846) (@lem4899845 _112866 _60497 _60498)). Qed.
Lemma lem4899848 {_112866 : Type'} (_60498 : type1402 _112866) (_60497 : type1402 _112866) : (term412 _112866 _60498 _60497) = (term412 _112866 _60498 _60497).
Proof. exact (MK_COMB (@lem4899847 _112866 _60497 _60498) (@lem4899841 _112866 _60497)). Qed.
Lemma lem4899849 {_112866 : Type'} (_60498 : type1402 _112866) : (term413 _112866 _60498) = (term413 _112866 _60498).
Proof. exact (fun_ext (fun _60497 : type1402 _112866 => @lem4899848 _112866 _60498 _60497)). Qed.
Lemma lem4899850 {_112866 : Type'} : (@all (_112866 -> _112866 -> Prop)) = (@all (_112866 -> _112866 -> Prop)).
Proof. exact (eq_refl (@all (_112866 -> _112866 -> Prop))). Qed.
Lemma lem4899851 {_112866 : Type'} (_60498 : type1402 _112866) : (term414 _112866 _60498) = (term414 _112866 _60498).
Proof. exact (MK_COMB (@lem4899850 _112866) (@lem4899849 _112866 _60498)). Qed.
Lemma lem4899858 {_112866 : Type'} (_60498 : type1402 _112866) (x : _112866) (y : _112866) : ((_60498 x y) = (term291 _112866 x y)) = ((_60498 x y) = (term291 _112866 x y)).
Proof. exact (eq_refl ((_60498 x y) = (term291 _112866 x y))). Qed.
Lemma lem4899859 {_112866 : Type'} (_60498 : type1402 _112866) (x : _112866) : (term441 _112866 _60498 x) = (term441 _112866 _60498 x).
Proof. exact (fun_ext (fun y : _112866 => @lem4899858 _112866 _60498 x y)). Qed.
Lemma lem4899860 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4899861 {_112866 : Type'} (_60498 : type1402 _112866) (x : _112866) : (term442 _112866 _60498 x) = (term442 _112866 _60498 x).
Proof. exact (MK_COMB (@lem4899860 _112866) (@lem4899859 _112866 _60498 x)). Qed.
Lemma lem4899862 {_112866 : Type'} (_60498 : type1402 _112866) : (term443 _112866 _60498) = (term443 _112866 _60498).
Proof. exact (fun_ext (fun x : _112866 => @lem4899861 _112866 _60498 x)). Qed.
Lemma lem4899863 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4899864 {_112866 : Type'} (_60498 : type1402 _112866) : (term444 _112866 _60498) = (term444 _112866 _60498).
Proof. exact (MK_COMB (@lem4899863 _112866) (@lem4899862 _112866 _60498)). Qed.
Lemma lem4899865 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4899866 {_112866 : Type'} (_60498 : type1402 _112866) : (term445 _112866 _60498) = (term445 _112866 _60498).
Proof. exact (MK_COMB (@lem4899865) (@lem4899864 _112866 _60498)). Qed.
Lemma lem4899867 {_112866 : Type'} (_60498 : type1402 _112866) : (term446 _112866 _60498) = (term446 _112866 _60498).
Proof. exact (MK_COMB (@lem4899866 _112866 _60498) (@lem4899851 _112866 _60498)). Qed.
Lemma lem4899868 {_112866 : Type'} : (term447 _112866) = (term447 _112866).
Proof. exact (fun_ext (fun _60498 : type1402 _112866 => @lem4899867 _112866 _60498)). Qed.
Lemma lem4899869 {_112866 : Type'} : (@all (_112866 -> _112866 -> Prop)) = (@all (_112866 -> _112866 -> Prop)).
Proof. exact (eq_refl (@all (_112866 -> _112866 -> Prop))). Qed.
Lemma lem4899870 {_112866 : Type'} : (term448 _112866) = (term448 _112866).
Proof. exact (MK_COMB (@lem4899869 _112866) (@lem4899868 _112866)). Qed.
Lemma lem4899949 {_112866 : Type'} : (term355 _112866) = (term448 _112866).
Proof. exact (TRANS (@lem4899785 _112866) (@lem4899870 _112866)). Qed.
Lemma lem4899950 {_112866 : Type'} : (term448 _112866) = (term355 _112866).
Proof. exact (SYM (@lem4899949 _112866)). Qed.
Lemma lem4899953 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) (h1 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t).
Proof. exact (h1). Qed.
Lemma lem4899955 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term363 _112866 h _60497 t) : term363 _112866 h _60497 t.
Proof. exact (h1). Qed.
Lemma lem4899956 (h1 : term152) : term152.
Proof. exact (h1). Qed.
Lemma lem4899957 {_112866 : Type'} (h1 : term333 _112866) : term333 _112866.
Proof. exact (h1). Qed.
Lemma lem4900278 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) : (((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) = (term449 _112866 _60497 t).
Proof. exact (@lem17500 ((term171 _112866 t) = (@List.length _112866 t)) (@List.ForallOrdPairs _112866 _60497 t)). Qed.
Lemma lem4900285 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : @List.In _112866 h t) : @List.In _112866 h t.
Proof. exact (h1). Qed.
Lemma lem4900293 {_112866 : Type'} (h : _112866) (x : _112866) : (term450 _112866 h x) = (h = x).
Proof. exact (@lem16933 (h = x)). Qed.
Lemma lem4900295 {_112866 : Type'} (x : _112866) (t : list _112866) : (term451 _112866 x t) = (term451 _112866 x t).
Proof. exact (eq_refl (term451 _112866 x t)). Qed.
Lemma lem4900296 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term452 _112866 t h x) = (term453 _112866 t h x).
Proof. exact (MK_COMB (@lem4900295 _112866 x t) (@lem4900293 _112866 h x)). Qed.
Lemma lem4900297 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term454 _112866 t h x) = (term452 _112866 t h x).
Proof. exact (@lem17362 (@List.In _112866 x t) (term291 _112866 h x)). Qed.
Lemma lem4900298 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term454 _112866 t h x) = (term453 _112866 t h x).
Proof. exact (TRANS (@lem4900297 _112866 t h x) (@lem4900296 _112866 t h x)). Qed.
Lemma lem4900303 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term298 _112866 t h x) = (term455 _112866 t h x).
Proof. exact (@lem17265 (@List.In _112866 x t) (term291 _112866 h x)). Qed.
Lemma lem4900304 {_112866 : Type'} (P : _112866 -> Prop) : (term456 _112866 P) = (term457 _112866 P).
Proof. exact (@lem18392 _112866 P). Qed.
Lemma lem4900305 {_112866 : Type'} (t : list _112866) (h : _112866) : (term458 _112866 t h) = (term459 _112866 t h).
Proof. exact (@lem4900304 _112866 (term300 _112866 t h)). Qed.
Lemma lem4900306 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term460 _112866 t h x) = (term298 _112866 t h x).
Proof. exact (eq_refl (term460 _112866 t h x)). Qed.
Lemma lem4900307 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4900308 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term461 _112866 t h x) = (term454 _112866 t h x).
Proof. exact (MK_COMB (@lem4900307) (@lem4900306 _112866 t h x)). Qed.
Lemma lem4900309 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term461 _112866 t h x) = (term453 _112866 t h x).
Proof. exact (TRANS (@lem4900308 _112866 t h x) (@lem4900298 _112866 t h x)). Qed.
Lemma lem4900310 {_112866 : Type'} (t : list _112866) (h : _112866) : (term462 _112866 t h) = (term463 _112866 t h).
Proof. exact (fun_ext (fun x : _112866 => @lem4900309 _112866 t h x)). Qed.
Lemma lem4900311 {_112866 : Type'} : (@ex _112866) = (@ex _112866).
Proof. exact (eq_refl (@ex _112866)). Qed.
Lemma lem4900312 {_112866 : Type'} (t : list _112866) (h : _112866) : (term459 _112866 t h) = (term464 _112866 t h).
Proof. exact (MK_COMB (@lem4900311 _112866) (@lem4900310 _112866 t h)). Qed.
Lemma lem4900313 {_112866 : Type'} (t : list _112866) (h : _112866) : (term458 _112866 t h) = (term464 _112866 t h).
Proof. exact (TRANS (@lem4900305 _112866 t h) (@lem4900312 _112866 t h)). Qed.
Lemma lem4900314 {_112866 : Type'} (t : list _112866) (h : _112866) : (term300 _112866 t h) = (term465 _112866 t h).
Proof. exact (fun_ext (fun x : _112866 => @lem4900303 _112866 t h x)). Qed.
Lemma lem4900315 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4900316 {_112866 : Type'} (t : list _112866) (h : _112866) : (term301 _112866 t h) = (term466 _112866 t h).
Proof. exact (MK_COMB (@lem4900315 _112866) (@lem4900314 _112866 t h)). Qed.
Lemma lem4900317 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) : (term467 _112866 _60497 t) = (term467 _112866 _60497 t).
Proof. exact (eq_refl (term467 _112866 _60497 t)). Qed.
Lemma lem4900318 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) : (@List.ForallOrdPairs _112866 _60497 t) = (@List.ForallOrdPairs _112866 _60497 t).
Proof. exact (eq_refl (@List.ForallOrdPairs _112866 _60497 t)). Qed.
Lemma lem4900319 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4900320 {_112866 : Type'} (t : list _112866) (h : _112866) : (term468 _112866 t h) = (term469 _112866 t h).
Proof. exact (MK_COMB (@lem4900319) (@lem4900313 _112866 t h)). Qed.
Lemma lem4900321 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term470 _112866 h _60497 t) = (term471 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4900320 _112866 t h) (@lem4900317 _112866 _60497 t)). Qed.
Lemma lem4900322 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term472 _112866 h _60497 t) = (term470 _112866 h _60497 t).
Proof. exact (@lem17045 (term301 _112866 t h) (@List.ForallOrdPairs _112866 _60497 t)). Qed.
Lemma lem4900323 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term472 _112866 h _60497 t) = (term471 _112866 h _60497 t).
Proof. exact (TRANS (@lem4900322 _112866 h _60497 t) (@lem4900321 _112866 h _60497 t)). Qed.
Lemma lem4900324 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4900325 {_112866 : Type'} (t : list _112866) (h : _112866) : (term303 _112866 t h) = (term473 _112866 t h).
Proof. exact (MK_COMB (@lem4900324) (@lem4900316 _112866 t h)). Qed.
Lemma lem4900326 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term361 _112866 h _60497 t) = (term474 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4900325 _112866 t h) (@lem4900318 _112866 _60497 t)). Qed.
Lemma lem4900328 {_112866 : Type'} (t : list _112866) : (term475 _112866 t) = (term475 _112866 t).
Proof. exact (eq_refl (term475 _112866 t)). Qed.
Lemma lem4900329 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term476 _112866 h _60497 t) = (term477 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4900328 _112866 t) (@lem4900326 _112866 h _60497 t)). Qed.
Lemma lem4900331 {_112866 : Type'} (t : list _112866) : (term478 _112866 t) = (term478 _112866 t).
Proof. exact (eq_refl (term478 _112866 t)). Qed.
Lemma lem4900332 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term479 _112866 h _60497 t) = (term480 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4900331 _112866 t) (@lem4900323 _112866 h _60497 t)). Qed.
Lemma lem4900333 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4900334 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term481 _112866 h _60497 t) = (term482 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4900333) (@lem4900332 _112866 h _60497 t)). Qed.
Lemma lem4900335 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term483 _112866 h _60497 t) = (term484 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4900334 _112866 h _60497 t) (@lem4900329 _112866 h _60497 t)). Qed.
Lemma lem4900336 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term363 _112866 h _60497 t) = (term483 _112866 h _60497 t).
Proof. exact (@lem17646 ((term171 _112866 t) = (term225 _112866 t)) (term361 _112866 h _60497 t)). Qed.
Lemma lem4900337 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term363 _112866 h _60497 t) = (term484 _112866 h _60497 t).
Proof. exact (TRANS (@lem4900336 _112866 h _60497 t) (@lem4900335 _112866 h _60497 t)). Qed.
Lemma lem4900436 {A : Type'} (P : A -> Prop) (Q : Prop) : (term485 A P Q) = (term486 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4900437 {_112866 : Type'} (P : _112866 -> Prop) (Q : Prop) : (term485 _112866 P Q) = (term486 _112866 P Q).
Proof. exact (@lem4900436 _112866 P Q). Qed.
Lemma lem4900438 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term487 _112866 h _60497 t) = (term488 _112866 h _60497 t).
Proof. exact (@lem4900437 _112866 (term463 _112866 t h) (term467 _112866 _60497 t)). Qed.
Lemma lem4900439 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term489 _112866 t h x) = (term453 _112866 t h x).
Proof. exact (eq_refl (term489 _112866 t h x)). Qed.
Lemma lem4900440 {_112866 : Type'} (t : list _112866) (h : _112866) : (term490 _112866 t h) = (term463 _112866 t h).
Proof. exact (fun_ext (fun x : _112866 => @lem4900439 _112866 t h x)). Qed.
Lemma lem4900441 {_112866 : Type'} : (@ex _112866) = (@ex _112866).
Proof. exact (eq_refl (@ex _112866)). Qed.
Lemma lem4900442 {_112866 : Type'} (t : list _112866) (h : _112866) : (term491 _112866 t h) = (term464 _112866 t h).
Proof. exact (MK_COMB (@lem4900441 _112866) (@lem4900440 _112866 t h)). Qed.
Lemma lem4900443 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4900444 {_112866 : Type'} (t : list _112866) (h : _112866) : (term492 _112866 t h) = (term469 _112866 t h).
Proof. exact (MK_COMB (@lem4900443) (@lem4900442 _112866 t h)). Qed.
Lemma lem4900445 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) : (term467 _112866 _60497 t) = (term467 _112866 _60497 t).
Proof. exact (eq_refl (term467 _112866 _60497 t)). Qed.
Lemma lem4900446 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term487 _112866 h _60497 t) = (term471 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4900444 _112866 t h) (@lem4900445 _112866 _60497 t)). Qed.
Lemma lem4900447 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4900448 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term493 _112866 h _60497 t) = (term494 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4900447) (@lem4900446 _112866 h _60497 t)). Qed.
Lemma lem4900449 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term489 _112866 t h x) = (term453 _112866 t h x).
Proof. exact (eq_refl (term489 _112866 t h x)). Qed.
Lemma lem4900450 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4900451 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term495 _112866 t h x) = (term496 _112866 t h x).
Proof. exact (MK_COMB (@lem4900450) (@lem4900449 _112866 t h x)). Qed.
Lemma lem4900452 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) : (term467 _112866 _60497 t) = (term467 _112866 _60497 t).
Proof. exact (eq_refl (term467 _112866 _60497 t)). Qed.
Lemma lem4900453 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term497 _112866 h x _60497 t) = (term498 _112866 h x _60497 t).
Proof. exact (MK_COMB (@lem4900451 _112866 t h x) (@lem4900452 _112866 _60497 t)). Qed.
Lemma lem4900454 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term499 _112866 h _60497 t) = (term500 _112866 h _60497 t).
Proof. exact (fun_ext (fun x : _112866 => @lem4900453 _112866 h x _60497 t)). Qed.
Lemma lem4900455 {_112866 : Type'} : (@ex _112866) = (@ex _112866).
Proof. exact (eq_refl (@ex _112866)). Qed.
Lemma lem4900456 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term488 _112866 h _60497 t) = (term501 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4900455 _112866) (@lem4900454 _112866 h _60497 t)). Qed.
Lemma lem4900457 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : ((term487 _112866 h _60497 t) = (term488 _112866 h _60497 t)) = ((term471 _112866 h _60497 t) = (term501 _112866 h _60497 t)).
Proof. exact (MK_COMB (@lem4900448 _112866 h _60497 t) (@lem4900456 _112866 h _60497 t)). Qed.
Lemma lem4900458 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term471 _112866 h _60497 t) = (term501 _112866 h _60497 t).
Proof. exact (EQ_MP (@lem4900457 _112866 h _60497 t) (@lem4900438 _112866 h _60497 t)). Qed.
Lemma lem4900459 {_112866 : Type'} (t : list _112866) : (term478 _112866 t) = (term478 _112866 t).
Proof. exact (eq_refl (term478 _112866 t)). Qed.
Lemma lem4900460 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term480 _112866 h _60497 t) = (term502 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4900459 _112866 t) (@lem4900458 _112866 h _60497 t)). Qed.
Lemma lem4900462 {A : Type'} (P : Prop) (Q : A -> Prop) : (term503 A P Q) = (term504 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4900463 {_112866 : Type'} (P : Prop) (Q : _112866 -> Prop) : (term503 _112866 P Q) = (term504 _112866 P Q).
Proof. exact (@lem4900462 _112866 P Q). Qed.
Lemma lem4900464 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term505 _112866 h _60497 t) = (term506 _112866 h _60497 t).
Proof. exact (@lem4900463 _112866 ((term171 _112866 t) = (term225 _112866 t)) (term500 _112866 h _60497 t)). Qed.
Lemma lem4900465 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term507 _112866 h _60497 t x) = (term498 _112866 h x _60497 t).
Proof. exact (eq_refl (term507 _112866 h _60497 t x)). Qed.
Lemma lem4900466 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term508 _112866 h _60497 t) = (term500 _112866 h _60497 t).
Proof. exact (fun_ext (fun x : _112866 => @lem4900465 _112866 h x _60497 t)). Qed.
Lemma lem4900467 {_112866 : Type'} : (@ex _112866) = (@ex _112866).
Proof. exact (eq_refl (@ex _112866)). Qed.
Lemma lem4900468 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term509 _112866 h _60497 t) = (term501 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4900467 _112866) (@lem4900466 _112866 h _60497 t)). Qed.
Lemma lem4900469 {_112866 : Type'} (t : list _112866) : (term478 _112866 t) = (term478 _112866 t).
Proof. exact (eq_refl (term478 _112866 t)). Qed.
Lemma lem4900470 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term505 _112866 h _60497 t) = (term502 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4900469 _112866 t) (@lem4900468 _112866 h _60497 t)). Qed.
Lemma lem4900471 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4900472 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term510 _112866 h _60497 t) = (term511 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4900471) (@lem4900470 _112866 h _60497 t)). Qed.
Lemma lem4900473 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term507 _112866 h _60497 t x) = (term498 _112866 h x _60497 t).
Proof. exact (eq_refl (term507 _112866 h _60497 t x)). Qed.
Lemma lem4900474 {_112866 : Type'} (t : list _112866) : (term478 _112866 t) = (term478 _112866 t).
Proof. exact (eq_refl (term478 _112866 t)). Qed.
Lemma lem4900475 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term512 _112866 h _60497 t x) = (term513 _112866 h x _60497 t).
Proof. exact (MK_COMB (@lem4900474 _112866 t) (@lem4900473 _112866 h x _60497 t)). Qed.
Lemma lem4900476 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term514 _112866 h _60497 t) = (term515 _112866 h _60497 t).
Proof. exact (fun_ext (fun x : _112866 => @lem4900475 _112866 h x _60497 t)). Qed.
Lemma lem4900477 {_112866 : Type'} : (@ex _112866) = (@ex _112866).
Proof. exact (eq_refl (@ex _112866)). Qed.
Lemma lem4900478 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term506 _112866 h _60497 t) = (term516 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4900477 _112866) (@lem4900476 _112866 h _60497 t)). Qed.
Lemma lem4900479 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : ((term505 _112866 h _60497 t) = (term506 _112866 h _60497 t)) = ((term502 _112866 h _60497 t) = (term516 _112866 h _60497 t)).
Proof. exact (MK_COMB (@lem4900472 _112866 h _60497 t) (@lem4900478 _112866 h _60497 t)). Qed.
Lemma lem4900480 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term502 _112866 h _60497 t) = (term516 _112866 h _60497 t).
Proof. exact (EQ_MP (@lem4900479 _112866 h _60497 t) (@lem4900464 _112866 h _60497 t)). Qed.
Lemma lem4900481 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term480 _112866 h _60497 t) = (term516 _112866 h _60497 t).
Proof. exact (TRANS (@lem4900460 _112866 h _60497 t) (@lem4900480 _112866 h _60497 t)). Qed.
Lemma lem4900482 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4900483 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term482 _112866 h _60497 t) = (term517 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4900482) (@lem4900481 _112866 h _60497 t)). Qed.
Lemma lem4900484 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term477 _112866 h _60497 t) = (term477 _112866 h _60497 t).
Proof. exact (eq_refl (term477 _112866 h _60497 t)). Qed.
Lemma lem4900485 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term484 _112866 h _60497 t) = (term518 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4900483 _112866 h _60497 t) (@lem4900484 _112866 h _60497 t)). Qed.
Lemma lem4900487 {A : Type'} (P : A -> Prop) (Q : Prop) : (term485 A P Q) = (term486 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4900488 {_112866 : Type'} (P : _112866 -> Prop) (Q : Prop) : (term485 _112866 P Q) = (term486 _112866 P Q).
Proof. exact (@lem4900487 _112866 P Q). Qed.
Lemma lem4900489 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term519 _112866 h _60497 t) = (term520 _112866 h _60497 t).
Proof. exact (@lem4900488 _112866 (term515 _112866 h _60497 t) (term477 _112866 h _60497 t)). Qed.
Lemma lem4900490 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term521 _112866 h _60497 t x) = (term513 _112866 h x _60497 t).
Proof. exact (eq_refl (term521 _112866 h _60497 t x)). Qed.
Lemma lem4900491 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term522 _112866 h _60497 t) = (term515 _112866 h _60497 t).
Proof. exact (fun_ext (fun x : _112866 => @lem4900490 _112866 h x _60497 t)). Qed.
Lemma lem4900492 {_112866 : Type'} : (@ex _112866) = (@ex _112866).
Proof. exact (eq_refl (@ex _112866)). Qed.
Lemma lem4900493 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term523 _112866 h _60497 t) = (term516 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4900492 _112866) (@lem4900491 _112866 h _60497 t)). Qed.
Lemma lem4900494 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4900495 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term524 _112866 h _60497 t) = (term517 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4900494) (@lem4900493 _112866 h _60497 t)). Qed.
Lemma lem4900496 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term477 _112866 h _60497 t) = (term477 _112866 h _60497 t).
Proof. exact (eq_refl (term477 _112866 h _60497 t)). Qed.
Lemma lem4900497 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term519 _112866 h _60497 t) = (term518 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4900495 _112866 h _60497 t) (@lem4900496 _112866 h _60497 t)). Qed.
Lemma lem4900498 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4900499 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term525 _112866 h _60497 t) = (term526 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4900498) (@lem4900497 _112866 h _60497 t)). Qed.
Lemma lem4900500 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term521 _112866 h _60497 t x) = (term513 _112866 h x _60497 t).
Proof. exact (eq_refl (term521 _112866 h _60497 t x)). Qed.
Lemma lem4900501 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4900502 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term527 _112866 h _60497 t x) = (term528 _112866 h x _60497 t).
Proof. exact (MK_COMB (@lem4900501) (@lem4900500 _112866 h x _60497 t)). Qed.
Lemma lem4900503 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term477 _112866 h _60497 t) = (term477 _112866 h _60497 t).
Proof. exact (eq_refl (term477 _112866 h _60497 t)). Qed.
Lemma lem4900504 {_112866 : Type'} (x : _112866) (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term529 _112866 x h _60497 t) = (term530 _112866 x h _60497 t).
Proof. exact (MK_COMB (@lem4900502 _112866 h x _60497 t) (@lem4900503 _112866 h _60497 t)). Qed.
Lemma lem4900505 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term531 _112866 h _60497 t) = (term532 _112866 h _60497 t).
Proof. exact (fun_ext (fun x : _112866 => @lem4900504 _112866 x h _60497 t)). Qed.
Lemma lem4900506 {_112866 : Type'} : (@ex _112866) = (@ex _112866).
Proof. exact (eq_refl (@ex _112866)). Qed.
Lemma lem4900507 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term520 _112866 h _60497 t) = (term533 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4900506 _112866) (@lem4900505 _112866 h _60497 t)). Qed.
Lemma lem4900508 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : ((term519 _112866 h _60497 t) = (term520 _112866 h _60497 t)) = ((term518 _112866 h _60497 t) = (term533 _112866 h _60497 t)).
Proof. exact (MK_COMB (@lem4900499 _112866 h _60497 t) (@lem4900507 _112866 h _60497 t)). Qed.
Lemma lem4900509 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term518 _112866 h _60497 t) = (term533 _112866 h _60497 t).
Proof. exact (EQ_MP (@lem4900508 _112866 h _60497 t) (@lem4900489 _112866 h _60497 t)). Qed.
Lemma lem4900511 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term484 _112866 h _60497 t) = (term533 _112866 h _60497 t).
Proof. exact (TRANS (@lem4900485 _112866 h _60497 t) (@lem4900509 _112866 h _60497 t)). Qed.
Lemma lem4900512 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term363 _112866 h _60497 t) = (term533 _112866 h _60497 t).
Proof. exact (TRANS (@lem4900337 _112866 h _60497 t) (@lem4900511 _112866 h _60497 t)). Qed.
Lemma lem4900513 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term363 _112866 h _60497 t) : term533 _112866 h _60497 t.
Proof. exact (EQ_MP (@lem4900512 _112866 h _60497 t) (@lem4899955 _112866 h _60497 t h1)). Qed.
Lemma lem4900514 (n : nat) : (term5 n) = (term5 n).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem4900515 : term359 = term359.
Proof. exact (fun_ext (fun n : nat => @lem4900514 n)). Qed.
Lemma lem4900516 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4900525 : term152 = term152.
Proof. exact (MK_COMB (@lem4900516) (@lem4900515)). Qed.
Lemma lem4900526 (h1 : term152) : term152.
Proof. exact (EQ_MP (@lem4900525) (@lem4899956 h1)). Qed.
Lemma lem4900527 {_112866 : Type'} (l : list _112866) : (term357 _112866 l) = (term357 _112866 l).
Proof. exact (eq_refl (term357 _112866 l)). Qed.
Lemma lem4900528 {_112866 : Type'} : (term358 _112866) = (term358 _112866).
Proof. exact (fun_ext (fun l : list _112866 => @lem4900527 _112866 l)). Qed.
Lemma lem4900529 {_112866 : Type'} : (@all (list _112866)) = (@all (list _112866)).
Proof. exact (eq_refl (@all (list _112866))). Qed.
Lemma lem4900538 {_112866 : Type'} : (term333 _112866) = (term333 _112866).
Proof. exact (MK_COMB (@lem4900529 _112866) (@lem4900528 _112866)). Qed.
Lemma lem4900539 {_112866 : Type'} (h1 : term333 _112866) : term333 _112866.
Proof. exact (EQ_MP (@lem4900538 _112866) (@lem4899957 _112866 h1)). Qed.
Lemma lem4900540 {_112866 : Type'} (x : _112866) (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term530 _112866 x h _60497 t) : term530 _112866 x h _60497 t.
Proof. exact (h1). Qed.
Lemma lem4900660 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) (h1 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) : term449 _112866 _60497 t.
Proof. exact (EQ_MP (@lem4900278 _112866 _60497 t) (@lem4899953 _112866 _60497 t h1)). Qed.
Lemma lem4900666 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : @List.In _112866 h t) : @List.In _112866 h t.
Proof. exact (h1). Qed.
Lemma lem4900675 (n : nat) : (term5 n) = (term5 n).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem4900676 : term359 = term359.
Proof. exact (fun_ext (fun n : nat => @lem4900675 n)). Qed.
Lemma lem4900677 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4900678 : term152 = term152.
Proof. exact (MK_COMB (@lem4900677) (@lem4900676)). Qed.
Lemma lem4900679 (h1 : term152) : term152.
Proof. exact (EQ_MP (@lem4900678) (@lem4900526 h1)). Qed.
Lemma lem4900690 {_112866 : Type'} (l : list _112866) : (term357 _112866 l) = (term357 _112866 l).
Proof. exact (eq_refl (term357 _112866 l)). Qed.
Lemma lem4900691 {_112866 : Type'} : (term358 _112866) = (term358 _112866).
Proof. exact (fun_ext (fun l : list _112866 => @lem4900690 _112866 l)). Qed.
Lemma lem4900692 {_112866 : Type'} : (@all (list _112866)) = (@all (list _112866)).
Proof. exact (eq_refl (@all (list _112866))). Qed.
Lemma lem4900693 {_112866 : Type'} : (term333 _112866) = (term333 _112866).
Proof. exact (MK_COMB (@lem4900692 _112866) (@lem4900691 _112866)). Qed.
Lemma lem4900694 {_112866 : Type'} (h1 : term333 _112866) : term333 _112866.
Proof. exact (EQ_MP (@lem4900693 _112866) (@lem4900539 _112866 h1)). Qed.
Lemma lem4900699 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) : (@List.ForallOrdPairs _112866 _60497 t) = (@List.ForallOrdPairs _112866 _60497 t).
Proof. exact (eq_refl (@List.ForallOrdPairs _112866 _60497 t)). Qed.
Lemma lem4900716 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term455 _112866 t h x) = (term455 _112866 t h x).
Proof. exact (eq_refl (term455 _112866 t h x)). Qed.
Lemma lem4900717 {_112866 : Type'} (t : list _112866) (h : _112866) : (term465 _112866 t h) = (term465 _112866 t h).
Proof. exact (fun_ext (fun x : _112866 => @lem4900716 _112866 t h x)). Qed.
Lemma lem4900718 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4900719 {_112866 : Type'} (t : list _112866) (h : _112866) : (term466 _112866 t h) = (term466 _112866 t h).
Proof. exact (MK_COMB (@lem4900718 _112866) (@lem4900717 _112866 t h)). Qed.
Lemma lem4900720 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4900721 {_112866 : Type'} (t : list _112866) (h : _112866) : (term473 _112866 t h) = (term473 _112866 t h).
Proof. exact (MK_COMB (@lem4900720) (@lem4900719 _112866 t h)). Qed.
Lemma lem4900722 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term474 _112866 h _60497 t) = (term474 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4900721 _112866 t h) (@lem4900699 _112866 _60497 t)). Qed.
Lemma lem4900739 {_112866 : Type'} (t : list _112866) : (term475 _112866 t) = (term475 _112866 t).
Proof. exact (eq_refl (term475 _112866 t)). Qed.
Lemma lem4900740 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term477 _112866 h _60497 t) = (term477 _112866 h _60497 t).
Proof. exact (MK_COMB (@lem4900739 _112866 t) (@lem4900722 _112866 h _60497 t)). Qed.
Lemma lem4900781 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term528 _112866 h x _60497 t) = (term528 _112866 h x _60497 t).
Proof. exact (eq_refl (term528 _112866 h x _60497 t)). Qed.
Lemma lem4900782 {_112866 : Type'} (x : _112866) (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : (term530 _112866 x h _60497 t) = (term530 _112866 x h _60497 t).
Proof. exact (MK_COMB (@lem4900781 _112866 h x _60497 t) (@lem4900740 _112866 h _60497 t)). Qed.
Lemma lem4900783 {_112866 : Type'} (x : _112866) (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term530 _112866 x h _60497 t) : term530 _112866 x h _60497 t.
Proof. exact (EQ_MP (@lem4900782 _112866 x h _60497 t) (@lem4900540 _112866 x h _60497 t h1)). Qed.
Lemma lem4900786 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term513 _112866 h x _60497 t) : term513 _112866 h x _60497 t.
Proof. exact (h1). Qed.
Lemma lem4900787 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term477 _112866 h _60497 t) : term477 _112866 h _60497 t.
Proof. exact (h1). Qed.
Lemma lem4900788 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term513 _112866 h x _60497 t) : term498 _112866 h x _60497 t.
Proof. exact (proj2 (@lem4900786 _112866 h x _60497 t h1)). Qed.
Lemma lem4900800 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) (h1 : term534 _112866 _60497 t) : term534 _112866 _60497 t.
Proof. exact (h1). Qed.
Lemma lem4900806 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term477 _112866 h _60497 t) : term474 _112866 h _60497 t.
Proof. exact (proj2 (@lem4900787 _112866 h _60497 t h1)). Qed.
Lemma lem4900809 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term477 _112866 h _60497 t) : term466 _112866 t h.
Proof. exact (proj1 (@lem4900806 _112866 h _60497 t h1)). Qed.
Lemma lem4900811 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) (h1 : term535 _112866 _60497 t) : term535 _112866 _60497 t.
Proof. exact (h1). Qed.
Lemma lem4900828 (n : nat) : (term5 n) = (term5 n).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem4900829 : term359 = term359.
Proof. exact (fun_ext (fun n : nat => @lem4900828 n)). Qed.
Lemma lem4900830 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4900832 : term152 = term152.
Proof. exact (MK_COMB (@lem4900830) (@lem4900829)). Qed.
Lemma lem4900833 (h1 : term152) : term152.
Proof. exact (EQ_MP (@lem4900832) (@lem4900679 h1)). Qed.
Lemma lem4900835 {_112866 : Type'} (l : list _112866) : (term357 _112866 l) = (term357 _112866 l).
Proof. exact (eq_refl (term357 _112866 l)). Qed.
Lemma lem4900836 {_112866 : Type'} : (term358 _112866) = (term358 _112866).
Proof. exact (fun_ext (fun l : list _112866 => @lem4900835 _112866 l)). Qed.
Lemma lem4900837 {_112866 : Type'} : (@all (list _112866)) = (@all (list _112866)).
Proof. exact (eq_refl (@all (list _112866))). Qed.
Lemma lem4900839 {_112866 : Type'} : (term333 _112866) = (term333 _112866).
Proof. exact (MK_COMB (@lem4900837 _112866) (@lem4900836 _112866)). Qed.
Lemma lem4900840 {_112866 : Type'} (h1 : term333 _112866) : term333 _112866.
Proof. exact (EQ_MP (@lem4900839 _112866) (@lem4900694 _112866 h1)). Qed.
Lemma lem4900905 (n : nat) : (term5 n) = (term5 n).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem4900906 : term359 = term359.
Proof. exact (fun_ext (fun n : nat => @lem4900905 n)). Qed.
Lemma lem4900907 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4900909 : term152 = term152.
Proof. exact (MK_COMB (@lem4900907) (@lem4900906)). Qed.
Lemma lem4900910 (h1 : term152) : term152.
Proof. exact (EQ_MP (@lem4900909) (@lem4900679 h1)). Qed.
Lemma lem4900912 {_112866 : Type'} (l : list _112866) : (term357 _112866 l) = (term357 _112866 l).
Proof. exact (eq_refl (term357 _112866 l)). Qed.
Lemma lem4900913 {_112866 : Type'} : (term358 _112866) = (term358 _112866).
Proof. exact (fun_ext (fun l : list _112866 => @lem4900912 _112866 l)). Qed.
Lemma lem4900914 {_112866 : Type'} : (@all (list _112866)) = (@all (list _112866)).
Proof. exact (eq_refl (@all (list _112866))). Qed.
Lemma lem4900916 {_112866 : Type'} : (term333 _112866) = (term333 _112866).
Proof. exact (MK_COMB (@lem4900914 _112866) (@lem4900913 _112866)). Qed.
Lemma lem4900917 {_112866 : Type'} (h1 : term333 _112866) : term333 _112866.
Proof. exact (EQ_MP (@lem4900916 _112866) (@lem4900694 _112866 h1)). Qed.
Lemma lem4901034 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) (h1 : term467 _112866 _60497 t) : term467 _112866 _60497 t.
Proof. exact (h1). Qed.
Lemma lem4901055 (n : nat) : (term5 n) = (term5 n).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem4901056 : term359 = term359.
Proof. exact (fun_ext (fun n : nat => @lem4901055 n)). Qed.
Lemma lem4901057 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4901059 : term152 = term152.
Proof. exact (MK_COMB (@lem4901057) (@lem4901056)). Qed.
Lemma lem4901060 (h1 : term152) : term152.
Proof. exact (EQ_MP (@lem4901059) (@lem4900679 h1)). Qed.
Lemma lem4901062 {_112866 : Type'} (l : list _112866) : (term357 _112866 l) = (term357 _112866 l).
Proof. exact (eq_refl (term357 _112866 l)). Qed.
Lemma lem4901063 {_112866 : Type'} : (term358 _112866) = (term358 _112866).
Proof. exact (fun_ext (fun l : list _112866 => @lem4901062 _112866 l)). Qed.
Lemma lem4901064 {_112866 : Type'} : (@all (list _112866)) = (@all (list _112866)).
Proof. exact (eq_refl (@all (list _112866))). Qed.
Lemma lem4901066 {_112866 : Type'} : (term333 _112866) = (term333 _112866).
Proof. exact (MK_COMB (@lem4901064 _112866) (@lem4901063 _112866)). Qed.
Lemma lem4901067 {_112866 : Type'} (h1 : term333 _112866) : term333 _112866.
Proof. exact (EQ_MP (@lem4901066 _112866) (@lem4900694 _112866 h1)). Qed.
Lemma lem4901126 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : @List.In _112866 h t) : @List.In _112866 h t.
Proof. exact (h1). Qed.
Lemma lem4901184 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term455 _112866 t h x) = (term455 _112866 t h x).
Proof. exact (eq_refl (term455 _112866 t h x)). Qed.
Lemma lem4901185 {_112866 : Type'} (t : list _112866) (h : _112866) : (term465 _112866 t h) = (term465 _112866 t h).
Proof. exact (fun_ext (fun x : _112866 => @lem4901184 _112866 t h x)). Qed.
Lemma lem4901186 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4901188 {_112866 : Type'} (t : list _112866) (h : _112866) : (term466 _112866 t h) = (term466 _112866 t h).
Proof. exact (MK_COMB (@lem4901186 _112866) (@lem4901185 _112866 t h)). Qed.
Lemma lem4901189 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term477 _112866 h _60497 t) : term466 _112866 t h.
Proof. exact (EQ_MP (@lem4901188 _112866 t h) (@lem4900809 _112866 h _60497 t h1)). Qed.
Lemma lem4901291 (_60500 : nat) (h1 : term152) : term536 _60500.
Proof. exact (@lem4900833 h1 _60500). Qed.
Lemma lem4901292 (_60500 : nat) : (term536 _60500) = (term5 _60500).
Proof. exact (eq_refl (term536 _60500)). Qed.
Lemma lem4901294 {_112866 : Type'} (_60501 : list _112866) (h1 : term333 _112866) : term537 _112866 _60501.
Proof. exact (@lem4900840 _112866 h1 _60501). Qed.
Lemma lem4901295 {_112866 : Type'} (_60501 : list _112866) : (term537 _112866 _60501) = (term357 _112866 _60501).
Proof. exact (eq_refl (term537 _112866 _60501)). Qed.
Lemma lem4901312 (_60507 : nat) (h1 : term152) : term536 _60507.
Proof. exact (@lem4900910 h1 _60507). Qed.
Lemma lem4901313 (_60507 : nat) : (term536 _60507) = (term5 _60507).
Proof. exact (eq_refl (term536 _60507)). Qed.
Lemma lem4901315 {_112866 : Type'} (_60508 : list _112866) (h1 : term333 _112866) : term537 _112866 _60508.
Proof. exact (@lem4900917 _112866 h1 _60508). Qed.
Lemma lem4901316 {_112866 : Type'} (_60508 : list _112866) : (term537 _112866 _60508) = (term357 _112866 _60508).
Proof. exact (eq_refl (term537 _112866 _60508)). Qed.
Lemma lem4901354 (_60521 : nat) (h1 : term152) : term536 _60521.
Proof. exact (@lem4901060 h1 _60521). Qed.
Lemma lem4901355 (_60521 : nat) : (term536 _60521) = (term5 _60521).
Proof. exact (eq_refl (term536 _60521)). Qed.
Lemma lem4901357 {_112866 : Type'} (_60522 : list _112866) (h1 : term333 _112866) : term537 _112866 _60522.
Proof. exact (@lem4901067 _112866 h1 _60522). Qed.
Lemma lem4901358 {_112866 : Type'} (_60522 : list _112866) : (term537 _112866 _60522) = (term357 _112866 _60522).
Proof. exact (eq_refl (term537 _112866 _60522)). Qed.
Lemma lem4901393 {_112866 : Type'} (_60534 : _112866) (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term477 _112866 h _60497 t) : term538 _112866 t h _60534.
Proof. exact (@lem4901189 _112866 h _60497 t h1 _60534). Qed.
Lemma lem4901394 {_112866 : Type'} (t : list _112866) (h : _112866) (_60534 : _112866) : (term538 _112866 t h _60534) = (term455 _112866 t h _60534).
Proof. exact (eq_refl (term538 _112866 t h _60534)). Qed.
Lemma lem4901503 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) (h1 : term467 _112866 _60497 t) : term467 _112866 _60497 t.
Proof. exact (h1). Qed.
Lemma lem4901513 (_60521 : nat) (h1 : term152) : term5 _60521.
Proof. exact (EQ_MP (@lem4901355 _60521) (@lem4901354 _60521 h1)). Qed.
Lemma lem4901539 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : @List.In _112866 h t) : @List.In _112866 h t.
Proof. exact (h1). Qed.
Lemma lem4901563 {_112866 : Type'} (_60534 : _112866) (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term477 _112866 h _60497 t) : term455 _112866 t h _60534.
Proof. exact (EQ_MP (@lem4901394 _112866 t h _60534) (@lem4901393 _112866 _60534 h _60497 t h1)). Qed.
Lemma lem4901603 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) (h1 : term535 _112866 _60497 t) : term467 _112866 _60497 t.
Proof. exact (proj2 (@lem4900811 _112866 _60497 t h1)). Qed.
Lemma lem4901658 (_60500 : nat) (h1 : term152) : term5 _60500.
Proof. exact (EQ_MP (@lem4901292 _60500) (@lem4901291 _60500 h1)). Qed.
Lemma lem4901811 (_60507 : nat) (h1 : term152) : term5 _60507.
Proof. exact (EQ_MP (@lem4901313 _60507) (@lem4901312 _60507 h1)). Qed.
Lemma lem4901948 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem4901949 (_60595 : nat) (_60597 : nat) (h1 : _60595 = _60597) : _60595 = _60597.
Proof. exact (h1). Qed.
Lemma lem4901950 (_60596 : nat) (_60598 : nat) (h1 : _60596 = _60598) : _60596 = _60598.
Proof. exact (h1). Qed.
Lemma lem4901951 (_60595 : nat) (_60597 : nat) (h1 : _60595 = _60597) : (Peano.le _60595) = (Peano.le _60597).
Proof. exact (MK_COMB (@lem4901948) (@lem4901949 _60595 _60597 h1)). Qed.
Lemma lem4901952 (_60595 : nat) (_60597 : nat) (_60596 : nat) (_60598 : nat) (h1 : _60595 = _60597) (h2 : _60596 = _60598) : (Peano.le _60595 _60596) = (Peano.le _60597 _60598).
Proof. exact (MK_COMB (@lem4901951 _60595 _60597 h1) (@lem4901950 _60596 _60598 h2)). Qed.
Lemma lem4901954 (b : Prop) (a : Prop) : term539 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem4901955 (_60597 : nat) (_60598 : nat) (_60595 : nat) (_60596 : nat) : term540 _60597 _60598 _60595 _60596.
Proof. exact (@lem4901954 (Peano.le _60597 _60598) (Peano.le _60595 _60596)). Qed.
Lemma lem4901956 (_60595 : nat) (_60597 : nat) (_60596 : nat) (_60598 : nat) (h1 : _60595 = _60597) (h2 : _60596 = _60598) : term541 _60597 _60598 _60595 _60596.
Proof. exact (@lem4901955 _60597 _60598 _60595 _60596 (@lem4901952 _60595 _60597 _60596 _60598 h1 h2)). Qed.
Lemma lem4901957 (_60598 : nat) (_60596 : nat) (_60595 : nat) (_60597 : nat) (h1 : _60595 = _60597) : term542 _60597 _60598 _60595 _60596.
Proof. exact (fun h0 : _60596 = _60598 => @lem4901956 _60595 _60597 _60596 _60598 h1 h0). Qed.
Lemma lem4901959 (a : Prop) (b : Prop) : (a -> b) = (term543 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4901960 (_60597 : nat) (_60598 : nat) (_60595 : nat) (_60596 : nat) : (term542 _60597 _60598 _60595 _60596) = (term544 _60597 _60598 _60595 _60596).
Proof. exact (@lem4901959 (_60596 = _60598) (term541 _60597 _60598 _60595 _60596)). Qed.
Lemma lem4901961 (_60598 : nat) (_60596 : nat) (_60595 : nat) (_60597 : nat) (h1 : _60595 = _60597) : term544 _60597 _60598 _60595 _60596.
Proof. exact (EQ_MP (@lem4901960 _60597 _60598 _60595 _60596) (@lem4901957 _60598 _60596 _60595 _60597 h1)). Qed.
Lemma lem4901962 (_60597 : nat) (_60598 : nat) (_60595 : nat) (_60596 : nat) : term545 _60597 _60598 _60595 _60596.
Proof. exact (fun h0 : _60595 = _60597 => @lem4901961 _60598 _60596 _60595 _60597 h0). Qed.
Lemma lem4901964 (a : Prop) (b : Prop) : (a -> b) = (term543 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4901965 (_60597 : nat) (_60598 : nat) (_60595 : nat) (_60596 : nat) : (term545 _60597 _60598 _60595 _60596) = (term546 _60597 _60598 _60595 _60596).
Proof. exact (@lem4901964 (_60595 = _60597) (term544 _60597 _60598 _60595 _60596)). Qed.
Lemma lem4901966 (_60597 : nat) (_60598 : nat) (_60595 : nat) (_60596 : nat) : term546 _60597 _60598 _60595 _60596.
Proof. exact (EQ_MP (@lem4901965 _60597 _60598 _60595 _60596) (@lem4901962 _60597 _60598 _60595 _60596)). Qed.
Lemma lem4902052 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term513 _112866 h x _60497 t) : (term171 _112866 t) = (term225 _112866 t).
Proof. exact (proj1 (@lem4900786 _112866 h x _60497 t h1)). Qed.
Lemma lem4902053 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term513 _112866 h x _60497 t) : term547 _112866 t.
Proof. exact (fun h0 : term548 _112866 t => @lem4902052 _112866 h x _60497 t h1). Qed.
Lemma lem4902055 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4902056 {_112866 : Type'} (t : list _112866) : (term547 _112866 t) = ((term171 _112866 t) = (term225 _112866 t)).
Proof. exact (@lem4902055 ((term171 _112866 t) = (term225 _112866 t))). Qed.
Lemma lem4902057 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term513 _112866 h x _60497 t) : (term171 _112866 t) = (term225 _112866 t).
Proof. exact (EQ_MP (@lem4902056 _112866 t) (@lem4902053 _112866 h x _60497 t h1)). Qed.
Lemma lem4902059 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem4902060 {_112866 : Type'} (t : list _112866) : (@List.length _112866 t) = (@List.length _112866 t).
Proof. exact (@lem4902059 (@List.length _112866 t)). Qed.
Lemma lem4902061 {_112866 : Type'} (t : list _112866) : term550 _112866 t.
Proof. exact (fun h0 : term551 _112866 t => @lem4902060 _112866 t). Qed.
Lemma lem4902063 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4902064 {_112866 : Type'} (t : list _112866) : (term550 _112866 t) = ((@List.length _112866 t) = (@List.length _112866 t)).
Proof. exact (@lem4902063 ((@List.length _112866 t) = (@List.length _112866 t))). Qed.
Lemma lem4902065 {_112866 : Type'} (t : list _112866) : (@List.length _112866 t) = (@List.length _112866 t).
Proof. exact (EQ_MP (@lem4902064 _112866 t) (@lem4902061 _112866 t)). Qed.
Lemma lem4902067 {_112866 : Type'} (_60501 : list _112866) (h1 : term333 _112866) : term357 _112866 _60501.
Proof. exact (EQ_MP (@lem4901295 _112866 _60501) (@lem4901294 _112866 _60501 h1)). Qed.
Lemma lem4902068 {_112866 : Type'} (_60501 : list _112866) (h1 : term333 _112866) : term357 _112866 _60501.
Proof. exact (@lem4902067 _112866 _60501 h1). Qed.
Lemma lem4902069 {_112866 : Type'} (t : list _112866) (h1 : term333 _112866) : term357 _112866 t.
Proof. exact (@lem4902068 _112866 t h1). Qed.
Lemma lem4902070 {_112866 : Type'} (t : list _112866) (h1 : term333 _112866) : term552 _112866 t.
Proof. exact (fun h0 : term553 _112866 t => @lem4902069 _112866 t h1). Qed.
Lemma lem4902072 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4902073 {_112866 : Type'} (t : list _112866) : (term552 _112866 t) = (term357 _112866 t).
Proof. exact (@lem4902072 (term357 _112866 t)). Qed.
Lemma lem4902074 {_112866 : Type'} (t : list _112866) (h1 : term333 _112866) : term357 _112866 t.
Proof. exact (EQ_MP (@lem4902073 _112866 t) (@lem4902070 _112866 t h1)). Qed.
Lemma lem4902092 (q : Prop) (p : Prop) (r : Prop) : (term554 p q r) = (term554 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4902093 (_60597 : nat) (_60598 : nat) (_60595 : nat) (_60596 : nat) : (term544 _60597 _60598 _60595 _60596) = (term555 _60597 _60598 _60595 _60596).
Proof. exact (@lem4902092 (Peano.le _60597 _60598) (term556 _60596 _60598) (term557 _60595 _60596)). Qed.
Lemma lem4902107 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4902108 (_60595 : nat) (_60596 : nat) (_60598 : nat) : (term558 _60598 _60595 _60596) = (term559 _60595 _60596 _60598).
Proof. exact (@lem4902107 (term557 _60595 _60596) (term556 _60596 _60598)). Qed.
Lemma lem4902116 (_60597 : nat) (_60598 : nat) : (term560 _60597 _60598) = (term560 _60597 _60598).
Proof. exact (eq_refl (term560 _60597 _60598)). Qed.
Lemma lem4902117 (_60597 : nat) (_60595 : nat) (_60596 : nat) (_60598 : nat) : (term555 _60597 _60598 _60595 _60596) = (term561 _60597 _60595 _60596 _60598).
Proof. exact (MK_COMB (@lem4902116 _60597 _60598) (@lem4902108 _60595 _60596 _60598)). Qed.
Lemma lem4902128 (_60597 : nat) (_60595 : nat) (_60596 : nat) (_60598 : nat) : (term544 _60597 _60598 _60595 _60596) = (term561 _60597 _60595 _60596 _60598).
Proof. exact (TRANS (@lem4902093 _60597 _60598 _60595 _60596) (@lem4902117 _60597 _60595 _60596 _60598)). Qed.
Lemma lem4902129 (_60595 : nat) (_60597 : nat) : (term562 _60595 _60597) = (term562 _60595 _60597).
Proof. exact (eq_refl (term562 _60595 _60597)). Qed.
Lemma lem4902130 (_60597 : nat) (_60595 : nat) (_60596 : nat) (_60598 : nat) : (term546 _60597 _60598 _60595 _60596) = (term563 _60597 _60595 _60596 _60598).
Proof. exact (MK_COMB (@lem4902129 _60595 _60597) (@lem4902128 _60597 _60595 _60596 _60598)). Qed.
Lemma lem4902134 (q : Prop) (p : Prop) (r : Prop) : (term554 p q r) = (term554 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4902135 (_60597 : nat) (_60595 : nat) (_60596 : nat) (_60598 : nat) : (term563 _60597 _60595 _60596 _60598) = (term564 _60597 _60595 _60596 _60598).
Proof. exact (@lem4902134 (Peano.le _60597 _60598) (term556 _60595 _60597) (term559 _60595 _60596 _60598)). Qed.
Lemma lem4902149 (q : Prop) (p : Prop) (r : Prop) : (term554 p q r) = (term554 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4902150 (_60595 : nat) (_60597 : nat) (_60596 : nat) (_60598 : nat) : (term565 _60597 _60595 _60596 _60598) = (term566 _60595 _60597 _60596 _60598).
Proof. exact (@lem4902149 (term557 _60595 _60596) (term556 _60595 _60597) (term556 _60596 _60598)). Qed.
Lemma lem4902170 (_60597 : nat) (_60598 : nat) : (term560 _60597 _60598) = (term560 _60597 _60598).
Proof. exact (eq_refl (term560 _60597 _60598)). Qed.
Lemma lem4902171 (_60595 : nat) (_60597 : nat) (_60596 : nat) (_60598 : nat) : (term564 _60597 _60595 _60596 _60598) = (term567 _60595 _60597 _60596 _60598).
Proof. exact (MK_COMB (@lem4902170 _60597 _60598) (@lem4902150 _60595 _60597 _60596 _60598)). Qed.
Lemma lem4902182 (_60595 : nat) (_60597 : nat) (_60596 : nat) (_60598 : nat) : (term563 _60597 _60595 _60596 _60598) = (term567 _60595 _60597 _60596 _60598).
Proof. exact (TRANS (@lem4902135 _60597 _60595 _60596 _60598) (@lem4902171 _60595 _60597 _60596 _60598)). Qed.
Lemma lem4902183 (_60595 : nat) (_60597 : nat) (_60596 : nat) (_60598 : nat) : (term546 _60597 _60598 _60595 _60596) = (term567 _60595 _60597 _60596 _60598).
Proof. exact (TRANS (@lem4902130 _60597 _60595 _60596 _60598) (@lem4902182 _60595 _60597 _60596 _60598)). Qed.
Lemma lem4902184 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4902185 (_60595 : nat) (_60597 : nat) (_60596 : nat) (_60598 : nat) : (term568 _60597 _60598 _60595 _60596) = (term569 _60595 _60597 _60596 _60598).
Proof. exact (MK_COMB (@lem4902184) (@lem4902183 _60595 _60597 _60596 _60598)). Qed.
Lemma lem4902211 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4902212 (_60595 : nat) (_60596 : nat) (_60598 : nat) : (term558 _60598 _60595 _60596) = (term559 _60595 _60596 _60598).
Proof. exact (@lem4902211 (term557 _60595 _60596) (term556 _60596 _60598)). Qed.
Lemma lem4902220 (_60595 : nat) (_60597 : nat) : (term562 _60595 _60597) = (term562 _60595 _60597).
Proof. exact (eq_refl (term562 _60595 _60597)). Qed.
Lemma lem4902221 (_60597 : nat) (_60595 : nat) (_60596 : nat) (_60598 : nat) : (term570 _60597 _60598 _60595 _60596) = (term565 _60597 _60595 _60596 _60598).
Proof. exact (MK_COMB (@lem4902220 _60595 _60597) (@lem4902212 _60595 _60596 _60598)). Qed.
Lemma lem4902225 (q : Prop) (p : Prop) (r : Prop) : (term554 p q r) = (term554 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4902226 (_60595 : nat) (_60597 : nat) (_60596 : nat) (_60598 : nat) : (term565 _60597 _60595 _60596 _60598) = (term566 _60595 _60597 _60596 _60598).
Proof. exact (@lem4902225 (term557 _60595 _60596) (term556 _60595 _60597) (term556 _60596 _60598)). Qed.
Lemma lem4902246 (_60595 : nat) (_60597 : nat) (_60596 : nat) (_60598 : nat) : (term570 _60597 _60598 _60595 _60596) = (term566 _60595 _60597 _60596 _60598).
Proof. exact (TRANS (@lem4902221 _60597 _60595 _60596 _60598) (@lem4902226 _60595 _60597 _60596 _60598)). Qed.
Lemma lem4902247 (_60597 : nat) (_60598 : nat) : (term560 _60597 _60598) = (term560 _60597 _60598).
Proof. exact (eq_refl (term560 _60597 _60598)). Qed.
Lemma lem4902248 (_60595 : nat) (_60597 : nat) (_60596 : nat) (_60598 : nat) : (term571 _60597 _60598 _60595 _60596) = (term567 _60595 _60597 _60596 _60598).
Proof. exact (MK_COMB (@lem4902247 _60597 _60598) (@lem4902246 _60595 _60597 _60596 _60598)). Qed.
Lemma lem4902259 (_60595 : nat) (_60597 : nat) (_60596 : nat) (_60598 : nat) : ((term546 _60597 _60598 _60595 _60596) = (term571 _60597 _60598 _60595 _60596)) = ((term567 _60595 _60597 _60596 _60598) = (term567 _60595 _60597 _60596 _60598)).
Proof. exact (MK_COMB (@lem4902185 _60595 _60597 _60596 _60598) (@lem4902248 _60595 _60597 _60596 _60598)). Qed.
Lemma lem4902261 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4902262 (x : Prop) : (x = x) = True.
Proof. exact (@lem4902261 Prop x). Qed.
Lemma lem4902263 (_60595 : nat) (_60597 : nat) (_60596 : nat) (_60598 : nat) : ((term567 _60595 _60597 _60596 _60598) = (term567 _60595 _60597 _60596 _60598)) = True.
Proof. exact (@lem4902262 (term567 _60595 _60597 _60596 _60598)). Qed.
Lemma lem4902264 (_60597 : nat) (_60598 : nat) (_60595 : nat) (_60596 : nat) : ((term546 _60597 _60598 _60595 _60596) = (term571 _60597 _60598 _60595 _60596)) = True.
Proof. exact (TRANS (@lem4902259 _60595 _60597 _60596 _60598) (@lem4902263 _60595 _60597 _60596 _60598)). Qed.
Lemma lem4902265 (_60597 : nat) (_60598 : nat) (_60595 : nat) (_60596 : nat) : True = ((term546 _60597 _60598 _60595 _60596) = (term571 _60597 _60598 _60595 _60596)).
Proof. exact (SYM (@lem4902264 _60597 _60598 _60595 _60596)). Qed.
Lemma lem4902266 (_60597 : nat) (_60598 : nat) (_60595 : nat) (_60596 : nat) : (term546 _60597 _60598 _60595 _60596) = (term571 _60597 _60598 _60595 _60596).
Proof. exact (EQ_MP (@lem4902265 _60597 _60598 _60595 _60596) (@lem0)). Qed.
Lemma lem4902267 (_60597 : nat) (_60598 : nat) (_60595 : nat) (_60596 : nat) : term571 _60597 _60598 _60595 _60596.
Proof. exact (EQ_MP (@lem4902266 _60597 _60598 _60595 _60596) (@lem4901966 _60597 _60598 _60595 _60596)). Qed.
Lemma lem4902269 (b : Prop) (a : Prop) : (a \/ b) = (term572 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4902270 (_60595 : nat) (_60596 : nat) (_60597 : nat) (_60598 : nat) : (term571 _60597 _60598 _60595 _60596) = (term573 _60595 _60596 _60597 _60598).
Proof. exact (@lem4902269 (term570 _60597 _60598 _60595 _60596) (Peano.le _60597 _60598)). Qed.
Lemma lem4902272 (a : Prop) (b : Prop) : (term574 a b) = (term575 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4902273 (_60597 : nat) (_60598 : nat) (_60595 : nat) (_60596 : nat) : (term576 _60597 _60598 _60595 _60596) = (term577 _60597 _60598 _60595 _60596).
Proof. exact (@lem4902272 (term556 _60595 _60597) (term558 _60598 _60595 _60596)). Qed.
Lemma lem4902275 (a : Prop) : (term55 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4902276 (_60595 : nat) (_60597 : nat) : (term578 _60595 _60597) = (_60595 = _60597).
Proof. exact (@lem4902275 (_60595 = _60597)). Qed.
Lemma lem4902277 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4902278 (_60595 : nat) (_60597 : nat) : (term579 _60595 _60597) = (term580 _60595 _60597).
Proof. exact (MK_COMB (@lem4902277) (@lem4902276 _60595 _60597)). Qed.
Lemma lem4902280 (a : Prop) (b : Prop) : (term574 a b) = (term575 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4902281 (_60598 : nat) (_60595 : nat) (_60596 : nat) : (term581 _60598 _60595 _60596) = (term582 _60598 _60595 _60596).
Proof. exact (@lem4902280 (term556 _60596 _60598) (term557 _60595 _60596)). Qed.
Lemma lem4902283 (a : Prop) : (term55 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4902284 (_60596 : nat) (_60598 : nat) : (term578 _60596 _60598) = (_60596 = _60598).
Proof. exact (@lem4902283 (_60596 = _60598)). Qed.
Lemma lem4902285 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4902286 (_60596 : nat) (_60598 : nat) : (term579 _60596 _60598) = (term580 _60596 _60598).
Proof. exact (MK_COMB (@lem4902285) (@lem4902284 _60596 _60598)). Qed.
Lemma lem4902288 (a : Prop) : (term55 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4902289 (_60595 : nat) (_60596 : nat) : (term583 _60595 _60596) = (Peano.le _60595 _60596).
Proof. exact (@lem4902288 (Peano.le _60595 _60596)). Qed.
Lemma lem4902290 (_60598 : nat) (_60595 : nat) (_60596 : nat) : (term582 _60598 _60595 _60596) = (term584 _60598 _60595 _60596).
Proof. exact (MK_COMB (@lem4902286 _60596 _60598) (@lem4902289 _60595 _60596)). Qed.
Lemma lem4902291 (_60598 : nat) (_60595 : nat) (_60596 : nat) : (term581 _60598 _60595 _60596) = (term584 _60598 _60595 _60596).
Proof. exact (TRANS (@lem4902281 _60598 _60595 _60596) (@lem4902290 _60598 _60595 _60596)). Qed.
Lemma lem4902292 (_60597 : nat) (_60598 : nat) (_60595 : nat) (_60596 : nat) : (term577 _60597 _60598 _60595 _60596) = (term585 _60597 _60598 _60595 _60596).
Proof. exact (MK_COMB (@lem4902278 _60595 _60597) (@lem4902291 _60598 _60595 _60596)). Qed.
Lemma lem4902293 (_60597 : nat) (_60598 : nat) (_60595 : nat) (_60596 : nat) : (term576 _60597 _60598 _60595 _60596) = (term585 _60597 _60598 _60595 _60596).
Proof. exact (TRANS (@lem4902273 _60597 _60598 _60595 _60596) (@lem4902292 _60597 _60598 _60595 _60596)). Qed.
Lemma lem4902294 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4902295 (_60597 : nat) (_60598 : nat) (_60595 : nat) (_60596 : nat) : (term586 _60597 _60598 _60595 _60596) = (term587 _60597 _60598 _60595 _60596).
Proof. exact (MK_COMB (@lem4902294) (@lem4902293 _60597 _60598 _60595 _60596)). Qed.
Lemma lem4902296 (_60597 : nat) (_60598 : nat) : (Peano.le _60597 _60598) = (Peano.le _60597 _60598).
Proof. exact (eq_refl (Peano.le _60597 _60598)). Qed.
Lemma lem4902297 (_60595 : nat) (_60596 : nat) (_60597 : nat) (_60598 : nat) : (term573 _60595 _60596 _60597 _60598) = (term588 _60595 _60596 _60597 _60598).
Proof. exact (MK_COMB (@lem4902295 _60597 _60598 _60595 _60596) (@lem4902296 _60597 _60598)). Qed.
Lemma lem4902298 (_60595 : nat) (_60596 : nat) (_60597 : nat) (_60598 : nat) : (term571 _60597 _60598 _60595 _60596) = (term588 _60595 _60596 _60597 _60598).
Proof. exact (TRANS (@lem4902270 _60595 _60596 _60597 _60598) (@lem4902297 _60595 _60596 _60597 _60598)). Qed.
Lemma lem4902300 {_112866 : Type'} (t : list _112866) (h1 : term333 _112866) : term589 _112866 t.
Proof. exact (conj (@lem4902065 _112866 t) (@lem4902074 _112866 t h1)). Qed.
Lemma lem4902301 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term513 _112866 h x _60497 t) : term590 _112866 t.
Proof. exact (conj (@lem4902057 _112866 h x _60497 t h2) (@lem4902300 _112866 t h1)). Qed.
Lemma lem4902303 (_60595 : nat) (_60596 : nat) (_60597 : nat) (_60598 : nat) : term588 _60595 _60596 _60597 _60598.
Proof. exact (EQ_MP (@lem4902298 _60595 _60596 _60597 _60598) (@lem4902267 _60597 _60598 _60595 _60596)). Qed.
Lemma lem4902304 {_112866 : Type'} (t : list _112866) : term591 _112866 t.
Proof. exact (@lem4902303 (term171 _112866 t) (@List.length _112866 t) (term225 _112866 t) (@List.length _112866 t)). Qed.
Lemma lem4902307 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term513 _112866 h x _60497 t) : term592 _112866 t.
Proof. exact (@lem4902304 _112866 t (@lem4902301 _112866 h x _60497 t h1 h2)). Qed.
Lemma lem4902308 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term513 _112866 h x _60497 t) : term593 _112866 t.
Proof. exact (fun h0 : term594 _112866 t => @lem4902307 _112866 h x _60497 t h1 h2). Qed.
Lemma lem4902310 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4902311 {_112866 : Type'} (t : list _112866) : (term593 _112866 t) = (term592 _112866 t).
Proof. exact (@lem4902310 (term592 _112866 t)). Qed.
Lemma lem4902312 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term513 _112866 h x _60497 t) : term592 _112866 t.
Proof. exact (EQ_MP (@lem4902311 _112866 t) (@lem4902308 _112866 h x _60497 t h1 h2)). Qed.
Lemma lem4902315 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4902317 (_60500 : nat) : (term5 _60500) = (term595 _60500).
Proof. exact (@lem4902315 (term3 _60500)). Qed.
Lemma lem4902320 (_60500 : nat) (h1 : term152) : term595 _60500.
Proof. exact (EQ_MP (@lem4902317 _60500) (@lem4901658 _60500 h1)). Qed.
Lemma lem4902321 {_112866 : Type'} (t : list _112866) (h1 : term152) : term596 _112866 t.
Proof. exact (@lem4902320 (@List.length _112866 t) h1). Qed.
Lemma lem4902324 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term513 _112866 h x _60497 t) : False.
Proof. exact (@lem4902321 _112866 t h2 (@lem4902312 _112866 h x _60497 t h1 h3)). Qed.
Lemma lem4902325 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term513 _112866 h x _60497 t) : term597.
Proof. exact (fun h0 : ~ False => @lem4902324 _112866 h x _60497 t h1 h2 h3). Qed.
Lemma lem4902327 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4902328 : term597 = False.
Proof. exact (@lem4902327 False). Qed.
Lemma lem4902368 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem4902369 (_60625 : nat) (_60627 : nat) (h1 : _60625 = _60627) : _60625 = _60627.
Proof. exact (h1). Qed.
Lemma lem4902370 (_60626 : nat) (_60628 : nat) (h1 : _60626 = _60628) : _60626 = _60628.
Proof. exact (h1). Qed.
Lemma lem4902371 (_60625 : nat) (_60627 : nat) (h1 : _60625 = _60627) : (Peano.le _60625) = (Peano.le _60627).
Proof. exact (MK_COMB (@lem4902368) (@lem4902369 _60625 _60627 h1)). Qed.
Lemma lem4902372 (_60625 : nat) (_60627 : nat) (_60626 : nat) (_60628 : nat) (h1 : _60625 = _60627) (h2 : _60626 = _60628) : (Peano.le _60625 _60626) = (Peano.le _60627 _60628).
Proof. exact (MK_COMB (@lem4902371 _60625 _60627 h1) (@lem4902370 _60626 _60628 h2)). Qed.
Lemma lem4902374 (b : Prop) (a : Prop) : term539 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem4902375 (_60627 : nat) (_60628 : nat) (_60625 : nat) (_60626 : nat) : term540 _60627 _60628 _60625 _60626.
Proof. exact (@lem4902374 (Peano.le _60627 _60628) (Peano.le _60625 _60626)). Qed.
Lemma lem4902376 (_60625 : nat) (_60627 : nat) (_60626 : nat) (_60628 : nat) (h1 : _60625 = _60627) (h2 : _60626 = _60628) : term541 _60627 _60628 _60625 _60626.
Proof. exact (@lem4902375 _60627 _60628 _60625 _60626 (@lem4902372 _60625 _60627 _60626 _60628 h1 h2)). Qed.
Lemma lem4902377 (_60628 : nat) (_60626 : nat) (_60625 : nat) (_60627 : nat) (h1 : _60625 = _60627) : term542 _60627 _60628 _60625 _60626.
Proof. exact (fun h0 : _60626 = _60628 => @lem4902376 _60625 _60627 _60626 _60628 h1 h0). Qed.
Lemma lem4902379 (a : Prop) (b : Prop) : (a -> b) = (term543 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4902380 (_60627 : nat) (_60628 : nat) (_60625 : nat) (_60626 : nat) : (term542 _60627 _60628 _60625 _60626) = (term544 _60627 _60628 _60625 _60626).
Proof. exact (@lem4902379 (_60626 = _60628) (term541 _60627 _60628 _60625 _60626)). Qed.
Lemma lem4902381 (_60628 : nat) (_60626 : nat) (_60625 : nat) (_60627 : nat) (h1 : _60625 = _60627) : term544 _60627 _60628 _60625 _60626.
Proof. exact (EQ_MP (@lem4902380 _60627 _60628 _60625 _60626) (@lem4902377 _60628 _60626 _60625 _60627 h1)). Qed.
Lemma lem4902382 (_60627 : nat) (_60628 : nat) (_60625 : nat) (_60626 : nat) : term545 _60627 _60628 _60625 _60626.
Proof. exact (fun h0 : _60625 = _60627 => @lem4902381 _60628 _60626 _60625 _60627 h0). Qed.
Lemma lem4902384 (a : Prop) (b : Prop) : (a -> b) = (term543 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4902385 (_60627 : nat) (_60628 : nat) (_60625 : nat) (_60626 : nat) : (term545 _60627 _60628 _60625 _60626) = (term546 _60627 _60628 _60625 _60626).
Proof. exact (@lem4902384 (_60625 = _60627) (term544 _60627 _60628 _60625 _60626)). Qed.
Lemma lem4902386 (_60627 : nat) (_60628 : nat) (_60625 : nat) (_60626 : nat) : term546 _60627 _60628 _60625 _60626.
Proof. exact (EQ_MP (@lem4902385 _60627 _60628 _60625 _60626) (@lem4902382 _60627 _60628 _60625 _60626)). Qed.
Lemma lem4902472 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term513 _112866 h x _60497 t) : (term171 _112866 t) = (term225 _112866 t).
Proof. exact (proj1 (@lem4900786 _112866 h x _60497 t h1)). Qed.
Lemma lem4902473 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term513 _112866 h x _60497 t) : term547 _112866 t.
Proof. exact (fun h0 : term548 _112866 t => @lem4902472 _112866 h x _60497 t h1). Qed.
Lemma lem4902475 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4902476 {_112866 : Type'} (t : list _112866) : (term547 _112866 t) = ((term171 _112866 t) = (term225 _112866 t)).
Proof. exact (@lem4902475 ((term171 _112866 t) = (term225 _112866 t))). Qed.
Lemma lem4902477 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term513 _112866 h x _60497 t) : (term171 _112866 t) = (term225 _112866 t).
Proof. exact (EQ_MP (@lem4902476 _112866 t) (@lem4902473 _112866 h x _60497 t h1)). Qed.
Lemma lem4902479 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem4902480 {_112866 : Type'} (t : list _112866) : (@List.length _112866 t) = (@List.length _112866 t).
Proof. exact (@lem4902479 (@List.length _112866 t)). Qed.
Lemma lem4902481 {_112866 : Type'} (t : list _112866) : term550 _112866 t.
Proof. exact (fun h0 : term551 _112866 t => @lem4902480 _112866 t). Qed.
Lemma lem4902483 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4902484 {_112866 : Type'} (t : list _112866) : (term550 _112866 t) = ((@List.length _112866 t) = (@List.length _112866 t)).
Proof. exact (@lem4902483 ((@List.length _112866 t) = (@List.length _112866 t))). Qed.
Lemma lem4902485 {_112866 : Type'} (t : list _112866) : (@List.length _112866 t) = (@List.length _112866 t).
Proof. exact (EQ_MP (@lem4902484 _112866 t) (@lem4902481 _112866 t)). Qed.
Lemma lem4902487 {_112866 : Type'} (_60508 : list _112866) (h1 : term333 _112866) : term357 _112866 _60508.
Proof. exact (EQ_MP (@lem4901316 _112866 _60508) (@lem4901315 _112866 _60508 h1)). Qed.
Lemma lem4902488 {_112866 : Type'} (_60508 : list _112866) (h1 : term333 _112866) : term357 _112866 _60508.
Proof. exact (@lem4902487 _112866 _60508 h1). Qed.
Lemma lem4902489 {_112866 : Type'} (t : list _112866) (h1 : term333 _112866) : term357 _112866 t.
Proof. exact (@lem4902488 _112866 t h1). Qed.
Lemma lem4902490 {_112866 : Type'} (t : list _112866) (h1 : term333 _112866) : term552 _112866 t.
Proof. exact (fun h0 : term553 _112866 t => @lem4902489 _112866 t h1). Qed.
Lemma lem4902492 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4902493 {_112866 : Type'} (t : list _112866) : (term552 _112866 t) = (term357 _112866 t).
Proof. exact (@lem4902492 (term357 _112866 t)). Qed.
Lemma lem4902494 {_112866 : Type'} (t : list _112866) (h1 : term333 _112866) : term357 _112866 t.
Proof. exact (EQ_MP (@lem4902493 _112866 t) (@lem4902490 _112866 t h1)). Qed.
Lemma lem4902512 (q : Prop) (p : Prop) (r : Prop) : (term554 p q r) = (term554 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4902513 (_60627 : nat) (_60628 : nat) (_60625 : nat) (_60626 : nat) : (term544 _60627 _60628 _60625 _60626) = (term555 _60627 _60628 _60625 _60626).
Proof. exact (@lem4902512 (Peano.le _60627 _60628) (term556 _60626 _60628) (term557 _60625 _60626)). Qed.
Lemma lem4902527 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4902528 (_60625 : nat) (_60626 : nat) (_60628 : nat) : (term558 _60628 _60625 _60626) = (term559 _60625 _60626 _60628).
Proof. exact (@lem4902527 (term557 _60625 _60626) (term556 _60626 _60628)). Qed.
Lemma lem4902536 (_60627 : nat) (_60628 : nat) : (term560 _60627 _60628) = (term560 _60627 _60628).
Proof. exact (eq_refl (term560 _60627 _60628)). Qed.
Lemma lem4902537 (_60627 : nat) (_60625 : nat) (_60626 : nat) (_60628 : nat) : (term555 _60627 _60628 _60625 _60626) = (term561 _60627 _60625 _60626 _60628).
Proof. exact (MK_COMB (@lem4902536 _60627 _60628) (@lem4902528 _60625 _60626 _60628)). Qed.
Lemma lem4902548 (_60627 : nat) (_60625 : nat) (_60626 : nat) (_60628 : nat) : (term544 _60627 _60628 _60625 _60626) = (term561 _60627 _60625 _60626 _60628).
Proof. exact (TRANS (@lem4902513 _60627 _60628 _60625 _60626) (@lem4902537 _60627 _60625 _60626 _60628)). Qed.
Lemma lem4902549 (_60625 : nat) (_60627 : nat) : (term562 _60625 _60627) = (term562 _60625 _60627).
Proof. exact (eq_refl (term562 _60625 _60627)). Qed.
Lemma lem4902550 (_60627 : nat) (_60625 : nat) (_60626 : nat) (_60628 : nat) : (term546 _60627 _60628 _60625 _60626) = (term563 _60627 _60625 _60626 _60628).
Proof. exact (MK_COMB (@lem4902549 _60625 _60627) (@lem4902548 _60627 _60625 _60626 _60628)). Qed.
Lemma lem4902554 (q : Prop) (p : Prop) (r : Prop) : (term554 p q r) = (term554 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4902555 (_60627 : nat) (_60625 : nat) (_60626 : nat) (_60628 : nat) : (term563 _60627 _60625 _60626 _60628) = (term564 _60627 _60625 _60626 _60628).
Proof. exact (@lem4902554 (Peano.le _60627 _60628) (term556 _60625 _60627) (term559 _60625 _60626 _60628)). Qed.
Lemma lem4902569 (q : Prop) (p : Prop) (r : Prop) : (term554 p q r) = (term554 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4902570 (_60625 : nat) (_60627 : nat) (_60626 : nat) (_60628 : nat) : (term565 _60627 _60625 _60626 _60628) = (term566 _60625 _60627 _60626 _60628).
Proof. exact (@lem4902569 (term557 _60625 _60626) (term556 _60625 _60627) (term556 _60626 _60628)). Qed.
Lemma lem4902590 (_60627 : nat) (_60628 : nat) : (term560 _60627 _60628) = (term560 _60627 _60628).
Proof. exact (eq_refl (term560 _60627 _60628)). Qed.
Lemma lem4902591 (_60625 : nat) (_60627 : nat) (_60626 : nat) (_60628 : nat) : (term564 _60627 _60625 _60626 _60628) = (term567 _60625 _60627 _60626 _60628).
Proof. exact (MK_COMB (@lem4902590 _60627 _60628) (@lem4902570 _60625 _60627 _60626 _60628)). Qed.
Lemma lem4902602 (_60625 : nat) (_60627 : nat) (_60626 : nat) (_60628 : nat) : (term563 _60627 _60625 _60626 _60628) = (term567 _60625 _60627 _60626 _60628).
Proof. exact (TRANS (@lem4902555 _60627 _60625 _60626 _60628) (@lem4902591 _60625 _60627 _60626 _60628)). Qed.
Lemma lem4902603 (_60625 : nat) (_60627 : nat) (_60626 : nat) (_60628 : nat) : (term546 _60627 _60628 _60625 _60626) = (term567 _60625 _60627 _60626 _60628).
Proof. exact (TRANS (@lem4902550 _60627 _60625 _60626 _60628) (@lem4902602 _60625 _60627 _60626 _60628)). Qed.
Lemma lem4902604 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4902605 (_60625 : nat) (_60627 : nat) (_60626 : nat) (_60628 : nat) : (term568 _60627 _60628 _60625 _60626) = (term569 _60625 _60627 _60626 _60628).
Proof. exact (MK_COMB (@lem4902604) (@lem4902603 _60625 _60627 _60626 _60628)). Qed.
Lemma lem4902631 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4902632 (_60625 : nat) (_60626 : nat) (_60628 : nat) : (term558 _60628 _60625 _60626) = (term559 _60625 _60626 _60628).
Proof. exact (@lem4902631 (term557 _60625 _60626) (term556 _60626 _60628)). Qed.
Lemma lem4902640 (_60625 : nat) (_60627 : nat) : (term562 _60625 _60627) = (term562 _60625 _60627).
Proof. exact (eq_refl (term562 _60625 _60627)). Qed.
Lemma lem4902641 (_60627 : nat) (_60625 : nat) (_60626 : nat) (_60628 : nat) : (term570 _60627 _60628 _60625 _60626) = (term565 _60627 _60625 _60626 _60628).
Proof. exact (MK_COMB (@lem4902640 _60625 _60627) (@lem4902632 _60625 _60626 _60628)). Qed.
Lemma lem4902645 (q : Prop) (p : Prop) (r : Prop) : (term554 p q r) = (term554 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4902646 (_60625 : nat) (_60627 : nat) (_60626 : nat) (_60628 : nat) : (term565 _60627 _60625 _60626 _60628) = (term566 _60625 _60627 _60626 _60628).
Proof. exact (@lem4902645 (term557 _60625 _60626) (term556 _60625 _60627) (term556 _60626 _60628)). Qed.
Lemma lem4902666 (_60625 : nat) (_60627 : nat) (_60626 : nat) (_60628 : nat) : (term570 _60627 _60628 _60625 _60626) = (term566 _60625 _60627 _60626 _60628).
Proof. exact (TRANS (@lem4902641 _60627 _60625 _60626 _60628) (@lem4902646 _60625 _60627 _60626 _60628)). Qed.
Lemma lem4902667 (_60627 : nat) (_60628 : nat) : (term560 _60627 _60628) = (term560 _60627 _60628).
Proof. exact (eq_refl (term560 _60627 _60628)). Qed.
Lemma lem4902668 (_60625 : nat) (_60627 : nat) (_60626 : nat) (_60628 : nat) : (term571 _60627 _60628 _60625 _60626) = (term567 _60625 _60627 _60626 _60628).
Proof. exact (MK_COMB (@lem4902667 _60627 _60628) (@lem4902666 _60625 _60627 _60626 _60628)). Qed.
Lemma lem4902679 (_60625 : nat) (_60627 : nat) (_60626 : nat) (_60628 : nat) : ((term546 _60627 _60628 _60625 _60626) = (term571 _60627 _60628 _60625 _60626)) = ((term567 _60625 _60627 _60626 _60628) = (term567 _60625 _60627 _60626 _60628)).
Proof. exact (MK_COMB (@lem4902605 _60625 _60627 _60626 _60628) (@lem4902668 _60625 _60627 _60626 _60628)). Qed.
Lemma lem4902681 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4902682 (x : Prop) : (x = x) = True.
Proof. exact (@lem4902681 Prop x). Qed.
Lemma lem4902683 (_60625 : nat) (_60627 : nat) (_60626 : nat) (_60628 : nat) : ((term567 _60625 _60627 _60626 _60628) = (term567 _60625 _60627 _60626 _60628)) = True.
Proof. exact (@lem4902682 (term567 _60625 _60627 _60626 _60628)). Qed.
Lemma lem4902684 (_60627 : nat) (_60628 : nat) (_60625 : nat) (_60626 : nat) : ((term546 _60627 _60628 _60625 _60626) = (term571 _60627 _60628 _60625 _60626)) = True.
Proof. exact (TRANS (@lem4902679 _60625 _60627 _60626 _60628) (@lem4902683 _60625 _60627 _60626 _60628)). Qed.
Lemma lem4902685 (_60627 : nat) (_60628 : nat) (_60625 : nat) (_60626 : nat) : True = ((term546 _60627 _60628 _60625 _60626) = (term571 _60627 _60628 _60625 _60626)).
Proof. exact (SYM (@lem4902684 _60627 _60628 _60625 _60626)). Qed.
Lemma lem4902686 (_60627 : nat) (_60628 : nat) (_60625 : nat) (_60626 : nat) : (term546 _60627 _60628 _60625 _60626) = (term571 _60627 _60628 _60625 _60626).
Proof. exact (EQ_MP (@lem4902685 _60627 _60628 _60625 _60626) (@lem0)). Qed.
Lemma lem4902687 (_60627 : nat) (_60628 : nat) (_60625 : nat) (_60626 : nat) : term571 _60627 _60628 _60625 _60626.
Proof. exact (EQ_MP (@lem4902686 _60627 _60628 _60625 _60626) (@lem4902386 _60627 _60628 _60625 _60626)). Qed.
Lemma lem4902689 (b : Prop) (a : Prop) : (a \/ b) = (term572 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4902690 (_60625 : nat) (_60626 : nat) (_60627 : nat) (_60628 : nat) : (term571 _60627 _60628 _60625 _60626) = (term573 _60625 _60626 _60627 _60628).
Proof. exact (@lem4902689 (term570 _60627 _60628 _60625 _60626) (Peano.le _60627 _60628)). Qed.
Lemma lem4902692 (a : Prop) (b : Prop) : (term574 a b) = (term575 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4902693 (_60627 : nat) (_60628 : nat) (_60625 : nat) (_60626 : nat) : (term576 _60627 _60628 _60625 _60626) = (term577 _60627 _60628 _60625 _60626).
Proof. exact (@lem4902692 (term556 _60625 _60627) (term558 _60628 _60625 _60626)). Qed.
Lemma lem4902695 (a : Prop) : (term55 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4902696 (_60625 : nat) (_60627 : nat) : (term578 _60625 _60627) = (_60625 = _60627).
Proof. exact (@lem4902695 (_60625 = _60627)). Qed.
Lemma lem4902697 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4902698 (_60625 : nat) (_60627 : nat) : (term579 _60625 _60627) = (term580 _60625 _60627).
Proof. exact (MK_COMB (@lem4902697) (@lem4902696 _60625 _60627)). Qed.
Lemma lem4902700 (a : Prop) (b : Prop) : (term574 a b) = (term575 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4902701 (_60628 : nat) (_60625 : nat) (_60626 : nat) : (term581 _60628 _60625 _60626) = (term582 _60628 _60625 _60626).
Proof. exact (@lem4902700 (term556 _60626 _60628) (term557 _60625 _60626)). Qed.
Lemma lem4902703 (a : Prop) : (term55 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4902704 (_60626 : nat) (_60628 : nat) : (term578 _60626 _60628) = (_60626 = _60628).
Proof. exact (@lem4902703 (_60626 = _60628)). Qed.
Lemma lem4902705 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4902706 (_60626 : nat) (_60628 : nat) : (term579 _60626 _60628) = (term580 _60626 _60628).
Proof. exact (MK_COMB (@lem4902705) (@lem4902704 _60626 _60628)). Qed.
Lemma lem4902708 (a : Prop) : (term55 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4902709 (_60625 : nat) (_60626 : nat) : (term583 _60625 _60626) = (Peano.le _60625 _60626).
Proof. exact (@lem4902708 (Peano.le _60625 _60626)). Qed.
Lemma lem4902710 (_60628 : nat) (_60625 : nat) (_60626 : nat) : (term582 _60628 _60625 _60626) = (term584 _60628 _60625 _60626).
Proof. exact (MK_COMB (@lem4902706 _60626 _60628) (@lem4902709 _60625 _60626)). Qed.
Lemma lem4902711 (_60628 : nat) (_60625 : nat) (_60626 : nat) : (term581 _60628 _60625 _60626) = (term584 _60628 _60625 _60626).
Proof. exact (TRANS (@lem4902701 _60628 _60625 _60626) (@lem4902710 _60628 _60625 _60626)). Qed.
Lemma lem4902712 (_60627 : nat) (_60628 : nat) (_60625 : nat) (_60626 : nat) : (term577 _60627 _60628 _60625 _60626) = (term585 _60627 _60628 _60625 _60626).
Proof. exact (MK_COMB (@lem4902698 _60625 _60627) (@lem4902711 _60628 _60625 _60626)). Qed.
Lemma lem4902713 (_60627 : nat) (_60628 : nat) (_60625 : nat) (_60626 : nat) : (term576 _60627 _60628 _60625 _60626) = (term585 _60627 _60628 _60625 _60626).
Proof. exact (TRANS (@lem4902693 _60627 _60628 _60625 _60626) (@lem4902712 _60627 _60628 _60625 _60626)). Qed.
Lemma lem4902714 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4902715 (_60627 : nat) (_60628 : nat) (_60625 : nat) (_60626 : nat) : (term586 _60627 _60628 _60625 _60626) = (term587 _60627 _60628 _60625 _60626).
Proof. exact (MK_COMB (@lem4902714) (@lem4902713 _60627 _60628 _60625 _60626)). Qed.
Lemma lem4902716 (_60627 : nat) (_60628 : nat) : (Peano.le _60627 _60628) = (Peano.le _60627 _60628).
Proof. exact (eq_refl (Peano.le _60627 _60628)). Qed.
Lemma lem4902717 (_60625 : nat) (_60626 : nat) (_60627 : nat) (_60628 : nat) : (term573 _60625 _60626 _60627 _60628) = (term588 _60625 _60626 _60627 _60628).
Proof. exact (MK_COMB (@lem4902715 _60627 _60628 _60625 _60626) (@lem4902716 _60627 _60628)). Qed.
Lemma lem4902718 (_60625 : nat) (_60626 : nat) (_60627 : nat) (_60628 : nat) : (term571 _60627 _60628 _60625 _60626) = (term588 _60625 _60626 _60627 _60628).
Proof. exact (TRANS (@lem4902690 _60625 _60626 _60627 _60628) (@lem4902717 _60625 _60626 _60627 _60628)). Qed.
Lemma lem4902720 {_112866 : Type'} (t : list _112866) (h1 : term333 _112866) : term589 _112866 t.
Proof. exact (conj (@lem4902485 _112866 t) (@lem4902494 _112866 t h1)). Qed.
Lemma lem4902721 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term513 _112866 h x _60497 t) : term590 _112866 t.
Proof. exact (conj (@lem4902477 _112866 h x _60497 t h2) (@lem4902720 _112866 t h1)). Qed.
Lemma lem4902723 (_60625 : nat) (_60626 : nat) (_60627 : nat) (_60628 : nat) : term588 _60625 _60626 _60627 _60628.
Proof. exact (EQ_MP (@lem4902718 _60625 _60626 _60627 _60628) (@lem4902687 _60627 _60628 _60625 _60626)). Qed.
Lemma lem4902724 {_112866 : Type'} (t : list _112866) : term591 _112866 t.
Proof. exact (@lem4902723 (term171 _112866 t) (@List.length _112866 t) (term225 _112866 t) (@List.length _112866 t)). Qed.
Lemma lem4902727 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term513 _112866 h x _60497 t) : term592 _112866 t.
Proof. exact (@lem4902724 _112866 t (@lem4902721 _112866 h x _60497 t h1 h2)). Qed.
Lemma lem4902728 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term513 _112866 h x _60497 t) : term593 _112866 t.
Proof. exact (fun h0 : term594 _112866 t => @lem4902727 _112866 h x _60497 t h1 h2). Qed.
Lemma lem4902730 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4902731 {_112866 : Type'} (t : list _112866) : (term593 _112866 t) = (term592 _112866 t).
Proof. exact (@lem4902730 (term592 _112866 t)). Qed.
Lemma lem4902732 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term513 _112866 h x _60497 t) : term592 _112866 t.
Proof. exact (EQ_MP (@lem4902731 _112866 t) (@lem4902728 _112866 h x _60497 t h1 h2)). Qed.
Lemma lem4902735 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4902737 (_60507 : nat) : (term5 _60507) = (term595 _60507).
Proof. exact (@lem4902735 (term3 _60507)). Qed.
Lemma lem4902740 (_60507 : nat) (h1 : term152) : term595 _60507.
Proof. exact (EQ_MP (@lem4902737 _60507) (@lem4901811 _60507 h1)). Qed.
Lemma lem4902741 {_112866 : Type'} (t : list _112866) (h1 : term152) : term596 _112866 t.
Proof. exact (@lem4902740 (@List.length _112866 t) h1). Qed.
Lemma lem4902744 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term513 _112866 h x _60497 t) : False.
Proof. exact (@lem4902741 _112866 t h2 (@lem4902732 _112866 h x _60497 t h1 h3)). Qed.
Lemma lem4902745 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term513 _112866 h x _60497 t) : term597.
Proof. exact (fun h0 : ~ False => @lem4902744 _112866 h x _60497 t h1 h2 h3). Qed.
Lemma lem4902747 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4902748 : term597 = False.
Proof. exact (@lem4902747 False). Qed.
Lemma lem4902892 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) (h1 : term534 _112866 _60497 t) : @List.ForallOrdPairs _112866 _60497 t.
Proof. exact (proj2 (@lem4900800 _112866 _60497 t h1)). Qed.
Lemma lem4902893 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) (h1 : term534 _112866 _60497 t) : term598 _112866 _60497 t.
Proof. exact (fun h0 : term467 _112866 _60497 t => @lem4902892 _112866 _60497 t h1). Qed.
Lemma lem4902895 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4902896 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) : (term598 _112866 _60497 t) = (@List.ForallOrdPairs _112866 _60497 t).
Proof. exact (@lem4902895 (@List.ForallOrdPairs _112866 _60497 t)). Qed.
Lemma lem4902897 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) (h1 : term534 _112866 _60497 t) : @List.ForallOrdPairs _112866 _60497 t.
Proof. exact (EQ_MP (@lem4902896 _112866 _60497 t) (@lem4902893 _112866 _60497 t h1)). Qed.
Lemma lem4902900 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4902902 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) : (term467 _112866 _60497 t) = (term599 _112866 _60497 t).
Proof. exact (@lem4902900 (@List.ForallOrdPairs _112866 _60497 t)). Qed.
Lemma lem4902905 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) (h1 : term467 _112866 _60497 t) : term599 _112866 _60497 t.
Proof. exact (EQ_MP (@lem4902902 _112866 _60497 t) (@lem4901503 _112866 _60497 t h1)). Qed.
Lemma lem4902908 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) (h1 : term467 _112866 _60497 t) (h2 : term534 _112866 _60497 t) : False.
Proof. exact (@lem4902905 _112866 _60497 t h1 (@lem4902897 _112866 _60497 t h2)). Qed.
Lemma lem4902909 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) (h1 : term467 _112866 _60497 t) (h2 : term534 _112866 _60497 t) : term597.
Proof. exact (fun h0 : ~ False => @lem4902908 _112866 _60497 t h1 h2). Qed.
Lemma lem4902911 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4902912 : term597 = False.
Proof. exact (@lem4902911 False). Qed.
Lemma lem4902913 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) (h1 : term467 _112866 _60497 t) (h2 : term534 _112866 _60497 t) : False.
Proof. exact (EQ_MP (@lem4902912) (@lem4902909 _112866 _60497 t h1 h2)). Qed.
Lemma lem4902952 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem4902953 (_60685 : nat) (_60687 : nat) (h1 : _60685 = _60687) : _60685 = _60687.
Proof. exact (h1). Qed.
Lemma lem4902954 (_60686 : nat) (_60688 : nat) (h1 : _60686 = _60688) : _60686 = _60688.
Proof. exact (h1). Qed.
Lemma lem4902955 (_60685 : nat) (_60687 : nat) (h1 : _60685 = _60687) : (Peano.le _60685) = (Peano.le _60687).
Proof. exact (MK_COMB (@lem4902952) (@lem4902953 _60685 _60687 h1)). Qed.
Lemma lem4902956 (_60685 : nat) (_60687 : nat) (_60686 : nat) (_60688 : nat) (h1 : _60685 = _60687) (h2 : _60686 = _60688) : (Peano.le _60685 _60686) = (Peano.le _60687 _60688).
Proof. exact (MK_COMB (@lem4902955 _60685 _60687 h1) (@lem4902954 _60686 _60688 h2)). Qed.
Lemma lem4902958 (b : Prop) (a : Prop) : term539 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem4902959 (_60687 : nat) (_60688 : nat) (_60685 : nat) (_60686 : nat) : term540 _60687 _60688 _60685 _60686.
Proof. exact (@lem4902958 (Peano.le _60687 _60688) (Peano.le _60685 _60686)). Qed.
Lemma lem4902960 (_60685 : nat) (_60687 : nat) (_60686 : nat) (_60688 : nat) (h1 : _60685 = _60687) (h2 : _60686 = _60688) : term541 _60687 _60688 _60685 _60686.
Proof. exact (@lem4902959 _60687 _60688 _60685 _60686 (@lem4902956 _60685 _60687 _60686 _60688 h1 h2)). Qed.
Lemma lem4902961 (_60688 : nat) (_60686 : nat) (_60685 : nat) (_60687 : nat) (h1 : _60685 = _60687) : term542 _60687 _60688 _60685 _60686.
Proof. exact (fun h0 : _60686 = _60688 => @lem4902960 _60685 _60687 _60686 _60688 h1 h0). Qed.
Lemma lem4902963 (a : Prop) (b : Prop) : (a -> b) = (term543 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4902964 (_60687 : nat) (_60688 : nat) (_60685 : nat) (_60686 : nat) : (term542 _60687 _60688 _60685 _60686) = (term544 _60687 _60688 _60685 _60686).
Proof. exact (@lem4902963 (_60686 = _60688) (term541 _60687 _60688 _60685 _60686)). Qed.
Lemma lem4902965 (_60688 : nat) (_60686 : nat) (_60685 : nat) (_60687 : nat) (h1 : _60685 = _60687) : term544 _60687 _60688 _60685 _60686.
Proof. exact (EQ_MP (@lem4902964 _60687 _60688 _60685 _60686) (@lem4902961 _60688 _60686 _60685 _60687 h1)). Qed.
Lemma lem4902966 (_60687 : nat) (_60688 : nat) (_60685 : nat) (_60686 : nat) : term545 _60687 _60688 _60685 _60686.
Proof. exact (fun h0 : _60685 = _60687 => @lem4902965 _60688 _60686 _60685 _60687 h0). Qed.
Lemma lem4902968 (a : Prop) (b : Prop) : (a -> b) = (term543 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4902969 (_60687 : nat) (_60688 : nat) (_60685 : nat) (_60686 : nat) : (term545 _60687 _60688 _60685 _60686) = (term546 _60687 _60688 _60685 _60686).
Proof. exact (@lem4902968 (_60685 = _60687) (term544 _60687 _60688 _60685 _60686)). Qed.
Lemma lem4902970 (_60687 : nat) (_60688 : nat) (_60685 : nat) (_60686 : nat) : term546 _60687 _60688 _60685 _60686.
Proof. exact (EQ_MP (@lem4902969 _60687 _60688 _60685 _60686) (@lem4902966 _60687 _60688 _60685 _60686)). Qed.
Lemma lem4903056 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term513 _112866 h x _60497 t) : (term171 _112866 t) = (term225 _112866 t).
Proof. exact (proj1 (@lem4900786 _112866 h x _60497 t h1)). Qed.
Lemma lem4903057 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term513 _112866 h x _60497 t) : term547 _112866 t.
Proof. exact (fun h0 : term548 _112866 t => @lem4903056 _112866 h x _60497 t h1). Qed.
Lemma lem4903059 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4903060 {_112866 : Type'} (t : list _112866) : (term547 _112866 t) = ((term171 _112866 t) = (term225 _112866 t)).
Proof. exact (@lem4903059 ((term171 _112866 t) = (term225 _112866 t))). Qed.
Lemma lem4903061 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term513 _112866 h x _60497 t) : (term171 _112866 t) = (term225 _112866 t).
Proof. exact (EQ_MP (@lem4903060 _112866 t) (@lem4903057 _112866 h x _60497 t h1)). Qed.
Lemma lem4903063 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem4903064 {_112866 : Type'} (t : list _112866) : (@List.length _112866 t) = (@List.length _112866 t).
Proof. exact (@lem4903063 (@List.length _112866 t)). Qed.
Lemma lem4903065 {_112866 : Type'} (t : list _112866) : term550 _112866 t.
Proof. exact (fun h0 : term551 _112866 t => @lem4903064 _112866 t). Qed.
Lemma lem4903067 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4903068 {_112866 : Type'} (t : list _112866) : (term550 _112866 t) = ((@List.length _112866 t) = (@List.length _112866 t)).
Proof. exact (@lem4903067 ((@List.length _112866 t) = (@List.length _112866 t))). Qed.
Lemma lem4903069 {_112866 : Type'} (t : list _112866) : (@List.length _112866 t) = (@List.length _112866 t).
Proof. exact (EQ_MP (@lem4903068 _112866 t) (@lem4903065 _112866 t)). Qed.
Lemma lem4903071 {_112866 : Type'} (_60522 : list _112866) (h1 : term333 _112866) : term357 _112866 _60522.
Proof. exact (EQ_MP (@lem4901358 _112866 _60522) (@lem4901357 _112866 _60522 h1)). Qed.
Lemma lem4903072 {_112866 : Type'} (_60522 : list _112866) (h1 : term333 _112866) : term357 _112866 _60522.
Proof. exact (@lem4903071 _112866 _60522 h1). Qed.
Lemma lem4903073 {_112866 : Type'} (t : list _112866) (h1 : term333 _112866) : term357 _112866 t.
Proof. exact (@lem4903072 _112866 t h1). Qed.
Lemma lem4903074 {_112866 : Type'} (t : list _112866) (h1 : term333 _112866) : term552 _112866 t.
Proof. exact (fun h0 : term553 _112866 t => @lem4903073 _112866 t h1). Qed.
Lemma lem4903076 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4903077 {_112866 : Type'} (t : list _112866) : (term552 _112866 t) = (term357 _112866 t).
Proof. exact (@lem4903076 (term357 _112866 t)). Qed.
Lemma lem4903078 {_112866 : Type'} (t : list _112866) (h1 : term333 _112866) : term357 _112866 t.
Proof. exact (EQ_MP (@lem4903077 _112866 t) (@lem4903074 _112866 t h1)). Qed.
Lemma lem4903096 (q : Prop) (p : Prop) (r : Prop) : (term554 p q r) = (term554 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4903097 (_60687 : nat) (_60688 : nat) (_60685 : nat) (_60686 : nat) : (term544 _60687 _60688 _60685 _60686) = (term555 _60687 _60688 _60685 _60686).
Proof. exact (@lem4903096 (Peano.le _60687 _60688) (term556 _60686 _60688) (term557 _60685 _60686)). Qed.
Lemma lem4903111 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4903112 (_60685 : nat) (_60686 : nat) (_60688 : nat) : (term558 _60688 _60685 _60686) = (term559 _60685 _60686 _60688).
Proof. exact (@lem4903111 (term557 _60685 _60686) (term556 _60686 _60688)). Qed.
Lemma lem4903120 (_60687 : nat) (_60688 : nat) : (term560 _60687 _60688) = (term560 _60687 _60688).
Proof. exact (eq_refl (term560 _60687 _60688)). Qed.
Lemma lem4903121 (_60687 : nat) (_60685 : nat) (_60686 : nat) (_60688 : nat) : (term555 _60687 _60688 _60685 _60686) = (term561 _60687 _60685 _60686 _60688).
Proof. exact (MK_COMB (@lem4903120 _60687 _60688) (@lem4903112 _60685 _60686 _60688)). Qed.
Lemma lem4903132 (_60687 : nat) (_60685 : nat) (_60686 : nat) (_60688 : nat) : (term544 _60687 _60688 _60685 _60686) = (term561 _60687 _60685 _60686 _60688).
Proof. exact (TRANS (@lem4903097 _60687 _60688 _60685 _60686) (@lem4903121 _60687 _60685 _60686 _60688)). Qed.
Lemma lem4903133 (_60685 : nat) (_60687 : nat) : (term562 _60685 _60687) = (term562 _60685 _60687).
Proof. exact (eq_refl (term562 _60685 _60687)). Qed.
Lemma lem4903134 (_60687 : nat) (_60685 : nat) (_60686 : nat) (_60688 : nat) : (term546 _60687 _60688 _60685 _60686) = (term563 _60687 _60685 _60686 _60688).
Proof. exact (MK_COMB (@lem4903133 _60685 _60687) (@lem4903132 _60687 _60685 _60686 _60688)). Qed.
Lemma lem4903138 (q : Prop) (p : Prop) (r : Prop) : (term554 p q r) = (term554 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4903139 (_60687 : nat) (_60685 : nat) (_60686 : nat) (_60688 : nat) : (term563 _60687 _60685 _60686 _60688) = (term564 _60687 _60685 _60686 _60688).
Proof. exact (@lem4903138 (Peano.le _60687 _60688) (term556 _60685 _60687) (term559 _60685 _60686 _60688)). Qed.
Lemma lem4903153 (q : Prop) (p : Prop) (r : Prop) : (term554 p q r) = (term554 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4903154 (_60685 : nat) (_60687 : nat) (_60686 : nat) (_60688 : nat) : (term565 _60687 _60685 _60686 _60688) = (term566 _60685 _60687 _60686 _60688).
Proof. exact (@lem4903153 (term557 _60685 _60686) (term556 _60685 _60687) (term556 _60686 _60688)). Qed.
Lemma lem4903174 (_60687 : nat) (_60688 : nat) : (term560 _60687 _60688) = (term560 _60687 _60688).
Proof. exact (eq_refl (term560 _60687 _60688)). Qed.
Lemma lem4903175 (_60685 : nat) (_60687 : nat) (_60686 : nat) (_60688 : nat) : (term564 _60687 _60685 _60686 _60688) = (term567 _60685 _60687 _60686 _60688).
Proof. exact (MK_COMB (@lem4903174 _60687 _60688) (@lem4903154 _60685 _60687 _60686 _60688)). Qed.
Lemma lem4903186 (_60685 : nat) (_60687 : nat) (_60686 : nat) (_60688 : nat) : (term563 _60687 _60685 _60686 _60688) = (term567 _60685 _60687 _60686 _60688).
Proof. exact (TRANS (@lem4903139 _60687 _60685 _60686 _60688) (@lem4903175 _60685 _60687 _60686 _60688)). Qed.
Lemma lem4903187 (_60685 : nat) (_60687 : nat) (_60686 : nat) (_60688 : nat) : (term546 _60687 _60688 _60685 _60686) = (term567 _60685 _60687 _60686 _60688).
Proof. exact (TRANS (@lem4903134 _60687 _60685 _60686 _60688) (@lem4903186 _60685 _60687 _60686 _60688)). Qed.
Lemma lem4903188 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4903189 (_60685 : nat) (_60687 : nat) (_60686 : nat) (_60688 : nat) : (term568 _60687 _60688 _60685 _60686) = (term569 _60685 _60687 _60686 _60688).
Proof. exact (MK_COMB (@lem4903188) (@lem4903187 _60685 _60687 _60686 _60688)). Qed.
Lemma lem4903215 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4903216 (_60685 : nat) (_60686 : nat) (_60688 : nat) : (term558 _60688 _60685 _60686) = (term559 _60685 _60686 _60688).
Proof. exact (@lem4903215 (term557 _60685 _60686) (term556 _60686 _60688)). Qed.
Lemma lem4903224 (_60685 : nat) (_60687 : nat) : (term562 _60685 _60687) = (term562 _60685 _60687).
Proof. exact (eq_refl (term562 _60685 _60687)). Qed.
Lemma lem4903225 (_60687 : nat) (_60685 : nat) (_60686 : nat) (_60688 : nat) : (term570 _60687 _60688 _60685 _60686) = (term565 _60687 _60685 _60686 _60688).
Proof. exact (MK_COMB (@lem4903224 _60685 _60687) (@lem4903216 _60685 _60686 _60688)). Qed.
Lemma lem4903229 (q : Prop) (p : Prop) (r : Prop) : (term554 p q r) = (term554 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4903230 (_60685 : nat) (_60687 : nat) (_60686 : nat) (_60688 : nat) : (term565 _60687 _60685 _60686 _60688) = (term566 _60685 _60687 _60686 _60688).
Proof. exact (@lem4903229 (term557 _60685 _60686) (term556 _60685 _60687) (term556 _60686 _60688)). Qed.
Lemma lem4903250 (_60685 : nat) (_60687 : nat) (_60686 : nat) (_60688 : nat) : (term570 _60687 _60688 _60685 _60686) = (term566 _60685 _60687 _60686 _60688).
Proof. exact (TRANS (@lem4903225 _60687 _60685 _60686 _60688) (@lem4903230 _60685 _60687 _60686 _60688)). Qed.
Lemma lem4903251 (_60687 : nat) (_60688 : nat) : (term560 _60687 _60688) = (term560 _60687 _60688).
Proof. exact (eq_refl (term560 _60687 _60688)). Qed.
Lemma lem4903252 (_60685 : nat) (_60687 : nat) (_60686 : nat) (_60688 : nat) : (term571 _60687 _60688 _60685 _60686) = (term567 _60685 _60687 _60686 _60688).
Proof. exact (MK_COMB (@lem4903251 _60687 _60688) (@lem4903250 _60685 _60687 _60686 _60688)). Qed.
Lemma lem4903263 (_60685 : nat) (_60687 : nat) (_60686 : nat) (_60688 : nat) : ((term546 _60687 _60688 _60685 _60686) = (term571 _60687 _60688 _60685 _60686)) = ((term567 _60685 _60687 _60686 _60688) = (term567 _60685 _60687 _60686 _60688)).
Proof. exact (MK_COMB (@lem4903189 _60685 _60687 _60686 _60688) (@lem4903252 _60685 _60687 _60686 _60688)). Qed.
Lemma lem4903265 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4903266 (x : Prop) : (x = x) = True.
Proof. exact (@lem4903265 Prop x). Qed.
Lemma lem4903267 (_60685 : nat) (_60687 : nat) (_60686 : nat) (_60688 : nat) : ((term567 _60685 _60687 _60686 _60688) = (term567 _60685 _60687 _60686 _60688)) = True.
Proof. exact (@lem4903266 (term567 _60685 _60687 _60686 _60688)). Qed.
Lemma lem4903268 (_60687 : nat) (_60688 : nat) (_60685 : nat) (_60686 : nat) : ((term546 _60687 _60688 _60685 _60686) = (term571 _60687 _60688 _60685 _60686)) = True.
Proof. exact (TRANS (@lem4903263 _60685 _60687 _60686 _60688) (@lem4903267 _60685 _60687 _60686 _60688)). Qed.
Lemma lem4903269 (_60687 : nat) (_60688 : nat) (_60685 : nat) (_60686 : nat) : True = ((term546 _60687 _60688 _60685 _60686) = (term571 _60687 _60688 _60685 _60686)).
Proof. exact (SYM (@lem4903268 _60687 _60688 _60685 _60686)). Qed.
Lemma lem4903270 (_60687 : nat) (_60688 : nat) (_60685 : nat) (_60686 : nat) : (term546 _60687 _60688 _60685 _60686) = (term571 _60687 _60688 _60685 _60686).
Proof. exact (EQ_MP (@lem4903269 _60687 _60688 _60685 _60686) (@lem0)). Qed.
Lemma lem4903271 (_60687 : nat) (_60688 : nat) (_60685 : nat) (_60686 : nat) : term571 _60687 _60688 _60685 _60686.
Proof. exact (EQ_MP (@lem4903270 _60687 _60688 _60685 _60686) (@lem4902970 _60687 _60688 _60685 _60686)). Qed.
Lemma lem4903273 (b : Prop) (a : Prop) : (a \/ b) = (term572 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4903274 (_60685 : nat) (_60686 : nat) (_60687 : nat) (_60688 : nat) : (term571 _60687 _60688 _60685 _60686) = (term573 _60685 _60686 _60687 _60688).
Proof. exact (@lem4903273 (term570 _60687 _60688 _60685 _60686) (Peano.le _60687 _60688)). Qed.
Lemma lem4903276 (a : Prop) (b : Prop) : (term574 a b) = (term575 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4903277 (_60687 : nat) (_60688 : nat) (_60685 : nat) (_60686 : nat) : (term576 _60687 _60688 _60685 _60686) = (term577 _60687 _60688 _60685 _60686).
Proof. exact (@lem4903276 (term556 _60685 _60687) (term558 _60688 _60685 _60686)). Qed.
Lemma lem4903279 (a : Prop) : (term55 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4903280 (_60685 : nat) (_60687 : nat) : (term578 _60685 _60687) = (_60685 = _60687).
Proof. exact (@lem4903279 (_60685 = _60687)). Qed.
Lemma lem4903281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4903282 (_60685 : nat) (_60687 : nat) : (term579 _60685 _60687) = (term580 _60685 _60687).
Proof. exact (MK_COMB (@lem4903281) (@lem4903280 _60685 _60687)). Qed.
Lemma lem4903284 (a : Prop) (b : Prop) : (term574 a b) = (term575 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4903285 (_60688 : nat) (_60685 : nat) (_60686 : nat) : (term581 _60688 _60685 _60686) = (term582 _60688 _60685 _60686).
Proof. exact (@lem4903284 (term556 _60686 _60688) (term557 _60685 _60686)). Qed.
Lemma lem4903287 (a : Prop) : (term55 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4903288 (_60686 : nat) (_60688 : nat) : (term578 _60686 _60688) = (_60686 = _60688).
Proof. exact (@lem4903287 (_60686 = _60688)). Qed.
Lemma lem4903289 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4903290 (_60686 : nat) (_60688 : nat) : (term579 _60686 _60688) = (term580 _60686 _60688).
Proof. exact (MK_COMB (@lem4903289) (@lem4903288 _60686 _60688)). Qed.
Lemma lem4903292 (a : Prop) : (term55 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4903293 (_60685 : nat) (_60686 : nat) : (term583 _60685 _60686) = (Peano.le _60685 _60686).
Proof. exact (@lem4903292 (Peano.le _60685 _60686)). Qed.
Lemma lem4903294 (_60688 : nat) (_60685 : nat) (_60686 : nat) : (term582 _60688 _60685 _60686) = (term584 _60688 _60685 _60686).
Proof. exact (MK_COMB (@lem4903290 _60686 _60688) (@lem4903293 _60685 _60686)). Qed.
Lemma lem4903295 (_60688 : nat) (_60685 : nat) (_60686 : nat) : (term581 _60688 _60685 _60686) = (term584 _60688 _60685 _60686).
Proof. exact (TRANS (@lem4903285 _60688 _60685 _60686) (@lem4903294 _60688 _60685 _60686)). Qed.
Lemma lem4903296 (_60687 : nat) (_60688 : nat) (_60685 : nat) (_60686 : nat) : (term577 _60687 _60688 _60685 _60686) = (term585 _60687 _60688 _60685 _60686).
Proof. exact (MK_COMB (@lem4903282 _60685 _60687) (@lem4903295 _60688 _60685 _60686)). Qed.
Lemma lem4903297 (_60687 : nat) (_60688 : nat) (_60685 : nat) (_60686 : nat) : (term576 _60687 _60688 _60685 _60686) = (term585 _60687 _60688 _60685 _60686).
Proof. exact (TRANS (@lem4903277 _60687 _60688 _60685 _60686) (@lem4903296 _60687 _60688 _60685 _60686)). Qed.
Lemma lem4903298 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4903299 (_60687 : nat) (_60688 : nat) (_60685 : nat) (_60686 : nat) : (term586 _60687 _60688 _60685 _60686) = (term587 _60687 _60688 _60685 _60686).
Proof. exact (MK_COMB (@lem4903298) (@lem4903297 _60687 _60688 _60685 _60686)). Qed.
Lemma lem4903300 (_60687 : nat) (_60688 : nat) : (Peano.le _60687 _60688) = (Peano.le _60687 _60688).
Proof. exact (eq_refl (Peano.le _60687 _60688)). Qed.
Lemma lem4903301 (_60685 : nat) (_60686 : nat) (_60687 : nat) (_60688 : nat) : (term573 _60685 _60686 _60687 _60688) = (term588 _60685 _60686 _60687 _60688).
Proof. exact (MK_COMB (@lem4903299 _60687 _60688 _60685 _60686) (@lem4903300 _60687 _60688)). Qed.
Lemma lem4903302 (_60685 : nat) (_60686 : nat) (_60687 : nat) (_60688 : nat) : (term571 _60687 _60688 _60685 _60686) = (term588 _60685 _60686 _60687 _60688).
Proof. exact (TRANS (@lem4903274 _60685 _60686 _60687 _60688) (@lem4903301 _60685 _60686 _60687 _60688)). Qed.
Lemma lem4903304 {_112866 : Type'} (t : list _112866) (h1 : term333 _112866) : term589 _112866 t.
Proof. exact (conj (@lem4903069 _112866 t) (@lem4903078 _112866 t h1)). Qed.
Lemma lem4903305 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term513 _112866 h x _60497 t) : term590 _112866 t.
Proof. exact (conj (@lem4903061 _112866 h x _60497 t h2) (@lem4903304 _112866 t h1)). Qed.
Lemma lem4903307 (_60685 : nat) (_60686 : nat) (_60687 : nat) (_60688 : nat) : term588 _60685 _60686 _60687 _60688.
Proof. exact (EQ_MP (@lem4903302 _60685 _60686 _60687 _60688) (@lem4903271 _60687 _60688 _60685 _60686)). Qed.
Lemma lem4903308 {_112866 : Type'} (t : list _112866) : term591 _112866 t.
Proof. exact (@lem4903307 (term171 _112866 t) (@List.length _112866 t) (term225 _112866 t) (@List.length _112866 t)). Qed.
Lemma lem4903311 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term513 _112866 h x _60497 t) : term592 _112866 t.
Proof. exact (@lem4903308 _112866 t (@lem4903305 _112866 h x _60497 t h1 h2)). Qed.
Lemma lem4903312 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term513 _112866 h x _60497 t) : term593 _112866 t.
Proof. exact (fun h0 : term594 _112866 t => @lem4903311 _112866 h x _60497 t h1 h2). Qed.
Lemma lem4903314 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4903315 {_112866 : Type'} (t : list _112866) : (term593 _112866 t) = (term592 _112866 t).
Proof. exact (@lem4903314 (term592 _112866 t)). Qed.
Lemma lem4903316 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term513 _112866 h x _60497 t) : term592 _112866 t.
Proof. exact (EQ_MP (@lem4903315 _112866 t) (@lem4903312 _112866 h x _60497 t h1 h2)). Qed.
Lemma lem4903319 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4903321 (_60521 : nat) : (term5 _60521) = (term595 _60521).
Proof. exact (@lem4903319 (term3 _60521)). Qed.
Lemma lem4903324 (_60521 : nat) (h1 : term152) : term595 _60521.
Proof. exact (EQ_MP (@lem4903321 _60521) (@lem4901513 _60521 h1)). Qed.
Lemma lem4903325 {_112866 : Type'} (t : list _112866) (h1 : term152) : term596 _112866 t.
Proof. exact (@lem4903324 (@List.length _112866 t) h1). Qed.
Lemma lem4903328 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term513 _112866 h x _60497 t) : False.
Proof. exact (@lem4903325 _112866 t h2 (@lem4903316 _112866 h x _60497 t h1 h3)). Qed.
Lemma lem4903329 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term513 _112866 h x _60497 t) : term597.
Proof. exact (fun h0 : ~ False => @lem4903328 _112866 h x _60497 t h1 h2 h3). Qed.
Lemma lem4903331 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4903332 : term597 = False.
Proof. exact (@lem4903331 False). Qed.
Lemma lem4903333 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term513 _112866 h x _60497 t) : False.
Proof. exact (EQ_MP (@lem4903332) (@lem4903329 _112866 h x _60497 t h1 h2 h3)). Qed.
Lemma lem4903476 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : @List.In _112866 h t) : @List.In _112866 h t.
Proof. exact (h1). Qed.
Lemma lem4903477 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : @List.In _112866 h t) : term600 _112866 h t.
Proof. exact (fun h0 : term257 _112866 h t => @lem4903476 _112866 h t h1). Qed.
Lemma lem4903479 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4903480 {_112866 : Type'} (h : _112866) (t : list _112866) : (term600 _112866 h t) = (@List.In _112866 h t).
Proof. exact (@lem4903479 (@List.In _112866 h t)). Qed.
Lemma lem4903481 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : @List.In _112866 h t) : @List.In _112866 h t.
Proof. exact (EQ_MP (@lem4903480 _112866 h t) (@lem4903477 _112866 h t h1)). Qed.
Lemma lem4903483 {_112866 : Type'} (x : _112866) : x = x.
Proof. exact (@lem21386 _112866 x). Qed.
Lemma lem4903484 {_112866 : Type'} (x : _112866) : x = x.
Proof. exact (@lem4903483 _112866 x). Qed.
Lemma lem4903485 {_112866 : Type'} (h : _112866) : h = h.
Proof. exact (@lem4903484 _112866 h). Qed.
Lemma lem4903486 {_112866 : Type'} (h : _112866) : term601 _112866 h.
Proof. exact (fun h0 : term602 _112866 h => @lem4903485 _112866 h). Qed.
Lemma lem4903488 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4903489 {_112866 : Type'} (h : _112866) : (term601 _112866 h) = (h = h).
Proof. exact (@lem4903488 (h = h)). Qed.
Lemma lem4903490 {_112866 : Type'} (h : _112866) : h = h.
Proof. exact (EQ_MP (@lem4903489 _112866 h) (@lem4903486 _112866 h)). Qed.
Lemma lem4903492 (a : Prop) (b : Prop) : (term603 a b) = (term604 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4903493 {_112866 : Type'} (t : list _112866) (h : _112866) (_60534 : _112866) : (term455 _112866 t h _60534) = (term605 _112866 t h _60534).
Proof. exact (@lem4903492 (@List.In _112866 _60534 t) (h = _60534)). Qed.
Lemma lem4903495 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4903496 {_112866 : Type'} (t : list _112866) (h : _112866) (_60534 : _112866) : (term605 _112866 t h _60534) = (term606 _112866 t h _60534).
Proof. exact (@lem4903495 (term453 _112866 t h _60534)). Qed.
Lemma lem4903497 {_112866 : Type'} (t : list _112866) (h : _112866) (_60534 : _112866) : (term455 _112866 t h _60534) = (term606 _112866 t h _60534).
Proof. exact (TRANS (@lem4903493 _112866 t h _60534) (@lem4903496 _112866 t h _60534)). Qed.
Lemma lem4903499 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : @List.In _112866 h t) : term607 _112866 t h.
Proof. exact (conj (@lem4903481 _112866 h t h1) (@lem4903490 _112866 h)). Qed.
Lemma lem4903501 {_112866 : Type'} (_60534 : _112866) (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term477 _112866 h _60497 t) : term606 _112866 t h _60534.
Proof. exact (EQ_MP (@lem4903497 _112866 t h _60534) (@lem4901563 _112866 _60534 h _60497 t h1)). Qed.
Lemma lem4903502 {_112866 : Type'} (_60534 : _112866) (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term477 _112866 h _60497 t) : term606 _112866 t h _60534.
Proof. exact (@lem4903501 _112866 _60534 h _60497 t h1). Qed.
Lemma lem4903503 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term477 _112866 h _60497 t) : term608 _112866 t h.
Proof. exact (@lem4903502 _112866 h h _60497 t h1). Qed.
Lemma lem4903506 {_112866 : Type'} (_60497 : type1402 _112866) (h : _112866) (t : list _112866) (h1 : term477 _112866 h _60497 t) (h2 : @List.In _112866 h t) : False.
Proof. exact (@lem4903503 _112866 h _60497 t h1 (@lem4903499 _112866 h t h2)). Qed.
Lemma lem4903507 {_112866 : Type'} (_60497 : type1402 _112866) (h : _112866) (t : list _112866) (h1 : term477 _112866 h _60497 t) (h2 : @List.In _112866 h t) : term597.
Proof. exact (fun h0 : ~ False => @lem4903506 _112866 _60497 h t h1 h2). Qed.
Lemma lem4903509 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4903510 : term597 = False.
Proof. exact (@lem4903509 False). Qed.
Lemma lem4903511 {_112866 : Type'} (_60497 : type1402 _112866) (h : _112866) (t : list _112866) (h1 : term477 _112866 h _60497 t) (h2 : @List.In _112866 h t) : False.
Proof. exact (EQ_MP (@lem4903510) (@lem4903507 _112866 _60497 h t h1 h2)). Qed.
Lemma lem4903654 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term477 _112866 h _60497 t) : @List.ForallOrdPairs _112866 _60497 t.
Proof. exact (proj2 (@lem4900806 _112866 h _60497 t h1)). Qed.
Lemma lem4903655 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term477 _112866 h _60497 t) : term598 _112866 _60497 t.
Proof. exact (fun h0 : term467 _112866 _60497 t => @lem4903654 _112866 h _60497 t h1). Qed.
Lemma lem4903657 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4903658 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) : (term598 _112866 _60497 t) = (@List.ForallOrdPairs _112866 _60497 t).
Proof. exact (@lem4903657 (@List.ForallOrdPairs _112866 _60497 t)). Qed.
Lemma lem4903659 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term477 _112866 h _60497 t) : @List.ForallOrdPairs _112866 _60497 t.
Proof. exact (EQ_MP (@lem4903658 _112866 _60497 t) (@lem4903655 _112866 h _60497 t h1)). Qed.
Lemma lem4903662 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4903664 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) : (term467 _112866 _60497 t) = (term599 _112866 _60497 t).
Proof. exact (@lem4903662 (@List.ForallOrdPairs _112866 _60497 t)). Qed.
Lemma lem4903667 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) (h1 : term535 _112866 _60497 t) : term599 _112866 _60497 t.
Proof. exact (EQ_MP (@lem4903664 _112866 _60497 t) (@lem4901603 _112866 _60497 t h1)). Qed.
Lemma lem4903670 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term535 _112866 _60497 t) (h2 : term477 _112866 h _60497 t) : False.
Proof. exact (@lem4903667 _112866 _60497 t h1 (@lem4903659 _112866 h _60497 t h2)). Qed.
Lemma lem4903671 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term535 _112866 _60497 t) (h2 : term477 _112866 h _60497 t) : term597.
Proof. exact (fun h0 : ~ False => @lem4903670 _112866 h _60497 t h1 h2). Qed.
Lemma lem4903673 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4903674 : term597 = False.
Proof. exact (@lem4903673 False). Qed.
Lemma lem4903675 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term535 _112866 _60497 t) (h2 : term477 _112866 h _60497 t) : False.
Proof. exact (EQ_MP (@lem4903674) (@lem4903671 _112866 h _60497 t h1 h2)). Qed.
Lemma lem4903676 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term513 _112866 h x _60497 t) : False.
Proof. exact (EQ_MP (@lem4902748) (@lem4902745 _112866 h x _60497 t h1 h2 h3)). Qed.
Lemma lem4903677 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term513 _112866 h x _60497 t) : False.
Proof. exact (EQ_MP (@lem4902328) (@lem4902325 _112866 h x _60497 t h1 h2 h3)). Qed.
Lemma lem4903678 {_112866 : Type'} (_60497 : type1402 _112866) (h : _112866) (t : list _112866) (h1 : term477 _112866 h _60497 t) (h2 : @List.In _112866 h t) : (@List.In _112866 h t) = False.
Proof. exact (prop_ext (fun h3 : @List.In _112866 h t => @lem4903511 _112866 _60497 h t h1 h2) (fun h3 : False => @lem4901539 _112866 h t h2)). Qed.
Lemma lem4903679 {_112866 : Type'} (_60497 : type1402 _112866) (h : _112866) (t : list _112866) (h1 : term477 _112866 h _60497 t) (h2 : @List.In _112866 h t) : False.
Proof. exact (EQ_MP (@lem4903678 _112866 _60497 h t h1 h2) (@lem4901539 _112866 h t h2)). Qed.
Lemma lem4903680 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) (h1 : term467 _112866 _60497 t) (h2 : term534 _112866 _60497 t) : (term467 _112866 _60497 t) = False.
Proof. exact (prop_ext (fun h3 : term467 _112866 _60497 t => @lem4902913 _112866 _60497 t h1 h2) (fun h3 : False => @lem4901503 _112866 _60497 t h1)). Qed.
Lemma lem4903681 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) (h1 : term467 _112866 _60497 t) (h2 : term534 _112866 _60497 t) : False.
Proof. exact (EQ_MP (@lem4903680 _112866 _60497 t h1 h2) (@lem4901503 _112866 _60497 t h1)). Qed.
Lemma lem4903682 {_112866 : Type'} (_60497 : type1402 _112866) (h : _112866) (t : list _112866) (h1 : term477 _112866 h _60497 t) (h2 : @List.In _112866 h t) : (@List.In _112866 h t) = False.
Proof. exact (prop_ext (fun h3 : @List.In _112866 h t => @lem4903679 _112866 _60497 h t h1 h2) (fun h3 : False => @lem4901126 _112866 h t h2)). Qed.
Lemma lem4903683 {_112866 : Type'} (_60497 : type1402 _112866) (h : _112866) (t : list _112866) (h1 : term477 _112866 h _60497 t) (h2 : @List.In _112866 h t) : False.
Proof. exact (EQ_MP (@lem4903682 _112866 _60497 h t h1 h2) (@lem4901126 _112866 h t h2)). Qed.
Lemma lem4903684 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) (h1 : term467 _112866 _60497 t) (h2 : term534 _112866 _60497 t) : (term467 _112866 _60497 t) = False.
Proof. exact (prop_ext (fun h3 : term467 _112866 _60497 t => @lem4903681 _112866 _60497 t h1 h2) (fun h3 : False => @lem4901034 _112866 _60497 t h1)). Qed.
Lemma lem4903685 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) (h1 : term467 _112866 _60497 t) (h2 : term534 _112866 _60497 t) : False.
Proof. exact (EQ_MP (@lem4903684 _112866 _60497 t h1 h2) (@lem4901034 _112866 _60497 t h1)). Qed.
Lemma lem4903686 {_112866 : Type'} (_60497 : type1402 _112866) (h : _112866) (t : list _112866) (h1 : term477 _112866 h _60497 t) (h2 : @List.In _112866 h t) : (@List.In _112866 h t) = False.
Proof. exact (prop_ext (fun h3 : @List.In _112866 h t => @lem4903683 _112866 _60497 h t h1 h2) (fun h3 : False => @lem4901126 _112866 h t h2)). Qed.
Lemma lem4903687 {_112866 : Type'} (_60497 : type1402 _112866) (h : _112866) (t : list _112866) (h1 : term477 _112866 h _60497 t) (h2 : @List.In _112866 h t) : False.
Proof. exact (EQ_MP (@lem4903686 _112866 _60497 h t h1 h2) (@lem4901126 _112866 h t h2)). Qed.
Lemma lem4903688 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term513 _112866 h x _60497 t) : (term333 _112866) = False.
Proof. exact (prop_ext (fun h4 : term333 _112866 => @lem4903333 _112866 h x _60497 t h1 h2 h3) (fun h4 : False => @lem4901067 _112866 h1)). Qed.
Lemma lem4903689 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term513 _112866 h x _60497 t) : False.
Proof. exact (EQ_MP (@lem4903688 _112866 h x _60497 t h1 h2 h3) (@lem4901067 _112866 h1)). Qed.
Lemma lem4903690 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term513 _112866 h x _60497 t) : term152 = False.
Proof. exact (prop_ext (fun h4 : term152 => @lem4903689 _112866 h x _60497 t h1 h2 h3) (fun h4 : False => @lem4901060 h2)). Qed.
Lemma lem4903691 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term513 _112866 h x _60497 t) : False.
Proof. exact (EQ_MP (@lem4903690 _112866 h x _60497 t h1 h2 h3) (@lem4901060 h2)). Qed.
Lemma lem4903692 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) (h1 : term467 _112866 _60497 t) (h2 : term534 _112866 _60497 t) : (term467 _112866 _60497 t) = False.
Proof. exact (prop_ext (fun h3 : term467 _112866 _60497 t => @lem4903685 _112866 _60497 t h1 h2) (fun h3 : False => @lem4901034 _112866 _60497 t h1)). Qed.
Lemma lem4903693 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) (h1 : term467 _112866 _60497 t) (h2 : term534 _112866 _60497 t) : False.
Proof. exact (EQ_MP (@lem4903692 _112866 _60497 t h1 h2) (@lem4901034 _112866 _60497 t h1)). Qed.
Lemma lem4903694 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term513 _112866 h x _60497 t) : (term333 _112866) = False.
Proof. exact (prop_ext (fun h4 : term333 _112866 => @lem4903676 _112866 h x _60497 t h1 h2 h3) (fun h4 : False => @lem4900917 _112866 h1)). Qed.
Lemma lem4903695 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term513 _112866 h x _60497 t) : False.
Proof. exact (EQ_MP (@lem4903694 _112866 h x _60497 t h1 h2 h3) (@lem4900917 _112866 h1)). Qed.
Lemma lem4903696 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term513 _112866 h x _60497 t) : term152 = False.
Proof. exact (prop_ext (fun h4 : term152 => @lem4903695 _112866 h x _60497 t h1 h2 h3) (fun h4 : False => @lem4900910 h2)). Qed.
Lemma lem4903697 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term513 _112866 h x _60497 t) : False.
Proof. exact (EQ_MP (@lem4903696 _112866 h x _60497 t h1 h2 h3) (@lem4900910 h2)). Qed.
Lemma lem4903698 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term513 _112866 h x _60497 t) : (term333 _112866) = False.
Proof. exact (prop_ext (fun h4 : term333 _112866 => @lem4903677 _112866 h x _60497 t h1 h2 h3) (fun h4 : False => @lem4900840 _112866 h1)). Qed.
Lemma lem4903699 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term513 _112866 h x _60497 t) : False.
Proof. exact (EQ_MP (@lem4903698 _112866 h x _60497 t h1 h2 h3) (@lem4900840 _112866 h1)). Qed.
Lemma lem4903700 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term513 _112866 h x _60497 t) : term152 = False.
Proof. exact (prop_ext (fun h4 : term152 => @lem4903699 _112866 h x _60497 t h1 h2 h3) (fun h4 : False => @lem4900833 h2)). Qed.
Lemma lem4903701 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term513 _112866 h x _60497 t) : False.
Proof. exact (EQ_MP (@lem4903700 _112866 h x _60497 t h1 h2 h3) (@lem4900833 h2)). Qed.
Lemma lem4903702 {_112866 : Type'} (_60497 : type1402 _112866) (h : _112866) (t : list _112866) (h1 : term477 _112866 h _60497 t) (h2 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) (h3 : @List.In _112866 h t) : False.
Proof. exact (or_elim (@lem4900660 _112866 _60497 t h2) (fun h0 : term534 _112866 _60497 t => @lem4903687 _112866 _60497 h t h1 h3) (fun h0 : term535 _112866 _60497 t => @lem4903675 _112866 h _60497 t h0 h1)). Qed.
Lemma lem4903703 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term467 _112866 _60497 t) (h4 : term513 _112866 h x _60497 t) (h5 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) : False.
Proof. exact (or_elim (@lem4900660 _112866 _60497 t h5) (fun h0 : term534 _112866 _60497 t => @lem4903693 _112866 _60497 t h3 h0) (fun h0 : term535 _112866 _60497 t => @lem4903691 _112866 h x _60497 t h1 h2 h4)). Qed.
Lemma lem4903704 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term513 _112866 h x _60497 t) (h4 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) : False.
Proof. exact (or_elim (@lem4900660 _112866 _60497 t h4) (fun h0 : term534 _112866 _60497 t => @lem4903701 _112866 h x _60497 t h1 h2 h3) (fun h0 : term535 _112866 _60497 t => @lem4903697 _112866 h x _60497 t h1 h2 h3)). Qed.
Lemma lem4903705 {_112866 : Type'} (h : _112866) (x : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term513 _112866 h x _60497 t) (h4 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) : False.
Proof. exact (or_elim (@lem4900788 _112866 h x _60497 t h3) (fun h0 : term453 _112866 t h x => @lem4903704 _112866 h x _60497 t h1 h2 h3 h4) (fun h0 : term467 _112866 _60497 t => @lem4903703 _112866 h x _60497 t h1 h2 h0 h3 h4)). Qed.
Lemma lem4903706 {_112866 : Type'} (x : _112866) (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) (h4 : @List.In _112866 h t) (h5 : term530 _112866 x h _60497 t) : False.
Proof. exact (or_elim (@lem4900783 _112866 x h _60497 t h5) (fun h0 : term513 _112866 h x _60497 t => @lem4903705 _112866 h x _60497 t h1 h2 h0 h3) (fun h0 : term477 _112866 h _60497 t => @lem4903702 _112866 _60497 h t h0 h3 h4)). Qed.
Lemma lem4903707 {_112866 : Type'} (x : _112866) (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) (h4 : @List.In _112866 h t) (h5 : term530 _112866 x h _60497 t) : (term530 _112866 x h _60497 t) = False.
Proof. exact (prop_ext (fun h6 : term530 _112866 x h _60497 t => @lem4903706 _112866 x h _60497 t h1 h2 h3 h4 h5) (fun h6 : False => @lem4900783 _112866 x h _60497 t h5)). Qed.
Lemma lem4903708 {_112866 : Type'} (x : _112866) (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) (h4 : @List.In _112866 h t) (h5 : term530 _112866 x h _60497 t) : False.
Proof. exact (EQ_MP (@lem4903707 _112866 x h _60497 t h1 h2 h3 h4 h5) (@lem4900783 _112866 x h _60497 t h5)). Qed.
Lemma lem4903709 {_112866 : Type'} (x : _112866) (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) (h4 : @List.In _112866 h t) (h5 : term530 _112866 x h _60497 t) : (term333 _112866) = False.
Proof. exact (prop_ext (fun h6 : term333 _112866 => @lem4903708 _112866 x h _60497 t h1 h2 h3 h4 h5) (fun h6 : False => @lem4900694 _112866 h1)). Qed.
Lemma lem4903710 {_112866 : Type'} (x : _112866) (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) (h4 : @List.In _112866 h t) (h5 : term530 _112866 x h _60497 t) : False.
Proof. exact (EQ_MP (@lem4903709 _112866 x h _60497 t h1 h2 h3 h4 h5) (@lem4900694 _112866 h1)). Qed.
Lemma lem4903711 {_112866 : Type'} (x : _112866) (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) (h4 : @List.In _112866 h t) (h5 : term530 _112866 x h _60497 t) : term152 = False.
Proof. exact (prop_ext (fun h6 : term152 => @lem4903710 _112866 x h _60497 t h1 h2 h3 h4 h5) (fun h6 : False => @lem4900679 h2)). Qed.
Lemma lem4903712 {_112866 : Type'} (x : _112866) (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) (h4 : @List.In _112866 h t) (h5 : term530 _112866 x h _60497 t) : False.
Proof. exact (EQ_MP (@lem4903711 _112866 x h _60497 t h1 h2 h3 h4 h5) (@lem4900679 h2)). Qed.
Lemma lem4903713 {_112866 : Type'} (x : _112866) (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) (h4 : @List.In _112866 h t) (h5 : term530 _112866 x h _60497 t) : (@List.In _112866 h t) = False.
Proof. exact (prop_ext (fun h6 : @List.In _112866 h t => @lem4903712 _112866 x h _60497 t h1 h2 h3 h4 h5) (fun h6 : False => @lem4900666 _112866 h t h4)). Qed.
Lemma lem4903714 {_112866 : Type'} (x : _112866) (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) (h4 : @List.In _112866 h t) (h5 : term530 _112866 x h _60497 t) : False.
Proof. exact (EQ_MP (@lem4903713 _112866 x h _60497 t h1 h2 h3 h4 h5) (@lem4900666 _112866 h t h4)). Qed.
Lemma lem4903715 {_112866 : Type'} (_60497 : type1402 _112866) (h : _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term363 _112866 h _60497 t) (h4 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) (h5 : @List.In _112866 h t) : False.
Proof. exact (ex_elim (@lem4900513 _112866 h _60497 t h3) (fun x : _112866 => fun h0 : term532 _112866 h _60497 t x => @lem4903714 _112866 x h _60497 t h1 h2 h4 h5 h0)). Qed.
Lemma lem4903716 {_112866 : Type'} (_60497 : type1402 _112866) (h : _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term363 _112866 h _60497 t) (h4 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) (h5 : @List.In _112866 h t) : (term333 _112866) = False.
Proof. exact (prop_ext (fun h6 : term333 _112866 => @lem4903715 _112866 _60497 h t h1 h2 h3 h4 h5) (fun h6 : False => @lem4900539 _112866 h1)). Qed.
Lemma lem4903717 {_112866 : Type'} (_60497 : type1402 _112866) (h : _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term363 _112866 h _60497 t) (h4 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) (h5 : @List.In _112866 h t) : False.
Proof. exact (EQ_MP (@lem4903716 _112866 _60497 h t h1 h2 h3 h4 h5) (@lem4900539 _112866 h1)). Qed.
Lemma lem4903718 {_112866 : Type'} (_60497 : type1402 _112866) (h : _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term363 _112866 h _60497 t) (h4 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) (h5 : @List.In _112866 h t) : term152 = False.
Proof. exact (prop_ext (fun h6 : term152 => @lem4903717 _112866 _60497 h t h1 h2 h3 h4 h5) (fun h6 : False => @lem4900526 h2)). Qed.
Lemma lem4903719 {_112866 : Type'} (_60497 : type1402 _112866) (h : _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term363 _112866 h _60497 t) (h4 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) (h5 : @List.In _112866 h t) : False.
Proof. exact (EQ_MP (@lem4903718 _112866 _60497 h t h1 h2 h3 h4 h5) (@lem4900526 h2)). Qed.
Lemma lem4903720 {_112866 : Type'} (_60497 : type1402 _112866) (h : _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term363 _112866 h _60497 t) (h4 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) (h5 : @List.In _112866 h t) : (@List.In _112866 h t) = False.
Proof. exact (prop_ext (fun h6 : @List.In _112866 h t => @lem4903719 _112866 _60497 h t h1 h2 h3 h4 h5) (fun h6 : False => @lem4900285 _112866 h t h5)). Qed.
Lemma lem4903721 {_112866 : Type'} (_60497 : type1402 _112866) (h : _112866) (t : list _112866) (h1 : term333 _112866) (h2 : term152) (h3 : term363 _112866 h _60497 t) (h4 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) (h5 : @List.In _112866 h t) : False.
Proof. exact (EQ_MP (@lem4903720 _112866 _60497 h t h1 h2 h3 h4 h5) (@lem4900285 _112866 h t h5)). Qed.
Lemma lem4903722 {_112866 : Type'} (_60497 : type1402 _112866) (h : _112866) (t : list _112866) (h1 : term152) (h2 : term363 _112866 h _60497 t) (h3 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) (h4 : @List.In _112866 h t) : term338 _112866.
Proof. exact (fun h0 : term333 _112866 => @lem4903721 _112866 _60497 h t h0 h1 h2 h3 h4). Qed.
Lemma lem4903723 {_112866 : Type'} : (term338 _112866) = (term339 _112866).
Proof. exact (@lem69 (term333 _112866)). Qed.
Lemma lem4903724 {_112866 : Type'} (_60497 : type1402 _112866) (h : _112866) (t : list _112866) (h1 : term152) (h2 : term363 _112866 h _60497 t) (h3 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) (h4 : @List.In _112866 h t) : term339 _112866.
Proof. exact (EQ_MP (@lem4903723 _112866) (@lem4903722 _112866 _60497 h t h1 h2 h3 h4)). Qed.
Lemma lem4903725 {_112866 : Type'} (_60497 : type1402 _112866) (h : _112866) (t : list _112866) (h1 : term363 _112866 h _60497 t) (h2 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) (h3 : @List.In _112866 h t) : term342 _112866.
Proof. exact (fun h0 : term152 => @lem4903724 _112866 _60497 h t h0 h1 h2 h3). Qed.
Lemma lem4903726 {_112866 : Type'} (_60497 : type1402 _112866) (h : _112866) (t : list _112866) (h1 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) (h2 : @List.In _112866 h t) : term365 _112866 h _60497 t.
Proof. exact (fun h0 : term363 _112866 h _60497 t => @lem4903725 _112866 _60497 h t h0 h1 h2). Qed.
Lemma lem4903727 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) (h1 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t)) : term366 _112866 h _60497 t.
Proof. exact (fun h0 : @List.In _112866 h t => @lem4903726 _112866 _60497 h t h1 h0). Qed.
Lemma lem4903728 {_112866 : Type'} (h : _112866) (_60497 : type1402 _112866) (t : list _112866) : term368 _112866 h _60497 t.
Proof. exact (fun h0 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60497 t) => @lem4903727 _112866 h _60497 t h0). Qed.
Lemma lem4903733 {_112866 : Type'} (_60497 : type1402 _112866) (t : list _112866) : term370 _112866 _60497 t.
Proof. exact (fun h : _112866 => @lem4903728 _112866 h _60497 t). Qed.
Lemma lem4903738 {_112866 : Type'} (_60497 : type1402 _112866) : term372 _112866 _60497.
Proof. exact (fun t : list _112866 => @lem4903733 _112866 _60497 t). Qed.
Lemma lem4903739 {_112866 : Type'} (_60498 : type1402 _112866) (_60497 : type1402 _112866) : term412 _112866 _60498 _60497.
Proof. exact (fun h0 : term398 _112866 _60497 _60498 => @lem4903738 _112866 _60497). Qed.
Lemma lem4903744 {_112866 : Type'} (_60498 : type1402 _112866) : term414 _112866 _60498.
Proof. exact (fun _60497 : type1402 _112866 => @lem4903739 _112866 _60498 _60497). Qed.
Lemma lem4903745 {_112866 : Type'} (_60498 : type1402 _112866) : term446 _112866 _60498.
Proof. exact (fun h0 : term444 _112866 _60498 => @lem4903744 _112866 _60498). Qed.
Lemma lem4903750 {_112866 : Type'} : term448 _112866.
Proof. exact (fun _60498 : type1402 _112866 => @lem4903745 _112866 _60498). Qed.
Lemma lem4903751 {_112866 : Type'} : term355 _112866.
Proof. exact (EQ_MP (@lem4899950 _112866) (@lem4903750 _112866)). Qed.
Lemma lem4903752 {_112866 : Type'} (t : list _112866) : term609 _112866 t.
Proof. exact (@lem4903751 _112866 t). Qed.
Lemma lem4903753 {_112866 : Type'} (t : list _112866) : (term609 _112866 t) = (term351 _112866 t).
Proof. exact (eq_refl (term609 _112866 t)). Qed.
Lemma lem4903754 {_112866 : Type'} (t : list _112866) : term351 _112866 t.
Proof. exact (EQ_MP (@lem4903753 _112866 t) (@lem4903752 _112866 t)). Qed.
Lemma lem4903755 {_112866 : Type'} (t : list _112866) (h : _112866) : term610 _112866 t h.
Proof. exact (@lem4903754 _112866 t h). Qed.
Lemma lem4903756 {_112866 : Type'} (h : _112866) (t : list _112866) : (term610 _112866 t h) = (term334 _112866 h t).
Proof. exact (eq_refl (term610 _112866 t h)). Qed.
Lemma lem4903757 {_112866 : Type'} (h : _112866) (t : list _112866) : term334 _112866 h t.
Proof. exact (EQ_MP (@lem4903756 _112866 h t) (@lem4903755 _112866 t h)). Qed.
Lemma lem4903759 {_112866 : Type'} (h : _112866) (t : list _112866) : term334 _112866 h t.
Proof. exact (@lem4899312 _112866 h t (@lem4903757 _112866 h t)). Qed.
Lemma lem4903760 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) : term346 _112866 h t.
Proof. exact (@lem4903759 _112866 h t (@lem4898537 _112866 t h1)). Qed.
Lemma lem4903761 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) (h2 : @List.In _112866 h t) : term344 _112866 h t.
Proof. exact (@lem4903760 _112866 h t h1 (@lem4899192 _112866 h t h2)). Qed.
Lemma lem4903762 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term332 _112866 h t) (h2 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) (h3 : @List.In _112866 h t) : term341 _112866.
Proof. exact (@lem4903761 _112866 h t h2 h3 (@lem4899293 _112866 h t h1)). Qed.
Lemma lem4903763 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term332 _112866 h t) (h2 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) (h3 : @List.In _112866 h t) : term338 _112866.
Proof. exact (@lem4903762 _112866 h t h1 h2 h3 (@lem4898440)). Qed.
Lemma lem4903764 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term332 _112866 h t) (h2 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) (h3 : @List.In _112866 h t) : False.
Proof. exact (@lem4903763 _112866 h t h1 h2 h3 (@lem4899294 _112866)). Qed.
Lemma lem4903765 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term332 _112866 h t) (h2 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) (h3 : @List.In _112866 h t) : (term332 _112866 h t) = False.
Proof. exact (prop_ext (fun h4 : term332 _112866 h t => @lem4903764 _112866 h t h1 h2 h3) (fun h4 : False => @lem4899293 _112866 h t h1)). Qed.
Lemma lem4903766 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term332 _112866 h t) (h2 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) (h3 : @List.In _112866 h t) : False.
Proof. exact (EQ_MP (@lem4903765 _112866 h t h1 h2 h3) (@lem4899293 _112866 h t h1)). Qed.
Lemma lem4903767 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) (h2 : @List.In _112866 h t) : term331 _112866 h t.
Proof. exact (fun h0 : term332 _112866 h t => @lem4903766 _112866 h t h0 h1 h2). Qed.
Lemma lem4903770 (p : Prop) : p = (term330 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4903771 {_112866 : Type'} (h : _112866) (t : list _112866) : ((term175 _112866 t) = (term304 _112866 h t)) = (term611 _112866 h t).
Proof. exact (@lem4903770 ((term175 _112866 t) = (term304 _112866 h t))). Qed.
Lemma lem4903772 {_112866 : Type'} (h : _112866) (t : list _112866) : (term611 _112866 h t) = ((term175 _112866 t) = (term304 _112866 h t)).
Proof. exact (SYM (@lem4903771 _112866 h t)). Qed.
Lemma lem4903773 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term612 _112866 h t) : term612 _112866 h t.
Proof. exact (h1). Qed.
Lemma lem4903774 {_112866 : Type'} : term333 _112866.
Proof. exact (@lem4897948 _112866). Qed.
Lemma lem4903779 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term613 _112866 h t) : term613 _112866 h t.
Proof. exact (h1). Qed.
Lemma lem4903780 {_112866 : Type'} (h : _112866) (t : list _112866) : term614 _112866 h t.
Proof. exact (fun h0 : term613 _112866 h t => @lem4903779 _112866 h t h0). Qed.
Lemma lem4903781 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term614 _112866 h t) : term614 _112866 h t.
Proof. exact (h1). Qed.
Lemma lem4903782 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term613 _112866 h t) : term613 _112866 h t.
Proof. exact (h1). Qed.
Lemma lem4903783 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term613 _112866 h t) (h2 : term614 _112866 h t) : term613 _112866 h t.
Proof. exact (@lem4903781 _112866 h t h2 (@lem4903782 _112866 h t h1)). Qed.
Lemma lem4903784 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term613 _112866 h t) : term615 _112866 h t.
Proof. exact (fun h0 : term614 _112866 h t => @lem4903783 _112866 h t h1 h0). Qed.
Lemma lem4903785 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term614 _112866 h t) : term614 _112866 h t.
Proof. exact (h1). Qed.
Lemma lem4903786 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term613 _112866 h t) (h2 : term614 _112866 h t) : term613 _112866 h t.
Proof. exact (@lem4903784 _112866 h t h1 (@lem4903785 _112866 h t h2)). Qed.
Lemma lem4903787 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term614 _112866 h t) : term614 _112866 h t.
Proof. exact (fun h0 : term613 _112866 h t => @lem4903786 _112866 h t h0 h1). Qed.
Lemma lem4903788 {_112866 : Type'} (h : _112866) (t : list _112866) : term616 _112866 h t.
Proof. exact (fun h0 : term614 _112866 h t => @lem4903787 _112866 h t h0). Qed.
Lemma lem4903791 {_112866 : Type'} (h : _112866) (t : list _112866) : term614 _112866 h t.
Proof. exact (@lem4903788 _112866 h t (@lem4903780 _112866 h t)). Qed.
Lemma lem4903792 {_112866 : Type'} (h : _112866) (t : list _112866) : term614 _112866 h t.
Proof. exact (@lem4903791 _112866 h t). Qed.
Lemma lem4903822 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4903823 {_112866 : Type'} : (term338 _112866) = (term339 _112866).
Proof. exact (@lem4903822 (term333 _112866)). Qed.
Lemma lem4903828 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem4903829 {_112866 : Type'} : (term341 _112866) = (term342 _112866).
Proof. exact (MK_COMB (@lem4903828) (@lem4903823 _112866)). Qed.
Lemma lem4903832 {_112866 : Type'} (h : _112866) (t : list _112866) : (term617 _112866 h t) = (term617 _112866 h t).
Proof. exact (eq_refl (term617 _112866 h t)). Qed.
Lemma lem4903833 {_112866 : Type'} (h : _112866) (t : list _112866) : (term618 _112866 h t) = (term619 _112866 h t).
Proof. exact (MK_COMB (@lem4903832 _112866 h t) (@lem4903829 _112866)). Qed.
Lemma lem4903836 {_112866 : Type'} (h : _112866) (t : list _112866) : (term313 _112866 h t) = (term313 _112866 h t).
Proof. exact (eq_refl (term313 _112866 h t)). Qed.
Lemma lem4903837 {_112866 : Type'} (h : _112866) (t : list _112866) : (term620 _112866 h t) = (term621 _112866 h t).
Proof. exact (MK_COMB (@lem4903836 _112866 h t) (@lem4903833 _112866 h t)). Qed.
Lemma lem4903840 {_112866 : Type'} (t : list _112866) : (term189 _112866 t) = (term189 _112866 t).
Proof. exact (eq_refl (term189 _112866 t)). Qed.
Lemma lem4903841 {_112866 : Type'} (h : _112866) (t : list _112866) : (term613 _112866 h t) = (term622 _112866 h t).
Proof. exact (MK_COMB (@lem4903840 _112866 t) (@lem4903837 _112866 h t)). Qed.
Lemma lem4903844 {_112866 : Type'} (t : list _112866) : (term623 _112866 t) = (term624 _112866 t).
Proof. exact (fun_ext (fun h : _112866 => @lem4903841 _112866 h t)). Qed.
Lemma lem4903845 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4903846 {_112866 : Type'} (t : list _112866) : (term625 _112866 t) = (term626 _112866 t).
Proof. exact (MK_COMB (@lem4903845 _112866) (@lem4903844 _112866 t)). Qed.
Lemma lem4903851 {_112866 : Type'} : (term627 _112866) = (term628 _112866).
Proof. exact (fun_ext (fun t : list _112866 => @lem4903846 _112866 t)). Qed.
Lemma lem4903852 {_112866 : Type'} : (@all (list _112866)) = (@all (list _112866)).
Proof. exact (eq_refl (@all (list _112866))). Qed.
Lemma lem4903859 {_112866 : Type'} : (term629 _112866) = (term630 _112866).
Proof. exact (MK_COMB (@lem4903852 _112866) (@lem4903851 _112866)). Qed.
Lemma lem4903860 {_112866 : Type'} (_60767 : type1402 _112866) (h1 : _60767 = (term214 _112866)) : _60767 = (term214 _112866).
Proof. exact (h1). Qed.
Lemma lem4903872 {_112866 : Type'} (l : list _112866) : (term357 _112866 l) = (term357 _112866 l).
Proof. exact (eq_refl (term357 _112866 l)). Qed.
Lemma lem4903873 {_112866 : Type'} : (term358 _112866) = (term358 _112866).
Proof. exact (fun_ext (fun l : list _112866 => @lem4903872 _112866 l)). Qed.
Lemma lem4903874 {_112866 : Type'} : (@all (list _112866)) = (@all (list _112866)).
Proof. exact (eq_refl (@all (list _112866))). Qed.
Lemma lem4903875 {_112866 : Type'} : (term333 _112866) = (term333 _112866).
Proof. exact (MK_COMB (@lem4903874 _112866) (@lem4903873 _112866)). Qed.
Lemma lem4903876 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4903877 {_112866 : Type'} : (term339 _112866) = (term339 _112866).
Proof. exact (MK_COMB (@lem4903876) (@lem4903875 _112866)). Qed.
Lemma lem4903886 (n : nat) : (term5 n) = (term5 n).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem4903887 : term359 = term359.
Proof. exact (fun_ext (fun n : nat => @lem4903886 n)). Qed.
Lemma lem4903888 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4903889 : term152 = term152.
Proof. exact (MK_COMB (@lem4903888) (@lem4903887)). Qed.
Lemma lem4903890 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4903891 : term340 = term340.
Proof. exact (MK_COMB (@lem4903890) (@lem4903889)). Qed.
Lemma lem4903892 {_112866 : Type'} : (term342 _112866) = (term342 _112866).
Proof. exact (MK_COMB (@lem4903891) (@lem4903877 _112866)). Qed.
Lemma lem4903893 {_112866 : Type'} (t : list _112866) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4903895 {_112866 : Type'} (_60767 : type1402 _112866) (h1 : _60767 = (term214 _112866)) : (term214 _112866) = _60767.
Proof. exact (SYM (@lem4903860 _112866 _60767 h1)). Qed.
Lemma lem4903896 {_112866 : Type'} (_60767 : type1402 _112866) (h1 : _60767 = (term214 _112866)) : (term214 _112866) = _60767.
Proof. exact (@lem4903895 _112866 _60767 h1). Qed.
Lemma lem4903897 {_112866 : Type'} : (@List.ForallOrdPairs _112866) = (@List.ForallOrdPairs _112866).
Proof. exact (eq_refl (@List.ForallOrdPairs _112866)). Qed.
Lemma lem4903898 {_112866 : Type'} (_60767 : type1402 _112866) (h1 : _60767 = (term214 _112866)) : (term360 _112866) = (@List.ForallOrdPairs _112866 _60767).
Proof. exact (MK_COMB (@lem4903897 _112866) (@lem4903896 _112866 _60767 h1)). Qed.
Lemma lem4903899 {_112866 : Type'} (t : list _112866) (_60767 : type1402 _112866) (h1 : _60767 = (term214 _112866)) : (term175 _112866 t) = (@List.ForallOrdPairs _112866 _60767 t).
Proof. exact (MK_COMB (@lem4903898 _112866 _60767 h1) (@lem4903893 _112866 t)). Qed.
Lemma lem4903914 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term298 _112866 t h x) = (term298 _112866 t h x).
Proof. exact (eq_refl (term298 _112866 t h x)). Qed.
Lemma lem4903915 {_112866 : Type'} (t : list _112866) (h : _112866) : (term300 _112866 t h) = (term300 _112866 t h).
Proof. exact (fun_ext (fun x : _112866 => @lem4903914 _112866 t h x)). Qed.
Lemma lem4903916 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4903917 {_112866 : Type'} (t : list _112866) (h : _112866) : (term301 _112866 t h) = (term301 _112866 t h).
Proof. exact (MK_COMB (@lem4903916 _112866) (@lem4903915 _112866 t h)). Qed.
Lemma lem4903918 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4903919 {_112866 : Type'} (t : list _112866) (h : _112866) : (term303 _112866 t h) = (term303 _112866 t h).
Proof. exact (MK_COMB (@lem4903918) (@lem4903917 _112866 t h)). Qed.
Lemma lem4903920 {_112866 : Type'} (h : _112866) (t : list _112866) (_60767 : type1402 _112866) (h1 : _60767 = (term214 _112866)) : (term304 _112866 h t) = (term361 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4903919 _112866 t h) (@lem4903899 _112866 t _60767 h1)). Qed.
Lemma lem4903921 {_112866 : Type'} (t : list _112866) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4903923 {_112866 : Type'} (_60767 : type1402 _112866) (h1 : _60767 = (term214 _112866)) : (term214 _112866) = _60767.
Proof. exact (SYM (@lem4903860 _112866 _60767 h1)). Qed.
Lemma lem4903924 {_112866 : Type'} (_60767 : type1402 _112866) (h1 : _60767 = (term214 _112866)) : (term214 _112866) = _60767.
Proof. exact (@lem4903923 _112866 _60767 h1). Qed.
Lemma lem4903925 {_112866 : Type'} : (@List.ForallOrdPairs _112866) = (@List.ForallOrdPairs _112866).
Proof. exact (eq_refl (@List.ForallOrdPairs _112866)). Qed.
Lemma lem4903926 {_112866 : Type'} (_60767 : type1402 _112866) (h1 : _60767 = (term214 _112866)) : (term360 _112866) = (@List.ForallOrdPairs _112866 _60767).
Proof. exact (MK_COMB (@lem4903925 _112866) (@lem4903924 _112866 _60767 h1)). Qed.
Lemma lem4903927 {_112866 : Type'} (t : list _112866) (_60767 : type1402 _112866) (h1 : _60767 = (term214 _112866)) : (term175 _112866 t) = (@List.ForallOrdPairs _112866 _60767 t).
Proof. exact (MK_COMB (@lem4903926 _112866 _60767 h1) (@lem4903921 _112866 t)). Qed.
Lemma lem4903928 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4903929 {_112866 : Type'} (t : list _112866) (_60767 : type1402 _112866) (h1 : _60767 = (term214 _112866)) : (term329 _112866 t) = (term631 _112866 _60767 t).
Proof. exact (MK_COMB (@lem4903928) (@lem4903927 _112866 t _60767 h1)). Qed.
Lemma lem4903930 {_112866 : Type'} (h : _112866) (t : list _112866) (_60767 : type1402 _112866) (h1 : _60767 = (term214 _112866)) : ((term175 _112866 t) = (term304 _112866 h t)) = ((@List.ForallOrdPairs _112866 _60767 t) = (term361 _112866 h _60767 t)).
Proof. exact (MK_COMB (@lem4903929 _112866 t _60767 h1) (@lem4903920 _112866 h t _60767 h1)). Qed.
Lemma lem4903931 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4903932 {_112866 : Type'} (h : _112866) (t : list _112866) (_60767 : type1402 _112866) (h1 : _60767 = (term214 _112866)) : (term612 _112866 h t) = (term632 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4903931) (@lem4903930 _112866 h t _60767 h1)). Qed.
Lemma lem4903933 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4903934 {_112866 : Type'} (h : _112866) (t : list _112866) (_60767 : type1402 _112866) (h1 : _60767 = (term214 _112866)) : (term617 _112866 h t) = (term633 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4903933) (@lem4903932 _112866 h t _60767 h1)). Qed.
Lemma lem4903935 {_112866 : Type'} (h : _112866) (t : list _112866) (_60767 : type1402 _112866) (h1 : _60767 = (term214 _112866)) : (term619 _112866 h t) = (term634 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4903934 _112866 h t _60767 h1) (@lem4903892 _112866)). Qed.
Lemma lem4903944 {_112866 : Type'} (h : _112866) (t : list _112866) : (term313 _112866 h t) = (term313 _112866 h t).
Proof. exact (eq_refl (term313 _112866 h t)). Qed.
Lemma lem4903945 {_112866 : Type'} (h : _112866) (t : list _112866) (_60767 : type1402 _112866) (h1 : _60767 = (term214 _112866)) : (term621 _112866 h t) = (term635 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4903944 _112866 h t) (@lem4903935 _112866 h t _60767 h1)). Qed.
Lemma lem4903946 {_112866 : Type'} (t : list _112866) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4903948 {_112866 : Type'} (_60767 : type1402 _112866) (h1 : _60767 = (term214 _112866)) : (term214 _112866) = _60767.
Proof. exact (SYM (@lem4903860 _112866 _60767 h1)). Qed.
Lemma lem4903949 {_112866 : Type'} (_60767 : type1402 _112866) (h1 : _60767 = (term214 _112866)) : (term214 _112866) = _60767.
Proof. exact (@lem4903948 _112866 _60767 h1). Qed.
Lemma lem4903950 {_112866 : Type'} : (@List.ForallOrdPairs _112866) = (@List.ForallOrdPairs _112866).
Proof. exact (eq_refl (@List.ForallOrdPairs _112866)). Qed.
Lemma lem4903951 {_112866 : Type'} (_60767 : type1402 _112866) (h1 : _60767 = (term214 _112866)) : (term360 _112866) = (@List.ForallOrdPairs _112866 _60767).
Proof. exact (MK_COMB (@lem4903950 _112866) (@lem4903949 _112866 _60767 h1)). Qed.
Lemma lem4903952 {_112866 : Type'} (t : list _112866) (_60767 : type1402 _112866) (h1 : _60767 = (term214 _112866)) : (term175 _112866 t) = (@List.ForallOrdPairs _112866 _60767 t).
Proof. exact (MK_COMB (@lem4903951 _112866 _60767 h1) (@lem4903946 _112866 t)). Qed.
Lemma lem4903965 {_112866 : Type'} (t : list _112866) : (term174 _112866 t) = (term174 _112866 t).
Proof. exact (eq_refl (term174 _112866 t)). Qed.
Lemma lem4903966 {_112866 : Type'} (t : list _112866) (_60767 : type1402 _112866) (h1 : _60767 = (term214 _112866)) : (((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) = (((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60767 t)).
Proof. exact (MK_COMB (@lem4903965 _112866 t) (@lem4903952 _112866 t _60767 h1)). Qed.
Lemma lem4903967 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4903968 {_112866 : Type'} (t : list _112866) (_60767 : type1402 _112866) (h1 : _60767 = (term214 _112866)) : (term189 _112866 t) = (term367 _112866 _60767 t).
Proof. exact (MK_COMB (@lem4903967) (@lem4903966 _112866 t _60767 h1)). Qed.
Lemma lem4903969 {_112866 : Type'} (h : _112866) (t : list _112866) (_60767 : type1402 _112866) (h1 : _60767 = (term214 _112866)) : (term622 _112866 h t) = (term636 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4903968 _112866 t _60767 h1) (@lem4903945 _112866 h t _60767 h1)). Qed.
Lemma lem4903970 {_112866 : Type'} (t : list _112866) (_60767 : type1402 _112866) (h1 : _60767 = (term214 _112866)) : (term624 _112866 t) = (term637 _112866 _60767 t).
Proof. exact (fun_ext (fun h : _112866 => @lem4903969 _112866 h t _60767 h1)). Qed.
Lemma lem4903971 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4903972 {_112866 : Type'} (t : list _112866) (_60767 : type1402 _112866) (h1 : _60767 = (term214 _112866)) : (term626 _112866 t) = (term638 _112866 _60767 t).
Proof. exact (MK_COMB (@lem4903971 _112866) (@lem4903970 _112866 t _60767 h1)). Qed.
Lemma lem4903973 {_112866 : Type'} (_60767 : type1402 _112866) (h1 : _60767 = (term214 _112866)) : (term628 _112866) = (term639 _112866 _60767).
Proof. exact (fun_ext (fun t : list _112866 => @lem4903972 _112866 t _60767 h1)). Qed.
Lemma lem4903974 {_112866 : Type'} : (@all (list _112866)) = (@all (list _112866)).
Proof. exact (eq_refl (@all (list _112866))). Qed.
Lemma lem4903975 {_112866 : Type'} (_60767 : type1402 _112866) (h1 : _60767 = (term214 _112866)) : (term630 _112866) = (term640 _112866 _60767).
Proof. exact (MK_COMB (@lem4903974 _112866) (@lem4903973 _112866 _60767 h1)). Qed.
Lemma lem4903976 {_112866 : Type'} (_60767 : type1402 _112866) : term641 _112866 _60767.
Proof. exact (fun h0 : _60767 = (term214 _112866) => @lem4903975 _112866 _60767 h0). Qed.
Lemma lem4903977 {_112866 : Type'} : term642 _112866.
Proof. exact (fun _60767 : type1402 _112866 => @lem4903976 _112866 _60767). Qed.
Lemma lem4903979 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term375 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem4903980 {_112866 : Type'} (P : Prop) (c : type1402 _112866) (Q : type421 _112866) : term376 _112866 P c Q.
Proof. exact (@lem4903979 (type1402 _112866) P c Q). Qed.
Lemma lem4903981 {_112866 : Type'} : term643 _112866.
Proof. exact (@lem4903980 _112866 (term630 _112866) (term214 _112866) (term644 _112866)). Qed.
Lemma lem4903982 {_112866 : Type'} (_60767 : type1402 _112866) : (term645 _112866 _60767) = (term640 _112866 _60767).
Proof. exact (eq_refl (term645 _112866 _60767)). Qed.
Lemma lem4903983 {_112866 : Type'} : (term646 _112866) = (term646 _112866).
Proof. exact (eq_refl (term646 _112866)). Qed.
Lemma lem4903984 {_112866 : Type'} (_60767 : type1402 _112866) : ((term630 _112866) = (term645 _112866 _60767)) = ((term630 _112866) = (term640 _112866 _60767)).
Proof. exact (MK_COMB (@lem4903983 _112866) (@lem4903982 _112866 _60767)). Qed.
Lemma lem4903985 {_112866 : Type'} (_60767 : type1402 _112866) : (term381 _112866 _60767) = (term381 _112866 _60767).
Proof. exact (eq_refl (term381 _112866 _60767)). Qed.
Lemma lem4903986 {_112866 : Type'} (_60767 : type1402 _112866) : (term647 _112866 _60767) = (term641 _112866 _60767).
Proof. exact (MK_COMB (@lem4903985 _112866 _60767) (@lem4903984 _112866 _60767)). Qed.
Lemma lem4903987 {_112866 : Type'} : (term648 _112866) = (term649 _112866).
Proof. exact (fun_ext (fun _60767 : type1402 _112866 => @lem4903986 _112866 _60767)). Qed.
Lemma lem4903988 {_112866 : Type'} : (@all (_112866 -> _112866 -> Prop)) = (@all (_112866 -> _112866 -> Prop)).
Proof. exact (eq_refl (@all (_112866 -> _112866 -> Prop))). Qed.
Lemma lem4903989 {_112866 : Type'} : (term650 _112866) = (term642 _112866).
Proof. exact (MK_COMB (@lem4903988 _112866) (@lem4903987 _112866)). Qed.
Lemma lem4903990 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4903991 {_112866 : Type'} : (term651 _112866) = (term652 _112866).
Proof. exact (MK_COMB (@lem4903990) (@lem4903989 _112866)). Qed.
Lemma lem4903992 {_112866 : Type'} (_60767 : type1402 _112866) : (term645 _112866 _60767) = (term640 _112866 _60767).
Proof. exact (eq_refl (term645 _112866 _60767)). Qed.
Lemma lem4903993 {_112866 : Type'} (_60767 : type1402 _112866) : (term381 _112866 _60767) = (term381 _112866 _60767).
Proof. exact (eq_refl (term381 _112866 _60767)). Qed.
Lemma lem4903994 {_112866 : Type'} (_60767 : type1402 _112866) : (term653 _112866 _60767) = (term654 _112866 _60767).
Proof. exact (MK_COMB (@lem4903993 _112866 _60767) (@lem4903992 _112866 _60767)). Qed.
Lemma lem4903995 {_112866 : Type'} : (term655 _112866) = (term656 _112866).
Proof. exact (fun_ext (fun _60767 : type1402 _112866 => @lem4903994 _112866 _60767)). Qed.
Lemma lem4903996 {_112866 : Type'} : (@all (_112866 -> _112866 -> Prop)) = (@all (_112866 -> _112866 -> Prop)).
Proof. exact (eq_refl (@all (_112866 -> _112866 -> Prop))). Qed.
Lemma lem4903997 {_112866 : Type'} : (term657 _112866) = (term658 _112866).
Proof. exact (MK_COMB (@lem4903996 _112866) (@lem4903995 _112866)). Qed.
Lemma lem4903998 {_112866 : Type'} : (term646 _112866) = (term646 _112866).
Proof. exact (eq_refl (term646 _112866)). Qed.
Lemma lem4903999 {_112866 : Type'} : ((term630 _112866) = (term657 _112866)) = ((term630 _112866) = (term658 _112866)).
Proof. exact (MK_COMB (@lem4903998 _112866) (@lem4903997 _112866)). Qed.
Lemma lem4904000 {_112866 : Type'} : (term643 _112866) = (term659 _112866).
Proof. exact (MK_COMB (@lem4903991 _112866) (@lem4903999 _112866)). Qed.
Lemma lem4904001 {_112866 : Type'} : term659 _112866.
Proof. exact (EQ_MP (@lem4904000 _112866) (@lem4903981 _112866)). Qed.
Lemma lem4904002 {_112866 : Type'} : (term630 _112866) = (term658 _112866).
Proof. exact (@lem4904001 _112866 (@lem4903977 _112866)). Qed.
Lemma lem4904004 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term395 _3571 _3575 t)) = (term396 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem4904005 {_112866 : Type'} (s : type1402 _112866) (t : type1402 _112866) : (s = (term397 _112866 t)) = (term398 _112866 s t).
Proof. exact (@lem4904004 (_112866 -> Prop) _112866 s t). Qed.
Lemma lem4904006 {_112866 : Type'} (_60767 : type1402 _112866) : (_60767 = (term285 _112866)) = (term399 _112866 _60767).
Proof. exact (@lem4904005 _112866 _60767 (term214 _112866)). Qed.
Lemma lem4904007 {_112866 : Type'} (x : _112866) : (term269 _112866 x) = (term284 _112866 x).
Proof. exact (eq_refl (term269 _112866 x)). Qed.
Lemma lem4904008 {_112866 : Type'} : (term285 _112866) = (term214 _112866).
Proof. exact (fun_ext (fun x : _112866 => @lem4904007 _112866 x)). Qed.
Lemma lem4904009 {_112866 : Type'} (_60767 : type1402 _112866) : (@eq (_112866 -> _112866 -> Prop) _60767) = (@eq (_112866 -> _112866 -> Prop) _60767).
Proof. exact (eq_refl (@eq (_112866 -> _112866 -> Prop) _60767)). Qed.
Lemma lem4904010 {_112866 : Type'} (_60767 : type1402 _112866) : (_60767 = (term285 _112866)) = (_60767 = (term214 _112866)).
Proof. exact (MK_COMB (@lem4904009 _112866 _60767) (@lem4904008 _112866)). Qed.
Lemma lem4904011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4904012 {_112866 : Type'} (_60767 : type1402 _112866) : (term400 _112866 _60767) = (term401 _112866 _60767).
Proof. exact (MK_COMB (@lem4904011) (@lem4904010 _112866 _60767)). Qed.
Lemma lem4904013 {_112866 : Type'} (x : _112866) : (term269 _112866 x) = (term284 _112866 x).
Proof. exact (eq_refl (term269 _112866 x)). Qed.
Lemma lem4904014 {_112866 : Type'} (_60767 : type1402 _112866) (x : _112866) : (term402 _112866 _60767 x) = (term402 _112866 _60767 x).
Proof. exact (eq_refl (term402 _112866 _60767 x)). Qed.
Lemma lem4904015 {_112866 : Type'} (_60767 : type1402 _112866) (x : _112866) : ((_60767 x) = (term269 _112866 x)) = ((_60767 x) = (term284 _112866 x)).
Proof. exact (MK_COMB (@lem4904014 _112866 _60767 x) (@lem4904013 _112866 x)). Qed.
Lemma lem4904016 {_112866 : Type'} (_60767 : type1402 _112866) : (term403 _112866 _60767) = (term404 _112866 _60767).
Proof. exact (fun_ext (fun x : _112866 => @lem4904015 _112866 _60767 x)). Qed.
Lemma lem4904017 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4904018 {_112866 : Type'} (_60767 : type1402 _112866) : (term399 _112866 _60767) = (term405 _112866 _60767).
Proof. exact (MK_COMB (@lem4904017 _112866) (@lem4904016 _112866 _60767)). Qed.
Lemma lem4904019 {_112866 : Type'} (_60767 : type1402 _112866) : ((_60767 = (term285 _112866)) = (term399 _112866 _60767)) = ((_60767 = (term214 _112866)) = (term405 _112866 _60767)).
Proof. exact (MK_COMB (@lem4904012 _112866 _60767) (@lem4904018 _112866 _60767)). Qed.
Lemma lem4904020 {_112866 : Type'} (_60767 : type1402 _112866) : (_60767 = (term214 _112866)) = (term405 _112866 _60767).
Proof. exact (EQ_MP (@lem4904019 _112866 _60767) (@lem4904006 _112866 _60767)). Qed.
Lemma lem4904021 {_112866 : Type'} (_60767 : type1402 _112866) (x : _112866) : ((_60767 x) = (term284 _112866 x)) = ((_60767 x) = (term284 _112866 x)).
Proof. exact (eq_refl ((_60767 x) = (term284 _112866 x))). Qed.
Lemma lem4904022 {_112866 : Type'} (_60767 : type1402 _112866) : (term404 _112866 _60767) = (term404 _112866 _60767).
Proof. exact (fun_ext (fun x : _112866 => @lem4904021 _112866 _60767 x)). Qed.
Lemma lem4904023 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4904024 {_112866 : Type'} (_60767 : type1402 _112866) : (term405 _112866 _60767) = (term405 _112866 _60767).
Proof. exact (MK_COMB (@lem4904023 _112866) (@lem4904022 _112866 _60767)). Qed.
Lemma lem4904025 {_112866 : Type'} (_60767 : type1402 _112866) : (_60767 = (term214 _112866)) = (term405 _112866 _60767).
Proof. exact (TRANS (@lem4904020 _112866 _60767) (@lem4904024 _112866 _60767)). Qed.
Lemma lem4904026 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4904027 {_112866 : Type'} (_60767 : type1402 _112866) : (term381 _112866 _60767) = (term406 _112866 _60767).
Proof. exact (MK_COMB (@lem4904026) (@lem4904025 _112866 _60767)). Qed.
Lemma lem4904028 {_112866 : Type'} (_60767 : type1402 _112866) : (term640 _112866 _60767) = (term640 _112866 _60767).
Proof. exact (eq_refl (term640 _112866 _60767)). Qed.
Lemma lem4904029 {_112866 : Type'} (_60767 : type1402 _112866) : (term654 _112866 _60767) = (term660 _112866 _60767).
Proof. exact (MK_COMB (@lem4904027 _112866 _60767) (@lem4904028 _112866 _60767)). Qed.
Lemma lem4904030 {_112866 : Type'} : (term656 _112866) = (term661 _112866).
Proof. exact (fun_ext (fun _60767 : type1402 _112866 => @lem4904029 _112866 _60767)). Qed.
Lemma lem4904031 {_112866 : Type'} : (@all (_112866 -> _112866 -> Prop)) = (@all (_112866 -> _112866 -> Prop)).
Proof. exact (eq_refl (@all (_112866 -> _112866 -> Prop))). Qed.
Lemma lem4904032 {_112866 : Type'} : (term658 _112866) = (term662 _112866).
Proof. exact (MK_COMB (@lem4904031 _112866) (@lem4904030 _112866)). Qed.
Lemma lem4904033 {_112866 : Type'} : (term646 _112866) = (term646 _112866).
Proof. exact (eq_refl (term646 _112866)). Qed.
Lemma lem4904034 {_112866 : Type'} : ((term630 _112866) = (term658 _112866)) = ((term630 _112866) = (term662 _112866)).
Proof. exact (MK_COMB (@lem4904033 _112866) (@lem4904032 _112866)). Qed.
Lemma lem4904035 {_112866 : Type'} : (term630 _112866) = (term662 _112866).
Proof. exact (EQ_MP (@lem4904034 _112866) (@lem4904002 _112866)). Qed.
Lemma lem4904036 {_112866 : Type'} (_60768 : type1402 _112866) (h1 : _60768 = (term214 _112866)) : _60768 = (term214 _112866).
Proof. exact (h1). Qed.
Lemma lem4904037 {_112866 : Type'} (x : _112866) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4904038 {_112866 : Type'} (x : _112866) (_60768 : type1402 _112866) (h1 : _60768 = (term214 _112866)) : (_60768 x) = (term269 _112866 x).
Proof. exact (MK_COMB (@lem4904036 _112866 _60768 h1) (@lem4904037 _112866 x)). Qed.
Lemma lem4904039 {_112866 : Type'} (x : _112866) : (term269 _112866 x) = (term284 _112866 x).
Proof. exact (eq_refl (term269 _112866 x)). Qed.
Lemma lem4904040 {_112866 : Type'} (_60768 : type1402 _112866) (x : _112866) : (term402 _112866 _60768 x) = (term402 _112866 _60768 x).
Proof. exact (eq_refl (term402 _112866 _60768 x)). Qed.
Lemma lem4904041 {_112866 : Type'} (_60768 : type1402 _112866) (x : _112866) : ((_60768 x) = (term269 _112866 x)) = ((_60768 x) = (term284 _112866 x)).
Proof. exact (MK_COMB (@lem4904040 _112866 _60768 x) (@lem4904039 _112866 x)). Qed.
Lemma lem4904042 {_112866 : Type'} (x : _112866) (_60768 : type1402 _112866) (h1 : _60768 = (term214 _112866)) : (_60768 x) = (term284 _112866 x).
Proof. exact (EQ_MP (@lem4904041 _112866 _60768 x) (@lem4904038 _112866 x _60768 h1)). Qed.
Lemma lem4904054 {_112866 : Type'} (l : list _112866) : (term357 _112866 l) = (term357 _112866 l).
Proof. exact (eq_refl (term357 _112866 l)). Qed.
Lemma lem4904055 {_112866 : Type'} : (term358 _112866) = (term358 _112866).
Proof. exact (fun_ext (fun l : list _112866 => @lem4904054 _112866 l)). Qed.
Lemma lem4904056 {_112866 : Type'} : (@all (list _112866)) = (@all (list _112866)).
Proof. exact (eq_refl (@all (list _112866))). Qed.
Lemma lem4904057 {_112866 : Type'} : (term333 _112866) = (term333 _112866).
Proof. exact (MK_COMB (@lem4904056 _112866) (@lem4904055 _112866)). Qed.
Lemma lem4904058 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4904059 {_112866 : Type'} : (term339 _112866) = (term339 _112866).
Proof. exact (MK_COMB (@lem4904058) (@lem4904057 _112866)). Qed.
Lemma lem4904068 (n : nat) : (term5 n) = (term5 n).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem4904069 : term359 = term359.
Proof. exact (fun_ext (fun n : nat => @lem4904068 n)). Qed.
Lemma lem4904070 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4904071 : term152 = term152.
Proof. exact (MK_COMB (@lem4904070) (@lem4904069)). Qed.
Lemma lem4904072 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4904073 : term340 = term340.
Proof. exact (MK_COMB (@lem4904072) (@lem4904071)). Qed.
Lemma lem4904074 {_112866 : Type'} : (term342 _112866) = (term342 _112866).
Proof. exact (MK_COMB (@lem4904073) (@lem4904059 _112866)). Qed.
Lemma lem4904079 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (@List.ForallOrdPairs _112866 _60767 t) = (@List.ForallOrdPairs _112866 _60767 t).
Proof. exact (eq_refl (@List.ForallOrdPairs _112866 _60767 t)). Qed.
Lemma lem4904094 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term298 _112866 t h x) = (term298 _112866 t h x).
Proof. exact (eq_refl (term298 _112866 t h x)). Qed.
Lemma lem4904095 {_112866 : Type'} (t : list _112866) (h : _112866) : (term300 _112866 t h) = (term300 _112866 t h).
Proof. exact (fun_ext (fun x : _112866 => @lem4904094 _112866 t h x)). Qed.
Lemma lem4904096 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4904097 {_112866 : Type'} (t : list _112866) (h : _112866) : (term301 _112866 t h) = (term301 _112866 t h).
Proof. exact (MK_COMB (@lem4904096 _112866) (@lem4904095 _112866 t h)). Qed.
Lemma lem4904098 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4904099 {_112866 : Type'} (t : list _112866) (h : _112866) : (term303 _112866 t h) = (term303 _112866 t h).
Proof. exact (MK_COMB (@lem4904098) (@lem4904097 _112866 t h)). Qed.
Lemma lem4904100 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term361 _112866 h _60767 t) = (term361 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904099 _112866 t h) (@lem4904079 _112866 _60767 t)). Qed.
Lemma lem4904107 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (term631 _112866 _60767 t) = (term631 _112866 _60767 t).
Proof. exact (eq_refl (term631 _112866 _60767 t)). Qed.
Lemma lem4904108 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : ((@List.ForallOrdPairs _112866 _60767 t) = (term361 _112866 h _60767 t)) = ((@List.ForallOrdPairs _112866 _60767 t) = (term361 _112866 h _60767 t)).
Proof. exact (MK_COMB (@lem4904107 _112866 _60767 t) (@lem4904100 _112866 h _60767 t)). Qed.
Lemma lem4904109 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4904110 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term632 _112866 h _60767 t) = (term632 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904109) (@lem4904108 _112866 h _60767 t)). Qed.
Lemma lem4904111 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4904112 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term633 _112866 h _60767 t) = (term633 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904111) (@lem4904110 _112866 h _60767 t)). Qed.
Lemma lem4904113 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term634 _112866 h _60767 t) = (term634 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904112 _112866 h _60767 t) (@lem4904074 _112866)). Qed.
Lemma lem4904122 {_112866 : Type'} (h : _112866) (t : list _112866) : (term313 _112866 h t) = (term313 _112866 h t).
Proof. exact (eq_refl (term313 _112866 h t)). Qed.
Lemma lem4904123 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term635 _112866 h _60767 t) = (term635 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904122 _112866 h t) (@lem4904113 _112866 h _60767 t)). Qed.
Lemma lem4904144 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (term367 _112866 _60767 t) = (term367 _112866 _60767 t).
Proof. exact (eq_refl (term367 _112866 _60767 t)). Qed.
Lemma lem4904145 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term636 _112866 h _60767 t) = (term636 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904144 _112866 _60767 t) (@lem4904123 _112866 h _60767 t)). Qed.
Lemma lem4904146 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (term637 _112866 _60767 t) = (term637 _112866 _60767 t).
Proof. exact (fun_ext (fun h : _112866 => @lem4904145 _112866 h _60767 t)). Qed.
Lemma lem4904147 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4904148 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (term638 _112866 _60767 t) = (term638 _112866 _60767 t).
Proof. exact (MK_COMB (@lem4904147 _112866) (@lem4904146 _112866 _60767 t)). Qed.
Lemma lem4904149 {_112866 : Type'} (_60767 : type1402 _112866) : (term639 _112866 _60767) = (term639 _112866 _60767).
Proof. exact (fun_ext (fun t : list _112866 => @lem4904148 _112866 _60767 t)). Qed.
Lemma lem4904150 {_112866 : Type'} : (@all (list _112866)) = (@all (list _112866)).
Proof. exact (eq_refl (@all (list _112866))). Qed.
Lemma lem4904151 {_112866 : Type'} (_60767 : type1402 _112866) : (term640 _112866 _60767) = (term640 _112866 _60767).
Proof. exact (MK_COMB (@lem4904150 _112866) (@lem4904149 _112866 _60767)). Qed.
Lemma lem4904153 {_112866 : Type'} (x : _112866) (_60768 : type1402 _112866) (h1 : _60768 = (term214 _112866)) : (term284 _112866 x) = (_60768 x).
Proof. exact (SYM (@lem4904042 _112866 x _60768 h1)). Qed.
Lemma lem4904154 {_112866 : Type'} (x : _112866) (_60768 : type1402 _112866) (h1 : _60768 = (term214 _112866)) : (term284 _112866 x) = (_60768 x).
Proof. exact (@lem4904153 _112866 x _60768 h1). Qed.
Lemma lem4904159 {_112866 : Type'} (_60767 : type1402 _112866) (x : _112866) : (term402 _112866 _60767 x) = (term402 _112866 _60767 x).
Proof. exact (eq_refl (term402 _112866 _60767 x)). Qed.
Lemma lem4904160 {_112866 : Type'} (_60767 : type1402 _112866) (x : _112866) (_60768 : type1402 _112866) (h1 : _60768 = (term214 _112866)) : ((_60767 x) = (term284 _112866 x)) = ((_60767 x) = (_60768 x)).
Proof. exact (MK_COMB (@lem4904159 _112866 _60767 x) (@lem4904154 _112866 x _60768 h1)). Qed.
Lemma lem4904161 {_112866 : Type'} (_60767 : type1402 _112866) (_60768 : type1402 _112866) (h1 : _60768 = (term214 _112866)) : (term404 _112866 _60767) = (term410 _112866 _60767 _60768).
Proof. exact (fun_ext (fun x : _112866 => @lem4904160 _112866 _60767 x _60768 h1)). Qed.
Lemma lem4904162 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4904163 {_112866 : Type'} (_60767 : type1402 _112866) (_60768 : type1402 _112866) (h1 : _60768 = (term214 _112866)) : (term405 _112866 _60767) = (term398 _112866 _60767 _60768).
Proof. exact (MK_COMB (@lem4904162 _112866) (@lem4904161 _112866 _60767 _60768 h1)). Qed.
Lemma lem4904164 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4904165 {_112866 : Type'} (_60767 : type1402 _112866) (_60768 : type1402 _112866) (h1 : _60768 = (term214 _112866)) : (term406 _112866 _60767) = (term411 _112866 _60767 _60768).
Proof. exact (MK_COMB (@lem4904164) (@lem4904163 _112866 _60767 _60768 h1)). Qed.
Lemma lem4904166 {_112866 : Type'} (_60767 : type1402 _112866) (_60768 : type1402 _112866) (h1 : _60768 = (term214 _112866)) : (term660 _112866 _60767) = (term663 _112866 _60768 _60767).
Proof. exact (MK_COMB (@lem4904165 _112866 _60767 _60768 h1) (@lem4904151 _112866 _60767)). Qed.
Lemma lem4904167 {_112866 : Type'} (_60768 : type1402 _112866) (h1 : _60768 = (term214 _112866)) : (term661 _112866) = (term664 _112866 _60768).
Proof. exact (fun_ext (fun _60767 : type1402 _112866 => @lem4904166 _112866 _60767 _60768 h1)). Qed.
Lemma lem4904168 {_112866 : Type'} : (@all (_112866 -> _112866 -> Prop)) = (@all (_112866 -> _112866 -> Prop)).
Proof. exact (eq_refl (@all (_112866 -> _112866 -> Prop))). Qed.
Lemma lem4904169 {_112866 : Type'} (_60768 : type1402 _112866) (h1 : _60768 = (term214 _112866)) : (term662 _112866) = (term665 _112866 _60768).
Proof. exact (MK_COMB (@lem4904168 _112866) (@lem4904167 _112866 _60768 h1)). Qed.
Lemma lem4904170 {_112866 : Type'} (_60768 : type1402 _112866) : term666 _112866 _60768.
Proof. exact (fun h0 : _60768 = (term214 _112866) => @lem4904169 _112866 _60768 h0). Qed.
Lemma lem4904171 {_112866 : Type'} : term667 _112866.
Proof. exact (fun _60768 : type1402 _112866 => @lem4904170 _112866 _60768). Qed.
Lemma lem4904173 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term375 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem4904174 {_112866 : Type'} (P : Prop) (c : type1402 _112866) (Q : type421 _112866) : term376 _112866 P c Q.
Proof. exact (@lem4904173 (type1402 _112866) P c Q). Qed.
Lemma lem4904175 {_112866 : Type'} : term668 _112866.
Proof. exact (@lem4904174 _112866 (term662 _112866) (term214 _112866) (term669 _112866)). Qed.
Lemma lem4904176 {_112866 : Type'} (_60768 : type1402 _112866) : (term670 _112866 _60768) = (term665 _112866 _60768).
Proof. exact (eq_refl (term670 _112866 _60768)). Qed.
Lemma lem4904177 {_112866 : Type'} : (term671 _112866) = (term671 _112866).
Proof. exact (eq_refl (term671 _112866)). Qed.
Lemma lem4904178 {_112866 : Type'} (_60768 : type1402 _112866) : ((term662 _112866) = (term670 _112866 _60768)) = ((term662 _112866) = (term665 _112866 _60768)).
Proof. exact (MK_COMB (@lem4904177 _112866) (@lem4904176 _112866 _60768)). Qed.
Lemma lem4904179 {_112866 : Type'} (_60768 : type1402 _112866) : (term381 _112866 _60768) = (term381 _112866 _60768).
Proof. exact (eq_refl (term381 _112866 _60768)). Qed.
Lemma lem4904180 {_112866 : Type'} (_60768 : type1402 _112866) : (term672 _112866 _60768) = (term666 _112866 _60768).
Proof. exact (MK_COMB (@lem4904179 _112866 _60768) (@lem4904178 _112866 _60768)). Qed.
Lemma lem4904181 {_112866 : Type'} : (term673 _112866) = (term674 _112866).
Proof. exact (fun_ext (fun _60768 : type1402 _112866 => @lem4904180 _112866 _60768)). Qed.
Lemma lem4904182 {_112866 : Type'} : (@all (_112866 -> _112866 -> Prop)) = (@all (_112866 -> _112866 -> Prop)).
Proof. exact (eq_refl (@all (_112866 -> _112866 -> Prop))). Qed.
Lemma lem4904183 {_112866 : Type'} : (term675 _112866) = (term667 _112866).
Proof. exact (MK_COMB (@lem4904182 _112866) (@lem4904181 _112866)). Qed.
Lemma lem4904184 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4904185 {_112866 : Type'} : (term676 _112866) = (term677 _112866).
Proof. exact (MK_COMB (@lem4904184) (@lem4904183 _112866)). Qed.
Lemma lem4904186 {_112866 : Type'} (_60768 : type1402 _112866) : (term670 _112866 _60768) = (term665 _112866 _60768).
Proof. exact (eq_refl (term670 _112866 _60768)). Qed.
Lemma lem4904187 {_112866 : Type'} (_60768 : type1402 _112866) : (term381 _112866 _60768) = (term381 _112866 _60768).
Proof. exact (eq_refl (term381 _112866 _60768)). Qed.
Lemma lem4904188 {_112866 : Type'} (_60768 : type1402 _112866) : (term678 _112866 _60768) = (term679 _112866 _60768).
Proof. exact (MK_COMB (@lem4904187 _112866 _60768) (@lem4904186 _112866 _60768)). Qed.
Lemma lem4904189 {_112866 : Type'} : (term680 _112866) = (term681 _112866).
Proof. exact (fun_ext (fun _60768 : type1402 _112866 => @lem4904188 _112866 _60768)). Qed.
Lemma lem4904190 {_112866 : Type'} : (@all (_112866 -> _112866 -> Prop)) = (@all (_112866 -> _112866 -> Prop)).
Proof. exact (eq_refl (@all (_112866 -> _112866 -> Prop))). Qed.
Lemma lem4904191 {_112866 : Type'} : (term682 _112866) = (term683 _112866).
Proof. exact (MK_COMB (@lem4904190 _112866) (@lem4904189 _112866)). Qed.
Lemma lem4904192 {_112866 : Type'} : (term671 _112866) = (term671 _112866).
Proof. exact (eq_refl (term671 _112866)). Qed.
Lemma lem4904193 {_112866 : Type'} : ((term662 _112866) = (term682 _112866)) = ((term662 _112866) = (term683 _112866)).
Proof. exact (MK_COMB (@lem4904192 _112866) (@lem4904191 _112866)). Qed.
Lemma lem4904194 {_112866 : Type'} : (term668 _112866) = (term684 _112866).
Proof. exact (MK_COMB (@lem4904185 _112866) (@lem4904193 _112866)). Qed.
Lemma lem4904195 {_112866 : Type'} : term684 _112866.
Proof. exact (EQ_MP (@lem4904194 _112866) (@lem4904175 _112866)). Qed.
Lemma lem4904196 {_112866 : Type'} : (term662 _112866) = (term683 _112866).
Proof. exact (@lem4904195 _112866 (@lem4904171 _112866)). Qed.
Lemma lem4904198 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term395 _3571 _3575 t)) = (term396 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem4904199 {_112866 : Type'} (s : type1402 _112866) (t : type1402 _112866) : (s = (term397 _112866 t)) = (term398 _112866 s t).
Proof. exact (@lem4904198 (_112866 -> Prop) _112866 s t). Qed.
Lemma lem4904200 {_112866 : Type'} (_60768 : type1402 _112866) : (_60768 = (term285 _112866)) = (term399 _112866 _60768).
Proof. exact (@lem4904199 _112866 _60768 (term214 _112866)). Qed.
Lemma lem4904201 {_112866 : Type'} (x : _112866) : (term269 _112866 x) = (term284 _112866 x).
Proof. exact (eq_refl (term269 _112866 x)). Qed.
Lemma lem4904202 {_112866 : Type'} : (term285 _112866) = (term214 _112866).
Proof. exact (fun_ext (fun x : _112866 => @lem4904201 _112866 x)). Qed.
Lemma lem4904203 {_112866 : Type'} (_60768 : type1402 _112866) : (@eq (_112866 -> _112866 -> Prop) _60768) = (@eq (_112866 -> _112866 -> Prop) _60768).
Proof. exact (eq_refl (@eq (_112866 -> _112866 -> Prop) _60768)). Qed.
Lemma lem4904204 {_112866 : Type'} (_60768 : type1402 _112866) : (_60768 = (term285 _112866)) = (_60768 = (term214 _112866)).
Proof. exact (MK_COMB (@lem4904203 _112866 _60768) (@lem4904202 _112866)). Qed.
Lemma lem4904205 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4904206 {_112866 : Type'} (_60768 : type1402 _112866) : (term400 _112866 _60768) = (term401 _112866 _60768).
Proof. exact (MK_COMB (@lem4904205) (@lem4904204 _112866 _60768)). Qed.
Lemma lem4904207 {_112866 : Type'} (x : _112866) : (term269 _112866 x) = (term284 _112866 x).
Proof. exact (eq_refl (term269 _112866 x)). Qed.
Lemma lem4904208 {_112866 : Type'} (_60768 : type1402 _112866) (x : _112866) : (term402 _112866 _60768 x) = (term402 _112866 _60768 x).
Proof. exact (eq_refl (term402 _112866 _60768 x)). Qed.
Lemma lem4904209 {_112866 : Type'} (_60768 : type1402 _112866) (x : _112866) : ((_60768 x) = (term269 _112866 x)) = ((_60768 x) = (term284 _112866 x)).
Proof. exact (MK_COMB (@lem4904208 _112866 _60768 x) (@lem4904207 _112866 x)). Qed.
Lemma lem4904210 {_112866 : Type'} (_60768 : type1402 _112866) : (term403 _112866 _60768) = (term404 _112866 _60768).
Proof. exact (fun_ext (fun x : _112866 => @lem4904209 _112866 _60768 x)). Qed.
Lemma lem4904211 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4904212 {_112866 : Type'} (_60768 : type1402 _112866) : (term399 _112866 _60768) = (term405 _112866 _60768).
Proof. exact (MK_COMB (@lem4904211 _112866) (@lem4904210 _112866 _60768)). Qed.
Lemma lem4904213 {_112866 : Type'} (_60768 : type1402 _112866) : ((_60768 = (term285 _112866)) = (term399 _112866 _60768)) = ((_60768 = (term214 _112866)) = (term405 _112866 _60768)).
Proof. exact (MK_COMB (@lem4904206 _112866 _60768) (@lem4904212 _112866 _60768)). Qed.
Lemma lem4904214 {_112866 : Type'} (_60768 : type1402 _112866) : (_60768 = (term214 _112866)) = (term405 _112866 _60768).
Proof. exact (EQ_MP (@lem4904213 _112866 _60768) (@lem4904200 _112866 _60768)). Qed.
Lemma lem4904216 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term395 _3571 _3575 t)) = (term396 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem4904217 {_112866 : Type'} (s : _112866 -> Prop) (t : _112866 -> Prop) : (s = (term434 _112866 t)) = (term435 _112866 s t).
Proof. exact (@lem4904216 Prop _112866 s t). Qed.
Lemma lem4904218 {_112866 : Type'} (_60768 : type1402 _112866) (x : _112866) : ((_60768 x) = (term292 _112866 x)) = (term436 _112866 _60768 x).
Proof. exact (@lem4904217 _112866 (_60768 x) (term284 _112866 x)). Qed.
Lemma lem4904219 {_112866 : Type'} (x : _112866) (y : _112866) : (term288 _112866 x y) = (term291 _112866 x y).
Proof. exact (eq_refl (term288 _112866 x y)). Qed.
Lemma lem4904220 {_112866 : Type'} (x : _112866) : (term292 _112866 x) = (term284 _112866 x).
Proof. exact (fun_ext (fun y : _112866 => @lem4904219 _112866 x y)). Qed.
Lemma lem4904221 {_112866 : Type'} (_60768 : type1402 _112866) (x : _112866) : (term402 _112866 _60768 x) = (term402 _112866 _60768 x).
Proof. exact (eq_refl (term402 _112866 _60768 x)). Qed.
Lemma lem4904222 {_112866 : Type'} (_60768 : type1402 _112866) (x : _112866) : ((_60768 x) = (term292 _112866 x)) = ((_60768 x) = (term284 _112866 x)).
Proof. exact (MK_COMB (@lem4904221 _112866 _60768 x) (@lem4904220 _112866 x)). Qed.
Lemma lem4904223 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4904224 {_112866 : Type'} (_60768 : type1402 _112866) (x : _112866) : (term437 _112866 _60768 x) = (term438 _112866 _60768 x).
Proof. exact (MK_COMB (@lem4904223) (@lem4904222 _112866 _60768 x)). Qed.
Lemma lem4904225 {_112866 : Type'} (x : _112866) (y : _112866) : (term288 _112866 x y) = (term291 _112866 x y).
Proof. exact (eq_refl (term288 _112866 x y)). Qed.
Lemma lem4904226 {_112866 : Type'} (_60768 : type1402 _112866) (x : _112866) (y : _112866) : (term439 _112866 _60768 x y) = (term439 _112866 _60768 x y).
Proof. exact (eq_refl (term439 _112866 _60768 x y)). Qed.
Lemma lem4904227 {_112866 : Type'} (_60768 : type1402 _112866) (x : _112866) (y : _112866) : ((_60768 x y) = (term288 _112866 x y)) = ((_60768 x y) = (term291 _112866 x y)).
Proof. exact (MK_COMB (@lem4904226 _112866 _60768 x y) (@lem4904225 _112866 x y)). Qed.
Lemma lem4904228 {_112866 : Type'} (_60768 : type1402 _112866) (x : _112866) : (term440 _112866 _60768 x) = (term441 _112866 _60768 x).
Proof. exact (fun_ext (fun y : _112866 => @lem4904227 _112866 _60768 x y)). Qed.
Lemma lem4904229 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4904230 {_112866 : Type'} (_60768 : type1402 _112866) (x : _112866) : (term436 _112866 _60768 x) = (term442 _112866 _60768 x).
Proof. exact (MK_COMB (@lem4904229 _112866) (@lem4904228 _112866 _60768 x)). Qed.
Lemma lem4904231 {_112866 : Type'} (_60768 : type1402 _112866) (x : _112866) : (((_60768 x) = (term292 _112866 x)) = (term436 _112866 _60768 x)) = (((_60768 x) = (term284 _112866 x)) = (term442 _112866 _60768 x)).
Proof. exact (MK_COMB (@lem4904224 _112866 _60768 x) (@lem4904230 _112866 _60768 x)). Qed.
Lemma lem4904232 {_112866 : Type'} (_60768 : type1402 _112866) (x : _112866) : ((_60768 x) = (term284 _112866 x)) = (term442 _112866 _60768 x).
Proof. exact (EQ_MP (@lem4904231 _112866 _60768 x) (@lem4904218 _112866 _60768 x)). Qed.
Lemma lem4904233 {_112866 : Type'} (_60768 : type1402 _112866) (x : _112866) (y : _112866) : ((_60768 x y) = (term291 _112866 x y)) = ((_60768 x y) = (term291 _112866 x y)).
Proof. exact (eq_refl ((_60768 x y) = (term291 _112866 x y))). Qed.
Lemma lem4904234 {_112866 : Type'} (_60768 : type1402 _112866) (x : _112866) : (term441 _112866 _60768 x) = (term441 _112866 _60768 x).
Proof. exact (fun_ext (fun y : _112866 => @lem4904233 _112866 _60768 x y)). Qed.
Lemma lem4904235 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4904236 {_112866 : Type'} (_60768 : type1402 _112866) (x : _112866) : (term442 _112866 _60768 x) = (term442 _112866 _60768 x).
Proof. exact (MK_COMB (@lem4904235 _112866) (@lem4904234 _112866 _60768 x)). Qed.
Lemma lem4904237 {_112866 : Type'} (_60768 : type1402 _112866) (x : _112866) : ((_60768 x) = (term284 _112866 x)) = (term442 _112866 _60768 x).
Proof. exact (TRANS (@lem4904232 _112866 _60768 x) (@lem4904236 _112866 _60768 x)). Qed.
Lemma lem4904238 {_112866 : Type'} (_60768 : type1402 _112866) : (term404 _112866 _60768) = (term443 _112866 _60768).
Proof. exact (fun_ext (fun x : _112866 => @lem4904237 _112866 _60768 x)). Qed.
Lemma lem4904239 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4904240 {_112866 : Type'} (_60768 : type1402 _112866) : (term405 _112866 _60768) = (term444 _112866 _60768).
Proof. exact (MK_COMB (@lem4904239 _112866) (@lem4904238 _112866 _60768)). Qed.
Lemma lem4904241 {_112866 : Type'} (_60768 : type1402 _112866) : (_60768 = (term214 _112866)) = (term444 _112866 _60768).
Proof. exact (TRANS (@lem4904214 _112866 _60768) (@lem4904240 _112866 _60768)). Qed.
Lemma lem4904242 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4904243 {_112866 : Type'} (_60768 : type1402 _112866) : (term381 _112866 _60768) = (term445 _112866 _60768).
Proof. exact (MK_COMB (@lem4904242) (@lem4904241 _112866 _60768)). Qed.
Lemma lem4904244 {_112866 : Type'} (_60768 : type1402 _112866) : (term665 _112866 _60768) = (term665 _112866 _60768).
Proof. exact (eq_refl (term665 _112866 _60768)). Qed.
Lemma lem4904245 {_112866 : Type'} (_60768 : type1402 _112866) : (term679 _112866 _60768) = (term685 _112866 _60768).
Proof. exact (MK_COMB (@lem4904243 _112866 _60768) (@lem4904244 _112866 _60768)). Qed.
Lemma lem4904246 {_112866 : Type'} : (term681 _112866) = (term686 _112866).
Proof. exact (fun_ext (fun _60768 : type1402 _112866 => @lem4904245 _112866 _60768)). Qed.
Lemma lem4904247 {_112866 : Type'} : (@all (_112866 -> _112866 -> Prop)) = (@all (_112866 -> _112866 -> Prop)).
Proof. exact (eq_refl (@all (_112866 -> _112866 -> Prop))). Qed.
Lemma lem4904248 {_112866 : Type'} : (term683 _112866) = (term687 _112866).
Proof. exact (MK_COMB (@lem4904247 _112866) (@lem4904246 _112866)). Qed.
Lemma lem4904249 {_112866 : Type'} : (term671 _112866) = (term671 _112866).
Proof. exact (eq_refl (term671 _112866)). Qed.
Lemma lem4904250 {_112866 : Type'} : ((term662 _112866) = (term683 _112866)) = ((term662 _112866) = (term687 _112866)).
Proof. exact (MK_COMB (@lem4904249 _112866) (@lem4904248 _112866)). Qed.
Lemma lem4904253 {_112866 : Type'} : (term662 _112866) = (term687 _112866).
Proof. exact (EQ_MP (@lem4904250 _112866) (@lem4904196 _112866)). Qed.
Lemma lem4904254 {_112866 : Type'} : (term630 _112866) = (term687 _112866).
Proof. exact (TRANS (@lem4904035 _112866) (@lem4904253 _112866)). Qed.
Lemma lem4904255 {_112866 : Type'} : (term629 _112866) = (term687 _112866).
Proof. exact (TRANS (@lem4903859 _112866) (@lem4904254 _112866)). Qed.
Lemma lem4904256 {_112866 : Type'} (l : list _112866) : (term357 _112866 l) = (term357 _112866 l).
Proof. exact (eq_refl (term357 _112866 l)). Qed.
Lemma lem4904257 {_112866 : Type'} : (term358 _112866) = (term358 _112866).
Proof. exact (fun_ext (fun l : list _112866 => @lem4904256 _112866 l)). Qed.
Lemma lem4904258 {_112866 : Type'} : (@all (list _112866)) = (@all (list _112866)).
Proof. exact (eq_refl (@all (list _112866))). Qed.
Lemma lem4904259 {_112866 : Type'} : (term333 _112866) = (term333 _112866).
Proof. exact (MK_COMB (@lem4904258 _112866) (@lem4904257 _112866)). Qed.
Lemma lem4904260 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4904261 {_112866 : Type'} : (term339 _112866) = (term339 _112866).
Proof. exact (MK_COMB (@lem4904260) (@lem4904259 _112866)). Qed.
Lemma lem4904264 (n : nat) : (term5 n) = (term5 n).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem4904265 : term359 = term359.
Proof. exact (fun_ext (fun n : nat => @lem4904264 n)). Qed.
Lemma lem4904266 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4904267 : term152 = term152.
Proof. exact (MK_COMB (@lem4904266) (@lem4904265)). Qed.
Lemma lem4904268 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4904269 : term340 = term340.
Proof. exact (MK_COMB (@lem4904268) (@lem4904267)). Qed.
Lemma lem4904270 {_112866 : Type'} : (term342 _112866) = (term342 _112866).
Proof. exact (MK_COMB (@lem4904269) (@lem4904261 _112866)). Qed.
Lemma lem4904271 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (@List.ForallOrdPairs _112866 _60767 t) = (@List.ForallOrdPairs _112866 _60767 t).
Proof. exact (eq_refl (@List.ForallOrdPairs _112866 _60767 t)). Qed.
Lemma lem4904278 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term298 _112866 t h x) = (term298 _112866 t h x).
Proof. exact (eq_refl (term298 _112866 t h x)). Qed.
Lemma lem4904279 {_112866 : Type'} (t : list _112866) (h : _112866) : (term300 _112866 t h) = (term300 _112866 t h).
Proof. exact (fun_ext (fun x : _112866 => @lem4904278 _112866 t h x)). Qed.
Lemma lem4904280 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4904281 {_112866 : Type'} (t : list _112866) (h : _112866) : (term301 _112866 t h) = (term301 _112866 t h).
Proof. exact (MK_COMB (@lem4904280 _112866) (@lem4904279 _112866 t h)). Qed.
Lemma lem4904282 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4904283 {_112866 : Type'} (t : list _112866) (h : _112866) : (term303 _112866 t h) = (term303 _112866 t h).
Proof. exact (MK_COMB (@lem4904282) (@lem4904281 _112866 t h)). Qed.
Lemma lem4904284 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term361 _112866 h _60767 t) = (term361 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904283 _112866 t h) (@lem4904271 _112866 _60767 t)). Qed.
Lemma lem4904287 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (term631 _112866 _60767 t) = (term631 _112866 _60767 t).
Proof. exact (eq_refl (term631 _112866 _60767 t)). Qed.
Lemma lem4904288 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : ((@List.ForallOrdPairs _112866 _60767 t) = (term361 _112866 h _60767 t)) = ((@List.ForallOrdPairs _112866 _60767 t) = (term361 _112866 h _60767 t)).
Proof. exact (MK_COMB (@lem4904287 _112866 _60767 t) (@lem4904284 _112866 h _60767 t)). Qed.
Lemma lem4904289 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4904290 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term632 _112866 h _60767 t) = (term632 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904289) (@lem4904288 _112866 h _60767 t)). Qed.
Lemma lem4904291 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4904292 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term633 _112866 h _60767 t) = (term633 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904291) (@lem4904290 _112866 h _60767 t)). Qed.
Lemma lem4904293 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term634 _112866 h _60767 t) = (term634 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904292 _112866 h _60767 t) (@lem4904270 _112866)). Qed.
Lemma lem4904298 {_112866 : Type'} (h : _112866) (t : list _112866) : (term313 _112866 h t) = (term313 _112866 h t).
Proof. exact (eq_refl (term313 _112866 h t)). Qed.
Lemma lem4904299 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term635 _112866 h _60767 t) = (term635 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904298 _112866 h t) (@lem4904293 _112866 h _60767 t)). Qed.
Lemma lem4904306 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (term367 _112866 _60767 t) = (term367 _112866 _60767 t).
Proof. exact (eq_refl (term367 _112866 _60767 t)). Qed.
Lemma lem4904307 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term636 _112866 h _60767 t) = (term636 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904306 _112866 _60767 t) (@lem4904299 _112866 h _60767 t)). Qed.
Lemma lem4904308 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (term637 _112866 _60767 t) = (term637 _112866 _60767 t).
Proof. exact (fun_ext (fun h : _112866 => @lem4904307 _112866 h _60767 t)). Qed.
Lemma lem4904309 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4904310 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (term638 _112866 _60767 t) = (term638 _112866 _60767 t).
Proof. exact (MK_COMB (@lem4904309 _112866) (@lem4904308 _112866 _60767 t)). Qed.
Lemma lem4904311 {_112866 : Type'} (_60767 : type1402 _112866) : (term639 _112866 _60767) = (term639 _112866 _60767).
Proof. exact (fun_ext (fun t : list _112866 => @lem4904310 _112866 _60767 t)). Qed.
Lemma lem4904312 {_112866 : Type'} : (@all (list _112866)) = (@all (list _112866)).
Proof. exact (eq_refl (@all (list _112866))). Qed.
Lemma lem4904313 {_112866 : Type'} (_60767 : type1402 _112866) : (term640 _112866 _60767) = (term640 _112866 _60767).
Proof. exact (MK_COMB (@lem4904312 _112866) (@lem4904311 _112866 _60767)). Qed.
Lemma lem4904314 {_112866 : Type'} (_60767 : type1402 _112866) (_60768 : type1402 _112866) (x : _112866) : ((_60767 x) = (_60768 x)) = ((_60767 x) = (_60768 x)).
Proof. exact (eq_refl ((_60767 x) = (_60768 x))). Qed.
Lemma lem4904315 {_112866 : Type'} (_60767 : type1402 _112866) (_60768 : type1402 _112866) : (term410 _112866 _60767 _60768) = (term410 _112866 _60767 _60768).
Proof. exact (fun_ext (fun x : _112866 => @lem4904314 _112866 _60767 _60768 x)). Qed.
Lemma lem4904316 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4904317 {_112866 : Type'} (_60767 : type1402 _112866) (_60768 : type1402 _112866) : (term398 _112866 _60767 _60768) = (term398 _112866 _60767 _60768).
Proof. exact (MK_COMB (@lem4904316 _112866) (@lem4904315 _112866 _60767 _60768)). Qed.
Lemma lem4904318 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4904319 {_112866 : Type'} (_60767 : type1402 _112866) (_60768 : type1402 _112866) : (term411 _112866 _60767 _60768) = (term411 _112866 _60767 _60768).
Proof. exact (MK_COMB (@lem4904318) (@lem4904317 _112866 _60767 _60768)). Qed.
Lemma lem4904320 {_112866 : Type'} (_60768 : type1402 _112866) (_60767 : type1402 _112866) : (term663 _112866 _60768 _60767) = (term663 _112866 _60768 _60767).
Proof. exact (MK_COMB (@lem4904319 _112866 _60767 _60768) (@lem4904313 _112866 _60767)). Qed.
Lemma lem4904321 {_112866 : Type'} (_60768 : type1402 _112866) : (term664 _112866 _60768) = (term664 _112866 _60768).
Proof. exact (fun_ext (fun _60767 : type1402 _112866 => @lem4904320 _112866 _60768 _60767)). Qed.
Lemma lem4904322 {_112866 : Type'} : (@all (_112866 -> _112866 -> Prop)) = (@all (_112866 -> _112866 -> Prop)).
Proof. exact (eq_refl (@all (_112866 -> _112866 -> Prop))). Qed.
Lemma lem4904323 {_112866 : Type'} (_60768 : type1402 _112866) : (term665 _112866 _60768) = (term665 _112866 _60768).
Proof. exact (MK_COMB (@lem4904322 _112866) (@lem4904321 _112866 _60768)). Qed.
Lemma lem4904330 {_112866 : Type'} (_60768 : type1402 _112866) (x : _112866) (y : _112866) : ((_60768 x y) = (term291 _112866 x y)) = ((_60768 x y) = (term291 _112866 x y)).
Proof. exact (eq_refl ((_60768 x y) = (term291 _112866 x y))). Qed.
Lemma lem4904331 {_112866 : Type'} (_60768 : type1402 _112866) (x : _112866) : (term441 _112866 _60768 x) = (term441 _112866 _60768 x).
Proof. exact (fun_ext (fun y : _112866 => @lem4904330 _112866 _60768 x y)). Qed.
Lemma lem4904332 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4904333 {_112866 : Type'} (_60768 : type1402 _112866) (x : _112866) : (term442 _112866 _60768 x) = (term442 _112866 _60768 x).
Proof. exact (MK_COMB (@lem4904332 _112866) (@lem4904331 _112866 _60768 x)). Qed.
Lemma lem4904334 {_112866 : Type'} (_60768 : type1402 _112866) : (term443 _112866 _60768) = (term443 _112866 _60768).
Proof. exact (fun_ext (fun x : _112866 => @lem4904333 _112866 _60768 x)). Qed.
Lemma lem4904335 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4904336 {_112866 : Type'} (_60768 : type1402 _112866) : (term444 _112866 _60768) = (term444 _112866 _60768).
Proof. exact (MK_COMB (@lem4904335 _112866) (@lem4904334 _112866 _60768)). Qed.
Lemma lem4904337 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4904338 {_112866 : Type'} (_60768 : type1402 _112866) : (term445 _112866 _60768) = (term445 _112866 _60768).
Proof. exact (MK_COMB (@lem4904337) (@lem4904336 _112866 _60768)). Qed.
Lemma lem4904339 {_112866 : Type'} (_60768 : type1402 _112866) : (term685 _112866 _60768) = (term685 _112866 _60768).
Proof. exact (MK_COMB (@lem4904338 _112866 _60768) (@lem4904323 _112866 _60768)). Qed.
Lemma lem4904340 {_112866 : Type'} : (term686 _112866) = (term686 _112866).
Proof. exact (fun_ext (fun _60768 : type1402 _112866 => @lem4904339 _112866 _60768)). Qed.
Lemma lem4904341 {_112866 : Type'} : (@all (_112866 -> _112866 -> Prop)) = (@all (_112866 -> _112866 -> Prop)).
Proof. exact (eq_refl (@all (_112866 -> _112866 -> Prop))). Qed.
Lemma lem4904342 {_112866 : Type'} : (term687 _112866) = (term687 _112866).
Proof. exact (MK_COMB (@lem4904341 _112866) (@lem4904340 _112866)). Qed.
Lemma lem4904421 {_112866 : Type'} : (term629 _112866) = (term687 _112866).
Proof. exact (TRANS (@lem4904255 _112866) (@lem4904342 _112866)). Qed.
Lemma lem4904422 {_112866 : Type'} : (term687 _112866) = (term629 _112866).
Proof. exact (SYM (@lem4904421 _112866)). Qed.
Lemma lem4904425 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60767 t)) : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60767 t).
Proof. exact (h1). Qed.
Lemma lem4904427 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term632 _112866 h _60767 t) : term632 _112866 h _60767 t.
Proof. exact (h1). Qed.
Lemma lem4904750 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60767 t)) = (term449 _112866 _60767 t).
Proof. exact (@lem17500 ((term171 _112866 t) = (@List.length _112866 t)) (@List.ForallOrdPairs _112866 _60767 t)). Qed.
Lemma lem4904757 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term257 _112866 h t) : term257 _112866 h t.
Proof. exact (h1). Qed.
Lemma lem4904765 {_112866 : Type'} (h : _112866) (x : _112866) : (term450 _112866 h x) = (h = x).
Proof. exact (@lem16933 (h = x)). Qed.
Lemma lem4904767 {_112866 : Type'} (x : _112866) (t : list _112866) : (term451 _112866 x t) = (term451 _112866 x t).
Proof. exact (eq_refl (term451 _112866 x t)). Qed.
Lemma lem4904768 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term452 _112866 t h x) = (term453 _112866 t h x).
Proof. exact (MK_COMB (@lem4904767 _112866 x t) (@lem4904765 _112866 h x)). Qed.
Lemma lem4904769 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term454 _112866 t h x) = (term452 _112866 t h x).
Proof. exact (@lem17362 (@List.In _112866 x t) (term291 _112866 h x)). Qed.
Lemma lem4904770 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term454 _112866 t h x) = (term453 _112866 t h x).
Proof. exact (TRANS (@lem4904769 _112866 t h x) (@lem4904768 _112866 t h x)). Qed.
Lemma lem4904775 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term298 _112866 t h x) = (term455 _112866 t h x).
Proof. exact (@lem17265 (@List.In _112866 x t) (term291 _112866 h x)). Qed.
Lemma lem4904776 {_112866 : Type'} (P : _112866 -> Prop) : (term456 _112866 P) = (term457 _112866 P).
Proof. exact (@lem18392 _112866 P). Qed.
Lemma lem4904777 {_112866 : Type'} (t : list _112866) (h : _112866) : (term458 _112866 t h) = (term459 _112866 t h).
Proof. exact (@lem4904776 _112866 (term300 _112866 t h)). Qed.
Lemma lem4904778 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term460 _112866 t h x) = (term298 _112866 t h x).
Proof. exact (eq_refl (term460 _112866 t h x)). Qed.
Lemma lem4904779 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4904780 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term461 _112866 t h x) = (term454 _112866 t h x).
Proof. exact (MK_COMB (@lem4904779) (@lem4904778 _112866 t h x)). Qed.
Lemma lem4904781 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term461 _112866 t h x) = (term453 _112866 t h x).
Proof. exact (TRANS (@lem4904780 _112866 t h x) (@lem4904770 _112866 t h x)). Qed.
Lemma lem4904782 {_112866 : Type'} (t : list _112866) (h : _112866) : (term462 _112866 t h) = (term463 _112866 t h).
Proof. exact (fun_ext (fun x : _112866 => @lem4904781 _112866 t h x)). Qed.
Lemma lem4904783 {_112866 : Type'} : (@ex _112866) = (@ex _112866).
Proof. exact (eq_refl (@ex _112866)). Qed.
Lemma lem4904784 {_112866 : Type'} (t : list _112866) (h : _112866) : (term459 _112866 t h) = (term464 _112866 t h).
Proof. exact (MK_COMB (@lem4904783 _112866) (@lem4904782 _112866 t h)). Qed.
Lemma lem4904785 {_112866 : Type'} (t : list _112866) (h : _112866) : (term458 _112866 t h) = (term464 _112866 t h).
Proof. exact (TRANS (@lem4904777 _112866 t h) (@lem4904784 _112866 t h)). Qed.
Lemma lem4904786 {_112866 : Type'} (t : list _112866) (h : _112866) : (term300 _112866 t h) = (term465 _112866 t h).
Proof. exact (fun_ext (fun x : _112866 => @lem4904775 _112866 t h x)). Qed.
Lemma lem4904787 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4904788 {_112866 : Type'} (t : list _112866) (h : _112866) : (term301 _112866 t h) = (term466 _112866 t h).
Proof. exact (MK_COMB (@lem4904787 _112866) (@lem4904786 _112866 t h)). Qed.
Lemma lem4904789 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (term467 _112866 _60767 t) = (term467 _112866 _60767 t).
Proof. exact (eq_refl (term467 _112866 _60767 t)). Qed.
Lemma lem4904790 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (@List.ForallOrdPairs _112866 _60767 t) = (@List.ForallOrdPairs _112866 _60767 t).
Proof. exact (eq_refl (@List.ForallOrdPairs _112866 _60767 t)). Qed.
Lemma lem4904791 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4904792 {_112866 : Type'} (t : list _112866) (h : _112866) : (term468 _112866 t h) = (term469 _112866 t h).
Proof. exact (MK_COMB (@lem4904791) (@lem4904785 _112866 t h)). Qed.
Lemma lem4904793 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term470 _112866 h _60767 t) = (term471 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904792 _112866 t h) (@lem4904789 _112866 _60767 t)). Qed.
Lemma lem4904794 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term472 _112866 h _60767 t) = (term470 _112866 h _60767 t).
Proof. exact (@lem17045 (term301 _112866 t h) (@List.ForallOrdPairs _112866 _60767 t)). Qed.
Lemma lem4904795 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term472 _112866 h _60767 t) = (term471 _112866 h _60767 t).
Proof. exact (TRANS (@lem4904794 _112866 h _60767 t) (@lem4904793 _112866 h _60767 t)). Qed.
Lemma lem4904796 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4904797 {_112866 : Type'} (t : list _112866) (h : _112866) : (term303 _112866 t h) = (term473 _112866 t h).
Proof. exact (MK_COMB (@lem4904796) (@lem4904788 _112866 t h)). Qed.
Lemma lem4904798 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term361 _112866 h _60767 t) = (term474 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904797 _112866 t h) (@lem4904790 _112866 _60767 t)). Qed.
Lemma lem4904800 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (term688 _112866 _60767 t) = (term688 _112866 _60767 t).
Proof. exact (eq_refl (term688 _112866 _60767 t)). Qed.
Lemma lem4904801 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term689 _112866 h _60767 t) = (term690 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904800 _112866 _60767 t) (@lem4904798 _112866 h _60767 t)). Qed.
Lemma lem4904803 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (term691 _112866 _60767 t) = (term691 _112866 _60767 t).
Proof. exact (eq_refl (term691 _112866 _60767 t)). Qed.
Lemma lem4904804 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term692 _112866 h _60767 t) = (term693 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904803 _112866 _60767 t) (@lem4904795 _112866 h _60767 t)). Qed.
Lemma lem4904805 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4904806 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term694 _112866 h _60767 t) = (term695 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904805) (@lem4904804 _112866 h _60767 t)). Qed.
Lemma lem4904807 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term696 _112866 h _60767 t) = (term697 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904806 _112866 h _60767 t) (@lem4904801 _112866 h _60767 t)). Qed.
Lemma lem4904808 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term632 _112866 h _60767 t) = (term696 _112866 h _60767 t).
Proof. exact (@lem17646 (@List.ForallOrdPairs _112866 _60767 t) (term361 _112866 h _60767 t)). Qed.
Lemma lem4904809 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term632 _112866 h _60767 t) = (term697 _112866 h _60767 t).
Proof. exact (TRANS (@lem4904808 _112866 h _60767 t) (@lem4904807 _112866 h _60767 t)). Qed.
Lemma lem4904908 {A : Type'} (P : A -> Prop) (Q : Prop) : (term485 A P Q) = (term486 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4904909 {_112866 : Type'} (P : _112866 -> Prop) (Q : Prop) : (term485 _112866 P Q) = (term486 _112866 P Q).
Proof. exact (@lem4904908 _112866 P Q). Qed.
Lemma lem4904910 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term487 _112866 h _60767 t) = (term488 _112866 h _60767 t).
Proof. exact (@lem4904909 _112866 (term463 _112866 t h) (term467 _112866 _60767 t)). Qed.
Lemma lem4904911 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term489 _112866 t h x) = (term453 _112866 t h x).
Proof. exact (eq_refl (term489 _112866 t h x)). Qed.
Lemma lem4904912 {_112866 : Type'} (t : list _112866) (h : _112866) : (term490 _112866 t h) = (term463 _112866 t h).
Proof. exact (fun_ext (fun x : _112866 => @lem4904911 _112866 t h x)). Qed.
Lemma lem4904913 {_112866 : Type'} : (@ex _112866) = (@ex _112866).
Proof. exact (eq_refl (@ex _112866)). Qed.
Lemma lem4904914 {_112866 : Type'} (t : list _112866) (h : _112866) : (term491 _112866 t h) = (term464 _112866 t h).
Proof. exact (MK_COMB (@lem4904913 _112866) (@lem4904912 _112866 t h)). Qed.
Lemma lem4904915 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4904916 {_112866 : Type'} (t : list _112866) (h : _112866) : (term492 _112866 t h) = (term469 _112866 t h).
Proof. exact (MK_COMB (@lem4904915) (@lem4904914 _112866 t h)). Qed.
Lemma lem4904917 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (term467 _112866 _60767 t) = (term467 _112866 _60767 t).
Proof. exact (eq_refl (term467 _112866 _60767 t)). Qed.
Lemma lem4904918 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term487 _112866 h _60767 t) = (term471 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904916 _112866 t h) (@lem4904917 _112866 _60767 t)). Qed.
Lemma lem4904919 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4904920 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term493 _112866 h _60767 t) = (term494 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904919) (@lem4904918 _112866 h _60767 t)). Qed.
Lemma lem4904921 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term489 _112866 t h x) = (term453 _112866 t h x).
Proof. exact (eq_refl (term489 _112866 t h x)). Qed.
Lemma lem4904922 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4904923 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term495 _112866 t h x) = (term496 _112866 t h x).
Proof. exact (MK_COMB (@lem4904922) (@lem4904921 _112866 t h x)). Qed.
Lemma lem4904924 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (term467 _112866 _60767 t) = (term467 _112866 _60767 t).
Proof. exact (eq_refl (term467 _112866 _60767 t)). Qed.
Lemma lem4904925 {_112866 : Type'} (h : _112866) (x : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term497 _112866 h x _60767 t) = (term498 _112866 h x _60767 t).
Proof. exact (MK_COMB (@lem4904923 _112866 t h x) (@lem4904924 _112866 _60767 t)). Qed.
Lemma lem4904926 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term499 _112866 h _60767 t) = (term500 _112866 h _60767 t).
Proof. exact (fun_ext (fun x : _112866 => @lem4904925 _112866 h x _60767 t)). Qed.
Lemma lem4904927 {_112866 : Type'} : (@ex _112866) = (@ex _112866).
Proof. exact (eq_refl (@ex _112866)). Qed.
Lemma lem4904928 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term488 _112866 h _60767 t) = (term501 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904927 _112866) (@lem4904926 _112866 h _60767 t)). Qed.
Lemma lem4904929 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : ((term487 _112866 h _60767 t) = (term488 _112866 h _60767 t)) = ((term471 _112866 h _60767 t) = (term501 _112866 h _60767 t)).
Proof. exact (MK_COMB (@lem4904920 _112866 h _60767 t) (@lem4904928 _112866 h _60767 t)). Qed.
Lemma lem4904930 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term471 _112866 h _60767 t) = (term501 _112866 h _60767 t).
Proof. exact (EQ_MP (@lem4904929 _112866 h _60767 t) (@lem4904910 _112866 h _60767 t)). Qed.
Lemma lem4904931 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (term691 _112866 _60767 t) = (term691 _112866 _60767 t).
Proof. exact (eq_refl (term691 _112866 _60767 t)). Qed.
Lemma lem4904932 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term693 _112866 h _60767 t) = (term698 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904931 _112866 _60767 t) (@lem4904930 _112866 h _60767 t)). Qed.
Lemma lem4904934 {A : Type'} (P : Prop) (Q : A -> Prop) : (term503 A P Q) = (term504 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4904935 {_112866 : Type'} (P : Prop) (Q : _112866 -> Prop) : (term503 _112866 P Q) = (term504 _112866 P Q).
Proof. exact (@lem4904934 _112866 P Q). Qed.
Lemma lem4904936 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term699 _112866 h _60767 t) = (term700 _112866 h _60767 t).
Proof. exact (@lem4904935 _112866 (@List.ForallOrdPairs _112866 _60767 t) (term500 _112866 h _60767 t)). Qed.
Lemma lem4904937 {_112866 : Type'} (h : _112866) (x : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term507 _112866 h _60767 t x) = (term498 _112866 h x _60767 t).
Proof. exact (eq_refl (term507 _112866 h _60767 t x)). Qed.
Lemma lem4904938 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term508 _112866 h _60767 t) = (term500 _112866 h _60767 t).
Proof. exact (fun_ext (fun x : _112866 => @lem4904937 _112866 h x _60767 t)). Qed.
Lemma lem4904939 {_112866 : Type'} : (@ex _112866) = (@ex _112866).
Proof. exact (eq_refl (@ex _112866)). Qed.
Lemma lem4904940 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term509 _112866 h _60767 t) = (term501 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904939 _112866) (@lem4904938 _112866 h _60767 t)). Qed.
Lemma lem4904941 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (term691 _112866 _60767 t) = (term691 _112866 _60767 t).
Proof. exact (eq_refl (term691 _112866 _60767 t)). Qed.
Lemma lem4904942 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term699 _112866 h _60767 t) = (term698 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904941 _112866 _60767 t) (@lem4904940 _112866 h _60767 t)). Qed.
Lemma lem4904943 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4904944 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term701 _112866 h _60767 t) = (term702 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904943) (@lem4904942 _112866 h _60767 t)). Qed.
Lemma lem4904945 {_112866 : Type'} (h : _112866) (x : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term507 _112866 h _60767 t x) = (term498 _112866 h x _60767 t).
Proof. exact (eq_refl (term507 _112866 h _60767 t x)). Qed.
Lemma lem4904946 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (term691 _112866 _60767 t) = (term691 _112866 _60767 t).
Proof. exact (eq_refl (term691 _112866 _60767 t)). Qed.
Lemma lem4904947 {_112866 : Type'} (h : _112866) (x : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term703 _112866 h _60767 t x) = (term704 _112866 h x _60767 t).
Proof. exact (MK_COMB (@lem4904946 _112866 _60767 t) (@lem4904945 _112866 h x _60767 t)). Qed.
Lemma lem4904948 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term705 _112866 h _60767 t) = (term706 _112866 h _60767 t).
Proof. exact (fun_ext (fun x : _112866 => @lem4904947 _112866 h x _60767 t)). Qed.
Lemma lem4904949 {_112866 : Type'} : (@ex _112866) = (@ex _112866).
Proof. exact (eq_refl (@ex _112866)). Qed.
Lemma lem4904950 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term700 _112866 h _60767 t) = (term707 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904949 _112866) (@lem4904948 _112866 h _60767 t)). Qed.
Lemma lem4904951 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : ((term699 _112866 h _60767 t) = (term700 _112866 h _60767 t)) = ((term698 _112866 h _60767 t) = (term707 _112866 h _60767 t)).
Proof. exact (MK_COMB (@lem4904944 _112866 h _60767 t) (@lem4904950 _112866 h _60767 t)). Qed.
Lemma lem4904952 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term698 _112866 h _60767 t) = (term707 _112866 h _60767 t).
Proof. exact (EQ_MP (@lem4904951 _112866 h _60767 t) (@lem4904936 _112866 h _60767 t)). Qed.
Lemma lem4904953 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term693 _112866 h _60767 t) = (term707 _112866 h _60767 t).
Proof. exact (TRANS (@lem4904932 _112866 h _60767 t) (@lem4904952 _112866 h _60767 t)). Qed.
Lemma lem4904954 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4904955 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term695 _112866 h _60767 t) = (term708 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904954) (@lem4904953 _112866 h _60767 t)). Qed.
Lemma lem4904956 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term690 _112866 h _60767 t) = (term690 _112866 h _60767 t).
Proof. exact (eq_refl (term690 _112866 h _60767 t)). Qed.
Lemma lem4904957 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term697 _112866 h _60767 t) = (term709 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904955 _112866 h _60767 t) (@lem4904956 _112866 h _60767 t)). Qed.
Lemma lem4904959 {A : Type'} (P : A -> Prop) (Q : Prop) : (term485 A P Q) = (term486 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4904960 {_112866 : Type'} (P : _112866 -> Prop) (Q : Prop) : (term485 _112866 P Q) = (term486 _112866 P Q).
Proof. exact (@lem4904959 _112866 P Q). Qed.
Lemma lem4904961 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term710 _112866 h _60767 t) = (term711 _112866 h _60767 t).
Proof. exact (@lem4904960 _112866 (term706 _112866 h _60767 t) (term690 _112866 h _60767 t)). Qed.
Lemma lem4904962 {_112866 : Type'} (h : _112866) (x : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term712 _112866 h _60767 t x) = (term704 _112866 h x _60767 t).
Proof. exact (eq_refl (term712 _112866 h _60767 t x)). Qed.
Lemma lem4904963 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term713 _112866 h _60767 t) = (term706 _112866 h _60767 t).
Proof. exact (fun_ext (fun x : _112866 => @lem4904962 _112866 h x _60767 t)). Qed.
Lemma lem4904964 {_112866 : Type'} : (@ex _112866) = (@ex _112866).
Proof. exact (eq_refl (@ex _112866)). Qed.
Lemma lem4904965 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term714 _112866 h _60767 t) = (term707 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904964 _112866) (@lem4904963 _112866 h _60767 t)). Qed.
Lemma lem4904966 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4904967 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term715 _112866 h _60767 t) = (term708 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904966) (@lem4904965 _112866 h _60767 t)). Qed.
Lemma lem4904968 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term690 _112866 h _60767 t) = (term690 _112866 h _60767 t).
Proof. exact (eq_refl (term690 _112866 h _60767 t)). Qed.
Lemma lem4904969 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term710 _112866 h _60767 t) = (term709 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904967 _112866 h _60767 t) (@lem4904968 _112866 h _60767 t)). Qed.
Lemma lem4904970 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4904971 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term716 _112866 h _60767 t) = (term717 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904970) (@lem4904969 _112866 h _60767 t)). Qed.
Lemma lem4904972 {_112866 : Type'} (h : _112866) (x : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term712 _112866 h _60767 t x) = (term704 _112866 h x _60767 t).
Proof. exact (eq_refl (term712 _112866 h _60767 t x)). Qed.
Lemma lem4904973 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4904974 {_112866 : Type'} (h : _112866) (x : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term718 _112866 h _60767 t x) = (term719 _112866 h x _60767 t).
Proof. exact (MK_COMB (@lem4904973) (@lem4904972 _112866 h x _60767 t)). Qed.
Lemma lem4904975 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term690 _112866 h _60767 t) = (term690 _112866 h _60767 t).
Proof. exact (eq_refl (term690 _112866 h _60767 t)). Qed.
Lemma lem4904976 {_112866 : Type'} (x : _112866) (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term720 _112866 x h _60767 t) = (term721 _112866 x h _60767 t).
Proof. exact (MK_COMB (@lem4904974 _112866 h x _60767 t) (@lem4904975 _112866 h _60767 t)). Qed.
Lemma lem4904977 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term722 _112866 h _60767 t) = (term723 _112866 h _60767 t).
Proof. exact (fun_ext (fun x : _112866 => @lem4904976 _112866 x h _60767 t)). Qed.
Lemma lem4904978 {_112866 : Type'} : (@ex _112866) = (@ex _112866).
Proof. exact (eq_refl (@ex _112866)). Qed.
Lemma lem4904979 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term711 _112866 h _60767 t) = (term724 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4904978 _112866) (@lem4904977 _112866 h _60767 t)). Qed.
Lemma lem4904980 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : ((term710 _112866 h _60767 t) = (term711 _112866 h _60767 t)) = ((term709 _112866 h _60767 t) = (term724 _112866 h _60767 t)).
Proof. exact (MK_COMB (@lem4904971 _112866 h _60767 t) (@lem4904979 _112866 h _60767 t)). Qed.
Lemma lem4904981 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term709 _112866 h _60767 t) = (term724 _112866 h _60767 t).
Proof. exact (EQ_MP (@lem4904980 _112866 h _60767 t) (@lem4904961 _112866 h _60767 t)). Qed.
Lemma lem4904983 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term697 _112866 h _60767 t) = (term724 _112866 h _60767 t).
Proof. exact (TRANS (@lem4904957 _112866 h _60767 t) (@lem4904981 _112866 h _60767 t)). Qed.
Lemma lem4904984 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term632 _112866 h _60767 t) = (term724 _112866 h _60767 t).
Proof. exact (TRANS (@lem4904809 _112866 h _60767 t) (@lem4904983 _112866 h _60767 t)). Qed.
Lemma lem4904985 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term632 _112866 h _60767 t) : term724 _112866 h _60767 t.
Proof. exact (EQ_MP (@lem4904984 _112866 h _60767 t) (@lem4904427 _112866 h _60767 t h1)). Qed.
Lemma lem4905012 {_112866 : Type'} (x : _112866) (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term721 _112866 x h _60767 t) : term721 _112866 x h _60767 t.
Proof. exact (h1). Qed.
Lemma lem4905132 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60767 t)) : term449 _112866 _60767 t.
Proof. exact (EQ_MP (@lem4904750 _112866 _60767 t) (@lem4904425 _112866 _60767 t h1)). Qed.
Lemma lem4905140 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term257 _112866 h t) : term257 _112866 h t.
Proof. exact (h1). Qed.
Lemma lem4905173 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (@List.ForallOrdPairs _112866 _60767 t) = (@List.ForallOrdPairs _112866 _60767 t).
Proof. exact (eq_refl (@List.ForallOrdPairs _112866 _60767 t)). Qed.
Lemma lem4905190 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) : (term455 _112866 t h x) = (term455 _112866 t h x).
Proof. exact (eq_refl (term455 _112866 t h x)). Qed.
Lemma lem4905191 {_112866 : Type'} (t : list _112866) (h : _112866) : (term465 _112866 t h) = (term465 _112866 t h).
Proof. exact (fun_ext (fun x : _112866 => @lem4905190 _112866 t h x)). Qed.
Lemma lem4905192 {_112866 : Type'} : (@all _112866) = (@all _112866).
Proof. exact (eq_refl (@all _112866)). Qed.
Lemma lem4905193 {_112866 : Type'} (t : list _112866) (h : _112866) : (term466 _112866 t h) = (term466 _112866 t h).
Proof. exact (MK_COMB (@lem4905192 _112866) (@lem4905191 _112866 t h)). Qed.
Lemma lem4905194 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4905195 {_112866 : Type'} (t : list _112866) (h : _112866) : (term473 _112866 t h) = (term473 _112866 t h).
Proof. exact (MK_COMB (@lem4905194) (@lem4905193 _112866 t h)). Qed.
Lemma lem4905196 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term474 _112866 h _60767 t) = (term474 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4905195 _112866 t h) (@lem4905173 _112866 _60767 t)). Qed.
Lemma lem4905205 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (term688 _112866 _60767 t) = (term688 _112866 _60767 t).
Proof. exact (eq_refl (term688 _112866 _60767 t)). Qed.
Lemma lem4905206 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term690 _112866 h _60767 t) = (term690 _112866 h _60767 t).
Proof. exact (MK_COMB (@lem4905205 _112866 _60767 t) (@lem4905196 _112866 h _60767 t)). Qed.
Lemma lem4905239 {_112866 : Type'} (h : _112866) (x : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term719 _112866 h x _60767 t) = (term719 _112866 h x _60767 t).
Proof. exact (eq_refl (term719 _112866 h x _60767 t)). Qed.
Lemma lem4905240 {_112866 : Type'} (x : _112866) (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : (term721 _112866 x h _60767 t) = (term721 _112866 x h _60767 t).
Proof. exact (MK_COMB (@lem4905239 _112866 h x _60767 t) (@lem4905206 _112866 h _60767 t)). Qed.
Lemma lem4905241 {_112866 : Type'} (x : _112866) (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term721 _112866 x h _60767 t) : term721 _112866 x h _60767 t.
Proof. exact (EQ_MP (@lem4905240 _112866 x h _60767 t) (@lem4905012 _112866 x h _60767 t h1)). Qed.
Lemma lem4905244 {_112866 : Type'} (h : _112866) (x : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term704 _112866 h x _60767 t) : term704 _112866 h x _60767 t.
Proof. exact (h1). Qed.
Lemma lem4905245 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term690 _112866 h _60767 t) : term690 _112866 h _60767 t.
Proof. exact (h1). Qed.
Lemma lem4905246 {_112866 : Type'} (h : _112866) (x : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term704 _112866 h x _60767 t) : term498 _112866 h x _60767 t.
Proof. exact (proj2 (@lem4905244 _112866 h x _60767 t h1)). Qed.
Lemma lem4905248 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) (h1 : term453 _112866 t h x) : term453 _112866 t h x.
Proof. exact (h1). Qed.
Lemma lem4905253 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term535 _112866 _60767 t) : term535 _112866 _60767 t.
Proof. exact (h1). Qed.
Lemma lem4905258 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term534 _112866 _60767 t) : term534 _112866 _60767 t.
Proof. exact (h1). Qed.
Lemma lem4905259 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term535 _112866 _60767 t) : term535 _112866 _60767 t.
Proof. exact (h1). Qed.
Lemma lem4905264 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term690 _112866 h _60767 t) : term474 _112866 h _60767 t.
Proof. exact (proj2 (@lem4905245 _112866 h _60767 t h1)). Qed.
Lemma lem4905268 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term534 _112866 _60767 t) : term534 _112866 _60767 t.
Proof. exact (h1). Qed.
Lemma lem4905269 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term535 _112866 _60767 t) : term535 _112866 _60767 t.
Proof. exact (h1). Qed.
Lemma lem4905284 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term257 _112866 h t) : term257 _112866 h t.
Proof. exact (h1). Qed.
Lemma lem4905492 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term467 _112866 _60767 t) : term467 _112866 _60767 t.
Proof. exact (h1). Qed.
Lemma lem4905881 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term257 _112866 h t) : term257 _112866 h t.
Proof. exact (h1). Qed.
Lemma lem4905903 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) (h1 : term453 _112866 t h x) : h = x.
Proof. exact (proj2 (@lem4905248 _112866 t h x h1)). Qed.
Lemma lem4905961 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term467 _112866 _60767 t) : term467 _112866 _60767 t.
Proof. exact (h1). Qed.
Lemma lem4905993 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term535 _112866 _60767 t) : term467 _112866 _60767 t.
Proof. exact (proj2 (@lem4905259 _112866 _60767 t h1)). Qed.
Lemma lem4906015 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term690 _112866 h _60767 t) : term467 _112866 _60767 t.
Proof. exact (proj1 (@lem4905245 _112866 h _60767 t h1)). Qed.
Lemma lem4906061 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term535 _112866 _60767 t) : term467 _112866 _60767 t.
Proof. exact (proj2 (@lem4905269 _112866 _60767 t h1)). Qed.
Lemma lem4906090 {_112866 : Type'} (t : list _112866) : (term725 _112866 t) = (term725 _112866 t).
Proof. exact (eq_refl (term725 _112866 t)). Qed.
Lemma lem4906091 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) (h1 : term453 _112866 t h x) : (term726 _112866 t h) = (term726 _112866 t x).
Proof. exact (MK_COMB (@lem4906090 _112866 t) (@lem4905903 _112866 t h x h1)). Qed.
Lemma lem4906092 {_112866 : Type'} (x : _112866) (t : list _112866) : (term726 _112866 t x) = (term257 _112866 x t).
Proof. exact (eq_refl (term726 _112866 t x)). Qed.
Lemma lem4906093 {_112866 : Type'} (t : list _112866) (h : _112866) : (term727 _112866 t h) = (term727 _112866 t h).
Proof. exact (eq_refl (term727 _112866 t h)). Qed.
Lemma lem4906094 {_112866 : Type'} (h : _112866) (x : _112866) (t : list _112866) : ((term726 _112866 t h) = (term726 _112866 t x)) = ((term726 _112866 t h) = (term257 _112866 x t)).
Proof. exact (MK_COMB (@lem4906093 _112866 t h) (@lem4906092 _112866 x t)). Qed.
Lemma lem4906095 {_112866 : Type'} (h : _112866) (t : list _112866) : (term726 _112866 t h) = (term257 _112866 h t).
Proof. exact (eq_refl (term726 _112866 t h)). Qed.
Lemma lem4906096 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4906097 {_112866 : Type'} (h : _112866) (t : list _112866) : (term727 _112866 t h) = (term728 _112866 h t).
Proof. exact (MK_COMB (@lem4906096) (@lem4906095 _112866 h t)). Qed.
Lemma lem4906098 {_112866 : Type'} (x : _112866) (t : list _112866) : (term257 _112866 x t) = (term257 _112866 x t).
Proof. exact (eq_refl (term257 _112866 x t)). Qed.
Lemma lem4906099 {_112866 : Type'} (h : _112866) (x : _112866) (t : list _112866) : ((term726 _112866 t h) = (term257 _112866 x t)) = ((term257 _112866 h t) = (term257 _112866 x t)).
Proof. exact (MK_COMB (@lem4906097 _112866 h t) (@lem4906098 _112866 x t)). Qed.
Lemma lem4906100 {_112866 : Type'} (h : _112866) (x : _112866) (t : list _112866) : ((term726 _112866 t h) = (term726 _112866 t x)) = ((term257 _112866 h t) = (term257 _112866 x t)).
Proof. exact (TRANS (@lem4906094 _112866 h x t) (@lem4906099 _112866 h x t)). Qed.
Lemma lem4906101 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) (h1 : term453 _112866 t h x) : (term257 _112866 h t) = (term257 _112866 x t).
Proof. exact (EQ_MP (@lem4906100 _112866 h x t) (@lem4906091 _112866 t h x h1)). Qed.
Lemma lem4906102 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) (h1 : term257 _112866 h t) (h2 : term453 _112866 t h x) : term257 _112866 x t.
Proof. exact (EQ_MP (@lem4906101 _112866 t h x h2) (@lem4905881 _112866 h t h1)). Qed.
Lemma lem4906367 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term535 _112866 _60767 t) : term467 _112866 _60767 t.
Proof. exact (proj2 (@lem4905253 _112866 _60767 t h1)). Qed.
Lemma lem4906510 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) (h1 : term453 _112866 t h x) : @List.In _112866 x t.
Proof. exact (proj1 (@lem4905248 _112866 t h x h1)). Qed.
Lemma lem4906511 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) (h1 : term453 _112866 t h x) : term600 _112866 x t.
Proof. exact (fun h0 : term257 _112866 x t => @lem4906510 _112866 t h x h1). Qed.
Lemma lem4906513 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4906514 {_112866 : Type'} (x : _112866) (t : list _112866) : (term600 _112866 x t) = (@List.In _112866 x t).
Proof. exact (@lem4906513 (@List.In _112866 x t)). Qed.
Lemma lem4906515 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) (h1 : term453 _112866 t h x) : @List.In _112866 x t.
Proof. exact (EQ_MP (@lem4906514 _112866 x t) (@lem4906511 _112866 t h x h1)). Qed.
Lemma lem4906518 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4906520 {_112866 : Type'} (x : _112866) (t : list _112866) : (term257 _112866 x t) = (term729 _112866 x t).
Proof. exact (@lem4906518 (@List.In _112866 x t)). Qed.
Lemma lem4906523 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) (h1 : term257 _112866 h t) (h2 : term453 _112866 t h x) : term729 _112866 x t.
Proof. exact (EQ_MP (@lem4906520 _112866 x t) (@lem4906102 _112866 t h x h1 h2)). Qed.
Lemma lem4906526 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) (h1 : term257 _112866 h t) (h2 : term453 _112866 t h x) : False.
Proof. exact (@lem4906523 _112866 t h x h1 h2 (@lem4906515 _112866 t h x h2)). Qed.
Lemma lem4906527 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) (h1 : term257 _112866 h t) (h2 : term453 _112866 t h x) : term597.
Proof. exact (fun h0 : ~ False => @lem4906526 _112866 t h x h1 h2). Qed.
Lemma lem4906529 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4906530 : term597 = False.
Proof. exact (@lem4906529 False). Qed.
Lemma lem4906674 {_112866 : Type'} (h : _112866) (x : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term704 _112866 h x _60767 t) : @List.ForallOrdPairs _112866 _60767 t.
Proof. exact (proj1 (@lem4905244 _112866 h x _60767 t h1)). Qed.
Lemma lem4906675 {_112866 : Type'} (h : _112866) (x : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term704 _112866 h x _60767 t) : term598 _112866 _60767 t.
Proof. exact (fun h0 : term467 _112866 _60767 t => @lem4906674 _112866 h x _60767 t h1). Qed.
Lemma lem4906677 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4906678 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (term598 _112866 _60767 t) = (@List.ForallOrdPairs _112866 _60767 t).
Proof. exact (@lem4906677 (@List.ForallOrdPairs _112866 _60767 t)). Qed.
Lemma lem4906679 {_112866 : Type'} (h : _112866) (x : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term704 _112866 h x _60767 t) : @List.ForallOrdPairs _112866 _60767 t.
Proof. exact (EQ_MP (@lem4906678 _112866 _60767 t) (@lem4906675 _112866 h x _60767 t h1)). Qed.
Lemma lem4906682 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4906684 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (term467 _112866 _60767 t) = (term599 _112866 _60767 t).
Proof. exact (@lem4906682 (@List.ForallOrdPairs _112866 _60767 t)). Qed.
Lemma lem4906687 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term535 _112866 _60767 t) : term599 _112866 _60767 t.
Proof. exact (EQ_MP (@lem4906684 _112866 _60767 t) (@lem4906367 _112866 _60767 t h1)). Qed.
Lemma lem4906690 {_112866 : Type'} (h : _112866) (x : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term535 _112866 _60767 t) (h2 : term704 _112866 h x _60767 t) : False.
Proof. exact (@lem4906687 _112866 _60767 t h1 (@lem4906679 _112866 h x _60767 t h2)). Qed.
Lemma lem4906691 {_112866 : Type'} (h : _112866) (x : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term535 _112866 _60767 t) (h2 : term704 _112866 h x _60767 t) : term597.
Proof. exact (fun h0 : ~ False => @lem4906690 _112866 h x _60767 t h1 h2). Qed.
Lemma lem4906693 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4906694 : term597 = False.
Proof. exact (@lem4906693 False). Qed.
Lemma lem4906838 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term534 _112866 _60767 t) : @List.ForallOrdPairs _112866 _60767 t.
Proof. exact (proj2 (@lem4905258 _112866 _60767 t h1)). Qed.
Lemma lem4906839 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term534 _112866 _60767 t) : term598 _112866 _60767 t.
Proof. exact (fun h0 : term467 _112866 _60767 t => @lem4906838 _112866 _60767 t h1). Qed.
Lemma lem4906841 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4906842 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (term598 _112866 _60767 t) = (@List.ForallOrdPairs _112866 _60767 t).
Proof. exact (@lem4906841 (@List.ForallOrdPairs _112866 _60767 t)). Qed.
Lemma lem4906843 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term534 _112866 _60767 t) : @List.ForallOrdPairs _112866 _60767 t.
Proof. exact (EQ_MP (@lem4906842 _112866 _60767 t) (@lem4906839 _112866 _60767 t h1)). Qed.
Lemma lem4906846 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4906848 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (term467 _112866 _60767 t) = (term599 _112866 _60767 t).
Proof. exact (@lem4906846 (@List.ForallOrdPairs _112866 _60767 t)). Qed.
Lemma lem4906851 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term467 _112866 _60767 t) : term599 _112866 _60767 t.
Proof. exact (EQ_MP (@lem4906848 _112866 _60767 t) (@lem4905961 _112866 _60767 t h1)). Qed.
Lemma lem4906854 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term467 _112866 _60767 t) (h2 : term534 _112866 _60767 t) : False.
Proof. exact (@lem4906851 _112866 _60767 t h1 (@lem4906843 _112866 _60767 t h2)). Qed.
Lemma lem4906855 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term467 _112866 _60767 t) (h2 : term534 _112866 _60767 t) : term597.
Proof. exact (fun h0 : ~ False => @lem4906854 _112866 _60767 t h1 h2). Qed.
Lemma lem4906857 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4906858 : term597 = False.
Proof. exact (@lem4906857 False). Qed.
Lemma lem4906859 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term467 _112866 _60767 t) (h2 : term534 _112866 _60767 t) : False.
Proof. exact (EQ_MP (@lem4906858) (@lem4906855 _112866 _60767 t h1 h2)). Qed.
Lemma lem4907002 {_112866 : Type'} (h : _112866) (x : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term704 _112866 h x _60767 t) : @List.ForallOrdPairs _112866 _60767 t.
Proof. exact (proj1 (@lem4905244 _112866 h x _60767 t h1)). Qed.
Lemma lem4907003 {_112866 : Type'} (h : _112866) (x : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term704 _112866 h x _60767 t) : term598 _112866 _60767 t.
Proof. exact (fun h0 : term467 _112866 _60767 t => @lem4907002 _112866 h x _60767 t h1). Qed.
Lemma lem4907005 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4907006 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (term598 _112866 _60767 t) = (@List.ForallOrdPairs _112866 _60767 t).
Proof. exact (@lem4907005 (@List.ForallOrdPairs _112866 _60767 t)). Qed.
Lemma lem4907007 {_112866 : Type'} (h : _112866) (x : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term704 _112866 h x _60767 t) : @List.ForallOrdPairs _112866 _60767 t.
Proof. exact (EQ_MP (@lem4907006 _112866 _60767 t) (@lem4907003 _112866 h x _60767 t h1)). Qed.
Lemma lem4907010 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4907012 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (term467 _112866 _60767 t) = (term599 _112866 _60767 t).
Proof. exact (@lem4907010 (@List.ForallOrdPairs _112866 _60767 t)). Qed.
Lemma lem4907015 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term535 _112866 _60767 t) : term599 _112866 _60767 t.
Proof. exact (EQ_MP (@lem4907012 _112866 _60767 t) (@lem4905993 _112866 _60767 t h1)). Qed.
Lemma lem4907018 {_112866 : Type'} (h : _112866) (x : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term535 _112866 _60767 t) (h2 : term704 _112866 h x _60767 t) : False.
Proof. exact (@lem4907015 _112866 _60767 t h1 (@lem4907007 _112866 h x _60767 t h2)). Qed.
Lemma lem4907019 {_112866 : Type'} (h : _112866) (x : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term535 _112866 _60767 t) (h2 : term704 _112866 h x _60767 t) : term597.
Proof. exact (fun h0 : ~ False => @lem4907018 _112866 h x _60767 t h1 h2). Qed.
Lemma lem4907021 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4907022 : term597 = False.
Proof. exact (@lem4907021 False). Qed.
Lemma lem4907023 {_112866 : Type'} (h : _112866) (x : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term535 _112866 _60767 t) (h2 : term704 _112866 h x _60767 t) : False.
Proof. exact (EQ_MP (@lem4907022) (@lem4907019 _112866 h x _60767 t h1 h2)). Qed.
Lemma lem4907166 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term534 _112866 _60767 t) : @List.ForallOrdPairs _112866 _60767 t.
Proof. exact (proj2 (@lem4905268 _112866 _60767 t h1)). Qed.
Lemma lem4907167 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term534 _112866 _60767 t) : term598 _112866 _60767 t.
Proof. exact (fun h0 : term467 _112866 _60767 t => @lem4907166 _112866 _60767 t h1). Qed.
Lemma lem4907169 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4907170 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (term598 _112866 _60767 t) = (@List.ForallOrdPairs _112866 _60767 t).
Proof. exact (@lem4907169 (@List.ForallOrdPairs _112866 _60767 t)). Qed.
Lemma lem4907171 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term534 _112866 _60767 t) : @List.ForallOrdPairs _112866 _60767 t.
Proof. exact (EQ_MP (@lem4907170 _112866 _60767 t) (@lem4907167 _112866 _60767 t h1)). Qed.
Lemma lem4907174 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4907176 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (term467 _112866 _60767 t) = (term599 _112866 _60767 t).
Proof. exact (@lem4907174 (@List.ForallOrdPairs _112866 _60767 t)). Qed.
Lemma lem4907179 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term690 _112866 h _60767 t) : term599 _112866 _60767 t.
Proof. exact (EQ_MP (@lem4907176 _112866 _60767 t) (@lem4906015 _112866 h _60767 t h1)). Qed.
Lemma lem4907182 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term690 _112866 h _60767 t) (h2 : term534 _112866 _60767 t) : False.
Proof. exact (@lem4907179 _112866 h _60767 t h1 (@lem4907171 _112866 _60767 t h2)). Qed.
Lemma lem4907183 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term690 _112866 h _60767 t) (h2 : term534 _112866 _60767 t) : term597.
Proof. exact (fun h0 : ~ False => @lem4907182 _112866 h _60767 t h1 h2). Qed.
Lemma lem4907185 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4907186 : term597 = False.
Proof. exact (@lem4907185 False). Qed.
Lemma lem4907187 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term690 _112866 h _60767 t) (h2 : term534 _112866 _60767 t) : False.
Proof. exact (EQ_MP (@lem4907186) (@lem4907183 _112866 h _60767 t h1 h2)). Qed.
Lemma lem4907330 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term690 _112866 h _60767 t) : @List.ForallOrdPairs _112866 _60767 t.
Proof. exact (proj2 (@lem4905264 _112866 h _60767 t h1)). Qed.
Lemma lem4907331 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term690 _112866 h _60767 t) : term598 _112866 _60767 t.
Proof. exact (fun h0 : term467 _112866 _60767 t => @lem4907330 _112866 h _60767 t h1). Qed.
Lemma lem4907333 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4907334 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (term598 _112866 _60767 t) = (@List.ForallOrdPairs _112866 _60767 t).
Proof. exact (@lem4907333 (@List.ForallOrdPairs _112866 _60767 t)). Qed.
Lemma lem4907335 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term690 _112866 h _60767 t) : @List.ForallOrdPairs _112866 _60767 t.
Proof. exact (EQ_MP (@lem4907334 _112866 _60767 t) (@lem4907331 _112866 h _60767 t h1)). Qed.
Lemma lem4907338 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4907340 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : (term467 _112866 _60767 t) = (term599 _112866 _60767 t).
Proof. exact (@lem4907338 (@List.ForallOrdPairs _112866 _60767 t)). Qed.
Lemma lem4907343 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term535 _112866 _60767 t) : term599 _112866 _60767 t.
Proof. exact (EQ_MP (@lem4907340 _112866 _60767 t) (@lem4906061 _112866 _60767 t h1)). Qed.
Lemma lem4907346 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term535 _112866 _60767 t) (h2 : term690 _112866 h _60767 t) : False.
Proof. exact (@lem4907343 _112866 _60767 t h1 (@lem4907335 _112866 h _60767 t h2)). Qed.
Lemma lem4907347 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term535 _112866 _60767 t) (h2 : term690 _112866 h _60767 t) : term597.
Proof. exact (fun h0 : ~ False => @lem4907346 _112866 h _60767 t h1 h2). Qed.
Lemma lem4907349 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4907350 : term597 = False.
Proof. exact (@lem4907349 False). Qed.
Lemma lem4907351 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term535 _112866 _60767 t) (h2 : term690 _112866 h _60767 t) : False.
Proof. exact (EQ_MP (@lem4907350) (@lem4907347 _112866 h _60767 t h1 h2)). Qed.
Lemma lem4907352 {_112866 : Type'} (h : _112866) (x : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term535 _112866 _60767 t) (h2 : term704 _112866 h x _60767 t) : False.
Proof. exact (EQ_MP (@lem4906694) (@lem4906691 _112866 h x _60767 t h1 h2)). Qed.
Lemma lem4907353 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) (h1 : term257 _112866 h t) (h2 : term453 _112866 t h x) : False.
Proof. exact (EQ_MP (@lem4906530) (@lem4906527 _112866 t h x h1 h2)). Qed.
Lemma lem4907354 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term467 _112866 _60767 t) (h2 : term534 _112866 _60767 t) : (term467 _112866 _60767 t) = False.
Proof. exact (prop_ext (fun h3 : term467 _112866 _60767 t => @lem4906859 _112866 _60767 t h1 h2) (fun h3 : False => @lem4905961 _112866 _60767 t h1)). Qed.
Lemma lem4907355 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term467 _112866 _60767 t) (h2 : term534 _112866 _60767 t) : False.
Proof. exact (EQ_MP (@lem4907354 _112866 _60767 t h1 h2) (@lem4905961 _112866 _60767 t h1)). Qed.
Lemma lem4907356 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) (h1 : term257 _112866 h t) (h2 : term453 _112866 t h x) : (term257 _112866 h t) = False.
Proof. exact (prop_ext (fun h3 : term257 _112866 h t => @lem4907353 _112866 t h x h1 h2) (fun h3 : False => @lem4905881 _112866 h t h1)). Qed.
Lemma lem4907357 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) (h1 : term257 _112866 h t) (h2 : term453 _112866 t h x) : False.
Proof. exact (EQ_MP (@lem4907356 _112866 t h x h1 h2) (@lem4905881 _112866 h t h1)). Qed.
Lemma lem4907358 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term467 _112866 _60767 t) (h2 : term534 _112866 _60767 t) : (term467 _112866 _60767 t) = False.
Proof. exact (prop_ext (fun h3 : term467 _112866 _60767 t => @lem4907355 _112866 _60767 t h1 h2) (fun h3 : False => @lem4905492 _112866 _60767 t h1)). Qed.
Lemma lem4907359 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term467 _112866 _60767 t) (h2 : term534 _112866 _60767 t) : False.
Proof. exact (EQ_MP (@lem4907358 _112866 _60767 t h1 h2) (@lem4905492 _112866 _60767 t h1)). Qed.
Lemma lem4907360 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) (h1 : term257 _112866 h t) (h2 : term453 _112866 t h x) : (term257 _112866 h t) = False.
Proof. exact (prop_ext (fun h3 : term257 _112866 h t => @lem4907357 _112866 t h x h1 h2) (fun h3 : False => @lem4905284 _112866 h t h1)). Qed.
Lemma lem4907361 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) (h1 : term257 _112866 h t) (h2 : term453 _112866 t h x) : False.
Proof. exact (EQ_MP (@lem4907360 _112866 t h x h1 h2) (@lem4905284 _112866 h t h1)). Qed.
Lemma lem4907362 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term467 _112866 _60767 t) (h2 : term534 _112866 _60767 t) : (term467 _112866 _60767 t) = False.
Proof. exact (prop_ext (fun h3 : term467 _112866 _60767 t => @lem4907359 _112866 _60767 t h1 h2) (fun h3 : False => @lem4905492 _112866 _60767 t h1)). Qed.
Lemma lem4907363 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) (h1 : term467 _112866 _60767 t) (h2 : term534 _112866 _60767 t) : False.
Proof. exact (EQ_MP (@lem4907362 _112866 _60767 t h1 h2) (@lem4905492 _112866 _60767 t h1)). Qed.
Lemma lem4907364 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) (h1 : term257 _112866 h t) (h2 : term453 _112866 t h x) : (term257 _112866 h t) = False.
Proof. exact (prop_ext (fun h3 : term257 _112866 h t => @lem4907361 _112866 t h x h1 h2) (fun h3 : False => @lem4905284 _112866 h t h1)). Qed.
Lemma lem4907365 {_112866 : Type'} (t : list _112866) (h : _112866) (x : _112866) (h1 : term257 _112866 h t) (h2 : term453 _112866 t h x) : False.
Proof. exact (EQ_MP (@lem4907364 _112866 t h x h1 h2) (@lem4905284 _112866 h t h1)). Qed.
Lemma lem4907366 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term690 _112866 h _60767 t) (h2 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60767 t)) : False.
Proof. exact (or_elim (@lem4905132 _112866 _60767 t h2) (fun h0 : term534 _112866 _60767 t => @lem4907187 _112866 h _60767 t h1 h0) (fun h0 : term535 _112866 _60767 t => @lem4907351 _112866 h _60767 t h0 h1)). Qed.
Lemma lem4907367 {_112866 : Type'} (h : _112866) (x : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term467 _112866 _60767 t) (h2 : term704 _112866 h x _60767 t) (h3 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60767 t)) : False.
Proof. exact (or_elim (@lem4905132 _112866 _60767 t h3) (fun h0 : term534 _112866 _60767 t => @lem4907363 _112866 _60767 t h1 h0) (fun h0 : term535 _112866 _60767 t => @lem4907023 _112866 h x _60767 t h0 h2)). Qed.
Lemma lem4907368 {_112866 : Type'} (h : _112866) (x : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term257 _112866 h t) (h2 : term453 _112866 t h x) (h3 : term704 _112866 h x _60767 t) (h4 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60767 t)) : False.
Proof. exact (or_elim (@lem4905132 _112866 _60767 t h4) (fun h0 : term534 _112866 _60767 t => @lem4907365 _112866 t h x h1 h2) (fun h0 : term535 _112866 _60767 t => @lem4907352 _112866 h x _60767 t h0 h3)). Qed.
Lemma lem4907369 {_112866 : Type'} (h : _112866) (x : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term257 _112866 h t) (h2 : term704 _112866 h x _60767 t) (h3 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60767 t)) : False.
Proof. exact (or_elim (@lem4905246 _112866 h x _60767 t h2) (fun h0 : term453 _112866 t h x => @lem4907368 _112866 h x _60767 t h1 h0 h2 h3) (fun h0 : term467 _112866 _60767 t => @lem4907367 _112866 h x _60767 t h0 h2 h3)). Qed.
Lemma lem4907370 {_112866 : Type'} (x : _112866) (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term257 _112866 h t) (h2 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60767 t)) (h3 : term721 _112866 x h _60767 t) : False.
Proof. exact (or_elim (@lem4905241 _112866 x h _60767 t h3) (fun h0 : term704 _112866 h x _60767 t => @lem4907369 _112866 h x _60767 t h1 h0 h2) (fun h0 : term690 _112866 h _60767 t => @lem4907366 _112866 h _60767 t h0 h2)). Qed.
Lemma lem4907371 {_112866 : Type'} (x : _112866) (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term257 _112866 h t) (h2 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60767 t)) (h3 : term721 _112866 x h _60767 t) : (term721 _112866 x h _60767 t) = False.
Proof. exact (prop_ext (fun h4 : term721 _112866 x h _60767 t => @lem4907370 _112866 x h _60767 t h1 h2 h3) (fun h4 : False => @lem4905241 _112866 x h _60767 t h3)). Qed.
Lemma lem4907372 {_112866 : Type'} (x : _112866) (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term257 _112866 h t) (h2 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60767 t)) (h3 : term721 _112866 x h _60767 t) : False.
Proof. exact (EQ_MP (@lem4907371 _112866 x h _60767 t h1 h2 h3) (@lem4905241 _112866 x h _60767 t h3)). Qed.
Lemma lem4907373 {_112866 : Type'} (x : _112866) (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term257 _112866 h t) (h2 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60767 t)) (h3 : term721 _112866 x h _60767 t) : (term257 _112866 h t) = False.
Proof. exact (prop_ext (fun h4 : term257 _112866 h t => @lem4907372 _112866 x h _60767 t h1 h2 h3) (fun h4 : False => @lem4905140 _112866 h t h1)). Qed.
Lemma lem4907374 {_112866 : Type'} (x : _112866) (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term257 _112866 h t) (h2 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60767 t)) (h3 : term721 _112866 x h _60767 t) : False.
Proof. exact (EQ_MP (@lem4907373 _112866 x h _60767 t h1 h2 h3) (@lem4905140 _112866 h t h1)). Qed.
Lemma lem4907375 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term632 _112866 h _60767 t) (h2 : term257 _112866 h t) (h3 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60767 t)) : False.
Proof. exact (ex_elim (@lem4904985 _112866 h _60767 t h1) (fun x : _112866 => fun h0 : term723 _112866 h _60767 t x => @lem4907374 _112866 x h _60767 t h2 h3 h0)). Qed.
Lemma lem4907376 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term632 _112866 h _60767 t) (h2 : term257 _112866 h t) (h3 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60767 t)) : (term257 _112866 h t) = False.
Proof. exact (prop_ext (fun h4 : term257 _112866 h t => @lem4907375 _112866 h _60767 t h1 h2 h3) (fun h4 : False => @lem4904757 _112866 h t h2)). Qed.
Lemma lem4907377 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term632 _112866 h _60767 t) (h2 : term257 _112866 h t) (h3 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60767 t)) : False.
Proof. exact (EQ_MP (@lem4907376 _112866 h _60767 t h1 h2 h3) (@lem4904757 _112866 h t h2)). Qed.
Lemma lem4907378 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term632 _112866 h _60767 t) (h2 : term257 _112866 h t) (h3 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60767 t)) : term338 _112866.
Proof. exact (fun h0 : term333 _112866 => @lem4907377 _112866 h _60767 t h1 h2 h3). Qed.
Lemma lem4907379 {_112866 : Type'} : (term338 _112866) = (term339 _112866).
Proof. exact (@lem69 (term333 _112866)). Qed.
Lemma lem4907380 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term632 _112866 h _60767 t) (h2 : term257 _112866 h t) (h3 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60767 t)) : term339 _112866.
Proof. exact (EQ_MP (@lem4907379 _112866) (@lem4907378 _112866 h _60767 t h1 h2 h3)). Qed.
Lemma lem4907381 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term632 _112866 h _60767 t) (h2 : term257 _112866 h t) (h3 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60767 t)) : term342 _112866.
Proof. exact (fun h0 : term152 => @lem4907380 _112866 h _60767 t h1 h2 h3). Qed.
Lemma lem4907382 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : term257 _112866 h t) (h2 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60767 t)) : term634 _112866 h _60767 t.
Proof. exact (fun h0 : term632 _112866 h _60767 t => @lem4907381 _112866 h _60767 t h0 h1 h2). Qed.
Lemma lem4907383 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) (h1 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60767 t)) : term635 _112866 h _60767 t.
Proof. exact (fun h0 : term257 _112866 h t => @lem4907382 _112866 h _60767 t h0 h1). Qed.
Lemma lem4907384 {_112866 : Type'} (h : _112866) (_60767 : type1402 _112866) (t : list _112866) : term636 _112866 h _60767 t.
Proof. exact (fun h0 : ((term171 _112866 t) = (@List.length _112866 t)) = (@List.ForallOrdPairs _112866 _60767 t) => @lem4907383 _112866 h _60767 t h0). Qed.
Lemma lem4907389 {_112866 : Type'} (_60767 : type1402 _112866) (t : list _112866) : term638 _112866 _60767 t.
Proof. exact (fun h : _112866 => @lem4907384 _112866 h _60767 t). Qed.
Lemma lem4907394 {_112866 : Type'} (_60767 : type1402 _112866) : term640 _112866 _60767.
Proof. exact (fun t : list _112866 => @lem4907389 _112866 _60767 t). Qed.
Lemma lem4907395 {_112866 : Type'} (_60768 : type1402 _112866) (_60767 : type1402 _112866) : term663 _112866 _60768 _60767.
Proof. exact (fun h0 : term398 _112866 _60767 _60768 => @lem4907394 _112866 _60767). Qed.
Lemma lem4907400 {_112866 : Type'} (_60768 : type1402 _112866) : term665 _112866 _60768.
Proof. exact (fun _60767 : type1402 _112866 => @lem4907395 _112866 _60768 _60767). Qed.
Lemma lem4907401 {_112866 : Type'} (_60768 : type1402 _112866) : term685 _112866 _60768.
Proof. exact (fun h0 : term444 _112866 _60768 => @lem4907400 _112866 _60768). Qed.
Lemma lem4907406 {_112866 : Type'} : term687 _112866.
Proof. exact (fun _60768 : type1402 _112866 => @lem4907401 _112866 _60768). Qed.
Lemma lem4907407 {_112866 : Type'} : term629 _112866.
Proof. exact (EQ_MP (@lem4904422 _112866) (@lem4907406 _112866)). Qed.
Lemma lem4907408 {_112866 : Type'} (t : list _112866) : term730 _112866 t.
Proof. exact (@lem4907407 _112866 t). Qed.
Lemma lem4907409 {_112866 : Type'} (t : list _112866) : (term730 _112866 t) = (term625 _112866 t).
Proof. exact (eq_refl (term730 _112866 t)). Qed.
Lemma lem4907410 {_112866 : Type'} (t : list _112866) : term625 _112866 t.
Proof. exact (EQ_MP (@lem4907409 _112866 t) (@lem4907408 _112866 t)). Qed.
Lemma lem4907411 {_112866 : Type'} (t : list _112866) (h : _112866) : term731 _112866 t h.
Proof. exact (@lem4907410 _112866 t h). Qed.
Lemma lem4907412 {_112866 : Type'} (h : _112866) (t : list _112866) : (term731 _112866 t h) = (term613 _112866 h t).
Proof. exact (eq_refl (term731 _112866 t h)). Qed.
Lemma lem4907413 {_112866 : Type'} (h : _112866) (t : list _112866) : term613 _112866 h t.
Proof. exact (EQ_MP (@lem4907412 _112866 h t) (@lem4907411 _112866 t h)). Qed.
Lemma lem4907415 {_112866 : Type'} (h : _112866) (t : list _112866) : term613 _112866 h t.
Proof. exact (@lem4903792 _112866 h t (@lem4907413 _112866 h t)). Qed.
Lemma lem4907416 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) : term620 _112866 h t.
Proof. exact (@lem4907415 _112866 h t (@lem4898537 _112866 t h1)). Qed.
Lemma lem4907417 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term257 _112866 h t) (h2 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) : term618 _112866 h t.
Proof. exact (@lem4907416 _112866 h t h2 (@lem4899209 _112866 h t h1)). Qed.
Lemma lem4907418 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term612 _112866 h t) (h2 : term257 _112866 h t) (h3 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) : term341 _112866.
Proof. exact (@lem4907417 _112866 h t h2 h3 (@lem4903773 _112866 h t h1)). Qed.
Lemma lem4907419 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term612 _112866 h t) (h2 : term257 _112866 h t) (h3 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) : term338 _112866.
Proof. exact (@lem4907418 _112866 h t h1 h2 h3 (@lem4898440)). Qed.
Lemma lem4907420 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term612 _112866 h t) (h2 : term257 _112866 h t) (h3 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) : False.
Proof. exact (@lem4907419 _112866 h t h1 h2 h3 (@lem4903774 _112866)). Qed.
Lemma lem4907421 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term612 _112866 h t) (h2 : term257 _112866 h t) (h3 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) : (term612 _112866 h t) = False.
Proof. exact (prop_ext (fun h4 : term612 _112866 h t => @lem4907420 _112866 h t h1 h2 h3) (fun h4 : False => @lem4903773 _112866 h t h1)). Qed.
Lemma lem4907422 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term612 _112866 h t) (h2 : term257 _112866 h t) (h3 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) : False.
Proof. exact (EQ_MP (@lem4907421 _112866 h t h1 h2 h3) (@lem4903773 _112866 h t h1)). Qed.
Lemma lem4907423 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term257 _112866 h t) (h2 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) : term611 _112866 h t.
Proof. exact (fun h0 : term612 _112866 h t => @lem4907422 _112866 h t h0 h1 h2). Qed.
Lemma lem4907424 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term257 _112866 h t) (h2 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) : (term175 _112866 t) = (term304 _112866 h t).
Proof. exact (EQ_MP (@lem4903772 _112866 h t) (@lem4907423 _112866 h t h1 h2)). Qed.
Lemma lem4907427 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term257 _112866 h t) (h2 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) : ((term244 _112866 t) = (term225 _112866 t)) = (term304 _112866 h t).
Proof. exact (EQ_MP (@lem4899288 _112866 h t h2) (@lem4907424 _112866 h t h1 h2)). Qed.
Lemma lem4907428 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term257 _112866 h t) (h2 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) : (term257 _112866 h t) = (((term244 _112866 t) = (term225 _112866 t)) = (term304 _112866 h t)).
Proof. exact (prop_ext (fun h3 : term257 _112866 h t => @lem4907427 _112866 h t h1 h2) (fun h3 : ((term244 _112866 t) = (term225 _112866 t)) = (term304 _112866 h t) => @lem4899209 _112866 h t h1)). Qed.
Lemma lem4907429 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : term257 _112866 h t) (h2 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) : ((term244 _112866 t) = (term225 _112866 t)) = (term304 _112866 h t).
Proof. exact (EQ_MP (@lem4907428 _112866 h t h1 h2) (@lem4899209 _112866 h t h1)). Qed.
Lemma lem4907430 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) : term315 _112866 h t.
Proof. exact (fun h0 : term257 _112866 h t => @lem4907429 _112866 h t h0 h1). Qed.
Lemma lem4907431 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) (h2 : @List.In _112866 h t) : ((term171 _112866 t) = (term225 _112866 t)) = (term304 _112866 h t).
Proof. exact (EQ_MP (@lem4899292 _112866 h t) (@lem4903767 _112866 h t h1 h2)). Qed.
Lemma lem4907432 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) (h2 : @List.In _112866 h t) : (@List.In _112866 h t) = (((term171 _112866 t) = (term225 _112866 t)) = (term304 _112866 h t)).
Proof. exact (prop_ext (fun h3 : @List.In _112866 h t => @lem4907431 _112866 h t h1 h2) (fun h3 : ((term171 _112866 t) = (term225 _112866 t)) = (term304 _112866 h t) => @lem4899192 _112866 h t h2)). Qed.
Lemma lem4907433 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) (h2 : @List.In _112866 h t) : ((term171 _112866 t) = (term225 _112866 t)) = (term304 _112866 h t).
Proof. exact (EQ_MP (@lem4907432 _112866 h t h1 h2) (@lem4899192 _112866 h t h2)). Qed.
Lemma lem4907434 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) : term319 _112866 h t.
Proof. exact (fun h0 : @List.In _112866 h t => @lem4907433 _112866 h t h1 h0). Qed.
Lemma lem4907435 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) : term322 _112866 h t.
Proof. exact (conj (@lem4907434 _112866 h t h1) (@lem4907430 _112866 h t h1)). Qed.
Lemma lem4907436 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) : ((term259 _112866 h t) = (term225 _112866 t)) = (term304 _112866 h t).
Proof. exact (EQ_MP (@lem4899191 _112866 h t) (@lem4907435 _112866 h t h1)). Qed.
Lemma lem4907437 {_112866 : Type'} (h : _112866) (t : list _112866) (h1 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t)) : ((term191 _112866 h t) = (term192 _112866 h t)) = (term193 _112866 h t).
Proof. exact (EQ_MP (@lem4899173 _112866 h t) (@lem4907436 _112866 h t h1)). Qed.
Lemma lem4907438 {_112866 : Type'} (h : _112866) (t : list _112866) : term195 _112866 h t.
Proof. exact (fun h0 : ((term171 _112866 t) = (@List.length _112866 t)) = (term175 _112866 t) => @lem4907437 _112866 h t h0). Qed.
Lemma lem4907443 {_112866 : Type'} (h : _112866) : term199 _112866 h.
Proof. exact (fun t : list _112866 => @lem4907438 _112866 h t). Qed.
Lemma lem4907448 {_112866 : Type'} : term203 _112866.
Proof. exact (fun h : _112866 => @lem4907443 _112866 h). Qed.
Lemma lem4907449 {_112866 : Type'} : term205 _112866.
Proof. exact (conj (@lem4898620 _112866) (@lem4907448 _112866)). Qed.
Lemma lem4907450 {_112866 : Type'} : term179 _112866.
Proof. exact (@lem4898536 _112866 (@lem4907449 _112866)). Qed.
Lemma lem4907451 {_112866 : Type'} : term178 _112866.
Proof. exact (EQ_MP (@lem4898509 _112866) (@lem4907450 _112866)). Qed.
