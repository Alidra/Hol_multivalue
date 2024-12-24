Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ARCH_POW_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import MONO_EXISTS_spec.
Require Import REAL_ARCH_spec.
Require Import REAL_LTE_TRANS_spec.
Require Import REAL_POW_LBOUND_spec.
Require Import REAL_SUB_ADD2_spec.
Require Import REAL_SUB_LT_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1366270_spec.
Require Import thm1366271_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483460_spec.
Require Import thm1483480_spec.
Require Import thm1483488_spec.
Require Import thm1483490_spec.
Require Import thm1483508_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483531_spec.
Require Import thm1483533_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm16474_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1820_spec.
Require Import thm1842_spec.
Require Import thm18940_spec.
Require Import thm18941_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
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
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1705012 (x : real) : (term0 x) = (term1 x).
Proof. exact (@lem17362 (term2 x) (term3 x)). Qed.
Lemma lem1705013 (x : real) : (term2 x) = (term4 x).
Proof. exact (@lem1483521 x term5). Qed.
Lemma lem1705019 (x : real) : (term6 x) = (term7 x).
Proof. exact (@lem1483519 x term5). Qed.
Lemma lem1705021 (m : nat) (n : nat) : (term8 m n) = (term9 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1705022 : term10 = term11.
Proof. exact (@lem1705021 term12 term12). Qed.
Lemma lem1705023 : (term13 = (BIT1 0)) = (term14 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1705024 : term14 = term12.
Proof. exact (EQ_MP (@lem1705023) (@lem940073)). Qed.
Lemma lem1705025 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1705026 : term15 = term5.
Proof. exact (MK_COMB (@lem1705025) (@lem1705024)). Qed.
Lemma lem1705027 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1705028 : term11 = term16.
Proof. exact (MK_COMB (@lem1705027) (@lem1705026)). Qed.
Lemma lem1705029 : term10 = term16.
Proof. exact (TRANS (@lem1705022) (@lem1705028)). Qed.
Lemma lem1705030 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1705033 (x : real) : (term7 x) = (term17 x).
Proof. exact (MK_COMB (@lem1705030 x) (@lem1705029)). Qed.
Lemma lem1705035 (x : real) : (term6 x) = (term17 x).
Proof. exact (TRANS (@lem1705019 x) (@lem1705033 x)). Qed.
Lemma lem1705036 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1705037 (x : real) : (term18 x) = (term19 x).
Proof. exact (MK_COMB (@lem1705036) (@lem1705035 x)). Qed.
Lemma lem1705038 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem1705039 (x : real) : (term4 x) = (term21 x).
Proof. exact (MK_COMB (@lem1705037 x) (@lem1705038)). Qed.
Lemma lem1705040 (x : real) : (term2 x) = (term21 x).
Proof. exact (TRANS (@lem1705013 x) (@lem1705039 x)). Qed.
Lemma lem1705041 (x : real) : (term22 x) = (term23 x).
Proof. exact (@lem1483533 term20 (term6 x)). Qed.
Lemma lem1705047 (x : real) : (term6 x) = (term7 x).
Proof. exact (@lem1483519 x term5). Qed.
Lemma lem1705049 (m : nat) (n : nat) : (term8 m n) = (term9 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1705050 : term10 = term11.
Proof. exact (@lem1705049 term12 term12). Qed.
Lemma lem1705051 : (term13 = (BIT1 0)) = (term14 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1705052 : term14 = term12.
Proof. exact (EQ_MP (@lem1705051) (@lem940073)). Qed.
Lemma lem1705053 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1705054 : term15 = term5.
Proof. exact (MK_COMB (@lem1705053) (@lem1705052)). Qed.
Lemma lem1705055 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1705056 : term11 = term16.
Proof. exact (MK_COMB (@lem1705055) (@lem1705054)). Qed.
Lemma lem1705057 : term10 = term16.
Proof. exact (TRANS (@lem1705050) (@lem1705056)). Qed.
Lemma lem1705058 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1705061 (x : real) : (term7 x) = (term17 x).
Proof. exact (MK_COMB (@lem1705058 x) (@lem1705057)). Qed.
Lemma lem1705063 (x : real) : (term6 x) = (term17 x).
Proof. exact (TRANS (@lem1705047 x) (@lem1705061 x)). Qed.
Lemma lem1705066 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1705067 (x : real) : (term25 x) = (term26 x).
Proof. exact (MK_COMB (@lem1705066) (@lem1705063 x)). Qed.
Lemma lem1705068 (x : real) : (term26 x) = (term27 x).
Proof. exact (@lem1483519 term20 (term17 x)). Qed.
Lemma lem1705069 (x : real) : (term28 x) = (term29 x).
Proof. exact (@lem1483508 x term16 term16). Qed.
Lemma lem1705071 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1705072 : term32 = term15.
Proof. exact (@lem1705071 term12 term12). Qed.
Lemma lem1705073 : (term13 = (BIT1 0)) = (term14 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1705074 : term14 = term12.
Proof. exact (EQ_MP (@lem1705073) (@lem940073)). Qed.
Lemma lem1705075 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1705076 : term15 = term5.
Proof. exact (MK_COMB (@lem1705075) (@lem1705074)). Qed.
Lemma lem1705077 : term32 = term5.
Proof. exact (TRANS (@lem1705072) (@lem1705076)). Qed.
Lemma lem1705080 (x : real) : (term33 x) = (term33 x).
Proof. exact (eq_refl (term33 x)). Qed.
Lemma lem1705081 (x : real) : (term29 x) = (term34 x).
Proof. exact (MK_COMB (@lem1705080 x) (@lem1705077)). Qed.
Lemma lem1705082 (x : real) : (term28 x) = (term34 x).
Proof. exact (TRANS (@lem1705069 x) (@lem1705081 x)). Qed.
Lemma lem1705083 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1705084 (x : real) : (term27 x) = (term36 x).
Proof. exact (MK_COMB (@lem1705083) (@lem1705082 x)). Qed.
Lemma lem1705085 (x : real) : (term36 x) = (term34 x).
Proof. exact (@lem1483448 (term34 x)). Qed.
Lemma lem1705086 (x : real) : (term27 x) = (term34 x).
Proof. exact (TRANS (@lem1705084 x) (@lem1705085 x)). Qed.
Lemma lem1705087 (x : real) : (term26 x) = (term34 x).
Proof. exact (TRANS (@lem1705068 x) (@lem1705086 x)). Qed.
Lemma lem1705088 (x : real) : (term25 x) = (term34 x).
Proof. exact (TRANS (@lem1705067 x) (@lem1705087 x)). Qed.
Lemma lem1705089 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1705090 (x : real) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem1705089) (@lem1705088 x)). Qed.
Lemma lem1705091 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem1705092 (x : real) : (term23 x) = (term39 x).
Proof. exact (MK_COMB (@lem1705090 x) (@lem1705091)). Qed.
Lemma lem1705093 (x : real) : (term22 x) = (term39 x).
Proof. exact (TRANS (@lem1705041 x) (@lem1705092 x)). Qed.
Lemma lem1705094 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1705095 (x : real) : (term40 x) = (term41 x).
Proof. exact (MK_COMB (@lem1705094) (@lem1705040 x)). Qed.
Lemma lem1705096 (x : real) : (term1 x) = (term42 x).
Proof. exact (MK_COMB (@lem1705095 x) (@lem1705093 x)). Qed.
Lemma lem1705111 (x : real) : (term0 x) = (term42 x).
Proof. exact (TRANS (@lem1705012 x) (@lem1705096 x)). Qed.
Lemma lem1705115 (x : real) (h1 : term42 x) : term42 x.
Proof. exact (h1). Qed.
Lemma lem1705116 (x : real) (h1 : term42 x) : term39 x.
Proof. exact (proj2 (@lem1705115 x h1)). Qed.
Lemma lem1705117 (x : real) (h1 : term42 x) : term21 x.
Proof. exact (proj1 (@lem1705115 x h1)). Qed.
Lemma lem1705119 (n : nat) (m : nat) : (term43 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1705120 : term44 = term45.
Proof. exact (@lem1705119 (NUMERAL 0) term12). Qed.
Lemma lem1705121 : term46 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1705122 (h1 : term46 = (BIT1 0)) : term45 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1705123 : (term46 = (BIT1 0)) = (term45 = True).
Proof. exact (prop_ext (fun h1 : term46 = (BIT1 0) => @lem1705122 h1) (fun h1 : term45 = True => @lem1705121)). Qed.
Lemma lem1705124 : term45 = True.
Proof. exact (EQ_MP (@lem1705123) (@lem1705121)). Qed.
Lemma lem1705125 : term44 = True.
Proof. exact (TRANS (@lem1705120) (@lem1705124)). Qed.
Lemma lem1705126 : True = term44.
Proof. exact (SYM (@lem1705125)). Qed.
Lemma lem1705127 : term44.
Proof. exact (EQ_MP (@lem1705126) (@lem0)). Qed.
Lemma lem1705128 (x : real) (h1 : term42 x) : term47 x.
Proof. exact (conj (@lem1705127) (@lem1705117 x h1)). Qed.
Lemma lem1705130 (x : real) (y : real) : term48 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1705131 (x : real) : term49 x.
Proof. exact (@lem1705130 term5 (term17 x)). Qed.
Lemma lem1705132 (x : real) (h1 : term42 x) : term50 x.
Proof. exact (@lem1705131 x (@lem1705128 x h1)). Qed.
Lemma lem1705133 (x : real) : (term51 x) = (term17 x).
Proof. exact (@lem1483460 (term17 x)). Qed.
Lemma lem1705134 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1705135 (x : real) : (term52 x) = (term19 x).
Proof. exact (MK_COMB (@lem1705134) (@lem1705133 x)). Qed.
Lemma lem1705136 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem1705137 (x : real) : (term50 x) = (term21 x).
Proof. exact (MK_COMB (@lem1705135 x) (@lem1705136)). Qed.
Lemma lem1705138 (x : real) (h1 : term42 x) : term21 x.
Proof. exact (EQ_MP (@lem1705137 x) (@lem1705132 x h1)). Qed.
Lemma lem1705140 (n : nat) (m : nat) : (term43 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1705141 : term44 = term45.
Proof. exact (@lem1705140 (NUMERAL 0) term12). Qed.
Lemma lem1705142 : term46 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1705143 (h1 : term46 = (BIT1 0)) : term45 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1705144 : (term46 = (BIT1 0)) = (term45 = True).
Proof. exact (prop_ext (fun h1 : term46 = (BIT1 0) => @lem1705143 h1) (fun h1 : term45 = True => @lem1705142)). Qed.
Lemma lem1705145 : term45 = True.
Proof. exact (EQ_MP (@lem1705144) (@lem1705142)). Qed.
Lemma lem1705146 : term44 = True.
Proof. exact (TRANS (@lem1705141) (@lem1705145)). Qed.
Lemma lem1705147 : True = term44.
Proof. exact (SYM (@lem1705146)). Qed.
Lemma lem1705148 : term44.
Proof. exact (EQ_MP (@lem1705147) (@lem0)). Qed.
Lemma lem1705149 (x : real) (h1 : term42 x) : term53 x.
Proof. exact (conj (@lem1705148) (@lem1705116 x h1)). Qed.
Lemma lem1705151 (x : real) (y : real) : term48 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1705152 (x : real) : term54 x.
Proof. exact (@lem1705151 term5 (term34 x)). Qed.
Lemma lem1705153 (x : real) (h1 : term42 x) : term55 x.
Proof. exact (@lem1705152 x (@lem1705149 x h1)). Qed.
Lemma lem1705154 (x : real) : (term56 x) = (term34 x).
Proof. exact (@lem1483460 (term34 x)). Qed.
Lemma lem1705155 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1705156 (x : real) : (term57 x) = (term38 x).
Proof. exact (MK_COMB (@lem1705155) (@lem1705154 x)). Qed.
Lemma lem1705157 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem1705158 (x : real) : (term55 x) = (term39 x).
Proof. exact (MK_COMB (@lem1705156 x) (@lem1705157)). Qed.
Lemma lem1705159 (x : real) (h1 : term42 x) : term39 x.
Proof. exact (EQ_MP (@lem1705158 x) (@lem1705153 x h1)). Qed.
Lemma lem1705160 (x : real) (h1 : term42 x) : term58 x.
Proof. exact (conj (@lem1705159 x h1) (@lem1705138 x h1)). Qed.
Lemma lem1705162 (x : real) (y : real) : term59 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1705163 (x : real) : term60 x.
Proof. exact (@lem1705162 (term34 x) (term17 x)). Qed.
Lemma lem1705164 (x : real) (h1 : term42 x) : term61 x.
Proof. exact (@lem1705163 x (@lem1705160 x h1)). Qed.
Lemma lem1705165 (x : real) : (term62 x) = (term63 x).
Proof. exact (@lem1483480 (term64 x) x term5 term16). Qed.
Lemma lem1705166 (x : real) : (term65 x) = (term66 x).
Proof. exact (@lem1483440 term16 x). Qed.
Lemma lem1705168 (m : nat) : (term67 m) = term20.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1705169 : term68 = term20.
Proof. exact (@lem1705168 term12). Qed.
Lemma lem1705170 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1705171 : term69 = term70.
Proof. exact (MK_COMB (@lem1705170) (@lem1705169)). Qed.
Lemma lem1705172 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1705173 (x : real) : (term66 x) = (term71 x).
Proof. exact (MK_COMB (@lem1705171) (@lem1705172 x)). Qed.
Lemma lem1705174 (x : real) : (term65 x) = (term71 x).
Proof. exact (TRANS (@lem1705166 x) (@lem1705173 x)). Qed.
Lemma lem1705175 (x : real) : (term71 x) = term20.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1705176 (x : real) : (term65 x) = term20.
Proof. exact (TRANS (@lem1705174 x) (@lem1705175 x)). Qed.
Lemma lem1705177 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1705178 (x : real) : (term72 x) = term35.
Proof. exact (MK_COMB (@lem1705177) (@lem1705176 x)). Qed.
Lemma lem1705180 (m : nat) : (term73 m) = term20.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1705181 : term74 = term20.
Proof. exact (@lem1705180 term12). Qed.
Lemma lem1705182 (x : real) : (term63 x) = term75.
Proof. exact (MK_COMB (@lem1705178 x) (@lem1705181)). Qed.
Lemma lem1705183 (x : real) : (term62 x) = term75.
Proof. exact (TRANS (@lem1705165 x) (@lem1705182 x)). Qed.
Lemma lem1705184 : term75 = term20.
Proof. exact (@lem1483448 term20). Qed.
Lemma lem1705185 (x : real) : (term62 x) = term20.
Proof. exact (TRANS (@lem1705183 x) (@lem1705184)). Qed.
Lemma lem1705186 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1705187 (x : real) : (term76 x) = term77.
Proof. exact (MK_COMB (@lem1705186) (@lem1705185 x)). Qed.
Lemma lem1705188 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem1705189 (x : real) : (term61 x) = term78.
Proof. exact (MK_COMB (@lem1705187 x) (@lem1705188)). Qed.
Lemma lem1705190 (x : real) (h1 : term42 x) : term78.
Proof. exact (EQ_MP (@lem1705189 x) (@lem1705164 x h1)). Qed.
Lemma lem1705192 (n : nat) (m : nat) : (term43 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1705193 : term78 = term79.
Proof. exact (@lem1705192 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1705194 : term79 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1705195 : term78 = False.
Proof. exact (TRANS (@lem1705193) (@lem1705194)). Qed.
Lemma lem1705196 (x : real) (h1 : term42 x) : False.
Proof. exact (EQ_MP (@lem1705195) (@lem1705190 x h1)). Qed.
Lemma lem1705198 (x : real) (h1 : term42 x) : term42 x.
Proof. exact (h1). Qed.
Lemma lem1705199 (x : real) (h1 : term42 x) : (term42 x) = False.
Proof. exact (prop_ext (fun h2 : term42 x => @lem1705196 x h1) (fun h2 : False => @lem1705198 x h1)). Qed.
Lemma lem1705200 (x : real) (h1 : term42 x) : False.
Proof. exact (EQ_MP (@lem1705199 x h1) (@lem1705198 x h1)). Qed.
Lemma lem1705201 (x : real) (h1 : term0 x) : term0 x.
Proof. exact (h1). Qed.
Lemma lem1705202 (x : real) (h1 : term0 x) : term42 x.
Proof. exact (EQ_MP (@lem1705111 x) (@lem1705201 x h1)). Qed.
Lemma lem1705203 (x : real) (h1 : term0 x) : (term42 x) = False.
Proof. exact (prop_ext (fun h2 : term42 x => @lem1705200 x h2) (fun h2 : False => @lem1705202 x h1)). Qed.
Lemma lem1705204 (x : real) (h1 : term0 x) : False.
Proof. exact (EQ_MP (@lem1705203 x h1) (@lem1705202 x h1)). Qed.
Lemma lem1705205 (x : real) : term80 x.
Proof. exact (fun h0 : term0 x => @lem1705204 x h0). Qed.
Lemma lem1705206 (x : real) : term81 x.
Proof. exact (@lem1386578 (term82 x)). Qed.
Lemma lem1705207 (x : real) : term82 x.
Proof. exact (@lem1705206 x (@lem1705205 x)). Qed.
Lemma lem1705218 : term83.
Proof. exact (fun x : real => @lem1705207 x). Qed.
Lemma lem1705239 (x : real) (y : real) : (term84 x y) = (term85 x y).
Proof. exact (@lem17362 (real_lt x y) (term86 x y)). Qed.
Lemma lem1705240 (y : real) (x : real) : (real_lt x y) = (term87 y x).
Proof. exact (@lem1483521 y x). Qed.
Lemma lem1705246 (y : real) (x : real) : (real_sub y x) = (term88 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1705251 (x : real) (y : real) : (term88 y x) = (term89 x y).
Proof. exact (@lem1483488 (term64 x) y). Qed.
Lemma lem1705253 (x : real) (y : real) : (real_sub y x) = (term89 x y).
Proof. exact (TRANS (@lem1705246 y x) (@lem1705251 x y)). Qed.
Lemma lem1705254 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1705255 (x : real) (y : real) : (term90 y x) = (term91 x y).
Proof. exact (MK_COMB (@lem1705254) (@lem1705253 x y)). Qed.
Lemma lem1705256 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem1705257 (x : real) (y : real) : (term87 y x) = (term92 x y).
Proof. exact (MK_COMB (@lem1705255 x y) (@lem1705256)). Qed.
Lemma lem1705258 (x : real) (y : real) : (real_lt x y) = (term92 x y).
Proof. exact (TRANS (@lem1705240 y x) (@lem1705257 x y)). Qed.
Lemma lem1705259 (x : real) (y : real) : (term93 x y) = (term94 x y).
Proof. exact (@lem1483531 x (term95 y)). Qed.
Lemma lem1705266 (y : real) : (term95 y) = (term96 y).
Proof. exact (@lem1483488 y term5). Qed.
Lemma lem1705269 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem1705270 (x : real) (y : real) : (term97 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem1705269 x) (@lem1705266 y)). Qed.
Lemma lem1705271 (x : real) (y : real) : (term98 x y) = (term99 x y).
Proof. exact (@lem1483519 x (term96 y)). Qed.
Lemma lem1705272 (y : real) : (term100 y) = (term101 y).
Proof. exact (@lem1483508 y term16 term5). Qed.
Lemma lem1705274 (m : nat) (n : nat) : (term8 m n) = (term9 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1705275 : term10 = term11.
Proof. exact (@lem1705274 term12 term12). Qed.
Lemma lem1705276 : (term13 = (BIT1 0)) = (term14 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1705277 : term14 = term12.
Proof. exact (EQ_MP (@lem1705276) (@lem940073)). Qed.
Lemma lem1705278 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1705279 : term15 = term5.
Proof. exact (MK_COMB (@lem1705278) (@lem1705277)). Qed.
Lemma lem1705280 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1705281 : term11 = term16.
Proof. exact (MK_COMB (@lem1705280) (@lem1705279)). Qed.
Lemma lem1705282 : term10 = term16.
Proof. exact (TRANS (@lem1705275) (@lem1705281)). Qed.
Lemma lem1705285 (y : real) : (term33 y) = (term33 y).
Proof. exact (eq_refl (term33 y)). Qed.
Lemma lem1705286 (y : real) : (term101 y) = (term102 y).
Proof. exact (MK_COMB (@lem1705285 y) (@lem1705282)). Qed.
Lemma lem1705287 (y : real) : (term100 y) = (term102 y).
Proof. exact (TRANS (@lem1705272 y) (@lem1705286 y)). Qed.
Lemma lem1705288 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1705291 (x : real) (y : real) : (term99 x y) = (term103 x y).
Proof. exact (MK_COMB (@lem1705288 x) (@lem1705287 y)). Qed.
Lemma lem1705292 (x : real) (y : real) : (term98 x y) = (term103 x y).
Proof. exact (TRANS (@lem1705271 x y) (@lem1705291 x y)). Qed.
Lemma lem1705293 (x : real) (y : real) : (term97 x y) = (term103 x y).
Proof. exact (TRANS (@lem1705270 x y) (@lem1705292 x y)). Qed.
Lemma lem1705294 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1705295 (x : real) (y : real) : (term104 x y) = (term105 x y).
Proof. exact (MK_COMB (@lem1705294) (@lem1705293 x y)). Qed.
Lemma lem1705296 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem1705297 (x : real) (y : real) : (term94 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1705295 x y) (@lem1705296)). Qed.
Lemma lem1705298 (x : real) (y : real) : (term93 x y) = (term106 x y).
Proof. exact (TRANS (@lem1705259 x y) (@lem1705297 x y)). Qed.
Lemma lem1705299 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1705300 (x : real) (y : real) : (term107 x y) = (term108 x y).
Proof. exact (MK_COMB (@lem1705299) (@lem1705258 x y)). Qed.
Lemma lem1705301 (x : real) (y : real) : (term85 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1705300 x y) (@lem1705298 x y)). Qed.
Lemma lem1705316 (x : real) (y : real) : (term84 x y) = (term109 x y).
Proof. exact (TRANS (@lem1705239 x y) (@lem1705301 x y)). Qed.
Lemma lem1705320 (x : real) (y : real) (h1 : term109 x y) : term109 x y.
Proof. exact (h1). Qed.
Lemma lem1705321 (x : real) (y : real) (h1 : term109 x y) : term106 x y.
Proof. exact (proj2 (@lem1705320 x y h1)). Qed.
Lemma lem1705322 (x : real) (y : real) (h1 : term109 x y) : term92 x y.
Proof. exact (proj1 (@lem1705320 x y h1)). Qed.
Lemma lem1705324 (n : nat) (m : nat) : (term43 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1705325 : term44 = term45.
Proof. exact (@lem1705324 (NUMERAL 0) term12). Qed.
Lemma lem1705326 : term46 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1705327 (h1 : term46 = (BIT1 0)) : term45 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1705328 : (term46 = (BIT1 0)) = (term45 = True).
Proof. exact (prop_ext (fun h1 : term46 = (BIT1 0) => @lem1705327 h1) (fun h1 : term45 = True => @lem1705326)). Qed.
Lemma lem1705329 : term45 = True.
Proof. exact (EQ_MP (@lem1705328) (@lem1705326)). Qed.
Lemma lem1705330 : term44 = True.
Proof. exact (TRANS (@lem1705325) (@lem1705329)). Qed.
Lemma lem1705331 : True = term44.
Proof. exact (SYM (@lem1705330)). Qed.
Lemma lem1705332 : term44.
Proof. exact (EQ_MP (@lem1705331) (@lem0)). Qed.
Lemma lem1705333 (x : real) (y : real) (h1 : term109 x y) : term110 x y.
Proof. exact (conj (@lem1705332) (@lem1705321 x y h1)). Qed.
Lemma lem1705335 (x : real) (y : real) : term111 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1705336 (x : real) (y : real) : term112 x y.
Proof. exact (@lem1705335 term5 (term103 x y)). Qed.
Lemma lem1705337 (x : real) (y : real) (h1 : term109 x y) : term113 x y.
Proof. exact (@lem1705336 x y (@lem1705333 x y h1)). Qed.
Lemma lem1705338 (x : real) (y : real) : (term114 x y) = (term103 x y).
Proof. exact (@lem1483460 (term103 x y)). Qed.
Lemma lem1705339 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1705340 (x : real) (y : real) : (term115 x y) = (term105 x y).
Proof. exact (MK_COMB (@lem1705339) (@lem1705338 x y)). Qed.
Lemma lem1705341 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem1705342 (x : real) (y : real) : (term113 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1705340 x y) (@lem1705341)). Qed.
Lemma lem1705343 (x : real) (y : real) (h1 : term109 x y) : term106 x y.
Proof. exact (EQ_MP (@lem1705342 x y) (@lem1705337 x y h1)). Qed.
Lemma lem1705345 (n : nat) (m : nat) : (term43 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1705346 : term44 = term45.
Proof. exact (@lem1705345 (NUMERAL 0) term12). Qed.
Lemma lem1705347 : term46 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1705348 (h1 : term46 = (BIT1 0)) : term45 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1705349 : (term46 = (BIT1 0)) = (term45 = True).
Proof. exact (prop_ext (fun h1 : term46 = (BIT1 0) => @lem1705348 h1) (fun h1 : term45 = True => @lem1705347)). Qed.
Lemma lem1705350 : term45 = True.
Proof. exact (EQ_MP (@lem1705349) (@lem1705347)). Qed.
Lemma lem1705351 : term44 = True.
Proof. exact (TRANS (@lem1705346) (@lem1705350)). Qed.
Lemma lem1705352 : True = term44.
Proof. exact (SYM (@lem1705351)). Qed.
Lemma lem1705353 : term44.
Proof. exact (EQ_MP (@lem1705352) (@lem0)). Qed.
Lemma lem1705354 (x : real) (y : real) (h1 : term109 x y) : term116 x y.
Proof. exact (conj (@lem1705353) (@lem1705322 x y h1)). Qed.
Lemma lem1705356 (x : real) (y : real) : term48 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1705357 (x : real) (y : real) : term117 x y.
Proof. exact (@lem1705356 term5 (term89 x y)). Qed.
Lemma lem1705358 (x : real) (y : real) (h1 : term109 x y) : term118 x y.
Proof. exact (@lem1705357 x y (@lem1705354 x y h1)). Qed.
Lemma lem1705359 (x : real) (y : real) : (term119 x y) = (term89 x y).
Proof. exact (@lem1483460 (term89 x y)). Qed.
Lemma lem1705360 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1705361 (x : real) (y : real) : (term120 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem1705360) (@lem1705359 x y)). Qed.
Lemma lem1705362 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem1705363 (x : real) (y : real) : (term118 x y) = (term92 x y).
Proof. exact (MK_COMB (@lem1705361 x y) (@lem1705362)). Qed.
Lemma lem1705364 (x : real) (y : real) (h1 : term109 x y) : term92 x y.
Proof. exact (EQ_MP (@lem1705363 x y) (@lem1705358 x y h1)). Qed.
Lemma lem1705365 (x : real) (y : real) (h1 : term109 x y) : term109 x y.
Proof. exact (conj (@lem1705364 x y h1) (@lem1705343 x y h1)). Qed.
Lemma lem1705367 (x : real) (y : real) : term121 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1705368 (x : real) (y : real) : term122 x y.
Proof. exact (@lem1705367 (term89 x y) (term103 x y)). Qed.
Lemma lem1705369 (x : real) (y : real) (h1 : term109 x y) : term123 x y.
Proof. exact (@lem1705368 x y (@lem1705365 x y h1)). Qed.
Lemma lem1705370 (x : real) (y : real) : (term124 x y) = (term125 x y).
Proof. exact (@lem1483480 (term64 x) x y (term102 y)). Qed.
Lemma lem1705371 (x : real) : (term65 x) = (term66 x).
Proof. exact (@lem1483440 term16 x). Qed.
Lemma lem1705373 (m : nat) : (term67 m) = term20.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1705374 : term68 = term20.
Proof. exact (@lem1705373 term12). Qed.
Lemma lem1705375 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1705376 : term69 = term70.
Proof. exact (MK_COMB (@lem1705375) (@lem1705374)). Qed.
Lemma lem1705377 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1705378 (x : real) : (term66 x) = (term71 x).
Proof. exact (MK_COMB (@lem1705376) (@lem1705377 x)). Qed.
Lemma lem1705379 (x : real) : (term65 x) = (term71 x).
Proof. exact (TRANS (@lem1705371 x) (@lem1705378 x)). Qed.
Lemma lem1705380 (x : real) : (term71 x) = term20.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1705381 (x : real) : (term65 x) = term20.
Proof. exact (TRANS (@lem1705379 x) (@lem1705380 x)). Qed.
Lemma lem1705382 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1705383 (x : real) : (term72 x) = term35.
Proof. exact (MK_COMB (@lem1705382) (@lem1705381 x)). Qed.
Lemma lem1705384 (y : real) : (term126 y) = (term127 y).
Proof. exact (@lem1483490 y (term64 y) term16). Qed.
Lemma lem1705385 (y : real) : (term128 y) = (term66 y).
Proof. exact (@lem1483442 term16 y). Qed.
Lemma lem1705387 (m : nat) : (term67 m) = term20.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1705388 : term68 = term20.
Proof. exact (@lem1705387 term12). Qed.
Lemma lem1705389 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1705390 : term69 = term70.
Proof. exact (MK_COMB (@lem1705389) (@lem1705388)). Qed.
Lemma lem1705391 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1705392 (y : real) : (term66 y) = (term71 y).
Proof. exact (MK_COMB (@lem1705390) (@lem1705391 y)). Qed.
Lemma lem1705393 (y : real) : (term128 y) = (term71 y).
Proof. exact (TRANS (@lem1705385 y) (@lem1705392 y)). Qed.
Lemma lem1705394 (y : real) : (term71 y) = term20.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1705395 (y : real) : (term128 y) = term20.
Proof. exact (TRANS (@lem1705393 y) (@lem1705394 y)). Qed.
Lemma lem1705396 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1705397 (y : real) : (term129 y) = term35.
Proof. exact (MK_COMB (@lem1705396) (@lem1705395 y)). Qed.
Lemma lem1705398 : term16 = term16.
Proof. exact (eq_refl term16). Qed.
Lemma lem1705399 (y : real) : (term127 y) = term130.
Proof. exact (MK_COMB (@lem1705397 y) (@lem1705398)). Qed.
Lemma lem1705400 (y : real) : (term126 y) = term130.
Proof. exact (TRANS (@lem1705384 y) (@lem1705399 y)). Qed.
Lemma lem1705401 : term130 = term16.
Proof. exact (@lem1483448 term16). Qed.
Lemma lem1705402 (y : real) : (term126 y) = term16.
Proof. exact (TRANS (@lem1705400 y) (@lem1705401)). Qed.
Lemma lem1705403 (x : real) (y : real) : (term125 x y) = term130.
Proof. exact (MK_COMB (@lem1705383 x) (@lem1705402 y)). Qed.
Lemma lem1705404 (x : real) (y : real) : (term124 x y) = term130.
Proof. exact (TRANS (@lem1705370 x y) (@lem1705403 x y)). Qed.
Lemma lem1705405 : term130 = term16.
Proof. exact (@lem1483448 term16). Qed.
Lemma lem1705406 (x : real) (y : real) : (term124 x y) = term16.
Proof. exact (TRANS (@lem1705404 x y) (@lem1705405)). Qed.
Lemma lem1705407 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1705408 (x : real) (y : real) : (term131 x y) = term132.
Proof. exact (MK_COMB (@lem1705407) (@lem1705406 x y)). Qed.
Lemma lem1705409 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem1705410 (x : real) (y : real) : (term123 x y) = term133.
Proof. exact (MK_COMB (@lem1705408 x y) (@lem1705409)). Qed.
Lemma lem1705411 (x : real) (y : real) (h1 : term109 x y) : term133.
Proof. exact (EQ_MP (@lem1705410 x y) (@lem1705369 x y h1)). Qed.
Lemma lem1705413 (m : nat) (n : nat) : (term134 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1705414 : term133 = False.
Proof. exact (@lem1705413 term12 (NUMERAL 0)). Qed.
Lemma lem1705415 (x : real) (y : real) (h1 : term109 x y) : False.
Proof. exact (EQ_MP (@lem1705414) (@lem1705411 x y h1)). Qed.
Lemma lem1705417 (x : real) (y : real) (h1 : term109 x y) : term109 x y.
Proof. exact (h1). Qed.
Lemma lem1705418 (x : real) (y : real) (h1 : term109 x y) : (term109 x y) = False.
Proof. exact (prop_ext (fun h2 : term109 x y => @lem1705415 x y h1) (fun h2 : False => @lem1705417 x y h1)). Qed.
Lemma lem1705419 (x : real) (y : real) (h1 : term109 x y) : False.
Proof. exact (EQ_MP (@lem1705418 x y h1) (@lem1705417 x y h1)). Qed.
Lemma lem1705420 (x : real) (y : real) (h1 : term84 x y) : term84 x y.
Proof. exact (h1). Qed.
Lemma lem1705421 (x : real) (y : real) (h1 : term84 x y) : term109 x y.
Proof. exact (EQ_MP (@lem1705316 x y) (@lem1705420 x y h1)). Qed.
Lemma lem1705422 (x : real) (y : real) (h1 : term84 x y) : (term109 x y) = False.
Proof. exact (prop_ext (fun h2 : term109 x y => @lem1705419 x y h2) (fun h2 : False => @lem1705421 x y h1)). Qed.
Lemma lem1705423 (x : real) (y : real) (h1 : term84 x y) : False.
Proof. exact (EQ_MP (@lem1705422 x y h1) (@lem1705421 x y h1)). Qed.
Lemma lem1705424 (x : real) (y : real) : term135 x y.
Proof. exact (fun h0 : term84 x y => @lem1705423 x y h0). Qed.
Lemma lem1705425 (x : real) (y : real) : term136 x y.
Proof. exact (@lem1386578 (term137 x y)). Qed.
Lemma lem1705426 (x : real) (y : real) : term137 x y.
Proof. exact (@lem1705425 x y (@lem1705424 x y)). Qed.
Lemma lem1705427 (h1 : term138) : term138.
Proof. exact (h1). Qed.
Lemma lem1705428 (x : real) (h1 : term138) : term139 x.
Proof. exact (@lem1705427 h1 x). Qed.
Lemma lem1705429 (x : real) : (term139 x) = (term140 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1705430 (x : real) (h1 : term138) : term140 x.
Proof. exact (EQ_MP (@lem1705429 x) (@lem1705428 x h1)). Qed.
Lemma lem1705431 (x : real) (y : real) (h1 : term138) : term141 x y.
Proof. exact (@lem1705430 x h1 y). Qed.
Lemma lem1705432 (y : real) (x : real) : (term141 x y) = (term142 y x).
Proof. exact (eq_refl (term141 x y)). Qed.
Lemma lem1705433 (y : real) (x : real) (h1 : term138) : term142 y x.
Proof. exact (EQ_MP (@lem1705432 y x) (@lem1705431 x y h1)). Qed.
Lemma lem1705434 (y : real) (x : real) (z : real) (h1 : term138) : term143 y x z.
Proof. exact (@lem1705433 y x h1 z). Qed.
Lemma lem1705435 (y : real) (x : real) (z : real) : (term143 y x z) = (term144 y x z).
Proof. exact (eq_refl (term143 y x z)). Qed.
Lemma lem1705436 (y : real) (x : real) (z : real) (h1 : term138) : term144 y x z.
Proof. exact (EQ_MP (@lem1705435 y x z) (@lem1705434 y x z h1)). Qed.
Lemma lem1705437 (x : real) (y : real) (z : real) (h1 : term145 x y z) : term145 x y z.
Proof. exact (h1). Qed.
Lemma lem1705438 (x : real) (y : real) (z : real) (h1 : term138) (h2 : term145 x y z) : real_lt x z.
Proof. exact (@lem1705436 y x z h1 (@lem1705437 x y z h2)). Qed.
Lemma lem1705439 (x : real) (y : real) (z : real) (h1 : term145 x y z) : term146 x z.
Proof. exact (fun h0 : term138 => @lem1705438 x y z h0 h1). Qed.
Lemma lem1705440 (x : real) (z : real) (h1 : term147 x z) : term147 x z.
Proof. exact (h1). Qed.
Lemma lem1705441 (x : real) (z : real) (h1 : term147 x z) : term146 x z.
Proof. exact (ex_elim (@lem1705440 x z h1) (fun y : real => fun h0 : term148 x z y => @lem1705439 x y z h0)). Qed.
Lemma lem1705442 (h1 : term138) : term138.
Proof. exact (h1). Qed.
Lemma lem1705443 (x : real) (z : real) (h1 : term138) (h2 : term147 x z) : real_lt x z.
Proof. exact (@lem1705441 x z h2 (@lem1705442 h1)). Qed.
Lemma lem1705444 (x : real) (z : real) (h1 : term138) : term149 x z.
Proof. exact (fun h0 : term147 x z => @lem1705443 x z h1 h0). Qed.
Lemma lem1705445 (x : real) (h1 : term138) : term150 x.
Proof. exact (fun z : real => @lem1705444 x z h1). Qed.
Lemma lem1705446 (h1 : term138) : term151.
Proof. exact (fun x : real => @lem1705445 x h1). Qed.
Lemma lem1705447 : term152.
Proof. exact (fun h0 : term138 => @lem1705446 h0). Qed.
Lemma lem1705448 : term151.
Proof. exact (@lem1705447 (@lem1370312)). Qed.
Lemma lem1705449 (x : real) : term153 x.
Proof. exact (@lem1705448 x). Qed.
Lemma lem1705450 (x : real) : (term153 x) = (term150 x).
Proof. exact (eq_refl (term153 x)). Qed.
Lemma lem1705451 (x : real) : term150 x.
Proof. exact (EQ_MP (@lem1705450 x) (@lem1705449 x)). Qed.
Lemma lem1705452 (x : real) (z : real) : term154 x z.
Proof. exact (@lem1705451 x z). Qed.
Lemma lem1705453 (x : real) (z : real) : (term154 x z) = (term149 x z).
Proof. exact (eq_refl (term154 x z)). Qed.
Lemma lem1705455 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term155 A P Q) : term155 A P Q.
Proof. exact (h1). Qed.
Lemma lem1705456 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term156 A P Q) : term156 A P Q.
Proof. exact (h1). Qed.
Lemma lem1705457 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term156 A P Q) (h2 : term155 A P Q) : term157 A P Q.
Proof. exact (@lem1705455 A P Q h2 (@lem1705456 A P Q h1)). Qed.
Lemma lem1705458 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term156 A P Q) : term158 A P Q.
Proof. exact (fun h0 : term155 A P Q => @lem1705457 A P Q h1 h0). Qed.
Lemma lem1705459 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term155 A P Q) : term155 A P Q.
Proof. exact (h1). Qed.
Lemma lem1705460 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term156 A P Q) (h2 : term155 A P Q) : term157 A P Q.
Proof. exact (@lem1705458 A P Q h1 (@lem1705459 A P Q h2)). Qed.
Lemma lem1705461 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term155 A P Q) : term155 A P Q.
Proof. exact (fun h0 : term156 A P Q => @lem1705460 A P Q h0 h1). Qed.
Lemma lem1705462 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term159 A P Q.
Proof. exact (fun h0 : term155 A P Q => @lem1705461 A P Q h0). Qed.
Lemma lem1705464 (x : real) : term160 x.
Proof. exact (@lem1700438 (term6 x)). Qed.
Lemma lem1705465 (x : real) : (term160 x) = (term161 x).
Proof. exact (eq_refl (term160 x)). Qed.
Lemma lem1705466 (x : real) : term161 x.
Proof. exact (EQ_MP (@lem1705465 x) (@lem1705464 x)). Qed.
Lemma lem1705467 (x : real) (h1 : term2 x) : term2 x.
Proof. exact (h1). Qed.
Lemma lem1705468 (x : real) : term162 x.
Proof. exact (@lem1376486 x). Qed.
Lemma lem1705469 (x : real) : (term162 x) = (term163 x).
Proof. exact (eq_refl (term162 x)). Qed.
Lemma lem1705470 (x : real) : term163 x.
Proof. exact (EQ_MP (@lem1705469 x) (@lem1705468 x)). Qed.
Lemma lem1705471 (x : real) (y : real) : term164 x y.
Proof. exact (@lem1705470 x y). Qed.
Lemma lem1705472 (y : real) (x : real) : (term164 x y) = ((term165 x y) = (real_lt y x)).
Proof. exact (eq_refl (term164 x y)). Qed.
Lemma lem1705474 (x : real) : (term2 x) = ((term2 x) = True).
Proof. exact (@lem7 (term2 x)). Qed.
Lemma lem1705481 (y : real) (x : real) : (term165 x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1705472 y x) (@lem1705471 x y)). Qed.
Lemma lem1705482 (x : real) : (term166 x) = (term2 x).
Proof. exact (@lem1705481 term5 x). Qed.
Lemma lem1705484 (x : real) (h1 : term2 x) : (term2 x) = True.
Proof. exact (EQ_MP (@lem1705474 x) (@lem1705467 x h1)). Qed.
Lemma lem1705485 (x : real) (h1 : term2 x) : (term166 x) = True.
Proof. exact (TRANS (@lem1705482 x) (@lem1705484 x h1)). Qed.
Lemma lem1705486 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1705487 (x : real) (h1 : term2 x) : (term167 x) = (imp True).
Proof. exact (MK_COMB (@lem1705486) (@lem1705485 x h1)). Qed.
Lemma lem1705496 (x : real) : (term168 x) = (term168 x).
Proof. exact (eq_refl (term168 x)). Qed.
Lemma lem1705497 (x : real) (h1 : term2 x) : (term161 x) = (term169 x).
Proof. exact (MK_COMB (@lem1705487 x h1) (@lem1705496 x)). Qed.
Lemma lem1705499 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1705500 (x : real) : (term169 x) = (term168 x).
Proof. exact (@lem1705499 (term168 x)). Qed.
Lemma lem1705509 (x : real) (h1 : term2 x) : (term161 x) = (term168 x).
Proof. exact (TRANS (@lem1705497 x h1) (@lem1705500 x)). Qed.
Lemma lem1705510 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1705511 (x : real) (h1 : term2 x) : (term170 x) = (term171 x).
Proof. exact (MK_COMB (@lem1705510) (@lem1705509 x h1)). Qed.
Lemma lem1705516 (y : real) (x : real) : (term172 y x) = (term172 y x).
Proof. exact (eq_refl (term172 y x)). Qed.
Lemma lem1705517 (y : real) (x : real) (h1 : term2 x) : (term173 y x) = (term174 y x).
Proof. exact (MK_COMB (@lem1705511 x h1) (@lem1705516 y x)). Qed.
Lemma lem1705520 (y : real) (x : real) (h1 : term2 x) : (term174 y x) = (term173 y x).
Proof. exact (SYM (@lem1705517 y x h1)). Qed.
Lemma lem1705521 (x : real) (h1 : term168 x) : term168 x.
Proof. exact (h1). Qed.
Lemma lem1705522 (y : real) (x : real) (h1 : term168 x) : term175 x y.
Proof. exact (@lem1705521 x h1 y). Qed.
Lemma lem1705523 (y : real) (x : real) : (term175 x y) = (term176 y x).
Proof. exact (eq_refl (term175 x y)). Qed.
Lemma lem1705524 (y : real) (x : real) (h1 : term168 x) : term176 y x.
Proof. exact (EQ_MP (@lem1705523 y x) (@lem1705522 y x h1)). Qed.
Lemma lem1705526 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term155 A P Q.
Proof. exact (@lem1705462 A P Q (@lem7401 A P Q)). Qed.
Lemma lem1705527 (P : nat -> Prop) (Q : nat -> Prop) : term177 P Q.
Proof. exact (@lem1705526 nat P Q). Qed.
Lemma lem1705528 (y : real) (x : real) : term178 y x.
Proof. exact (@lem1705527 (term179 y x) (term180 y x)). Qed.
Lemma lem1705529 (y : real) (n : nat) (x : real) : (term181 y x n) = (term182 y n x).
Proof. exact (eq_refl (term181 y x n)). Qed.
Lemma lem1705530 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1705531 (y : real) (n : nat) (x : real) : (term183 y x n) = (term184 y n x).
Proof. exact (MK_COMB (@lem1705530) (@lem1705529 y n x)). Qed.
Lemma lem1705532 (y : real) (x : real) (n : nat) : (term185 y x n) = (term186 y x n).
Proof. exact (eq_refl (term185 y x n)). Qed.
Lemma lem1705533 (y : real) (x : real) (n : nat) : (term187 y x n) = (term188 y x n).
Proof. exact (MK_COMB (@lem1705531 y n x) (@lem1705532 y x n)). Qed.
Lemma lem1705534 (y : real) (x : real) : (term189 y x) = (term190 y x).
Proof. exact (fun_ext (fun n : nat => @lem1705533 y x n)). Qed.
Lemma lem1705535 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1705536 (y : real) (x : real) : (term191 y x) = (term192 y x).
Proof. exact (MK_COMB (@lem1705535) (@lem1705534 y x)). Qed.
Lemma lem1705537 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1705538 (y : real) (x : real) : (term193 y x) = (term194 y x).
Proof. exact (MK_COMB (@lem1705537) (@lem1705536 y x)). Qed.
Lemma lem1705539 (y : real) (n : nat) (x : real) : (term181 y x n) = (term182 y n x).
Proof. exact (eq_refl (term181 y x n)). Qed.
Lemma lem1705540 (y : real) (x : real) : (term195 y x) = (term179 y x).
Proof. exact (fun_ext (fun n : nat => @lem1705539 y n x)). Qed.
Lemma lem1705541 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1705542 (y : real) (x : real) : (term196 y x) = (term176 y x).
Proof. exact (MK_COMB (@lem1705541) (@lem1705540 y x)). Qed.
Lemma lem1705543 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1705544 (y : real) (x : real) : (term197 y x) = (term198 y x).
Proof. exact (MK_COMB (@lem1705543) (@lem1705542 y x)). Qed.
Lemma lem1705545 (y : real) (x : real) (n : nat) : (term185 y x n) = (term186 y x n).
Proof. exact (eq_refl (term185 y x n)). Qed.
Lemma lem1705546 (y : real) (x : real) : (term199 y x) = (term180 y x).
Proof. exact (fun_ext (fun n : nat => @lem1705545 y x n)). Qed.
Lemma lem1705547 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1705548 (y : real) (x : real) : (term200 y x) = (term172 y x).
Proof. exact (MK_COMB (@lem1705547) (@lem1705546 y x)). Qed.
Lemma lem1705549 (y : real) (x : real) : (term201 y x) = (term202 y x).
Proof. exact (MK_COMB (@lem1705544 y x) (@lem1705548 y x)). Qed.
Lemma lem1705550 (y : real) (x : real) : (term178 y x) = (term203 y x).
Proof. exact (MK_COMB (@lem1705538 y x) (@lem1705549 y x)). Qed.
Lemma lem1705551 (y : real) (x : real) : term203 y x.
Proof. exact (EQ_MP (@lem1705550 y x) (@lem1705528 y x)). Qed.
Lemma lem1705552 (y : real) (n : nat) (x : real) (h1 : term182 y n x) : term182 y n x.
Proof. exact (h1). Qed.
Lemma lem1705554 (x : real) (z : real) : term149 x z.
Proof. exact (EQ_MP (@lem1705453 x z) (@lem1705452 x z)). Qed.
Lemma lem1705555 (y : real) (x : real) (n : nat) : term204 y x n.
Proof. exact (@lem1705554 y (real_pow x n)). Qed.
Lemma lem1705556 (x : real) (y : real) (h1 : real_lt x y) : real_lt x y.
Proof. exact (h1). Qed.
Lemma lem1705557 (x : real) (y : real) (h1 : real_lt x y) : term86 x y.
Proof. exact (@lem1705426 x y (@lem1705556 x y h1)). Qed.
Lemma lem1705558 (x : real) (y : real) : (term86 x y) = ((term86 x y) = True).
Proof. exact (@lem7 (term86 x y)). Qed.
Lemma lem1705559 (x : real) (y : real) (h1 : real_lt x y) : (term86 x y) = True.
Proof. exact (EQ_MP (@lem1705558 x y) (@lem1705557 x y h1)). Qed.
Lemma lem1705567 (y : real) (n : nat) (x : real) : (term182 y n x) = ((term182 y n x) = True).
Proof. exact (@lem7 (term182 y n x)). Qed.
Lemma lem1705572 (x : real) (y : real) : term205 x y.
Proof. exact (fun h0 : real_lt x y => @lem1705559 x y h0). Qed.
Lemma lem1705573 (y : real) (n : nat) (x : real) : term206 y n x.
Proof. exact (@lem1705572 y (term207 n x)). Qed.
Lemma lem1705575 (y : real) (n : nat) (x : real) (h1 : term182 y n x) : (term182 y n x) = True.
Proof. exact (EQ_MP (@lem1705567 y n x) (@lem1705552 y n x h1)). Qed.
Lemma lem1705576 (y : real) (n : nat) (x : real) (h1 : term182 y n x) : True = (term182 y n x).
Proof. exact (SYM (@lem1705575 y n x h1)). Qed.
Lemma lem1705577 (y : real) (n : nat) (x : real) (h1 : term182 y n x) : term182 y n x.
Proof. exact (EQ_MP (@lem1705576 y n x h1) (@lem0)). Qed.
Lemma lem1705578 (y : real) (n : nat) (x : real) (h1 : term182 y n x) : (term208 y n x) = True.
Proof. exact (@lem1705573 y n x (@lem1705577 y n x h1)). Qed.
Lemma lem1705579 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1705580 (y : real) (n : nat) (x : real) (h1 : term182 y n x) : (term209 y n x) = (and True).
Proof. exact (MK_COMB (@lem1705579) (@lem1705578 y n x h1)). Qed.
Lemma lem1705581 (x : real) (n : nat) : (term210 x n) = (term210 x n).
Proof. exact (eq_refl (term210 x n)). Qed.
Lemma lem1705582 (y : real) (n : nat) (x : real) (h1 : term182 y n x) : (term211 y x n) = (term212 x n).
Proof. exact (MK_COMB (@lem1705580 y n x h1) (@lem1705581 x n)). Qed.
Lemma lem1705584 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1705585 (x : real) (n : nat) : (term212 x n) = (term210 x n).
Proof. exact (@lem1705584 (term210 x n)). Qed.
Lemma lem1705586 (y : real) (n : nat) (x : real) (h1 : term182 y n x) : (term211 y x n) = (term210 x n).
Proof. exact (TRANS (@lem1705582 y n x h1) (@lem1705585 x n)). Qed.
Lemma lem1705587 (y : real) (n : nat) (x : real) (h1 : term182 y n x) : (term210 x n) = (term211 y x n).
Proof. exact (SYM (@lem1705586 y n x h1)). Qed.
Lemma lem1705589 (p : Prop) : p = (term213 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1705590 (x : real) (n : nat) : (term210 x n) = (term214 x n).
Proof. exact (@lem1705589 (term210 x n)). Qed.
Lemma lem1705591 (x : real) (n : nat) : (term214 x n) = (term210 x n).
Proof. exact (SYM (@lem1705590 x n)). Qed.
Lemma lem1705592 (x : real) (n : nat) (h1 : term215 x n) : term215 x n.
Proof. exact (h1). Qed.
Lemma lem1705595 (y : real) (x : real) (n : nat) (h1 : term216 y x n) : term216 y x n.
Proof. exact (h1). Qed.
Lemma lem1705596 (y : real) (x : real) (n : nat) : term217 y x n.
Proof. exact (fun h0 : term216 y x n => @lem1705595 y x n h0). Qed.
Lemma lem1705597 (y : real) (x : real) (n : nat) (h1 : term217 y x n) : term217 y x n.
Proof. exact (h1). Qed.
Lemma lem1705598 (y : real) (x : real) (n : nat) (h1 : term216 y x n) : term216 y x n.
Proof. exact (h1). Qed.
Lemma lem1705599 (y : real) (x : real) (n : nat) (h1 : term217 y x n) (h2 : term216 y x n) : term216 y x n.
Proof. exact (@lem1705597 y x n h1 (@lem1705598 y x n h2)). Qed.
Lemma lem1705600 (y : real) (x : real) (n : nat) (h1 : term216 y x n) : term218 y x n.
Proof. exact (fun h0 : term217 y x n => @lem1705599 y x n h0 h1). Qed.
Lemma lem1705601 (y : real) (x : real) (n : nat) (h1 : term217 y x n) : term217 y x n.
Proof. exact (h1). Qed.
Lemma lem1705602 (y : real) (x : real) (n : nat) (h1 : term217 y x n) (h2 : term216 y x n) : term216 y x n.
Proof. exact (@lem1705600 y x n h2 (@lem1705601 y x n h1)). Qed.
Lemma lem1705603 (y : real) (x : real) (n : nat) (h1 : term217 y x n) : term217 y x n.
Proof. exact (fun h0 : term216 y x n => @lem1705602 y x n h1 h0). Qed.
Lemma lem1705604 (y : real) (x : real) (n : nat) : term219 y x n.
Proof. exact (fun h0 : term217 y x n => @lem1705603 y x n h0). Qed.
Lemma lem1705607 (y : real) (x : real) (n : nat) : term217 y x n.
Proof. exact (@lem1705604 y x n (@lem1705596 y x n)). Qed.
Lemma lem1705645 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1705646 : term220 = term221.
Proof. exact (@lem1705645 term222). Qed.
Lemma lem1705657 : term223 = term223.
Proof. exact (eq_refl term223). Qed.
Lemma lem1705658 : term224 = term225.
Proof. exact (MK_COMB (@lem1705657) (@lem1705646)). Qed.
Lemma lem1705661 : term226 = term226.
Proof. exact (eq_refl term226). Qed.
Lemma lem1705662 : term227 = term228.
Proof. exact (MK_COMB (@lem1705661) (@lem1705658)). Qed.
Lemma lem1705665 (x : real) (n : nat) : (term229 x n) = (term229 x n).
Proof. exact (eq_refl (term229 x n)). Qed.
Lemma lem1705666 (x : real) (n : nat) : (term230 x n) = (term231 x n).
Proof. exact (MK_COMB (@lem1705665 x n) (@lem1705662)). Qed.
Lemma lem1705669 (y : real) (n : nat) (x : real) : (term184 y n x) = (term184 y n x).
Proof. exact (eq_refl (term184 y n x)). Qed.
Lemma lem1705670 (y : real) (x : real) (n : nat) : (term232 y x n) = (term233 y x n).
Proof. exact (MK_COMB (@lem1705669 y n x) (@lem1705666 x n)). Qed.
Lemma lem1705673 (x : real) : (term234 x) = (term234 x).
Proof. exact (eq_refl (term234 x)). Qed.
Lemma lem1705674 (y : real) (x : real) (n : nat) : (term216 y x n) = (term235 y x n).
Proof. exact (MK_COMB (@lem1705673 x) (@lem1705670 y x n)). Qed.
Lemma lem1705677 (x : real) (n : nat) : (term236 x n) = (term237 x n).
Proof. exact (fun_ext (fun y : real => @lem1705674 y x n)). Qed.
Lemma lem1705678 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1705679 (x : real) (n : nat) : (term238 x n) = (term239 x n).
Proof. exact (MK_COMB (@lem1705678) (@lem1705677 x n)). Qed.
Lemma lem1705684 (n : nat) : (term240 n) = (term241 n).
Proof. exact (fun_ext (fun x : real => @lem1705679 x n)). Qed.
Lemma lem1705685 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1705686 (n : nat) : (term242 n) = (term243 n).
Proof. exact (MK_COMB (@lem1705685) (@lem1705684 n)). Qed.
Lemma lem1705691 : term244 = term245.
Proof. exact (fun_ext (fun n : nat => @lem1705686 n)). Qed.
Lemma lem1705692 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1705701 : term246 = term247.
Proof. exact (MK_COMB (@lem1705692) (@lem1705691)). Qed.
Lemma lem1705706 (x : real) (n : nat) : (term248 x n) = (term248 x n).
Proof. exact (eq_refl (term248 x n)). Qed.
Lemma lem1705707 (x : real) : (term249 x) = (term249 x).
Proof. exact (fun_ext (fun n : nat => @lem1705706 x n)). Qed.
Lemma lem1705708 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1705709 (x : real) : (term250 x) = (term250 x).
Proof. exact (MK_COMB (@lem1705708) (@lem1705707 x)). Qed.
Lemma lem1705710 : term251 = term251.
Proof. exact (fun_ext (fun x : real => @lem1705709 x)). Qed.
Lemma lem1705711 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1705712 : term222 = term222.
Proof. exact (MK_COMB (@lem1705711) (@lem1705710)). Qed.
Lemma lem1705713 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1705714 : term221 = term221.
Proof. exact (MK_COMB (@lem1705713) (@lem1705712)). Qed.
Lemma lem1705715 (y : real) (x : real) : ((term252 x y) = x) = ((term252 x y) = x).
Proof. exact (eq_refl ((term252 x y) = x)). Qed.
Lemma lem1705716 (x : real) : (term253 x) = (term253 x).
Proof. exact (fun_ext (fun y : real => @lem1705715 y x)). Qed.
Lemma lem1705717 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1705718 (x : real) : (term254 x) = (term254 x).
Proof. exact (MK_COMB (@lem1705717) (@lem1705716 x)). Qed.
Lemma lem1705719 : term255 = term255.
Proof. exact (fun_ext (fun x : real => @lem1705718 x)). Qed.
Lemma lem1705720 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1705721 : term256 = term256.
Proof. exact (MK_COMB (@lem1705720) (@lem1705719)). Qed.
Lemma lem1705722 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1705723 : term223 = term223.
Proof. exact (MK_COMB (@lem1705722) (@lem1705721)). Qed.
Lemma lem1705724 : term225 = term225.
Proof. exact (MK_COMB (@lem1705723) (@lem1705714)). Qed.
Lemma lem1705729 (x : real) : (term82 x) = (term82 x).
Proof. exact (eq_refl (term82 x)). Qed.
Lemma lem1705730 : term257 = term257.
Proof. exact (fun_ext (fun x : real => @lem1705729 x)). Qed.
Lemma lem1705731 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1705732 : term83 = term83.
Proof. exact (MK_COMB (@lem1705731) (@lem1705730)). Qed.
Lemma lem1705733 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1705734 : term226 = term226.
Proof. exact (MK_COMB (@lem1705733) (@lem1705732)). Qed.
Lemma lem1705735 : term228 = term228.
Proof. exact (MK_COMB (@lem1705734) (@lem1705724)). Qed.
Lemma lem1705740 (x : real) (n : nat) : (term229 x n) = (term229 x n).
Proof. exact (eq_refl (term229 x n)). Qed.
Lemma lem1705741 (x : real) (n : nat) : (term231 x n) = (term231 x n).
Proof. exact (MK_COMB (@lem1705740 x n) (@lem1705735)). Qed.
Lemma lem1705744 (y : real) (n : nat) (x : real) : (term184 y n x) = (term184 y n x).
Proof. exact (eq_refl (term184 y n x)). Qed.
Lemma lem1705745 (y : real) (x : real) (n : nat) : (term233 y x n) = (term233 y x n).
Proof. exact (MK_COMB (@lem1705744 y n x) (@lem1705741 x n)). Qed.
Lemma lem1705748 (x : real) : (term234 x) = (term234 x).
Proof. exact (eq_refl (term234 x)). Qed.
Lemma lem1705749 (y : real) (x : real) (n : nat) : (term235 y x n) = (term235 y x n).
Proof. exact (MK_COMB (@lem1705748 x) (@lem1705745 y x n)). Qed.
Lemma lem1705750 (x : real) (n : nat) : (term237 x n) = (term237 x n).
Proof. exact (fun_ext (fun y : real => @lem1705749 y x n)). Qed.
Lemma lem1705751 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1705752 (x : real) (n : nat) : (term239 x n) = (term239 x n).
Proof. exact (MK_COMB (@lem1705751) (@lem1705750 x n)). Qed.
Lemma lem1705753 (n : nat) : (term241 n) = (term241 n).
Proof. exact (fun_ext (fun x : real => @lem1705752 x n)). Qed.
Lemma lem1705754 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1705755 (n : nat) : (term243 n) = (term243 n).
Proof. exact (MK_COMB (@lem1705754) (@lem1705753 n)). Qed.
Lemma lem1705756 : term245 = term245.
Proof. exact (fun_ext (fun n : nat => @lem1705755 n)). Qed.
Lemma lem1705757 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1705758 : term247 = term247.
Proof. exact (MK_COMB (@lem1705757) (@lem1705756)). Qed.
Lemma lem1705823 : term246 = term247.
Proof. exact (TRANS (@lem1705701) (@lem1705758)). Qed.
Lemma lem1705824 : term247 = term246.
Proof. exact (SYM (@lem1705823)). Qed.
Lemma lem1705828 (h1 : term83) : term83.
Proof. exact (h1). Qed.
Lemma lem1705829 (h1 : term256) : term256.
Proof. exact (h1). Qed.
Lemma lem1705830 (h1 : term222) : term222.
Proof. exact (h1). Qed.
Lemma lem1705836 (x : real) (h1 : term2 x) : term2 x.
Proof. exact (h1). Qed.
Lemma lem1705848 (x : real) (n : nat) (h1 : term215 x n) : term215 x n.
Proof. exact (h1). Qed.
Lemma lem1705855 (x : real) : (term82 x) = (term258 x).
Proof. exact (@lem17265 (term2 x) (term3 x)). Qed.
Lemma lem1705856 : term257 = term259.
Proof. exact (fun_ext (fun x : real => @lem1705855 x)). Qed.
Lemma lem1705857 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1705910 : term83 = term260.
Proof. exact (MK_COMB (@lem1705857) (@lem1705856)). Qed.
Lemma lem1705911 (h1 : term83) : term260.
Proof. exact (EQ_MP (@lem1705910) (@lem1705828 h1)). Qed.
Lemma lem1705912 (y : real) (x : real) : ((term252 x y) = x) = ((term252 x y) = x).
Proof. exact (eq_refl ((term252 x y) = x)). Qed.
Lemma lem1705913 (x : real) : (term253 x) = (term253 x).
Proof. exact (fun_ext (fun y : real => @lem1705912 y x)). Qed.
Lemma lem1705914 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1705915 (x : real) : (term254 x) = (term254 x).
Proof. exact (MK_COMB (@lem1705914) (@lem1705913 x)). Qed.
Lemma lem1705916 : term255 = term255.
Proof. exact (fun_ext (fun x : real => @lem1705915 x)). Qed.
Lemma lem1705917 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1705930 : term256 = term256.
Proof. exact (MK_COMB (@lem1705917) (@lem1705916)). Qed.
Lemma lem1705931 (h1 : term256) : term256.
Proof. exact (EQ_MP (@lem1705930) (@lem1705829 h1)). Qed.
Lemma lem1705938 (x : real) (n : nat) : (term248 x n) = (term261 x n).
Proof. exact (@lem17265 (term262 x) (term263 x n)). Qed.
Lemma lem1705939 (x : real) : (term249 x) = (term264 x).
Proof. exact (fun_ext (fun n : nat => @lem1705938 x n)). Qed.
Lemma lem1705940 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1705941 (x : real) : (term250 x) = (term265 x).
Proof. exact (MK_COMB (@lem1705940) (@lem1705939 x)). Qed.
Lemma lem1705942 : term251 = term266.
Proof. exact (fun_ext (fun x : real => @lem1705941 x)). Qed.
Lemma lem1705943 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1705944 : term222 = term267.
Proof. exact (MK_COMB (@lem1705943) (@lem1705942)). Qed.
Lemma lem1705950 {A : Type'} (P : Prop) (Q : A -> Prop) : (term268 A P Q) = (term269 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem1705951 (P : Prop) (Q : nat -> Prop) : (term270 P Q) = (term271 P Q).
Proof. exact (@lem1705950 nat P Q). Qed.
Lemma lem1705952 (x : real) : (term272 x) = (term273 x).
Proof. exact (@lem1705951 (term274 x) (term275 x)). Qed.
Lemma lem1705953 (x : real) (n : nat) : (term276 x n) = (term263 x n).
Proof. exact (eq_refl (term276 x n)). Qed.
Lemma lem1705954 (x : real) : (term277 x) = (term277 x).
Proof. exact (eq_refl (term277 x)). Qed.
Lemma lem1705955 (x : real) (n : nat) : (term278 x n) = (term261 x n).
Proof. exact (MK_COMB (@lem1705954 x) (@lem1705953 x n)). Qed.
Lemma lem1705956 (x : real) : (term279 x) = (term264 x).
Proof. exact (fun_ext (fun n : nat => @lem1705955 x n)). Qed.
Lemma lem1705957 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1705958 (x : real) : (term272 x) = (term265 x).
Proof. exact (MK_COMB (@lem1705957) (@lem1705956 x)). Qed.
Lemma lem1705959 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1705960 (x : real) : (term280 x) = (term281 x).
Proof. exact (MK_COMB (@lem1705959) (@lem1705958 x)). Qed.
Lemma lem1705961 (x : real) (n : nat) : (term276 x n) = (term263 x n).
Proof. exact (eq_refl (term276 x n)). Qed.
Lemma lem1705962 (x : real) : (term282 x) = (term275 x).
Proof. exact (fun_ext (fun n : nat => @lem1705961 x n)). Qed.
Lemma lem1705963 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1705964 (x : real) : (term283 x) = (term284 x).
Proof. exact (MK_COMB (@lem1705963) (@lem1705962 x)). Qed.
Lemma lem1705965 (x : real) : (term277 x) = (term277 x).
Proof. exact (eq_refl (term277 x)). Qed.
Lemma lem1705966 (x : real) : (term273 x) = (term285 x).
Proof. exact (MK_COMB (@lem1705965 x) (@lem1705964 x)). Qed.
Lemma lem1705967 (x : real) : ((term272 x) = (term273 x)) = ((term265 x) = (term285 x)).
Proof. exact (MK_COMB (@lem1705960 x) (@lem1705966 x)). Qed.
Lemma lem1705968 (x : real) : (term265 x) = (term285 x).
Proof. exact (EQ_MP (@lem1705967 x) (@lem1705952 x)). Qed.
Lemma lem1705973 : term266 = term286.
Proof. exact (fun_ext (fun x : real => @lem1705968 x)). Qed.
Lemma lem1705974 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1706025 : term267 = term287.
Proof. exact (MK_COMB (@lem1705974) (@lem1705973)). Qed.
Lemma lem1706026 : term222 = term287.
Proof. exact (TRANS (@lem1705944) (@lem1706025)). Qed.
Lemma lem1706027 (h1 : term222) : term287.
Proof. exact (EQ_MP (@lem1706026) (@lem1705830 h1)). Qed.
Lemma lem1706039 (x : real) (h1 : term2 x) : term2 x.
Proof. exact (h1). Qed.
Lemma lem1706099 (x : real) (n : nat) (h1 : term215 x n) : term215 x n.
Proof. exact (h1). Qed.
Lemma lem1706134 (x : real) : (term258 x) = (term258 x).
Proof. exact (eq_refl (term258 x)). Qed.
Lemma lem1706135 : term259 = term259.
Proof. exact (fun_ext (fun x : real => @lem1706134 x)). Qed.
Lemma lem1706136 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1706137 : term260 = term260.
Proof. exact (MK_COMB (@lem1706136) (@lem1706135)). Qed.
Lemma lem1706138 (h1 : term83) : term260.
Proof. exact (EQ_MP (@lem1706137) (@lem1705911 h1)). Qed.
Lemma lem1706151 (y : real) (x : real) : ((term252 x y) = x) = ((term252 x y) = x).
Proof. exact (eq_refl ((term252 x y) = x)). Qed.
Lemma lem1706152 (x : real) : (term253 x) = (term253 x).
Proof. exact (fun_ext (fun y : real => @lem1706151 y x)). Qed.
Lemma lem1706153 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1706154 (x : real) : (term254 x) = (term254 x).
Proof. exact (MK_COMB (@lem1706153) (@lem1706152 x)). Qed.
Lemma lem1706155 : term255 = term255.
Proof. exact (fun_ext (fun x : real => @lem1706154 x)). Qed.
Lemma lem1706156 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1706157 : term256 = term256.
Proof. exact (MK_COMB (@lem1706156) (@lem1706155)). Qed.
Lemma lem1706158 (h1 : term256) : term256.
Proof. exact (EQ_MP (@lem1706157) (@lem1705931 h1)). Qed.
Lemma lem1706193 (x : real) (n : nat) : (term263 x n) = (term263 x n).
Proof. exact (eq_refl (term263 x n)). Qed.
Lemma lem1706194 (x : real) : (term275 x) = (term275 x).
Proof. exact (fun_ext (fun n : nat => @lem1706193 x n)). Qed.
Lemma lem1706195 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1706196 (x : real) : (term284 x) = (term284 x).
Proof. exact (MK_COMB (@lem1706195) (@lem1706194 x)). Qed.
Lemma lem1706209 (x : real) : (term277 x) = (term277 x).
Proof. exact (eq_refl (term277 x)). Qed.
Lemma lem1706210 (x : real) : (term285 x) = (term285 x).
Proof. exact (MK_COMB (@lem1706209 x) (@lem1706196 x)). Qed.
Lemma lem1706211 : term286 = term286.
Proof. exact (fun_ext (fun x : real => @lem1706210 x)). Qed.
Lemma lem1706212 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1706213 : term287 = term287.
Proof. exact (MK_COMB (@lem1706212) (@lem1706211)). Qed.
Lemma lem1706214 (h1 : term222) : term287.
Proof. exact (EQ_MP (@lem1706213) (@lem1706027 h1)). Qed.
Lemma lem1706218 (x : real) (h1 : term2 x) : term2 x.
Proof. exact (h1). Qed.
Lemma lem1706226 (x : real) (n : nat) (h1 : term215 x n) : term215 x n.
Proof. exact (h1). Qed.
Lemma lem1706234 (x : real) : (term258 x) = (term258 x).
Proof. exact (eq_refl (term258 x)). Qed.
Lemma lem1706235 : term259 = term259.
Proof. exact (fun_ext (fun x : real => @lem1706234 x)). Qed.
Lemma lem1706236 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1706238 : term260 = term260.
Proof. exact (MK_COMB (@lem1706236) (@lem1706235)). Qed.
Lemma lem1706239 (h1 : term83) : term260.
Proof. exact (EQ_MP (@lem1706238) (@lem1706138 h1)). Qed.
Lemma lem1706241 (y : real) (x : real) : ((term252 x y) = x) = ((term252 x y) = x).
Proof. exact (eq_refl ((term252 x y) = x)). Qed.
Lemma lem1706242 (x : real) : (term253 x) = (term253 x).
Proof. exact (fun_ext (fun y : real => @lem1706241 y x)). Qed.
Lemma lem1706243 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1706244 (x : real) : (term254 x) = (term254 x).
Proof. exact (MK_COMB (@lem1706243) (@lem1706242 x)). Qed.
Lemma lem1706245 : term255 = term255.
Proof. exact (fun_ext (fun x : real => @lem1706244 x)). Qed.
Lemma lem1706246 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1706248 : term256 = term256.
Proof. exact (MK_COMB (@lem1706246) (@lem1706245)). Qed.
Lemma lem1706249 (h1 : term256) : term256.
Proof. exact (EQ_MP (@lem1706248) (@lem1706158 h1)). Qed.
Lemma lem1706251 {A : Type'} (P : Prop) (Q : A -> Prop) : (term269 A P Q) = (term268 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem1706252 (P : Prop) (Q : nat -> Prop) : (term271 P Q) = (term270 P Q).
Proof. exact (@lem1706251 nat P Q). Qed.
Lemma lem1706253 (x : real) : (term273 x) = (term272 x).
Proof. exact (@lem1706252 (term274 x) (term275 x)). Qed.
Lemma lem1706254 (x : real) (n : nat) : (term276 x n) = (term263 x n).
Proof. exact (eq_refl (term276 x n)). Qed.
Lemma lem1706255 (x : real) : (term282 x) = (term275 x).
Proof. exact (fun_ext (fun n : nat => @lem1706254 x n)). Qed.
Lemma lem1706256 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1706257 (x : real) : (term283 x) = (term284 x).
Proof. exact (MK_COMB (@lem1706256) (@lem1706255 x)). Qed.
Lemma lem1706258 (x : real) : (term277 x) = (term277 x).
Proof. exact (eq_refl (term277 x)). Qed.
Lemma lem1706259 (x : real) : (term273 x) = (term285 x).
Proof. exact (MK_COMB (@lem1706258 x) (@lem1706257 x)). Qed.
Lemma lem1706260 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1706261 (x : real) : (term288 x) = (term289 x).
Proof. exact (MK_COMB (@lem1706260) (@lem1706259 x)). Qed.
Lemma lem1706262 (x : real) (n : nat) : (term276 x n) = (term263 x n).
Proof. exact (eq_refl (term276 x n)). Qed.
Lemma lem1706263 (x : real) : (term277 x) = (term277 x).
Proof. exact (eq_refl (term277 x)). Qed.
Lemma lem1706264 (x : real) (n : nat) : (term278 x n) = (term261 x n).
Proof. exact (MK_COMB (@lem1706263 x) (@lem1706262 x n)). Qed.
Lemma lem1706265 (x : real) : (term279 x) = (term264 x).
Proof. exact (fun_ext (fun n : nat => @lem1706264 x n)). Qed.
Lemma lem1706266 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1706267 (x : real) : (term272 x) = (term265 x).
Proof. exact (MK_COMB (@lem1706266) (@lem1706265 x)). Qed.
Lemma lem1706268 (x : real) : ((term273 x) = (term272 x)) = ((term285 x) = (term265 x)).
Proof. exact (MK_COMB (@lem1706261 x) (@lem1706267 x)). Qed.
Lemma lem1706269 (x : real) : (term285 x) = (term265 x).
Proof. exact (EQ_MP (@lem1706268 x) (@lem1706253 x)). Qed.
Lemma lem1706270 : term286 = term266.
Proof. exact (fun_ext (fun x : real => @lem1706269 x)). Qed.
Lemma lem1706271 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1706272 : term287 = term267.
Proof. exact (MK_COMB (@lem1706271) (@lem1706270)). Qed.
Lemma lem1706279 (x : real) (n : nat) : (term261 x n) = (term261 x n).
Proof. exact (eq_refl (term261 x n)). Qed.
Lemma lem1706280 (x : real) : (term264 x) = (term264 x).
Proof. exact (fun_ext (fun n : nat => @lem1706279 x n)). Qed.
Lemma lem1706281 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1706282 (x : real) : (term265 x) = (term265 x).
Proof. exact (MK_COMB (@lem1706281) (@lem1706280 x)). Qed.
Lemma lem1706283 : term266 = term266.
Proof. exact (fun_ext (fun x : real => @lem1706282 x)). Qed.
Lemma lem1706284 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1706285 : term267 = term267.
Proof. exact (MK_COMB (@lem1706284) (@lem1706283)). Qed.
Lemma lem1706286 : term287 = term267.
Proof. exact (TRANS (@lem1706272) (@lem1706285)). Qed.
Lemma lem1706287 (h1 : term222) : term267.
Proof. exact (EQ_MP (@lem1706286) (@lem1706214 h1)). Qed.
Lemma lem1706288 (_26409 : real) (h1 : term83) : term290 _26409.
Proof. exact (@lem1706239 h1 _26409). Qed.
Lemma lem1706289 (_26409 : real) : (term290 _26409) = (term258 _26409).
Proof. exact (eq_refl (term290 _26409)). Qed.
Lemma lem1706291 (_26410 : real) (h1 : term256) : term291 _26410.
Proof. exact (@lem1706249 h1 _26410). Qed.
Lemma lem1706292 (_26410 : real) : (term291 _26410) = (term254 _26410).
Proof. exact (eq_refl (term291 _26410)). Qed.
Lemma lem1706293 (_26410 : real) (h1 : term256) : term254 _26410.
Proof. exact (EQ_MP (@lem1706292 _26410) (@lem1706291 _26410 h1)). Qed.
Lemma lem1706294 (_26410 : real) (_26411 : real) (h1 : term256) : term292 _26410 _26411.
Proof. exact (@lem1706293 _26410 h1 _26411). Qed.
Lemma lem1706295 (_26411 : real) (_26410 : real) : (term292 _26410 _26411) = ((term252 _26410 _26411) = _26410).
Proof. exact (eq_refl (term292 _26410 _26411)). Qed.
Lemma lem1706297 (_26412 : real) (h1 : term222) : term293 _26412.
Proof. exact (@lem1706287 h1 _26412). Qed.
Lemma lem1706298 (_26412 : real) : (term293 _26412) = (term265 _26412).
Proof. exact (eq_refl (term293 _26412)). Qed.
Lemma lem1706299 (_26412 : real) (h1 : term222) : term265 _26412.
Proof. exact (EQ_MP (@lem1706298 _26412) (@lem1706297 _26412 h1)). Qed.
Lemma lem1706300 (_26412 : real) (_26413 : nat) (h1 : term222) : term294 _26412 _26413.
Proof. exact (@lem1706299 _26412 h1 _26413). Qed.
Lemma lem1706301 (_26412 : real) (_26413 : nat) : (term294 _26412 _26413) = (term261 _26412 _26413).
Proof. exact (eq_refl (term294 _26412 _26413)). Qed.
Lemma lem1706304 (x : real) (h1 : term2 x) : term2 x.
Proof. exact (h1). Qed.
Lemma lem1706308 (x : real) (n : nat) (h1 : term215 x n) : term215 x n.
Proof. exact (h1). Qed.
Lemma lem1706314 (_26409 : real) (h1 : term83) : term258 _26409.
Proof. exact (EQ_MP (@lem1706289 _26409) (@lem1706288 _26409 h1)). Qed.
Lemma lem1706322 (_26412 : real) (_26413 : nat) (h1 : term222) : term261 _26412 _26413.
Proof. exact (EQ_MP (@lem1706301 _26412 _26413) (@lem1706300 _26412 _26413 h1)). Qed.
Lemma lem1706323 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1706324 (_26414 : real) (_26416 : real) (h1 : _26414 = _26416) : _26414 = _26416.
Proof. exact (h1). Qed.
Lemma lem1706325 (_26415 : real) (_26417 : real) (h1 : _26415 = _26417) : _26415 = _26417.
Proof. exact (h1). Qed.
Lemma lem1706326 (_26414 : real) (_26416 : real) (h1 : _26414 = _26416) : (real_le _26414) = (real_le _26416).
Proof. exact (MK_COMB (@lem1706323) (@lem1706324 _26414 _26416 h1)). Qed.
Lemma lem1706327 (_26414 : real) (_26416 : real) (_26415 : real) (_26417 : real) (h1 : _26414 = _26416) (h2 : _26415 = _26417) : (real_le _26414 _26415) = (real_le _26416 _26417).
Proof. exact (MK_COMB (@lem1706326 _26414 _26416 h1) (@lem1706325 _26415 _26417 h2)). Qed.
Lemma lem1706329 (b : Prop) (a : Prop) : term295 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1706330 (_26416 : real) (_26417 : real) (_26414 : real) (_26415 : real) : term296 _26416 _26417 _26414 _26415.
Proof. exact (@lem1706329 (real_le _26416 _26417) (real_le _26414 _26415)). Qed.
Lemma lem1706331 (_26414 : real) (_26416 : real) (_26415 : real) (_26417 : real) (h1 : _26414 = _26416) (h2 : _26415 = _26417) : term297 _26416 _26417 _26414 _26415.
Proof. exact (@lem1706330 _26416 _26417 _26414 _26415 (@lem1706327 _26414 _26416 _26415 _26417 h1 h2)). Qed.
Lemma lem1706332 (_26417 : real) (_26415 : real) (_26414 : real) (_26416 : real) (h1 : _26414 = _26416) : term298 _26416 _26417 _26414 _26415.
Proof. exact (fun h0 : _26415 = _26417 => @lem1706331 _26414 _26416 _26415 _26417 h1 h0). Qed.
Lemma lem1706334 (a : Prop) (b : Prop) : (a -> b) = (term299 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1706335 (_26416 : real) (_26417 : real) (_26414 : real) (_26415 : real) : (term298 _26416 _26417 _26414 _26415) = (term300 _26416 _26417 _26414 _26415).
Proof. exact (@lem1706334 (_26415 = _26417) (term297 _26416 _26417 _26414 _26415)). Qed.
Lemma lem1706336 (_26417 : real) (_26415 : real) (_26414 : real) (_26416 : real) (h1 : _26414 = _26416) : term300 _26416 _26417 _26414 _26415.
Proof. exact (EQ_MP (@lem1706335 _26416 _26417 _26414 _26415) (@lem1706332 _26417 _26415 _26414 _26416 h1)). Qed.
Lemma lem1706337 (_26416 : real) (_26417 : real) (_26414 : real) (_26415 : real) : term301 _26416 _26417 _26414 _26415.
Proof. exact (fun h0 : _26414 = _26416 => @lem1706336 _26417 _26415 _26414 _26416 h0). Qed.
Lemma lem1706339 (a : Prop) (b : Prop) : (a -> b) = (term299 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1706340 (_26416 : real) (_26417 : real) (_26414 : real) (_26415 : real) : (term301 _26416 _26417 _26414 _26415) = (term302 _26416 _26417 _26414 _26415).
Proof. exact (@lem1706339 (_26414 = _26416) (term300 _26416 _26417 _26414 _26415)). Qed.
Lemma lem1706341 (_26416 : real) (_26417 : real) (_26414 : real) (_26415 : real) : term302 _26416 _26417 _26414 _26415.
Proof. exact (EQ_MP (@lem1706340 _26416 _26417 _26414 _26415) (@lem1706337 _26416 _26417 _26414 _26415)). Qed.
Lemma lem1706376 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem1706377 (_26426 : real) (_26428 : real) (h1 : _26426 = _26428) : _26426 = _26428.
Proof. exact (h1). Qed.
Lemma lem1706378 (_26427 : nat) (_26429 : nat) (h1 : _26427 = _26429) : _26427 = _26429.
Proof. exact (h1). Qed.
Lemma lem1706379 (_26426 : real) (_26428 : real) (h1 : _26426 = _26428) : (real_pow _26426) = (real_pow _26428).
Proof. exact (MK_COMB (@lem1706376) (@lem1706377 _26426 _26428 h1)). Qed.
Lemma lem1706380 (_26427 : nat) (_26429 : nat) (_26426 : real) (_26428 : real) (h1 : _26427 = _26429) (h2 : _26426 = _26428) : (real_pow _26426 _26427) = (real_pow _26428 _26429).
Proof. exact (MK_COMB (@lem1706379 _26426 _26428 h2) (@lem1706378 _26427 _26429 h1)). Qed.
Lemma lem1706381 (_26426 : real) (_26428 : real) (_26427 : nat) (_26429 : nat) (h1 : _26427 = _26429) : term303 _26426 _26427 _26428 _26429.
Proof. exact (fun h0 : _26426 = _26428 => @lem1706380 _26427 _26429 _26426 _26428 h1 h0). Qed.
Lemma lem1706383 (a : Prop) (b : Prop) : (a -> b) = (term299 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1706384 (_26426 : real) (_26427 : nat) (_26428 : real) (_26429 : nat) : (term303 _26426 _26427 _26428 _26429) = (term304 _26426 _26427 _26428 _26429).
Proof. exact (@lem1706383 (_26426 = _26428) ((real_pow _26426 _26427) = (real_pow _26428 _26429))). Qed.
Lemma lem1706385 (_26426 : real) (_26428 : real) (_26427 : nat) (_26429 : nat) (h1 : _26427 = _26429) : term304 _26426 _26427 _26428 _26429.
Proof. exact (EQ_MP (@lem1706384 _26426 _26427 _26428 _26429) (@lem1706381 _26426 _26428 _26427 _26429 h1)). Qed.
Lemma lem1706386 (_26426 : real) (_26427 : nat) (_26428 : real) (_26429 : nat) : term305 _26426 _26427 _26428 _26429.
Proof. exact (fun h0 : _26427 = _26429 => @lem1706385 _26426 _26428 _26427 _26429 h0). Qed.
Lemma lem1706388 (a : Prop) (b : Prop) : (a -> b) = (term299 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1706389 (_26426 : real) (_26427 : nat) (_26428 : real) (_26429 : nat) : (term305 _26426 _26427 _26428 _26429) = (term306 _26426 _26427 _26428 _26429).
Proof. exact (@lem1706388 (_26427 = _26429) (term304 _26426 _26427 _26428 _26429)). Qed.
Lemma lem1706390 (_26426 : real) (_26427 : nat) (_26428 : real) (_26429 : nat) : term306 _26426 _26427 _26428 _26429.
Proof. exact (EQ_MP (@lem1706389 _26426 _26427 _26428 _26429) (@lem1706386 _26426 _26427 _26428 _26429)). Qed.
Lemma lem1706450 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1706451 (n : nat) (x : real) : (term307 n x) = (term307 n x).
Proof. exact (@lem1706450 (term307 n x)). Qed.
Lemma lem1706452 (n : nat) (x : real) : term308 n x.
Proof. exact (fun h0 : term309 n x => @lem1706451 n x). Qed.
Lemma lem1706454 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1706455 (n : nat) (x : real) : (term308 n x) = ((term307 n x) = (term307 n x)).
Proof. exact (@lem1706454 ((term307 n x) = (term307 n x))). Qed.
Lemma lem1706456 (n : nat) (x : real) : (term307 n x) = (term307 n x).
Proof. exact (EQ_MP (@lem1706455 n x) (@lem1706452 n x)). Qed.
Lemma lem1706458 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1706459 (n : nat) : n = n.
Proof. exact (@lem1706458 n). Qed.
Lemma lem1706460 (n : nat) : term311 n.
Proof. exact (fun h0 : term312 n => @lem1706459 n). Qed.
Lemma lem1706462 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1706463 (n : nat) : (term311 n) = (n = n).
Proof. exact (@lem1706462 (n = n)). Qed.
Lemma lem1706464 (n : nat) : n = n.
Proof. exact (EQ_MP (@lem1706463 n) (@lem1706460 n)). Qed.
Lemma lem1706466 (_26411 : real) (_26410 : real) (h1 : term256) : (term252 _26410 _26411) = _26410.
Proof. exact (EQ_MP (@lem1706295 _26411 _26410) (@lem1706294 _26410 _26411 h1)). Qed.
Lemma lem1706467 (x : real) (h1 : term256) : (term313 x) = x.
Proof. exact (@lem1706466 term5 x h1). Qed.
Lemma lem1706468 (x : real) (h1 : term256) : term314 x.
Proof. exact (fun h0 : term315 x => @lem1706467 x h1). Qed.
Lemma lem1706470 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1706471 (x : real) : (term314 x) = ((term313 x) = x).
Proof. exact (@lem1706470 ((term313 x) = x)). Qed.
Lemma lem1706472 (x : real) (h1 : term256) : (term313 x) = x.
Proof. exact (EQ_MP (@lem1706471 x) (@lem1706468 x h1)). Qed.
Lemma lem1706490 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1706491 (_26427 : nat) (_26429 : nat) (_26426 : real) (_26428 : real) : (term304 _26426 _26427 _26428 _26429) = (term316 _26427 _26429 _26426 _26428).
Proof. exact (@lem1706490 ((real_pow _26426 _26427) = (real_pow _26428 _26429)) (term317 _26426 _26428)). Qed.
Lemma lem1706501 (_26427 : nat) (_26429 : nat) : (term318 _26427 _26429) = (term318 _26427 _26429).
Proof. exact (eq_refl (term318 _26427 _26429)). Qed.
Lemma lem1706502 (_26427 : nat) (_26429 : nat) (_26426 : real) (_26428 : real) : (term306 _26426 _26427 _26428 _26429) = (term319 _26427 _26429 _26426 _26428).
Proof. exact (MK_COMB (@lem1706501 _26427 _26429) (@lem1706491 _26427 _26429 _26426 _26428)). Qed.
Lemma lem1706506 (q : Prop) (p : Prop) (r : Prop) : (term320 p q r) = (term320 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1706507 (_26427 : nat) (_26429 : nat) (_26426 : real) (_26428 : real) : (term319 _26427 _26429 _26426 _26428) = (term321 _26427 _26429 _26426 _26428).
Proof. exact (@lem1706506 ((real_pow _26426 _26427) = (real_pow _26428 _26429)) (term322 _26427 _26429) (term317 _26426 _26428)). Qed.
Lemma lem1706529 (_26427 : nat) (_26429 : nat) (_26426 : real) (_26428 : real) : (term306 _26426 _26427 _26428 _26429) = (term321 _26427 _26429 _26426 _26428).
Proof. exact (TRANS (@lem1706502 _26427 _26429 _26426 _26428) (@lem1706507 _26427 _26429 _26426 _26428)). Qed.
Lemma lem1706530 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1706531 (_26427 : nat) (_26429 : nat) (_26426 : real) (_26428 : real) : (term323 _26426 _26427 _26428 _26429) = (term324 _26427 _26429 _26426 _26428).
Proof. exact (MK_COMB (@lem1706530) (@lem1706529 _26427 _26429 _26426 _26428)). Qed.
Lemma lem1706553 (_26427 : nat) (_26429 : nat) (_26426 : real) (_26428 : real) : (term321 _26427 _26429 _26426 _26428) = (term321 _26427 _26429 _26426 _26428).
Proof. exact (eq_refl (term321 _26427 _26429 _26426 _26428)). Qed.
Lemma lem1706554 (_26427 : nat) (_26429 : nat) (_26426 : real) (_26428 : real) : ((term306 _26426 _26427 _26428 _26429) = (term321 _26427 _26429 _26426 _26428)) = ((term321 _26427 _26429 _26426 _26428) = (term321 _26427 _26429 _26426 _26428)).
Proof. exact (MK_COMB (@lem1706531 _26427 _26429 _26426 _26428) (@lem1706553 _26427 _26429 _26426 _26428)). Qed.
Lemma lem1706556 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1706557 (x : Prop) : (x = x) = True.
Proof. exact (@lem1706556 Prop x). Qed.
Lemma lem1706558 (_26427 : nat) (_26429 : nat) (_26426 : real) (_26428 : real) : ((term321 _26427 _26429 _26426 _26428) = (term321 _26427 _26429 _26426 _26428)) = True.
Proof. exact (@lem1706557 (term321 _26427 _26429 _26426 _26428)). Qed.
Lemma lem1706559 (_26427 : nat) (_26429 : nat) (_26426 : real) (_26428 : real) : ((term306 _26426 _26427 _26428 _26429) = (term321 _26427 _26429 _26426 _26428)) = True.
Proof. exact (TRANS (@lem1706554 _26427 _26429 _26426 _26428) (@lem1706558 _26427 _26429 _26426 _26428)). Qed.
Lemma lem1706560 (_26427 : nat) (_26429 : nat) (_26426 : real) (_26428 : real) : True = ((term306 _26426 _26427 _26428 _26429) = (term321 _26427 _26429 _26426 _26428)).
Proof. exact (SYM (@lem1706559 _26427 _26429 _26426 _26428)). Qed.
Lemma lem1706561 (_26427 : nat) (_26429 : nat) (_26426 : real) (_26428 : real) : (term306 _26426 _26427 _26428 _26429) = (term321 _26427 _26429 _26426 _26428).
Proof. exact (EQ_MP (@lem1706560 _26427 _26429 _26426 _26428) (@lem0)). Qed.
Lemma lem1706562 (_26427 : nat) (_26429 : nat) (_26426 : real) (_26428 : real) : term321 _26427 _26429 _26426 _26428.
Proof. exact (EQ_MP (@lem1706561 _26427 _26429 _26426 _26428) (@lem1706390 _26426 _26427 _26428 _26429)). Qed.
Lemma lem1706564 (b : Prop) (a : Prop) : (a \/ b) = (term325 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1706565 (_26426 : real) (_26427 : nat) (_26428 : real) (_26429 : nat) : (term321 _26427 _26429 _26426 _26428) = (term326 _26426 _26427 _26428 _26429).
Proof. exact (@lem1706564 (term327 _26427 _26429 _26426 _26428) ((real_pow _26426 _26427) = (real_pow _26428 _26429))). Qed.
Lemma lem1706567 (a : Prop) (b : Prop) : (term328 a b) = (term329 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1706568 (_26427 : nat) (_26429 : nat) (_26426 : real) (_26428 : real) : (term330 _26427 _26429 _26426 _26428) = (term331 _26427 _26429 _26426 _26428).
Proof. exact (@lem1706567 (term322 _26427 _26429) (term317 _26426 _26428)). Qed.
Lemma lem1706570 (a : Prop) : (term332 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1706571 (_26427 : nat) (_26429 : nat) : (term333 _26427 _26429) = (_26427 = _26429).
Proof. exact (@lem1706570 (_26427 = _26429)). Qed.
Lemma lem1706572 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1706573 (_26427 : nat) (_26429 : nat) : (term334 _26427 _26429) = (term335 _26427 _26429).
Proof. exact (MK_COMB (@lem1706572) (@lem1706571 _26427 _26429)). Qed.
Lemma lem1706575 (a : Prop) : (term332 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1706576 (_26426 : real) (_26428 : real) : (term336 _26426 _26428) = (_26426 = _26428).
Proof. exact (@lem1706575 (_26426 = _26428)). Qed.
Lemma lem1706577 (_26427 : nat) (_26429 : nat) (_26426 : real) (_26428 : real) : (term331 _26427 _26429 _26426 _26428) = (term337 _26427 _26429 _26426 _26428).
Proof. exact (MK_COMB (@lem1706573 _26427 _26429) (@lem1706576 _26426 _26428)). Qed.
Lemma lem1706578 (_26427 : nat) (_26429 : nat) (_26426 : real) (_26428 : real) : (term330 _26427 _26429 _26426 _26428) = (term337 _26427 _26429 _26426 _26428).
Proof. exact (TRANS (@lem1706568 _26427 _26429 _26426 _26428) (@lem1706577 _26427 _26429 _26426 _26428)). Qed.
Lemma lem1706579 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1706580 (_26427 : nat) (_26429 : nat) (_26426 : real) (_26428 : real) : (term338 _26427 _26429 _26426 _26428) = (term339 _26427 _26429 _26426 _26428).
Proof. exact (MK_COMB (@lem1706579) (@lem1706578 _26427 _26429 _26426 _26428)). Qed.
Lemma lem1706581 (_26426 : real) (_26427 : nat) (_26428 : real) (_26429 : nat) : ((real_pow _26426 _26427) = (real_pow _26428 _26429)) = ((real_pow _26426 _26427) = (real_pow _26428 _26429)).
Proof. exact (eq_refl ((real_pow _26426 _26427) = (real_pow _26428 _26429))). Qed.
Lemma lem1706582 (_26426 : real) (_26427 : nat) (_26428 : real) (_26429 : nat) : (term326 _26426 _26427 _26428 _26429) = (term340 _26426 _26427 _26428 _26429).
Proof. exact (MK_COMB (@lem1706580 _26427 _26429 _26426 _26428) (@lem1706581 _26426 _26427 _26428 _26429)). Qed.
Lemma lem1706583 (_26426 : real) (_26427 : nat) (_26428 : real) (_26429 : nat) : (term321 _26427 _26429 _26426 _26428) = (term340 _26426 _26427 _26428 _26429).
Proof. exact (TRANS (@lem1706565 _26426 _26427 _26428 _26429) (@lem1706582 _26426 _26427 _26428 _26429)). Qed.
Lemma lem1706585 (n : nat) (x : real) (h1 : term256) : term341 n x.
Proof. exact (conj (@lem1706464 n) (@lem1706472 x h1)). Qed.
Lemma lem1706587 (_26426 : real) (_26427 : nat) (_26428 : real) (_26429 : nat) : term340 _26426 _26427 _26428 _26429.
Proof. exact (EQ_MP (@lem1706583 _26426 _26427 _26428 _26429) (@lem1706562 _26427 _26429 _26426 _26428)). Qed.
Lemma lem1706588 (x : real) (n : nat) : term342 x n.
Proof. exact (@lem1706587 (term313 x) n x n). Qed.
Lemma lem1706591 (x : real) (n : nat) (h1 : term256) : (term343 x n) = (real_pow x n).
Proof. exact (@lem1706588 x n (@lem1706585 n x h1)). Qed.
Lemma lem1706592 (x : real) (n : nat) (h1 : term256) : term344 x n.
Proof. exact (fun h0 : term345 x n => @lem1706591 x n h1). Qed.
Lemma lem1706594 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1706595 (x : real) (n : nat) : (term344 x n) = ((term343 x n) = (real_pow x n)).
Proof. exact (@lem1706594 ((term343 x n) = (real_pow x n))). Qed.
Lemma lem1706596 (x : real) (n : nat) (h1 : term256) : (term343 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem1706595 x n) (@lem1706592 x n h1)). Qed.
Lemma lem1706598 (x : real) (h1 : term2 x) : term2 x.
Proof. exact (h1). Qed.
Lemma lem1706599 (x : real) (h1 : term2 x) : term346 x.
Proof. exact (fun h0 : term347 x => @lem1706598 x h1). Qed.
Lemma lem1706601 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1706602 (x : real) : (term346 x) = (term2 x).
Proof. exact (@lem1706601 (term2 x)). Qed.
Lemma lem1706603 (x : real) (h1 : term2 x) : term2 x.
Proof. exact (EQ_MP (@lem1706602 x) (@lem1706599 x h1)). Qed.
Lemma lem1706609 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1706610 (_26409 : real) : (term258 _26409) = (term348 _26409).
Proof. exact (@lem1706609 (term3 _26409) (term347 _26409)). Qed.
Lemma lem1706616 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1706617 (_26409 : real) : (term349 _26409) = (term350 _26409).
Proof. exact (MK_COMB (@lem1706616) (@lem1706610 _26409)). Qed.
Lemma lem1706623 (_26409 : real) : (term348 _26409) = (term348 _26409).
Proof. exact (eq_refl (term348 _26409)). Qed.
Lemma lem1706624 (_26409 : real) : ((term258 _26409) = (term348 _26409)) = ((term348 _26409) = (term348 _26409)).
Proof. exact (MK_COMB (@lem1706617 _26409) (@lem1706623 _26409)). Qed.
Lemma lem1706626 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1706627 (x : Prop) : (x = x) = True.
Proof. exact (@lem1706626 Prop x). Qed.
Lemma lem1706628 (_26409 : real) : ((term348 _26409) = (term348 _26409)) = True.
Proof. exact (@lem1706627 (term348 _26409)). Qed.
Lemma lem1706629 (_26409 : real) : ((term258 _26409) = (term348 _26409)) = True.
Proof. exact (TRANS (@lem1706624 _26409) (@lem1706628 _26409)). Qed.
Lemma lem1706630 (_26409 : real) : True = ((term258 _26409) = (term348 _26409)).
Proof. exact (SYM (@lem1706629 _26409)). Qed.
Lemma lem1706631 (_26409 : real) : (term258 _26409) = (term348 _26409).
Proof. exact (EQ_MP (@lem1706630 _26409) (@lem0)). Qed.
Lemma lem1706632 (_26409 : real) (h1 : term83) : term348 _26409.
Proof. exact (EQ_MP (@lem1706631 _26409) (@lem1706314 _26409 h1)). Qed.
Lemma lem1706634 (b : Prop) (a : Prop) : (a \/ b) = (term325 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1706635 (_26409 : real) : (term348 _26409) = (term351 _26409).
Proof. exact (@lem1706634 (term347 _26409) (term3 _26409)). Qed.
Lemma lem1706637 (a : Prop) : (term332 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1706638 (_26409 : real) : (term352 _26409) = (term2 _26409).
Proof. exact (@lem1706637 (term2 _26409)). Qed.
Lemma lem1706639 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1706640 (_26409 : real) : (term353 _26409) = (term234 _26409).
Proof. exact (MK_COMB (@lem1706639) (@lem1706638 _26409)). Qed.
Lemma lem1706641 (_26409 : real) : (term3 _26409) = (term3 _26409).
Proof. exact (eq_refl (term3 _26409)). Qed.
Lemma lem1706642 (_26409 : real) : (term351 _26409) = (term82 _26409).
Proof. exact (MK_COMB (@lem1706640 _26409) (@lem1706641 _26409)). Qed.
Lemma lem1706643 (_26409 : real) : (term348 _26409) = (term82 _26409).
Proof. exact (TRANS (@lem1706635 _26409) (@lem1706642 _26409)). Qed.
Lemma lem1706646 (_26409 : real) (h1 : term83) : term82 _26409.
Proof. exact (EQ_MP (@lem1706643 _26409) (@lem1706632 _26409 h1)). Qed.
Lemma lem1706647 (x : real) (h1 : term83) : term82 x.
Proof. exact (@lem1706646 x h1). Qed.
Lemma lem1706650 (x : real) (h1 : term83) (h2 : term2 x) : term3 x.
Proof. exact (@lem1706647 x h1 (@lem1706603 x h2)). Qed.
Lemma lem1706651 (x : real) (h1 : term83) (h2 : term2 x) : term354 x.
Proof. exact (fun h0 : term22 x => @lem1706650 x h1 h2). Qed.
Lemma lem1706653 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1706654 (x : real) : (term354 x) = (term3 x).
Proof. exact (@lem1706653 (term3 x)). Qed.
Lemma lem1706655 (x : real) (h1 : term83) (h2 : term2 x) : term3 x.
Proof. exact (EQ_MP (@lem1706654 x) (@lem1706651 x h1 h2)). Qed.
Lemma lem1706661 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1706662 (_26413 : nat) (_26412 : real) : (term261 _26412 _26413) = (term355 _26413 _26412).
Proof. exact (@lem1706661 (term263 _26412 _26413) (term274 _26412)). Qed.
Lemma lem1706668 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1706669 (_26413 : nat) (_26412 : real) : (term356 _26412 _26413) = (term357 _26413 _26412).
Proof. exact (MK_COMB (@lem1706668) (@lem1706662 _26413 _26412)). Qed.
Lemma lem1706675 (_26413 : nat) (_26412 : real) : (term355 _26413 _26412) = (term355 _26413 _26412).
Proof. exact (eq_refl (term355 _26413 _26412)). Qed.
Lemma lem1706676 (_26413 : nat) (_26412 : real) : ((term261 _26412 _26413) = (term355 _26413 _26412)) = ((term355 _26413 _26412) = (term355 _26413 _26412)).
Proof. exact (MK_COMB (@lem1706669 _26413 _26412) (@lem1706675 _26413 _26412)). Qed.
Lemma lem1706678 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1706679 (x : Prop) : (x = x) = True.
Proof. exact (@lem1706678 Prop x). Qed.
Lemma lem1706680 (_26413 : nat) (_26412 : real) : ((term355 _26413 _26412) = (term355 _26413 _26412)) = True.
Proof. exact (@lem1706679 (term355 _26413 _26412)). Qed.
Lemma lem1706681 (_26413 : nat) (_26412 : real) : ((term261 _26412 _26413) = (term355 _26413 _26412)) = True.
Proof. exact (TRANS (@lem1706676 _26413 _26412) (@lem1706680 _26413 _26412)). Qed.
Lemma lem1706682 (_26413 : nat) (_26412 : real) : True = ((term261 _26412 _26413) = (term355 _26413 _26412)).
Proof. exact (SYM (@lem1706681 _26413 _26412)). Qed.
Lemma lem1706683 (_26413 : nat) (_26412 : real) : (term261 _26412 _26413) = (term355 _26413 _26412).
Proof. exact (EQ_MP (@lem1706682 _26413 _26412) (@lem0)). Qed.
Lemma lem1706684 (_26413 : nat) (_26412 : real) (h1 : term222) : term355 _26413 _26412.
Proof. exact (EQ_MP (@lem1706683 _26413 _26412) (@lem1706322 _26412 _26413 h1)). Qed.
Lemma lem1706686 (b : Prop) (a : Prop) : (a \/ b) = (term325 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1706687 (_26412 : real) (_26413 : nat) : (term355 _26413 _26412) = (term358 _26412 _26413).
Proof. exact (@lem1706686 (term274 _26412) (term263 _26412 _26413)). Qed.
Lemma lem1706689 (a : Prop) : (term332 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1706690 (_26412 : real) : (term359 _26412) = (term262 _26412).
Proof. exact (@lem1706689 (term262 _26412)). Qed.
Lemma lem1706691 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1706692 (_26412 : real) : (term360 _26412) = (term361 _26412).
Proof. exact (MK_COMB (@lem1706691) (@lem1706690 _26412)). Qed.
Lemma lem1706693 (_26412 : real) (_26413 : nat) : (term263 _26412 _26413) = (term263 _26412 _26413).
Proof. exact (eq_refl (term263 _26412 _26413)). Qed.
Lemma lem1706694 (_26412 : real) (_26413 : nat) : (term358 _26412 _26413) = (term248 _26412 _26413).
Proof. exact (MK_COMB (@lem1706692 _26412) (@lem1706693 _26412 _26413)). Qed.
Lemma lem1706695 (_26412 : real) (_26413 : nat) : (term355 _26413 _26412) = (term248 _26412 _26413).
Proof. exact (TRANS (@lem1706687 _26412 _26413) (@lem1706694 _26412 _26413)). Qed.
Lemma lem1706698 (_26412 : real) (_26413 : nat) (h1 : term222) : term248 _26412 _26413.
Proof. exact (EQ_MP (@lem1706695 _26412 _26413) (@lem1706684 _26413 _26412 h1)). Qed.
Lemma lem1706699 (x : real) (_26413 : nat) (h1 : term222) : term362 x _26413.
Proof. exact (@lem1706698 (term6 x) _26413 h1). Qed.
Lemma lem1706702 (_26413 : nat) (x : real) (h1 : term222) (h2 : term83) (h3 : term2 x) : term363 x _26413.
Proof. exact (@lem1706699 x _26413 h1 (@lem1706655 x h2 h3)). Qed.
Lemma lem1706703 (n : nat) (x : real) (h1 : term222) (h2 : term83) (h3 : term2 x) : term363 x n.
Proof. exact (@lem1706702 n x h1 h2 h3). Qed.
Lemma lem1706704 (n : nat) (x : real) (h1 : term222) (h2 : term83) (h3 : term2 x) : term364 x n.
Proof. exact (fun h0 : term365 x n => @lem1706703 n x h1 h2 h3). Qed.
Lemma lem1706706 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1706707 (x : real) (n : nat) : (term364 x n) = (term363 x n).
Proof. exact (@lem1706706 (term363 x n)). Qed.
Lemma lem1706708 (n : nat) (x : real) (h1 : term222) (h2 : term83) (h3 : term2 x) : term363 x n.
Proof. exact (EQ_MP (@lem1706707 x n) (@lem1706704 n x h1 h2 h3)). Qed.
Lemma lem1706726 (q : Prop) (p : Prop) (r : Prop) : (term320 p q r) = (term320 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1706727 (_26416 : real) (_26417 : real) (_26414 : real) (_26415 : real) : (term300 _26416 _26417 _26414 _26415) = (term366 _26416 _26417 _26414 _26415).
Proof. exact (@lem1706726 (real_le _26416 _26417) (term317 _26415 _26417) (term367 _26414 _26415)). Qed.
Lemma lem1706745 (_26414 : real) (_26416 : real) : (term368 _26414 _26416) = (term368 _26414 _26416).
Proof. exact (eq_refl (term368 _26414 _26416)). Qed.
Lemma lem1706746 (_26416 : real) (_26417 : real) (_26414 : real) (_26415 : real) : (term302 _26416 _26417 _26414 _26415) = (term369 _26416 _26417 _26414 _26415).
Proof. exact (MK_COMB (@lem1706745 _26414 _26416) (@lem1706727 _26416 _26417 _26414 _26415)). Qed.
Lemma lem1706750 (q : Prop) (p : Prop) (r : Prop) : (term320 p q r) = (term320 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1706751 (_26416 : real) (_26417 : real) (_26414 : real) (_26415 : real) : (term369 _26416 _26417 _26414 _26415) = (term370 _26416 _26417 _26414 _26415).
Proof. exact (@lem1706750 (real_le _26416 _26417) (term317 _26414 _26416) (term371 _26417 _26414 _26415)). Qed.
Lemma lem1706781 (_26416 : real) (_26417 : real) (_26414 : real) (_26415 : real) : (term302 _26416 _26417 _26414 _26415) = (term370 _26416 _26417 _26414 _26415).
Proof. exact (TRANS (@lem1706746 _26416 _26417 _26414 _26415) (@lem1706751 _26416 _26417 _26414 _26415)). Qed.
Lemma lem1706782 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1706783 (_26416 : real) (_26417 : real) (_26414 : real) (_26415 : real) : (term372 _26416 _26417 _26414 _26415) = (term373 _26416 _26417 _26414 _26415).
Proof. exact (MK_COMB (@lem1706782) (@lem1706781 _26416 _26417 _26414 _26415)). Qed.
Lemma lem1706813 (_26416 : real) (_26417 : real) (_26414 : real) (_26415 : real) : (term370 _26416 _26417 _26414 _26415) = (term370 _26416 _26417 _26414 _26415).
Proof. exact (eq_refl (term370 _26416 _26417 _26414 _26415)). Qed.
Lemma lem1706814 (_26416 : real) (_26417 : real) (_26414 : real) (_26415 : real) : ((term302 _26416 _26417 _26414 _26415) = (term370 _26416 _26417 _26414 _26415)) = ((term370 _26416 _26417 _26414 _26415) = (term370 _26416 _26417 _26414 _26415)).
Proof. exact (MK_COMB (@lem1706783 _26416 _26417 _26414 _26415) (@lem1706813 _26416 _26417 _26414 _26415)). Qed.
Lemma lem1706816 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1706817 (x : Prop) : (x = x) = True.
Proof. exact (@lem1706816 Prop x). Qed.
Lemma lem1706818 (_26416 : real) (_26417 : real) (_26414 : real) (_26415 : real) : ((term370 _26416 _26417 _26414 _26415) = (term370 _26416 _26417 _26414 _26415)) = True.
Proof. exact (@lem1706817 (term370 _26416 _26417 _26414 _26415)). Qed.
Lemma lem1706819 (_26416 : real) (_26417 : real) (_26414 : real) (_26415 : real) : ((term302 _26416 _26417 _26414 _26415) = (term370 _26416 _26417 _26414 _26415)) = True.
Proof. exact (TRANS (@lem1706814 _26416 _26417 _26414 _26415) (@lem1706818 _26416 _26417 _26414 _26415)). Qed.
Lemma lem1706820 (_26416 : real) (_26417 : real) (_26414 : real) (_26415 : real) : True = ((term302 _26416 _26417 _26414 _26415) = (term370 _26416 _26417 _26414 _26415)).
Proof. exact (SYM (@lem1706819 _26416 _26417 _26414 _26415)). Qed.
Lemma lem1706821 (_26416 : real) (_26417 : real) (_26414 : real) (_26415 : real) : (term302 _26416 _26417 _26414 _26415) = (term370 _26416 _26417 _26414 _26415).
Proof. exact (EQ_MP (@lem1706820 _26416 _26417 _26414 _26415) (@lem0)). Qed.
Lemma lem1706822 (_26416 : real) (_26417 : real) (_26414 : real) (_26415 : real) : term370 _26416 _26417 _26414 _26415.
Proof. exact (EQ_MP (@lem1706821 _26416 _26417 _26414 _26415) (@lem1706341 _26416 _26417 _26414 _26415)). Qed.
Lemma lem1706824 (b : Prop) (a : Prop) : (a \/ b) = (term325 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1706825 (_26414 : real) (_26415 : real) (_26416 : real) (_26417 : real) : (term370 _26416 _26417 _26414 _26415) = (term374 _26414 _26415 _26416 _26417).
Proof. exact (@lem1706824 (term375 _26416 _26417 _26414 _26415) (real_le _26416 _26417)). Qed.
Lemma lem1706827 (a : Prop) (b : Prop) : (term328 a b) = (term329 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1706828 (_26416 : real) (_26417 : real) (_26414 : real) (_26415 : real) : (term376 _26416 _26417 _26414 _26415) = (term377 _26416 _26417 _26414 _26415).
Proof. exact (@lem1706827 (term317 _26414 _26416) (term371 _26417 _26414 _26415)). Qed.
Lemma lem1706830 (a : Prop) : (term332 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1706831 (_26414 : real) (_26416 : real) : (term336 _26414 _26416) = (_26414 = _26416).
Proof. exact (@lem1706830 (_26414 = _26416)). Qed.
Lemma lem1706832 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1706833 (_26414 : real) (_26416 : real) : (term378 _26414 _26416) = (term379 _26414 _26416).
Proof. exact (MK_COMB (@lem1706832) (@lem1706831 _26414 _26416)). Qed.
Lemma lem1706835 (a : Prop) (b : Prop) : (term328 a b) = (term329 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1706836 (_26417 : real) (_26414 : real) (_26415 : real) : (term380 _26417 _26414 _26415) = (term381 _26417 _26414 _26415).
Proof. exact (@lem1706835 (term317 _26415 _26417) (term367 _26414 _26415)). Qed.
Lemma lem1706838 (a : Prop) : (term332 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1706839 (_26415 : real) (_26417 : real) : (term336 _26415 _26417) = (_26415 = _26417).
Proof. exact (@lem1706838 (_26415 = _26417)). Qed.
Lemma lem1706840 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1706841 (_26415 : real) (_26417 : real) : (term378 _26415 _26417) = (term379 _26415 _26417).
Proof. exact (MK_COMB (@lem1706840) (@lem1706839 _26415 _26417)). Qed.
Lemma lem1706843 (a : Prop) : (term332 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1706844 (_26414 : real) (_26415 : real) : (term382 _26414 _26415) = (real_le _26414 _26415).
Proof. exact (@lem1706843 (real_le _26414 _26415)). Qed.
Lemma lem1706845 (_26417 : real) (_26414 : real) (_26415 : real) : (term381 _26417 _26414 _26415) = (term383 _26417 _26414 _26415).
Proof. exact (MK_COMB (@lem1706841 _26415 _26417) (@lem1706844 _26414 _26415)). Qed.
Lemma lem1706846 (_26417 : real) (_26414 : real) (_26415 : real) : (term380 _26417 _26414 _26415) = (term383 _26417 _26414 _26415).
Proof. exact (TRANS (@lem1706836 _26417 _26414 _26415) (@lem1706845 _26417 _26414 _26415)). Qed.
Lemma lem1706847 (_26416 : real) (_26417 : real) (_26414 : real) (_26415 : real) : (term377 _26416 _26417 _26414 _26415) = (term384 _26416 _26417 _26414 _26415).
Proof. exact (MK_COMB (@lem1706833 _26414 _26416) (@lem1706846 _26417 _26414 _26415)). Qed.
Lemma lem1706848 (_26416 : real) (_26417 : real) (_26414 : real) (_26415 : real) : (term376 _26416 _26417 _26414 _26415) = (term384 _26416 _26417 _26414 _26415).
Proof. exact (TRANS (@lem1706828 _26416 _26417 _26414 _26415) (@lem1706847 _26416 _26417 _26414 _26415)). Qed.
Lemma lem1706849 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1706850 (_26416 : real) (_26417 : real) (_26414 : real) (_26415 : real) : (term385 _26416 _26417 _26414 _26415) = (term386 _26416 _26417 _26414 _26415).
Proof. exact (MK_COMB (@lem1706849) (@lem1706848 _26416 _26417 _26414 _26415)). Qed.
Lemma lem1706851 (_26416 : real) (_26417 : real) : (real_le _26416 _26417) = (real_le _26416 _26417).
Proof. exact (eq_refl (real_le _26416 _26417)). Qed.
Lemma lem1706852 (_26414 : real) (_26415 : real) (_26416 : real) (_26417 : real) : (term374 _26414 _26415 _26416 _26417) = (term387 _26414 _26415 _26416 _26417).
Proof. exact (MK_COMB (@lem1706850 _26416 _26417 _26414 _26415) (@lem1706851 _26416 _26417)). Qed.
Lemma lem1706853 (_26414 : real) (_26415 : real) (_26416 : real) (_26417 : real) : (term370 _26416 _26417 _26414 _26415) = (term387 _26414 _26415 _26416 _26417).
Proof. exact (TRANS (@lem1706825 _26414 _26415 _26416 _26417) (@lem1706852 _26414 _26415 _26416 _26417)). Qed.
Lemma lem1706855 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term2 x) : term388 x n.
Proof. exact (conj (@lem1706596 x n h2) (@lem1706708 n x h1 h3 h4)). Qed.
Lemma lem1706856 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term2 x) : term389 x n.
Proof. exact (conj (@lem1706456 n x) (@lem1706855 n x h1 h2 h3 h4)). Qed.
Lemma lem1706858 (_26414 : real) (_26415 : real) (_26416 : real) (_26417 : real) : term387 _26414 _26415 _26416 _26417.
Proof. exact (EQ_MP (@lem1706853 _26414 _26415 _26416 _26417) (@lem1706822 _26416 _26417 _26414 _26415)). Qed.
Lemma lem1706859 (x : real) (n : nat) : term390 x n.
Proof. exact (@lem1706858 (term307 n x) (term343 x n) (term307 n x) (real_pow x n)). Qed.
Lemma lem1706862 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term2 x) : term210 x n.
Proof. exact (@lem1706859 x n (@lem1706856 n x h1 h2 h3 h4)). Qed.
Lemma lem1706863 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term2 x) : term391 x n.
Proof. exact (fun h0 : term215 x n => @lem1706862 n x h1 h2 h3 h4). Qed.
Lemma lem1706865 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1706866 (x : real) (n : nat) : (term391 x n) = (term210 x n).
Proof. exact (@lem1706865 (term210 x n)). Qed.
Lemma lem1706867 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term2 x) : term210 x n.
Proof. exact (EQ_MP (@lem1706866 x n) (@lem1706863 n x h1 h2 h3 h4)). Qed.
Lemma lem1706870 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1706872 (x : real) (n : nat) : (term215 x n) = (term392 x n).
Proof. exact (@lem1706870 (term210 x n)). Qed.
Lemma lem1706875 (x : real) (n : nat) (h1 : term215 x n) : term392 x n.
Proof. exact (EQ_MP (@lem1706872 x n) (@lem1706308 x n h1)). Qed.
Lemma lem1706878 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : False.
Proof. exact (@lem1706875 x n h4 (@lem1706867 n x h1 h2 h3 h5)). Qed.
Lemma lem1706879 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : term393.
Proof. exact (fun h0 : ~ False => @lem1706878 n x h1 h2 h3 h4 h5). Qed.
Lemma lem1706881 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1706882 : term393 = False.
Proof. exact (@lem1706881 False). Qed.
Lemma lem1706883 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : False.
Proof. exact (EQ_MP (@lem1706882) (@lem1706879 n x h1 h2 h3 h4 h5)). Qed.
Lemma lem1706884 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : (term215 x n) = False.
Proof. exact (prop_ext (fun h6 : term215 x n => @lem1706883 n x h1 h2 h3 h4 h5) (fun h6 : False => @lem1706308 x n h4)). Qed.
Lemma lem1706885 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : False.
Proof. exact (EQ_MP (@lem1706884 n x h1 h2 h3 h4 h5) (@lem1706308 x n h4)). Qed.
Lemma lem1706886 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : (term2 x) = False.
Proof. exact (prop_ext (fun h6 : term2 x => @lem1706885 n x h1 h2 h3 h4 h5) (fun h6 : False => @lem1706304 x h5)). Qed.
Lemma lem1706887 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : False.
Proof. exact (EQ_MP (@lem1706886 n x h1 h2 h3 h4 h5) (@lem1706304 x h5)). Qed.
Lemma lem1706888 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : (term215 x n) = False.
Proof. exact (prop_ext (fun h6 : term215 x n => @lem1706887 n x h1 h2 h3 h4 h5) (fun h6 : False => @lem1706226 x n h4)). Qed.
Lemma lem1706889 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : False.
Proof. exact (EQ_MP (@lem1706888 n x h1 h2 h3 h4 h5) (@lem1706226 x n h4)). Qed.
Lemma lem1706890 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : (term2 x) = False.
Proof. exact (prop_ext (fun h6 : term2 x => @lem1706889 n x h1 h2 h3 h4 h5) (fun h6 : False => @lem1706218 x h5)). Qed.
Lemma lem1706891 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : False.
Proof. exact (EQ_MP (@lem1706890 n x h1 h2 h3 h4 h5) (@lem1706218 x h5)). Qed.
Lemma lem1706892 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : term256 = False.
Proof. exact (prop_ext (fun h6 : term256 => @lem1706891 n x h1 h2 h3 h4 h5) (fun h6 : False => @lem1706249 h2)). Qed.
Lemma lem1706893 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : False.
Proof. exact (EQ_MP (@lem1706892 n x h1 h2 h3 h4 h5) (@lem1706249 h2)). Qed.
Lemma lem1706894 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : (term215 x n) = False.
Proof. exact (prop_ext (fun h6 : term215 x n => @lem1706893 n x h1 h2 h3 h4 h5) (fun h6 : False => @lem1706226 x n h4)). Qed.
Lemma lem1706895 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : False.
Proof. exact (EQ_MP (@lem1706894 n x h1 h2 h3 h4 h5) (@lem1706226 x n h4)). Qed.
Lemma lem1706896 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : (term2 x) = False.
Proof. exact (prop_ext (fun h6 : term2 x => @lem1706895 n x h1 h2 h3 h4 h5) (fun h6 : False => @lem1706218 x h5)). Qed.
Lemma lem1706897 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : False.
Proof. exact (EQ_MP (@lem1706896 n x h1 h2 h3 h4 h5) (@lem1706218 x h5)). Qed.
Lemma lem1706898 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : term256 = False.
Proof. exact (prop_ext (fun h6 : term256 => @lem1706897 n x h1 h2 h3 h4 h5) (fun h6 : False => @lem1706158 h2)). Qed.
Lemma lem1706899 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : False.
Proof. exact (EQ_MP (@lem1706898 n x h1 h2 h3 h4 h5) (@lem1706158 h2)). Qed.
Lemma lem1706900 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : (term215 x n) = False.
Proof. exact (prop_ext (fun h6 : term215 x n => @lem1706899 n x h1 h2 h3 h4 h5) (fun h6 : False => @lem1706099 x n h4)). Qed.
Lemma lem1706901 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : False.
Proof. exact (EQ_MP (@lem1706900 n x h1 h2 h3 h4 h5) (@lem1706099 x n h4)). Qed.
Lemma lem1706902 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : (term2 x) = False.
Proof. exact (prop_ext (fun h6 : term2 x => @lem1706901 n x h1 h2 h3 h4 h5) (fun h6 : False => @lem1706039 x h5)). Qed.
Lemma lem1706903 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : False.
Proof. exact (EQ_MP (@lem1706902 n x h1 h2 h3 h4 h5) (@lem1706039 x h5)). Qed.
Lemma lem1706904 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : term256 = False.
Proof. exact (prop_ext (fun h6 : term256 => @lem1706903 n x h1 h2 h3 h4 h5) (fun h6 : False => @lem1705931 h2)). Qed.
Lemma lem1706905 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : False.
Proof. exact (EQ_MP (@lem1706904 n x h1 h2 h3 h4 h5) (@lem1705931 h2)). Qed.
Lemma lem1706906 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : (term215 x n) = False.
Proof. exact (prop_ext (fun h6 : term215 x n => @lem1706905 n x h1 h2 h3 h4 h5) (fun h6 : False => @lem1705848 x n h4)). Qed.
Lemma lem1706907 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : False.
Proof. exact (EQ_MP (@lem1706906 n x h1 h2 h3 h4 h5) (@lem1705848 x n h4)). Qed.
Lemma lem1706908 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : (term2 x) = False.
Proof. exact (prop_ext (fun h6 : term2 x => @lem1706907 n x h1 h2 h3 h4 h5) (fun h6 : False => @lem1705836 x h5)). Qed.
Lemma lem1706909 (n : nat) (x : real) (h1 : term222) (h2 : term256) (h3 : term83) (h4 : term215 x n) (h5 : term2 x) : False.
Proof. exact (EQ_MP (@lem1706908 n x h1 h2 h3 h4 h5) (@lem1705836 x h5)). Qed.
Lemma lem1706910 (n : nat) (x : real) (h1 : term256) (h2 : term83) (h3 : term215 x n) (h4 : term2 x) : term220.
Proof. exact (fun h0 : term222 => @lem1706909 n x h0 h1 h2 h3 h4). Qed.
Lemma lem1706911 : term220 = term221.
Proof. exact (@lem69 term222). Qed.
Lemma lem1706912 (n : nat) (x : real) (h1 : term256) (h2 : term83) (h3 : term215 x n) (h4 : term2 x) : term221.
Proof. exact (EQ_MP (@lem1706911) (@lem1706910 n x h1 h2 h3 h4)). Qed.
Lemma lem1706913 (n : nat) (x : real) (h1 : term83) (h2 : term215 x n) (h3 : term2 x) : term225.
Proof. exact (fun h0 : term256 => @lem1706912 n x h0 h1 h2 h3). Qed.
Lemma lem1706914 (n : nat) (x : real) (h1 : term215 x n) (h2 : term2 x) : term228.
Proof. exact (fun h0 : term83 => @lem1706913 n x h0 h1 h2). Qed.
Lemma lem1706915 (n : nat) (x : real) (h1 : term2 x) : term231 x n.
Proof. exact (fun h0 : term215 x n => @lem1706914 n x h0 h1). Qed.
Lemma lem1706916 (y : real) (n : nat) (x : real) (h1 : term2 x) : term233 y x n.
Proof. exact (fun h0 : term182 y n x => @lem1706915 n x h1). Qed.
Lemma lem1706917 (y : real) (x : real) (n : nat) : term235 y x n.
Proof. exact (fun h0 : term2 x => @lem1706916 y n x h0). Qed.
Lemma lem1706922 (x : real) (n : nat) : term239 x n.
Proof. exact (fun y : real => @lem1706917 y x n). Qed.
Lemma lem1706927 (n : nat) : term243 n.
Proof. exact (fun x : real => @lem1706922 x n). Qed.
Lemma lem1706932 : term247.
Proof. exact (fun n : nat => @lem1706927 n). Qed.
Lemma lem1706933 : term246.
Proof. exact (EQ_MP (@lem1705824) (@lem1706932)). Qed.
Lemma lem1706934 (n : nat) : term394 n.
Proof. exact (@lem1706933 n). Qed.
Lemma lem1706935 (n : nat) : (term394 n) = (term242 n).
Proof. exact (eq_refl (term394 n)). Qed.
Lemma lem1706936 (n : nat) : term242 n.
Proof. exact (EQ_MP (@lem1706935 n) (@lem1706934 n)). Qed.
Lemma lem1706937 (n : nat) (x : real) : term395 n x.
Proof. exact (@lem1706936 n x). Qed.
Lemma lem1706938 (x : real) (n : nat) : (term395 n x) = (term238 x n).
Proof. exact (eq_refl (term395 n x)). Qed.
Lemma lem1706939 (x : real) (n : nat) : term238 x n.
Proof. exact (EQ_MP (@lem1706938 x n) (@lem1706937 n x)). Qed.
Lemma lem1706940 (x : real) (n : nat) (y : real) : term396 x n y.
Proof. exact (@lem1706939 x n y). Qed.
Lemma lem1706941 (y : real) (x : real) (n : nat) : (term396 x n y) = (term216 y x n).
Proof. exact (eq_refl (term396 x n y)). Qed.
Lemma lem1706942 (y : real) (x : real) (n : nat) : term216 y x n.
Proof. exact (EQ_MP (@lem1706941 y x n) (@lem1706940 x n y)). Qed.
Lemma lem1706944 (y : real) (x : real) (n : nat) : term216 y x n.
Proof. exact (@lem1705607 y x n (@lem1706942 y x n)). Qed.
Lemma lem1706945 (y : real) (n : nat) (x : real) (h1 : term2 x) : term232 y x n.
Proof. exact (@lem1706944 y x n (@lem1705467 x h1)). Qed.
Lemma lem1706946 (y : real) (n : nat) (x : real) (h1 : term182 y n x) (h2 : term2 x) : term230 x n.
Proof. exact (@lem1706945 y n x h2 (@lem1705552 y n x h1)). Qed.
Lemma lem1706947 (y : real) (n : nat) (x : real) (h1 : term215 x n) (h2 : term182 y n x) (h3 : term2 x) : term227.
Proof. exact (@lem1706946 y n x h2 h3 (@lem1705592 x n h1)). Qed.
Lemma lem1706948 (y : real) (n : nat) (x : real) (h1 : term215 x n) (h2 : term182 y n x) (h3 : term2 x) : term224.
Proof. exact (@lem1706947 y n x h1 h2 h3 (@lem1705218)). Qed.
Lemma lem1706949 (y : real) (n : nat) (x : real) (h1 : term215 x n) (h2 : term182 y n x) (h3 : term2 x) : term220.
Proof. exact (@lem1706948 y n x h1 h2 h3 (@lem1505085)). Qed.
Lemma lem1706950 (y : real) (n : nat) (x : real) (h1 : term215 x n) (h2 : term182 y n x) (h3 : term2 x) : False.
Proof. exact (@lem1706949 y n x h1 h2 h3 (@lem1704991)). Qed.
Lemma lem1706951 (y : real) (n : nat) (x : real) (h1 : term215 x n) (h2 : term182 y n x) (h3 : term2 x) : (term215 x n) = False.
Proof. exact (prop_ext (fun h4 : term215 x n => @lem1706950 y n x h1 h2 h3) (fun h4 : False => @lem1705592 x n h1)). Qed.
Lemma lem1706952 (y : real) (n : nat) (x : real) (h1 : term215 x n) (h2 : term182 y n x) (h3 : term2 x) : False.
Proof. exact (EQ_MP (@lem1706951 y n x h1 h2 h3) (@lem1705592 x n h1)). Qed.
Lemma lem1706953 (y : real) (n : nat) (x : real) (h1 : term182 y n x) (h2 : term2 x) : term214 x n.
Proof. exact (fun h0 : term215 x n => @lem1706952 y n x h0 h1 h2). Qed.
Lemma lem1706954 (y : real) (n : nat) (x : real) (h1 : term182 y n x) (h2 : term2 x) : term210 x n.
Proof. exact (EQ_MP (@lem1705591 x n) (@lem1706953 y n x h1 h2)). Qed.
Lemma lem1706955 (y : real) (n : nat) (x : real) (h1 : term182 y n x) (h2 : term2 x) : term211 y x n.
Proof. exact (EQ_MP (@lem1705587 y n x h1) (@lem1706954 y n x h1 h2)). Qed.
Lemma lem1706956 (y : real) (n : nat) (x : real) (h1 : term182 y n x) (h2 : term2 x) : term397 y x n.
Proof. exact (ex_intro (term398 y x n) (term307 n x) (@lem1706955 y n x h1 h2)). Qed.
Lemma lem1706957 (y : real) (n : nat) (x : real) (h1 : term182 y n x) (h2 : term2 x) : term186 y x n.
Proof. exact (@lem1705555 y x n (@lem1706956 y n x h1 h2)). Qed.
Lemma lem1706958 (y : real) (n : nat) (x : real) (h1 : term2 x) : term188 y x n.
Proof. exact (fun h0 : term182 y n x => @lem1706957 y n x h0 h1). Qed.
Lemma lem1706963 (y : real) (x : real) (h1 : term2 x) : term192 y x.
Proof. exact (fun n : nat => @lem1706958 y n x h1). Qed.
Lemma lem1706964 (y : real) (x : real) (h1 : term2 x) : term202 y x.
Proof. exact (@lem1705551 y x (@lem1706963 y x h1)). Qed.
Lemma lem1706965 (y : real) (x : real) (h1 : term168 x) (h2 : term2 x) : term172 y x.
Proof. exact (@lem1706964 y x h2 (@lem1705524 y x h1)). Qed.
Lemma lem1706966 (y : real) (x : real) (h1 : term2 x) : term174 y x.
Proof. exact (fun h0 : term168 x => @lem1706965 y x h0 h1). Qed.
Lemma lem1706967 (y : real) (x : real) (h1 : term2 x) : term173 y x.
Proof. exact (EQ_MP (@lem1705520 y x h1) (@lem1706966 y x h1)). Qed.
Lemma lem1706968 (y : real) (x : real) (h1 : term2 x) : term172 y x.
Proof. exact (@lem1706967 y x h1 (@lem1705466 x)). Qed.
Lemma lem1706969 (y : real) (x : real) (h1 : term2 x) : (term2 x) = (term172 y x).
Proof. exact (prop_ext (fun h2 : term2 x => @lem1706968 y x h1) (fun h2 : term172 y x => @lem1705467 x h1)). Qed.
Lemma lem1706970 (y : real) (x : real) (h1 : term2 x) : term172 y x.
Proof. exact (EQ_MP (@lem1706969 y x h1) (@lem1705467 x h1)). Qed.
Lemma lem1706971 (y : real) (x : real) : term399 y x.
Proof. exact (fun h0 : term2 x => @lem1706970 y x h0). Qed.
Lemma lem1706976 (x : real) : term400 x.
Proof. exact (fun y : real => @lem1706971 y x). Qed.
Lemma lem1706981 : term401.
Proof. exact (fun x : real => @lem1706976 x). Qed.
