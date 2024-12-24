Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_CLAUSES_NUMSEG_LE_term_abbrevs.
Require Import FINITE_NUMSEG_LE_spec.
Require Import INT_POS_spec.
Require Import ITERATE_CLAUSES_spec.
Require Import ITERATE_SING_spec.
Require Import NUMSEG_CLAUSES_LE_spec.
Require Import monoidal_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm196_spec.
Require Import thm197_spec.
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
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
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
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem6195012 (m : nat) : (S m) = (term0 m).
Proof. exact (EQ_MP (@lem2841417 m) (@lem2841416 m)). Qed.
Lemma lem6195013 (k : nat) : (S k) = (term0 k).
Proof. exact (@lem6195012 k). Qed.
Lemma lem6195014 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem6195015 (k : nat) : (term1 k) = (term2 k).
Proof. exact (MK_COMB (@lem6195014) (@lem6195013 k)). Qed.
Lemma lem6195016 (k : nat) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem6195017 (k : nat) : (term3 k) = (term4 k).
Proof. exact (MK_COMB (@lem6195015 k) (@lem6195016 k)). Qed.
Lemma lem6195018 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6195036 (k : nat) : (term5 k) = (term6 k).
Proof. exact (MK_COMB (@lem6195018) (@lem6195017 k)). Qed.
Lemma lem6195038 (m : nat) (n : nat) : (Peano.le m n) = (term7 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem6195039 (k : nat) : (term4 k) = (term8 k).
Proof. exact (@lem6195038 (term0 k) k). Qed.
Lemma lem6195041 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem6195042 (k : nat) : (term11 k) = (term12 k).
Proof. exact (@lem6195041 k term13). Qed.
Lemma lem6195043 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem6195044 (k : nat) : (term14 k) = (term15 k).
Proof. exact (MK_COMB (@lem6195043) (@lem6195042 k)). Qed.
Lemma lem6195045 (k : nat) : (int_of_num k) = (int_of_num k).
Proof. exact (eq_refl (int_of_num k)). Qed.
Lemma lem6195046 (k : nat) : (term8 k) = (term16 k).
Proof. exact (MK_COMB (@lem6195044 k) (@lem6195045 k)). Qed.
Lemma lem6195047 (k : nat) : (term4 k) = (term16 k).
Proof. exact (TRANS (@lem6195039 k) (@lem6195046 k)). Qed.
Lemma lem6195048 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6195049 (k : nat) : (term6 k) = (term17 k).
Proof. exact (MK_COMB (@lem6195048) (@lem6195047 k)). Qed.
Lemma lem6195050 (k : nat) : (term5 k) = (term17 k).
Proof. exact (TRANS (@lem6195036 k) (@lem6195049 k)). Qed.
Lemma lem6195051 (k : nat) : term18 k.
Proof. exact (@lem2307535 k). Qed.
Lemma lem6195052 (k : nat) : (term18 k) = (term19 k).
Proof. exact (eq_refl (term18 k)). Qed.
Lemma lem6195053 (k : nat) : term19 k.
Proof. exact (EQ_MP (@lem6195052 k) (@lem6195051 k)). Qed.
Lemma lem6195054 (_78955 : int) : (term20 _78955) = (term21 _78955).
Proof. exact (@lem2318604 (term21 _78955)). Qed.
Lemma lem6195065 (_78955 : int) : (term22 _78955) = (term23 _78955).
Proof. exact (@lem16933 (term23 _78955)). Qed.
Lemma lem6195067 (_78955 : int) : (term24 _78955) = (term24 _78955).
Proof. exact (eq_refl (term24 _78955)). Qed.
Lemma lem6195068 (_78955 : int) : (term25 _78955) = (term26 _78955).
Proof. exact (MK_COMB (@lem6195067 _78955) (@lem6195065 _78955)). Qed.
Lemma lem6195069 (_78955 : int) : (term27 _78955) = (term25 _78955).
Proof. exact (@lem17362 (term28 _78955) (term29 _78955)). Qed.
Lemma lem6195077 (_78955 : int) : (term27 _78955) = (term26 _78955).
Proof. exact (TRANS (@lem6195069 _78955) (@lem6195068 _78955)). Qed.
Lemma lem6195080 (x : int) (y : int) : (int_le x y) = (term30 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6195081 (_78955 : int) : (term28 _78955) = (term31 _78955).
Proof. exact (@lem6195080 term32 _78955). Qed.
Lemma lem6195083 (n : nat) : (term33 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6195084 : term34 = term35.
Proof. exact (@lem6195083 (NUMERAL 0)). Qed.
Lemma lem6195085 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6195086 : term36 = term37.
Proof. exact (MK_COMB (@lem6195085) (@lem6195084)). Qed.
Lemma lem6195087 (_78955 : int) : (real_of_int _78955) = (real_of_int _78955).
Proof. exact (eq_refl (real_of_int _78955)). Qed.
Lemma lem6195088 (_78955 : int) : (term31 _78955) = (term38 _78955).
Proof. exact (MK_COMB (@lem6195086) (@lem6195087 _78955)). Qed.
Lemma lem6195090 (_78955 : int) : (term28 _78955) = (term38 _78955).
Proof. exact (TRANS (@lem6195081 _78955) (@lem6195088 _78955)). Qed.
Lemma lem6195093 (x : int) (y : int) : (int_le x y) = (term30 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6195094 (_78955 : int) : (term23 _78955) = (term39 _78955).
Proof. exact (@lem6195093 (term40 _78955) _78955). Qed.
Lemma lem6195096 (x : int) (y : int) : (term41 x y) = (term42 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6195097 (_78955 : int) : (term43 _78955) = (term44 _78955).
Proof. exact (@lem6195096 _78955 term45). Qed.
Lemma lem6195099 (n : nat) : (term33 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6195100 : term46 = term47.
Proof. exact (@lem6195099 term13). Qed.
Lemma lem6195101 (_78955 : int) : (term48 _78955) = (term48 _78955).
Proof. exact (eq_refl (term48 _78955)). Qed.
Lemma lem6195102 (_78955 : int) : (term44 _78955) = (term49 _78955).
Proof. exact (MK_COMB (@lem6195101 _78955) (@lem6195100)). Qed.
Lemma lem6195103 (_78955 : int) : (term43 _78955) = (term49 _78955).
Proof. exact (TRANS (@lem6195097 _78955) (@lem6195102 _78955)). Qed.
Lemma lem6195104 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6195105 (_78955 : int) : (term50 _78955) = (term51 _78955).
Proof. exact (MK_COMB (@lem6195104) (@lem6195103 _78955)). Qed.
Lemma lem6195106 (_78955 : int) : (real_of_int _78955) = (real_of_int _78955).
Proof. exact (eq_refl (real_of_int _78955)). Qed.
Lemma lem6195107 (_78955 : int) : (term39 _78955) = (term52 _78955).
Proof. exact (MK_COMB (@lem6195105 _78955) (@lem6195106 _78955)). Qed.
Lemma lem6195109 (_78955 : int) : (term23 _78955) = (term52 _78955).
Proof. exact (TRANS (@lem6195094 _78955) (@lem6195107 _78955)). Qed.
Lemma lem6195110 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6195111 (_78955 : int) : (term24 _78955) = (term53 _78955).
Proof. exact (MK_COMB (@lem6195110) (@lem6195090 _78955)). Qed.
Lemma lem6195112 (_78955 : int) : (term26 _78955) = (term54 _78955).
Proof. exact (MK_COMB (@lem6195111 _78955) (@lem6195109 _78955)). Qed.
Lemma lem6195113 (_78955 : int) : (term27 _78955) = (term54 _78955).
Proof. exact (TRANS (@lem6195077 _78955) (@lem6195112 _78955)). Qed.
Lemma lem6195117 (t : Prop) : (term55 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6195133 (_78955 : int) : (term56 _78955) = (term54 _78955).
Proof. exact (@lem6195117 (term54 _78955)). Qed.
Lemma lem6195134 (_78955 : int) : (term38 _78955) = (term57 _78955).
Proof. exact (@lem1988287 (real_of_int _78955) term35). Qed.
Lemma lem6195140 (_78955 : int) : (term58 _78955) = (term59 _78955).
Proof. exact (@lem1982792 (real_of_int _78955) term35). Qed.
Lemma lem6195142 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6195143 : term35 = term61.
Proof. exact (@lem6195142 (NUMERAL 0)). Qed.
Lemma lem6195145 (x : nat) : (term62 x) = (term63 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6195146 : term64 = term65.
Proof. exact (@lem6195145 term13). Qed.
Lemma lem6195147 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6195148 : term66 = term67.
Proof. exact (MK_COMB (@lem6195147) (@lem6195146)). Qed.
Lemma lem6195149 : term68 = term69.
Proof. exact (MK_COMB (@lem6195148) (@lem6195143)). Qed.
Lemma lem6195150 : term69 = term70.
Proof. exact (@lem1981613 term64 term35 term47 term47). Qed.
Lemma lem6195152 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6195153 : term73 = term74.
Proof. exact (@lem6195152 term13 term13). Qed.
Lemma lem6195154 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6195155 : term76 = term13.
Proof. exact (EQ_MP (@lem6195154) (@lem940073)). Qed.
Lemma lem6195156 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6195157 : term74 = term47.
Proof. exact (MK_COMB (@lem6195156) (@lem6195155)). Qed.
Lemma lem6195158 : term73 = term47.
Proof. exact (TRANS (@lem6195153) (@lem6195157)). Qed.
Lemma lem6195160 (x : nat) : (term77 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6195161 : term68 = term35.
Proof. exact (@lem6195160 term13). Qed.
Lemma lem6195162 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6195163 : term78 = term79.
Proof. exact (MK_COMB (@lem6195162) (@lem6195161)). Qed.
Lemma lem6195164 : term70 = term61.
Proof. exact (MK_COMB (@lem6195163) (@lem6195158)). Qed.
Lemma lem6195165 : term69 = term61.
Proof. exact (TRANS (@lem6195150) (@lem6195164)). Qed.
Lemma lem6195166 : term68 = term61.
Proof. exact (TRANS (@lem6195149) (@lem6195165)). Qed.
Lemma lem6195168 (x : real) : (term80 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6195169 : term61 = term35.
Proof. exact (@lem6195168 term35). Qed.
Lemma lem6195170 : term68 = term35.
Proof. exact (TRANS (@lem6195166) (@lem6195169)). Qed.
Lemma lem6195171 (_78955 : int) : (term48 _78955) = (term48 _78955).
Proof. exact (eq_refl (term48 _78955)). Qed.
Lemma lem6195172 (_78955 : int) : (term59 _78955) = (term81 _78955).
Proof. exact (MK_COMB (@lem6195171 _78955) (@lem6195170)). Qed.
Lemma lem6195173 (_78955 : int) : (term81 _78955) = (real_of_int _78955).
Proof. exact (@lem1982723 (real_of_int _78955)). Qed.
Lemma lem6195174 (_78955 : int) : (term59 _78955) = (real_of_int _78955).
Proof. exact (TRANS (@lem6195172 _78955) (@lem6195173 _78955)). Qed.
Lemma lem6195176 (_78955 : int) : (term58 _78955) = (real_of_int _78955).
Proof. exact (TRANS (@lem6195140 _78955) (@lem6195174 _78955)). Qed.
Lemma lem6195177 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6195178 (_78955 : int) : (term82 _78955) = (term83 _78955).
Proof. exact (MK_COMB (@lem6195177) (@lem6195176 _78955)). Qed.
Lemma lem6195179 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem6195180 (_78955 : int) : (term57 _78955) = (term84 _78955).
Proof. exact (MK_COMB (@lem6195178 _78955) (@lem6195179)). Qed.
Lemma lem6195181 (_78955 : int) : (term38 _78955) = (term84 _78955).
Proof. exact (TRANS (@lem6195134 _78955) (@lem6195180 _78955)). Qed.
Lemma lem6195182 (_78955 : int) : (term52 _78955) = (term85 _78955).
Proof. exact (@lem1988287 (real_of_int _78955) (term49 _78955)). Qed.
Lemma lem6195194 (_78955 : int) : (term86 _78955) = (term87 _78955).
Proof. exact (@lem1982792 (real_of_int _78955) (term49 _78955)). Qed.
Lemma lem6195195 (_78955 : int) : (term88 _78955) = (term89 _78955).
Proof. exact (@lem1982781 (real_of_int _78955) term64 term47). Qed.
Lemma lem6195197 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6195198 : term47 = term90.
Proof. exact (@lem6195197 term13). Qed.
Lemma lem6195200 (x : nat) : (term62 x) = (term63 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6195201 : term64 = term65.
Proof. exact (@lem6195200 term13). Qed.
Lemma lem6195202 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6195203 : term66 = term67.
Proof. exact (MK_COMB (@lem6195202) (@lem6195201)). Qed.
Lemma lem6195204 : term91 = term92.
Proof. exact (MK_COMB (@lem6195203) (@lem6195198)). Qed.
Lemma lem6195205 : term92 = term93.
Proof. exact (@lem1981613 term64 term47 term47 term47). Qed.
Lemma lem6195207 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6195208 : term73 = term74.
Proof. exact (@lem6195207 term13 term13). Qed.
Lemma lem6195209 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6195210 : term76 = term13.
Proof. exact (EQ_MP (@lem6195209) (@lem940073)). Qed.
Lemma lem6195211 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6195212 : term74 = term47.
Proof. exact (MK_COMB (@lem6195211) (@lem6195210)). Qed.
Lemma lem6195213 : term73 = term47.
Proof. exact (TRANS (@lem6195208) (@lem6195212)). Qed.
Lemma lem6195215 (m : nat) (n : nat) : (term94 m n) = (term95 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6195216 : term91 = term96.
Proof. exact (@lem6195215 term13 term13). Qed.
Lemma lem6195217 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6195218 : term76 = term13.
Proof. exact (EQ_MP (@lem6195217) (@lem940073)). Qed.
Lemma lem6195219 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6195220 : term74 = term47.
Proof. exact (MK_COMB (@lem6195219) (@lem6195218)). Qed.
Lemma lem6195221 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6195222 : term96 = term64.
Proof. exact (MK_COMB (@lem6195221) (@lem6195220)). Qed.
Lemma lem6195223 : term91 = term64.
Proof. exact (TRANS (@lem6195216) (@lem6195222)). Qed.
Lemma lem6195224 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6195225 : term97 = term98.
Proof. exact (MK_COMB (@lem6195224) (@lem6195223)). Qed.
Lemma lem6195226 : term93 = term65.
Proof. exact (MK_COMB (@lem6195225) (@lem6195213)). Qed.
Lemma lem6195227 : term92 = term65.
Proof. exact (TRANS (@lem6195205) (@lem6195226)). Qed.
Lemma lem6195228 : term91 = term65.
Proof. exact (TRANS (@lem6195204) (@lem6195227)). Qed.
Lemma lem6195230 (x : real) : (term80 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6195231 : term65 = term64.
Proof. exact (@lem6195230 term64). Qed.
Lemma lem6195232 : term91 = term64.
Proof. exact (TRANS (@lem6195228) (@lem6195231)). Qed.
Lemma lem6195235 (_78955 : int) : (term99 _78955) = (term99 _78955).
Proof. exact (eq_refl (term99 _78955)). Qed.
Lemma lem6195236 (_78955 : int) : (term89 _78955) = (term100 _78955).
Proof. exact (MK_COMB (@lem6195235 _78955) (@lem6195232)). Qed.
Lemma lem6195237 (_78955 : int) : (term88 _78955) = (term100 _78955).
Proof. exact (TRANS (@lem6195195 _78955) (@lem6195236 _78955)). Qed.
Lemma lem6195238 (_78955 : int) : (term48 _78955) = (term48 _78955).
Proof. exact (eq_refl (term48 _78955)). Qed.
Lemma lem6195239 (_78955 : int) : (term87 _78955) = (term101 _78955).
Proof. exact (MK_COMB (@lem6195238 _78955) (@lem6195237 _78955)). Qed.
Lemma lem6195240 (_78955 : int) : (term101 _78955) = (term102 _78955).
Proof. exact (@lem1982763 (real_of_int _78955) (term103 _78955) term64). Qed.
Lemma lem6195241 (_78955 : int) : (term104 _78955) = (term105 _78955).
Proof. exact (@lem1982715 term64 (real_of_int _78955)). Qed.
Lemma lem6195243 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6195244 : term47 = term90.
Proof. exact (@lem6195243 term13). Qed.
Lemma lem6195246 (x : nat) : (term62 x) = (term63 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6195247 : term64 = term65.
Proof. exact (@lem6195246 term13). Qed.
Lemma lem6195248 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6195249 : term106 = term107.
Proof. exact (MK_COMB (@lem6195248) (@lem6195247)). Qed.
Lemma lem6195250 : term108 = term109.
Proof. exact (MK_COMB (@lem6195249) (@lem6195244)). Qed.
Lemma lem6195251 : term110.
Proof. exact (@lem1981473 term64 term47 term47 term47 term35 term47). Qed.
Lemma lem6195253 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6195254 : term112 = term113.
Proof. exact (@lem6195253 (NUMERAL 0) term13). Qed.
Lemma lem6195255 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6195256 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6195257 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem6195256 h1) (fun h1 : term113 = True => @lem6195255)). Qed.
Lemma lem6195258 : term113 = True.
Proof. exact (EQ_MP (@lem6195257) (@lem6195255)). Qed.
Lemma lem6195259 : term112 = True.
Proof. exact (TRANS (@lem6195254) (@lem6195258)). Qed.
Lemma lem6195260 : True = term112.
Proof. exact (SYM (@lem6195259)). Qed.
Lemma lem6195261 : term112.
Proof. exact (EQ_MP (@lem6195260) (@lem0)). Qed.
Lemma lem6195262 : term115.
Proof. exact (@lem6195251 (@lem6195261)). Qed.
Lemma lem6195264 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6195265 : term112 = term113.
Proof. exact (@lem6195264 (NUMERAL 0) term13). Qed.
Lemma lem6195266 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6195267 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6195268 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem6195267 h1) (fun h1 : term113 = True => @lem6195266)). Qed.
Lemma lem6195269 : term113 = True.
Proof. exact (EQ_MP (@lem6195268) (@lem6195266)). Qed.
Lemma lem6195270 : term112 = True.
Proof. exact (TRANS (@lem6195265) (@lem6195269)). Qed.
Lemma lem6195271 : True = term112.
Proof. exact (SYM (@lem6195270)). Qed.
Lemma lem6195272 : term112.
Proof. exact (EQ_MP (@lem6195271) (@lem0)). Qed.
Lemma lem6195273 : term116.
Proof. exact (@lem6195262 (@lem6195272)). Qed.
Lemma lem6195275 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6195276 : term112 = term113.
Proof. exact (@lem6195275 (NUMERAL 0) term13). Qed.
Lemma lem6195277 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6195278 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6195279 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem6195278 h1) (fun h1 : term113 = True => @lem6195277)). Qed.
Lemma lem6195280 : term113 = True.
Proof. exact (EQ_MP (@lem6195279) (@lem6195277)). Qed.
Lemma lem6195281 : term112 = True.
Proof. exact (TRANS (@lem6195276) (@lem6195280)). Qed.
Lemma lem6195282 : True = term112.
Proof. exact (SYM (@lem6195281)). Qed.
Lemma lem6195283 : term112.
Proof. exact (EQ_MP (@lem6195282) (@lem0)). Qed.
Lemma lem6195284 : term117.
Proof. exact (@lem6195273 (@lem6195283)). Qed.
Lemma lem6195286 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6195287 : term73 = term74.
Proof. exact (@lem6195286 term13 term13). Qed.
Lemma lem6195288 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6195289 : term76 = term13.
Proof. exact (EQ_MP (@lem6195288) (@lem940073)). Qed.
Lemma lem6195290 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6195291 : term74 = term47.
Proof. exact (MK_COMB (@lem6195290) (@lem6195289)). Qed.
Lemma lem6195292 : term73 = term47.
Proof. exact (TRANS (@lem6195287) (@lem6195291)). Qed.
Lemma lem6195294 (m : nat) (n : nat) : (term94 m n) = (term95 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6195295 : term91 = term96.
Proof. exact (@lem6195294 term13 term13). Qed.
Lemma lem6195296 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6195297 : term76 = term13.
Proof. exact (EQ_MP (@lem6195296) (@lem940073)). Qed.
Lemma lem6195298 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6195299 : term74 = term47.
Proof. exact (MK_COMB (@lem6195298) (@lem6195297)). Qed.
Lemma lem6195300 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6195301 : term96 = term64.
Proof. exact (MK_COMB (@lem6195300) (@lem6195299)). Qed.
Lemma lem6195302 : term91 = term64.
Proof. exact (TRANS (@lem6195295) (@lem6195301)). Qed.
Lemma lem6195303 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6195304 : term118 = term106.
Proof. exact (MK_COMB (@lem6195303) (@lem6195302)). Qed.
Lemma lem6195305 : term119 = term108.
Proof. exact (MK_COMB (@lem6195304) (@lem6195292)). Qed.
Lemma lem6195307 (m : nat) : (term120 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6195308 : term108 = term35.
Proof. exact (@lem6195307 term13). Qed.
Lemma lem6195309 : term119 = term35.
Proof. exact (TRANS (@lem6195305) (@lem6195308)). Qed.
Lemma lem6195310 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6195311 : term121 = term122.
Proof. exact (MK_COMB (@lem6195310) (@lem6195309)). Qed.
Lemma lem6195312 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem6195313 : term123 = term124.
Proof. exact (MK_COMB (@lem6195311) (@lem6195312)). Qed.
Lemma lem6195315 (x : nat) : (term125 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6195316 : term124 = term35.
Proof. exact (@lem6195315 term13). Qed.
Lemma lem6195317 : term123 = term35.
Proof. exact (TRANS (@lem6195313) (@lem6195316)). Qed.
Lemma lem6195319 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6195320 : term73 = term74.
Proof. exact (@lem6195319 term13 term13). Qed.
Lemma lem6195321 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6195322 : term76 = term13.
Proof. exact (EQ_MP (@lem6195321) (@lem940073)). Qed.
Lemma lem6195323 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6195324 : term74 = term47.
Proof. exact (MK_COMB (@lem6195323) (@lem6195322)). Qed.
Lemma lem6195325 : term73 = term47.
Proof. exact (TRANS (@lem6195320) (@lem6195324)). Qed.
Lemma lem6195326 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem6195327 : term126 = term124.
Proof. exact (MK_COMB (@lem6195326) (@lem6195325)). Qed.
Lemma lem6195329 (x : nat) : (term125 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6195330 : term124 = term35.
Proof. exact (@lem6195329 term13). Qed.
Lemma lem6195331 : term126 = term35.
Proof. exact (TRANS (@lem6195327) (@lem6195330)). Qed.
Lemma lem6195332 : term35 = term126.
Proof. exact (SYM (@lem6195331)). Qed.
Lemma lem6195333 : term123 = term126.
Proof. exact (TRANS (@lem6195317) (@lem6195332)). Qed.
Lemma lem6195334 : term109 = term61.
Proof. exact (@lem6195284 (@lem6195333)). Qed.
Lemma lem6195335 : term108 = term61.
Proof. exact (TRANS (@lem6195250) (@lem6195334)). Qed.
Lemma lem6195337 (x : real) : (term80 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6195338 : term61 = term35.
Proof. exact (@lem6195337 term35). Qed.
Lemma lem6195339 : term108 = term35.
Proof. exact (TRANS (@lem6195335) (@lem6195338)). Qed.
Lemma lem6195340 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6195341 : term127 = term122.
Proof. exact (MK_COMB (@lem6195340) (@lem6195339)). Qed.
Lemma lem6195342 (_78955 : int) : (real_of_int _78955) = (real_of_int _78955).
Proof. exact (eq_refl (real_of_int _78955)). Qed.
Lemma lem6195343 (_78955 : int) : (term105 _78955) = (term128 _78955).
Proof. exact (MK_COMB (@lem6195341) (@lem6195342 _78955)). Qed.
Lemma lem6195344 (_78955 : int) : (term104 _78955) = (term128 _78955).
Proof. exact (TRANS (@lem6195241 _78955) (@lem6195343 _78955)). Qed.
Lemma lem6195345 (_78955 : int) : (term128 _78955) = term35.
Proof. exact (@lem1982719 (real_of_int _78955)). Qed.
Lemma lem6195346 (_78955 : int) : (term104 _78955) = term35.
Proof. exact (TRANS (@lem6195344 _78955) (@lem6195345 _78955)). Qed.
Lemma lem6195347 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6195348 (_78955 : int) : (term129 _78955) = term130.
Proof. exact (MK_COMB (@lem6195347) (@lem6195346 _78955)). Qed.
Lemma lem6195349 : term64 = term64.
Proof. exact (eq_refl term64). Qed.
Lemma lem6195350 (_78955 : int) : (term102 _78955) = term131.
Proof. exact (MK_COMB (@lem6195348 _78955) (@lem6195349)). Qed.
Lemma lem6195351 (_78955 : int) : (term101 _78955) = term131.
Proof. exact (TRANS (@lem6195240 _78955) (@lem6195350 _78955)). Qed.
Lemma lem6195352 : term131 = term64.
Proof. exact (@lem1982721 term64). Qed.
Lemma lem6195353 (_78955 : int) : (term101 _78955) = term64.
Proof. exact (TRANS (@lem6195351 _78955) (@lem6195352)). Qed.
Lemma lem6195354 (_78955 : int) : (term87 _78955) = term64.
Proof. exact (TRANS (@lem6195239 _78955) (@lem6195353 _78955)). Qed.
Lemma lem6195356 (_78955 : int) : (term86 _78955) = term64.
Proof. exact (TRANS (@lem6195194 _78955) (@lem6195354 _78955)). Qed.
Lemma lem6195357 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6195358 (_78955 : int) : (term132 _78955) = term133.
Proof. exact (MK_COMB (@lem6195357) (@lem6195356 _78955)). Qed.
Lemma lem6195359 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem6195360 (_78955 : int) : (term85 _78955) = term134.
Proof. exact (MK_COMB (@lem6195358 _78955) (@lem6195359)). Qed.
Lemma lem6195361 (_78955 : int) : (term52 _78955) = term134.
Proof. exact (TRANS (@lem6195182 _78955) (@lem6195360 _78955)). Qed.
Lemma lem6195362 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6195363 (_78955 : int) : (term53 _78955) = (term135 _78955).
Proof. exact (MK_COMB (@lem6195362) (@lem6195181 _78955)). Qed.
Lemma lem6195364 (_78955 : int) : (term54 _78955) = (term136 _78955).
Proof. exact (MK_COMB (@lem6195363 _78955) (@lem6195361 _78955)). Qed.
Lemma lem6195379 (_78955 : int) : (term56 _78955) = (term136 _78955).
Proof. exact (TRANS (@lem6195133 _78955) (@lem6195364 _78955)). Qed.
Lemma lem6195383 (_78955 : int) (h1 : term136 _78955) : term136 _78955.
Proof. exact (h1). Qed.
Lemma lem6195384 (_78955 : int) (h1 : term136 _78955) : term134.
Proof. exact (proj2 (@lem6195383 _78955 h1)). Qed.
Lemma lem6195387 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6195388 : term134 = term137.
Proof. exact (@lem6195387 term35 term64). Qed.
Lemma lem6195390 (x : nat) : (term62 x) = (term63 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6195391 : term64 = term65.
Proof. exact (@lem6195390 term13). Qed.
Lemma lem6195393 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6195394 : term35 = term61.
Proof. exact (@lem6195393 (NUMERAL 0)). Qed.
Lemma lem6195395 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6195396 : term37 = term138.
Proof. exact (MK_COMB (@lem6195395) (@lem6195394)). Qed.
Lemma lem6195397 : term137 = term139.
Proof. exact (MK_COMB (@lem6195396) (@lem6195391)). Qed.
Lemma lem6195398 : term140.
Proof. exact (@lem1980026 term35 term47 term64 term47). Qed.
Lemma lem6195400 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6195401 : term112 = term113.
Proof. exact (@lem6195400 (NUMERAL 0) term13). Qed.
Lemma lem6195402 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6195403 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6195404 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem6195403 h1) (fun h1 : term113 = True => @lem6195402)). Qed.
Lemma lem6195405 : term113 = True.
Proof. exact (EQ_MP (@lem6195404) (@lem6195402)). Qed.
Lemma lem6195406 : term112 = True.
Proof. exact (TRANS (@lem6195401) (@lem6195405)). Qed.
Lemma lem6195407 : True = term112.
Proof. exact (SYM (@lem6195406)). Qed.
Lemma lem6195408 : term112.
Proof. exact (EQ_MP (@lem6195407) (@lem0)). Qed.
Lemma lem6195409 : term141.
Proof. exact (@lem6195398 (@lem6195408)). Qed.
Lemma lem6195411 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6195412 : term112 = term113.
Proof. exact (@lem6195411 (NUMERAL 0) term13). Qed.
Lemma lem6195413 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6195414 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6195415 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem6195414 h1) (fun h1 : term113 = True => @lem6195413)). Qed.
Lemma lem6195416 : term113 = True.
Proof. exact (EQ_MP (@lem6195415) (@lem6195413)). Qed.
Lemma lem6195417 : term112 = True.
Proof. exact (TRANS (@lem6195412) (@lem6195416)). Qed.
Lemma lem6195418 : True = term112.
Proof. exact (SYM (@lem6195417)). Qed.
Lemma lem6195419 : term112.
Proof. exact (EQ_MP (@lem6195418) (@lem0)). Qed.
Lemma lem6195420 : term139 = term142.
Proof. exact (@lem6195409 (@lem6195419)). Qed.
Lemma lem6195422 (m : nat) (n : nat) : (term94 m n) = (term95 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6195423 : term91 = term96.
Proof. exact (@lem6195422 term13 term13). Qed.
Lemma lem6195424 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6195425 : term76 = term13.
Proof. exact (EQ_MP (@lem6195424) (@lem940073)). Qed.
Lemma lem6195426 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6195427 : term74 = term47.
Proof. exact (MK_COMB (@lem6195426) (@lem6195425)). Qed.
Lemma lem6195428 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6195429 : term96 = term64.
Proof. exact (MK_COMB (@lem6195428) (@lem6195427)). Qed.
Lemma lem6195430 : term91 = term64.
Proof. exact (TRANS (@lem6195423) (@lem6195429)). Qed.
Lemma lem6195432 (x : nat) : (term125 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6195433 : term124 = term35.
Proof. exact (@lem6195432 term13). Qed.
Lemma lem6195434 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6195435 : term143 = term37.
Proof. exact (MK_COMB (@lem6195434) (@lem6195433)). Qed.
Lemma lem6195436 : term142 = term137.
Proof. exact (MK_COMB (@lem6195435) (@lem6195430)). Qed.
Lemma lem6195438 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6195439 : term137 = term146.
Proof. exact (@lem6195438 (NUMERAL 0) term13). Qed.
Lemma lem6195440 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6195441 (h1 : term114 = (BIT1 0)) : (term13 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6195442 : (term114 = (BIT1 0)) = ((term13 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem6195441 h1) (fun h1 : (term13 = (NUMERAL 0)) = False => @lem6195440)). Qed.
Lemma lem6195443 : (term13 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6195442) (@lem6195440)). Qed.
Lemma lem6195444 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6195445 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6195446 : term147 = (and True).
Proof. exact (MK_COMB (@lem6195445) (@lem6195444)). Qed.
Lemma lem6195447 : term146 = (True /\ False).
Proof. exact (MK_COMB (@lem6195446) (@lem6195443)). Qed.
Lemma lem6195449 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6195450 : term146 = False.
Proof. exact (TRANS (@lem6195447) (@lem6195449)). Qed.
Lemma lem6195451 : term137 = False.
Proof. exact (TRANS (@lem6195439) (@lem6195450)). Qed.
Lemma lem6195452 : term142 = False.
Proof. exact (TRANS (@lem6195436) (@lem6195451)). Qed.
Lemma lem6195453 : term139 = False.
Proof. exact (TRANS (@lem6195420) (@lem6195452)). Qed.
Lemma lem6195454 : term137 = False.
Proof. exact (TRANS (@lem6195397) (@lem6195453)). Qed.
Lemma lem6195455 : term134 = False.
Proof. exact (TRANS (@lem6195388) (@lem6195454)). Qed.
Lemma lem6195456 (_78955 : int) (h1 : term136 _78955) : False.
Proof. exact (EQ_MP (@lem6195455) (@lem6195384 _78955 h1)). Qed.
Lemma lem6195458 (_78955 : int) (h1 : term136 _78955) : term136 _78955.
Proof. exact (h1). Qed.
Lemma lem6195459 (_78955 : int) (h1 : term136 _78955) : (term136 _78955) = False.
Proof. exact (prop_ext (fun h2 : term136 _78955 => @lem6195456 _78955 h1) (fun h2 : False => @lem6195458 _78955 h1)). Qed.
Lemma lem6195460 (_78955 : int) (h1 : term136 _78955) : False.
Proof. exact (EQ_MP (@lem6195459 _78955 h1) (@lem6195458 _78955 h1)). Qed.
Lemma lem6195461 (_78955 : int) (h1 : term56 _78955) : term56 _78955.
Proof. exact (h1). Qed.
Lemma lem6195462 (_78955 : int) (h1 : term56 _78955) : term136 _78955.
Proof. exact (EQ_MP (@lem6195379 _78955) (@lem6195461 _78955 h1)). Qed.
Lemma lem6195463 (_78955 : int) (h1 : term56 _78955) : (term136 _78955) = False.
Proof. exact (prop_ext (fun h2 : term136 _78955 => @lem6195460 _78955 h2) (fun h2 : False => @lem6195462 _78955 h1)). Qed.
Lemma lem6195464 (_78955 : int) (h1 : term56 _78955) : False.
Proof. exact (EQ_MP (@lem6195463 _78955 h1) (@lem6195462 _78955 h1)). Qed.
Lemma lem6195465 (_78955 : int) : term148 _78955.
Proof. exact (fun h0 : term56 _78955 => @lem6195464 _78955 h0). Qed.
Lemma lem6195466 (_78955 : int) : term149 _78955.
Proof. exact (@lem1386578 (term150 _78955)). Qed.
Lemma lem6195469 (_78955 : int) : term150 _78955.
Proof. exact (@lem6195466 _78955 (@lem6195465 _78955)). Qed.
Lemma lem6195470 (_78955 : int) : (term54 _78955) = (term27 _78955).
Proof. exact (SYM (@lem6195113 _78955)). Qed.
Lemma lem6195471 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6195472 (_78955 : int) : (term150 _78955) = (term20 _78955).
Proof. exact (MK_COMB (@lem6195471) (@lem6195470 _78955)). Qed.
Lemma lem6195473 (_78955 : int) : term20 _78955.
Proof. exact (EQ_MP (@lem6195472 _78955) (@lem6195469 _78955)). Qed.
Lemma lem6195474 (_78955 : int) : term21 _78955.
Proof. exact (EQ_MP (@lem6195054 _78955) (@lem6195473 _78955)). Qed.
Lemma lem6195475 (k : nat) : term151 k.
Proof. exact (@lem6195474 (int_of_num k)). Qed.
Lemma lem6195476 (k : nat) : term17 k.
Proof. exact (@lem6195475 k (@lem6195053 k)). Qed.
Lemma lem6195477 (k : nat) : (term17 k) = (term5 k).
Proof. exact (SYM (@lem6195050 k)). Qed.
Lemma lem6195478 (k : nat) : term5 k.
Proof. exact (EQ_MP (@lem6195477 k) (@lem6195476 k)). Qed.
Lemma lem6195479 (k : nat) : term152 k.
Proof. exact (@lem82 (term3 k)). Qed.
Lemma lem6195505 {_83095 : Type'} : term153 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem6195506 {_83095 : Type'} (p : _83095 -> Prop) : term154 _83095 p.
Proof. exact (@lem6195505 _83095 p). Qed.
Lemma lem6195507 {_83095 : Type'} (p : _83095 -> Prop) : (term154 _83095 p) = (term155 _83095 p).
Proof. exact (eq_refl (term154 _83095 p)). Qed.
Lemma lem6195508 {_83095 : Type'} (p : _83095 -> Prop) : term155 _83095 p.
Proof. exact (EQ_MP (@lem6195507 _83095 p) (@lem6195506 _83095 p)). Qed.
Lemma lem6195509 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term156 _83095 p x.
Proof. exact (@lem6195508 _83095 p x). Qed.
Lemma lem6195510 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term156 _83095 p x) = ((term157 _83095 x p) = (p x)).
Proof. exact (eq_refl (term156 _83095 p x)). Qed.
Lemma lem6195519 {A : Type'} (op : type1400 A) : term158 A op.
Proof. exact (@lem5712802 A op). Qed.
Lemma lem6195520 {A : Type'} (op : type1400 A) : (term158 A op) = ((@monoidal A op) = (term159 A op)).
Proof. exact (eq_refl (term158 A op)). Qed.
Lemma lem6195522 {A B : Type'} (op : type1400 B) : term160 A B op.
Proof. exact (@lem5807175 A B op). Qed.
Lemma lem6195523 {A B : Type'} (op : type1400 B) : (term160 A B op) = (term161 A B op).
Proof. exact (eq_refl (term160 A B op)). Qed.
Lemma lem6195524 {A B : Type'} (op : type1400 B) : term161 A B op.
Proof. exact (EQ_MP (@lem6195523 A B op) (@lem6195522 A B op)). Qed.
Lemma lem6195525 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem6195526 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term162 A B op.
Proof. exact (@lem6195524 A B op (@lem6195525 B op h1)). Qed.
Lemma lem6195527 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term163 A B op f.
Proof. exact (@lem6195526 A B op h1 f). Qed.
Lemma lem6195528 {A B : Type'} (op : type1400 B) (f : A -> B) : (term163 A B op f) = (term164 A B op f).
Proof. exact (eq_refl (term163 A B op f)). Qed.
Lemma lem6195529 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term164 A B op f.
Proof. exact (EQ_MP (@lem6195528 A B op f) (@lem6195527 A B f op h1)). Qed.
Lemma lem6195530 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : @monoidal B op) : term165 A B op f x.
Proof. exact (@lem6195529 A B f op h1 x). Qed.
Lemma lem6195531 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) : (term165 A B op f x) = ((term166 A B op x f) = (f x)).
Proof. exact (eq_refl (term165 A B op f x)). Qed.
Lemma lem6195532 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : @monoidal B op) : (term166 A B op x f) = (f x).
Proof. exact (EQ_MP (@lem6195531 A B op f x) (@lem6195530 A B f x op h1)). Qed.
Lemma lem6195538 (n : nat) : term167 n.
Proof. exact (@lem4621993 n). Qed.
Lemma lem6195539 (n : nat) : (term167 n) = (term168 n).
Proof. exact (eq_refl (term167 n)). Qed.
Lemma lem6195540 (n : nat) : term168 n.
Proof. exact (EQ_MP (@lem6195539 n) (@lem6195538 n)). Qed.
Lemma lem6195541 (n : nat) : (term168 n) = ((term168 n) = True).
Proof. exact (@lem7 (term168 n)). Qed.
Lemma lem6195543 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term169 _120477 _120519 _120521 op.
Proof. exact (@lem5753565 _120477 _120519 _120521 op). Qed.
Lemma lem6195544 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term169 _120477 _120519 _120521 op) = (term170 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term169 _120477 _120519 _120521 op)). Qed.
Lemma lem6195545 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term170 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem6195544 _120477 _120519 _120521 op) (@lem6195543 _120477 _120519 _120521 op)). Qed.
Lemma lem6195546 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (h1). Qed.
Lemma lem6195547 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term171 _120477 _120519 _120521 op.
Proof. exact (@lem6195545 _120477 _120519 _120521 op (@lem6195546 _120519 op h1)). Qed.
Lemma lem6195548 {_120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term172 _120519 _120521 op.
Proof. exact (proj2 (@lem6195547 Prop _120519 _120521 op h1)). Qed.
Lemma lem6195549 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term173 _120519 _120521 op f.
Proof. exact (@lem6195548 _120519 _120521 op h1 f). Qed.
Lemma lem6195550 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) : (term173 _120519 _120521 op f) = (term174 _120519 _120521 op f).
Proof. exact (eq_refl (term173 _120519 _120521 op f)). Qed.
Lemma lem6195551 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term174 _120519 _120521 op f.
Proof. exact (EQ_MP (@lem6195550 _120519 _120521 op f) (@lem6195549 _120519 _120521 f op h1)). Qed.
Lemma lem6195552 {_120519 _120521 : Type'} (f : _120521 -> _120519) (x : _120521) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term175 _120519 _120521 op f x.
Proof. exact (@lem6195551 _120519 _120521 f op h1 x). Qed.
Lemma lem6195553 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) : (term175 _120519 _120521 op f x) = (term176 _120519 _120521 x op f).
Proof. exact (eq_refl (term175 _120519 _120521 op f x)). Qed.
Lemma lem6195554 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term176 _120519 _120521 x op f.
Proof. exact (EQ_MP (@lem6195553 _120519 _120521 x op f) (@lem6195552 _120519 _120521 f x op h1)). Qed.
Lemma lem6195555 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term177 _120519 _120521 x op f s.
Proof. exact (@lem6195554 _120519 _120521 x f op h1 s). Qed.
Lemma lem6195556 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term177 _120519 _120521 x op f s) = (term178 _120519 _120521 x op s f).
Proof. exact (eq_refl (term177 _120519 _120521 x op f s)). Qed.
Lemma lem6195557 {_120519 _120521 : Type'} (x : _120521) (s : _120521 -> Prop) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term178 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem6195556 _120519 _120521 x op s f) (@lem6195555 _120519 _120521 x f s op h1)). Qed.
Lemma lem6195558 {_120521 : Type'} (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : @FINITE _120521 s.
Proof. exact (h1). Qed.
Lemma lem6195559 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @FINITE _120521 s) (h2 : @monoidal _120519 op) : (term179 _120519 _120521 op x s f) = (term180 _120519 _120521 x op s f).
Proof. exact (@lem6195557 _120519 _120521 x s f op h2 (@lem6195558 _120521 s h1)). Qed.
Lemma lem6195560 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : term181 _120519 _120521 x op s f.
Proof. exact (fun h0 : @monoidal _120519 op => @lem6195559 _120519 _120521 x f s op h1 h0). Qed.
Lemma lem6195561 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term182 _120519 _120521 x op s f.
Proof. exact (fun h0 : @FINITE _120521 s => @lem6195560 _120519 _120521 x op f s h0). Qed.
Lemma lem6195563 (p : Prop) (q : Prop) (r : Prop) : (term183 p q r) = (term184 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem6195568 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term182 _120519 _120521 x op s f) = (term185 _120519 _120521 x op s f).
Proof. exact (@lem6195563 (@FINITE _120521 s) (@monoidal _120519 op) ((term179 _120519 _120521 op x s f) = (term180 _120519 _120521 x op s f))). Qed.
Lemma lem6195579 : term186.
Proof. exact (proj2 (@lem4621860)). Qed.
Lemma lem6195580 (k : nat) : term187 k.
Proof. exact (@lem6195579 k). Qed.
Lemma lem6195581 (k : nat) : (term187 k) = ((term188 k) = (term189 k)).
Proof. exact (eq_refl (term187 k)). Qed.
Lemma lem6195591 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term190 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6195592 (p : Prop) (q : Prop) (p' : Prop) : term191 p q p'.
Proof. exact (fun q' : Prop => @lem6195591 p q p' q'). Qed.
Lemma lem6195593 (p : Prop) (q : Prop) : term192 p q.
Proof. exact (fun p' : Prop => @lem6195592 p q p'). Qed.
Lemma lem6195594 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) : term193 _123593 op f.
Proof. exact (@lem6195593 (@monoidal _123593 op) (term194 _123593 op f)). Qed.
Lemma lem6195595 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) (p' : Prop) : term195 _123593 op f p'.
Proof. exact (@lem6195594 _123593 op f p'). Qed.
Lemma lem6195596 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) (p' : Prop) : (term195 _123593 op f p') = (term196 _123593 op f p').
Proof. exact (eq_refl (term195 _123593 op f p')). Qed.
Lemma lem6195597 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) (p' : Prop) : term196 _123593 op f p'.
Proof. exact (EQ_MP (@lem6195596 _123593 op f p') (@lem6195595 _123593 op f p')). Qed.
Lemma lem6195598 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) (p' : Prop) (q' : Prop) : term197 _123593 op f p' q'.
Proof. exact (@lem6195597 _123593 op f p' q'). Qed.
Lemma lem6195599 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) (p' : Prop) (q' : Prop) : (term197 _123593 op f p' q') = (term198 _123593 op f p' q').
Proof. exact (eq_refl (term197 _123593 op f p' q')). Qed.
Lemma lem6195600 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) (p' : Prop) (q' : Prop) : term198 _123593 op f p' q'.
Proof. exact (EQ_MP (@lem6195599 _123593 op f p' q') (@lem6195598 _123593 op f p' q')). Qed.
Lemma lem6195601 {_123593 : Type'} (op : type1400 _123593) : (@monoidal _123593 op) = (@monoidal _123593 op).
Proof. exact (eq_refl (@monoidal _123593 op)). Qed.
Lemma lem6195602 {_123593 : Type'} (f : nat -> _123593) (op : type1400 _123593) (q' : Prop) : term199 _123593 f op q'.
Proof. exact (@lem6195600 _123593 op f (@monoidal _123593 op) q'). Qed.
Lemma lem6195603 {_123593 : Type'} (f : nat -> _123593) (op : type1400 _123593) (q' : Prop) : term200 _123593 f op q'.
Proof. exact (@lem6195602 _123593 f op q' (@lem6195601 _123593 op)). Qed.
Lemma lem6195604 {_123593 : Type'} (op : type1400 _123593) (h1 : @monoidal _123593 op) : @monoidal _123593 op.
Proof. exact (h1). Qed.
Lemma lem6195605 {_123593 : Type'} (op : type1400 _123593) : (@monoidal _123593 op) = ((@monoidal _123593 op) = True).
Proof. exact (@lem7 (@monoidal _123593 op)). Qed.
Lemma lem6195612 : term201 = term202.
Proof. exact (proj1 (@lem4621860)). Qed.
Lemma lem6195613 {_123593 : Type'} (op : type1400 _123593) : (@iterate _123593 nat op) = (@iterate _123593 nat op).
Proof. exact (eq_refl (@iterate _123593 nat op)). Qed.
Lemma lem6195614 {_123593 : Type'} (op : type1400 _123593) : (term203 _123593 op) = (term204 _123593 op).
Proof. exact (MK_COMB (@lem6195613 _123593 op) (@lem6195612)). Qed.
Lemma lem6195615 {_123593 : Type'} (f : nat -> _123593) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6195616 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) : (term205 _123593 op f) = (term206 _123593 op f).
Proof. exact (MK_COMB (@lem6195614 _123593 op) (@lem6195615 _123593 f)). Qed.
Lemma lem6195618 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) : term207 A B op f x.
Proof. exact (fun h0 : @monoidal B op => @lem6195532 A B f x op h0). Qed.
Lemma lem6195619 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) (x : nat) : term208 _123593 op f x.
Proof. exact (@lem6195618 nat _123593 op f x). Qed.
Lemma lem6195620 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) : term209 _123593 op f.
Proof. exact (@lem6195619 _123593 op f (NUMERAL 0)). Qed.
Lemma lem6195622 {_123593 : Type'} (op : type1400 _123593) (h1 : @monoidal _123593 op) : (@monoidal _123593 op) = True.
Proof. exact (EQ_MP (@lem6195605 _123593 op) (@lem6195604 _123593 op h1)). Qed.
Lemma lem6195623 {_123593 : Type'} (op : type1400 _123593) (h1 : @monoidal _123593 op) : True = (@monoidal _123593 op).
Proof. exact (SYM (@lem6195622 _123593 op h1)). Qed.
Lemma lem6195624 {_123593 : Type'} (op : type1400 _123593) (h1 : @monoidal _123593 op) : @monoidal _123593 op.
Proof. exact (EQ_MP (@lem6195623 _123593 op h1) (@lem0)). Qed.
Lemma lem6195625 {_123593 : Type'} (f : nat -> _123593) (op : type1400 _123593) (h1 : @monoidal _123593 op) : (term206 _123593 op f) = (term210 _123593 f).
Proof. exact (@lem6195620 _123593 op f (@lem6195624 _123593 op h1)). Qed.
Lemma lem6195626 {_123593 : Type'} (f : nat -> _123593) (op : type1400 _123593) (h1 : @monoidal _123593 op) : (term205 _123593 op f) = (term210 _123593 f).
Proof. exact (TRANS (@lem6195616 _123593 op f) (@lem6195625 _123593 f op h1)). Qed.
Lemma lem6195627 {_123593 : Type'} : (@eq _123593) = (@eq _123593).
Proof. exact (eq_refl (@eq _123593)). Qed.
Lemma lem6195628 {_123593 : Type'} (f : nat -> _123593) (op : type1400 _123593) (h1 : @monoidal _123593 op) : (term211 _123593 op f) = (term212 _123593 f).
Proof. exact (MK_COMB (@lem6195627 _123593) (@lem6195626 _123593 f op h1)). Qed.
Lemma lem6195629 {_123593 : Type'} (f : nat -> _123593) : (term210 _123593 f) = (term210 _123593 f).
Proof. exact (eq_refl (term210 _123593 f)). Qed.
Lemma lem6195630 {_123593 : Type'} (f : nat -> _123593) (op : type1400 _123593) (h1 : @monoidal _123593 op) : ((term205 _123593 op f) = (term210 _123593 f)) = ((term210 _123593 f) = (term210 _123593 f)).
Proof. exact (MK_COMB (@lem6195628 _123593 f op h1) (@lem6195629 _123593 f)). Qed.
Lemma lem6195632 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6195633 {_123593 : Type'} (x : _123593) : (x = x) = True.
Proof. exact (@lem6195632 _123593 x). Qed.
Lemma lem6195634 {_123593 : Type'} (f : nat -> _123593) : ((term210 _123593 f) = (term210 _123593 f)) = True.
Proof. exact (@lem6195633 _123593 (term210 _123593 f)). Qed.
Lemma lem6195635 {_123593 : Type'} (f : nat -> _123593) (op : type1400 _123593) (h1 : @monoidal _123593 op) : ((term205 _123593 op f) = (term210 _123593 f)) = True.
Proof. exact (TRANS (@lem6195630 _123593 f op h1) (@lem6195634 _123593 f)). Qed.
Lemma lem6195636 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6195637 {_123593 : Type'} (f : nat -> _123593) (op : type1400 _123593) (h1 : @monoidal _123593 op) : (term213 _123593 op f) = (and True).
Proof. exact (MK_COMB (@lem6195636) (@lem6195635 _123593 f op h1)). Qed.
Lemma lem6195645 (k : nat) : (term188 k) = (term189 k).
Proof. exact (EQ_MP (@lem6195581 k) (@lem6195580 k)). Qed.
Lemma lem6195650 {_123593 : Type'} (op : type1400 _123593) : (@iterate _123593 nat op) = (@iterate _123593 nat op).
Proof. exact (eq_refl (@iterate _123593 nat op)). Qed.
Lemma lem6195651 {_123593 : Type'} (op : type1400 _123593) (k : nat) : (term214 _123593 op k) = (term215 _123593 op k).
Proof. exact (MK_COMB (@lem6195650 _123593 op) (@lem6195645 k)). Qed.
Lemma lem6195656 {_123593 : Type'} (f : nat -> _123593) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6195657 {_123593 : Type'} (op : type1400 _123593) (k : nat) (f : nat -> _123593) : (term216 _123593 op k f) = (term217 _123593 op k f).
Proof. exact (MK_COMB (@lem6195651 _123593 op k) (@lem6195656 _123593 f)). Qed.
Lemma lem6195659 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term185 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem6195568 _120519 _120521 x op s f) (@lem6195561 _120519 _120521 x op s f)). Qed.
Lemma lem6195660 {_123593 : Type'} (x : nat) (op : type1400 _123593) (s : nat -> Prop) (f : nat -> _123593) : term218 _123593 x op s f.
Proof. exact (@lem6195659 _123593 nat x op s f). Qed.
Lemma lem6195661 {_123593 : Type'} (op : type1400 _123593) (k : nat) (f : nat -> _123593) : term219 _123593 op k f.
Proof. exact (@lem6195660 _123593 (S k) op (term220 k) f). Qed.
Lemma lem6195665 (n : nat) : (term168 n) = True.
Proof. exact (EQ_MP (@lem6195541 n) (@lem6195540 n)). Qed.
Lemma lem6195666 (k : nat) : (term168 k) = True.
Proof. exact (@lem6195665 k). Qed.
Lemma lem6195667 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6195668 (k : nat) : (term221 k) = (and True).
Proof. exact (MK_COMB (@lem6195667) (@lem6195666 k)). Qed.
Lemma lem6195670 {_123593 : Type'} (op : type1400 _123593) (h1 : @monoidal _123593 op) : (@monoidal _123593 op) = True.
Proof. exact (EQ_MP (@lem6195605 _123593 op) (@lem6195604 _123593 op h1)). Qed.
Lemma lem6195671 {_123593 : Type'} (k : nat) (op : type1400 _123593) (h1 : @monoidal _123593 op) : (term222 _123593 k op) = (True /\ True).
Proof. exact (MK_COMB (@lem6195668 k) (@lem6195670 _123593 op h1)). Qed.
Lemma lem6195673 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6195674 : (True /\ True) = True.
Proof. exact (@lem6195673 True). Qed.
Lemma lem6195675 {_123593 : Type'} (k : nat) (op : type1400 _123593) (h1 : @monoidal _123593 op) : (term222 _123593 k op) = True.
Proof. exact (TRANS (@lem6195671 _123593 k op h1) (@lem6195674)). Qed.
Lemma lem6195676 {_123593 : Type'} (k : nat) (op : type1400 _123593) (h1 : @monoidal _123593 op) : True = (term222 _123593 k op).
Proof. exact (SYM (@lem6195675 _123593 k op h1)). Qed.
Lemma lem6195677 {_123593 : Type'} (k : nat) (op : type1400 _123593) (h1 : @monoidal _123593 op) : term222 _123593 k op.
Proof. exact (EQ_MP (@lem6195676 _123593 k op h1) (@lem0)). Qed.
Lemma lem6195678 {_123593 : Type'} (k : nat) (f : nat -> _123593) (op : type1400 _123593) (h1 : @monoidal _123593 op) : (term217 _123593 op k f) = (term223 _123593 op k f).
Proof. exact (@lem6195661 _123593 op k f (@lem6195677 _123593 k op h1)). Qed.
Lemma lem6195736 {_123593 : Type'} (k : nat) (f : nat -> _123593) (op : type1400 _123593) (h1 : @monoidal _123593 op) : (term216 _123593 op k f) = (term223 _123593 op k f).
Proof. exact (TRANS (@lem6195657 _123593 op k f) (@lem6195678 _123593 k f op h1)). Qed.
Lemma lem6195737 {_123593 : Type'} : (@eq _123593) = (@eq _123593).
Proof. exact (eq_refl (@eq _123593)). Qed.
Lemma lem6195738 {_123593 : Type'} (k : nat) (f : nat -> _123593) (op : type1400 _123593) (h1 : @monoidal _123593 op) : (term224 _123593 op k f) = (term225 _123593 op k f).
Proof. exact (MK_COMB (@lem6195737 _123593) (@lem6195736 _123593 k f op h1)). Qed.
Lemma lem6195800 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) (k : nat) : (term226 _123593 op f k) = (term226 _123593 op f k).
Proof. exact (eq_refl (term226 _123593 op f k)). Qed.
Lemma lem6195801 {_123593 : Type'} (f : nat -> _123593) (k : nat) (op : type1400 _123593) (h1 : @monoidal _123593 op) : ((term216 _123593 op k f) = (term226 _123593 op f k)) = ((term223 _123593 op k f) = (term226 _123593 op f k)).
Proof. exact (MK_COMB (@lem6195738 _123593 k f op h1) (@lem6195800 _123593 op f k)). Qed.
Lemma lem6195865 {_123593 : Type'} (f : nat -> _123593) (op : type1400 _123593) (h1 : @monoidal _123593 op) : (term227 _123593 op f) = (term228 _123593 op f).
Proof. exact (fun_ext (fun k : nat => @lem6195801 _123593 f k op h1)). Qed.
Lemma lem6195929 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6195930 {_123593 : Type'} (f : nat -> _123593) (op : type1400 _123593) (h1 : @monoidal _123593 op) : (term229 _123593 op f) = (term230 _123593 op f).
Proof. exact (MK_COMB (@lem6195929) (@lem6195865 _123593 f op h1)). Qed.
Lemma lem6195998 {_123593 : Type'} (f : nat -> _123593) (op : type1400 _123593) (h1 : @monoidal _123593 op) : (term194 _123593 op f) = (term231 _123593 op f).
Proof. exact (MK_COMB (@lem6195637 _123593 f op h1) (@lem6195930 _123593 f op h1)). Qed.
Lemma lem6196000 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6196001 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) : (term231 _123593 op f) = (term230 _123593 op f).
Proof. exact (@lem6196000 (term230 _123593 op f)). Qed.
Lemma lem6196069 {_123593 : Type'} (f : nat -> _123593) (op : type1400 _123593) (h1 : @monoidal _123593 op) : (term194 _123593 op f) = (term230 _123593 op f).
Proof. exact (TRANS (@lem6195998 _123593 f op h1) (@lem6196001 _123593 op f)). Qed.
Lemma lem6196070 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) : term232 _123593 op f.
Proof. exact (fun h0 : @monoidal _123593 op => @lem6196069 _123593 f op h0). Qed.
Lemma lem6196071 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) : term233 _123593 op f.
Proof. exact (@lem6195603 _123593 f op (term230 _123593 op f)). Qed.
Lemma lem6196072 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) : (term234 _123593 op f) = (term235 _123593 op f).
Proof. exact (@lem6196071 _123593 op f (@lem6196070 _123593 op f)). Qed.
Lemma lem6196230 {_123593 : Type'} (f : nat -> _123593) : (term236 _123593 f) = (term237 _123593 f).
Proof. exact (fun_ext (fun op : type1400 _123593 => @lem6196072 _123593 op f)). Qed.
Lemma lem6196388 {_123593 : Type'} : (@all (_123593 -> _123593 -> _123593)) = (@all (_123593 -> _123593 -> _123593)).
Proof. exact (eq_refl (@all (_123593 -> _123593 -> _123593))). Qed.
Lemma lem6196389 {_123593 : Type'} (f : nat -> _123593) : (term238 _123593 f) = (term239 _123593 f).
Proof. exact (MK_COMB (@lem6196388 _123593) (@lem6196230 _123593 f)). Qed.
Lemma lem6196551 {_123593 : Type'} (f : nat -> _123593) : (term239 _123593 f) = (term238 _123593 f).
Proof. exact (SYM (@lem6196389 _123593 f)). Qed.
Lemma lem6196559 {A : Type'} (op : type1400 A) : (@monoidal A op) = (term159 A op).
Proof. exact (EQ_MP (@lem6195520 A op) (@lem6195519 A op)). Qed.
Lemma lem6196560 {_123593 : Type'} (op : type1400 _123593) : (@monoidal _123593 op) = (term159 _123593 op).
Proof. exact (@lem6196559 _123593 op). Qed.
Lemma lem6196595 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6196596 {_123593 : Type'} (op : type1400 _123593) : (term240 _123593 op) = (term241 _123593 op).
Proof. exact (MK_COMB (@lem6196595) (@lem6196560 _123593 op)). Qed.
Lemma lem6196604 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term157 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem6195510 _83095 p x) (@lem6195509 _83095 p x)). Qed.
Lemma lem6196605 (p : nat -> Prop) (x : nat) : (term242 x p) = (p x).
Proof. exact (@lem6196604 nat p x). Qed.
Lemma lem6196606 (k : nat) : (term243 k) = (term244 k).
Proof. exact (@lem6196605 (term245 k) (S k)). Qed.
Lemma lem6196607 (i : nat) (k : nat) : (term246 k i) = (Peano.le i k).
Proof. exact (eq_refl (term246 k i)). Qed.
Lemma lem6196608 (GEN_PVAR_187 : nat) : (@SETSPEC nat GEN_PVAR_187) = (@SETSPEC nat GEN_PVAR_187).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_187)). Qed.
Lemma lem6196609 (GEN_PVAR_187 : nat) (i : nat) (k : nat) : (term247 GEN_PVAR_187 k i) = (term248 GEN_PVAR_187 i k).
Proof. exact (MK_COMB (@lem6196608 GEN_PVAR_187) (@lem6196607 i k)). Qed.
Lemma lem6196610 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6196611 (GEN_PVAR_187 : nat) (k : nat) (i : nat) : (term249 GEN_PVAR_187 k i) = (term250 GEN_PVAR_187 k i).
Proof. exact (MK_COMB (@lem6196609 GEN_PVAR_187 i k) (@lem6196610 i)). Qed.
Lemma lem6196612 (GEN_PVAR_187 : nat) (k : nat) : (term251 GEN_PVAR_187 k) = (term252 GEN_PVAR_187 k).
Proof. exact (fun_ext (fun i : nat => @lem6196611 GEN_PVAR_187 k i)). Qed.
Lemma lem6196613 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6196614 (GEN_PVAR_187 : nat) (k : nat) : (term253 GEN_PVAR_187 k) = (term254 GEN_PVAR_187 k).
Proof. exact (MK_COMB (@lem6196613) (@lem6196612 GEN_PVAR_187 k)). Qed.
Lemma lem6196615 (k : nat) : (term255 k) = (term256 k).
Proof. exact (fun_ext (fun GEN_PVAR_187 : nat => @lem6196614 GEN_PVAR_187 k)). Qed.
Lemma lem6196616 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem6196617 (k : nat) : (term257 k) = (term220 k).
Proof. exact (MK_COMB (@lem6196616) (@lem6196615 k)). Qed.
Lemma lem6196618 (k : nat) : (term258 k) = (term258 k).
Proof. exact (eq_refl (term258 k)). Qed.
Lemma lem6196619 (k : nat) : (term243 k) = (term259 k).
Proof. exact (MK_COMB (@lem6196618 k) (@lem6196617 k)). Qed.
Lemma lem6196620 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6196621 (k : nat) : (term260 k) = (term261 k).
Proof. exact (MK_COMB (@lem6196620) (@lem6196619 k)). Qed.
Lemma lem6196622 (k : nat) : (term244 k) = (term3 k).
Proof. exact (eq_refl (term244 k)). Qed.
Lemma lem6196623 (k : nat) : ((term243 k) = (term244 k)) = ((term259 k) = (term3 k)).
Proof. exact (MK_COMB (@lem6196621 k) (@lem6196622 k)). Qed.
Lemma lem6196624 (k : nat) : (term259 k) = (term3 k).
Proof. exact (EQ_MP (@lem6196623 k) (@lem6196606 k)). Qed.
Lemma lem6196626 (k : nat) : (term3 k) = False.
Proof. exact (@lem6195479 k (@lem6195478 k)). Qed.
Lemma lem6196627 (k : nat) : (term259 k) = False.
Proof. exact (TRANS (@lem6196624 k) (@lem6196626 k)). Qed.
Lemma lem6196628 {_123593 : Type'} : (@COND _123593) = (@COND _123593).
Proof. exact (eq_refl (@COND _123593)). Qed.
Lemma lem6196629 {_123593 : Type'} (k : nat) : (term262 _123593 k) = (@COND _123593 False).
Proof. exact (MK_COMB (@lem6196628 _123593) (@lem6196627 k)). Qed.
Lemma lem6196634 {_123593 : Type'} (op : type1400 _123593) (k : nat) (f : nat -> _123593) : (term263 _123593 op k f) = (term263 _123593 op k f).
Proof. exact (eq_refl (term263 _123593 op k f)). Qed.
Lemma lem6196635 {_123593 : Type'} (op : type1400 _123593) (k : nat) (f : nat -> _123593) : (term264 _123593 op k f) = (term265 _123593 op k f).
Proof. exact (MK_COMB (@lem6196629 _123593 k) (@lem6196634 _123593 op k f)). Qed.
Lemma lem6196640 {_123593 : Type'} (op : type1400 _123593) (k : nat) (f : nat -> _123593) : (term266 _123593 op k f) = (term266 _123593 op k f).
Proof. exact (eq_refl (term266 _123593 op k f)). Qed.
Lemma lem6196641 {_123593 : Type'} (op : type1400 _123593) (k : nat) (f : nat -> _123593) : (term223 _123593 op k f) = (term267 _123593 op k f).
Proof. exact (MK_COMB (@lem6196635 _123593 op k f) (@lem6196640 _123593 op k f)). Qed.
Lemma lem6196643 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6196644 {_123593 : Type'} (t1 : _123593) (t2 : _123593) : (@COND _123593 False t1 t2) = t2.
Proof. exact (@lem6196643 _123593 t1 t2). Qed.
Lemma lem6196645 {_123593 : Type'} (op : type1400 _123593) (k : nat) (f : nat -> _123593) : (term267 _123593 op k f) = (term266 _123593 op k f).
Proof. exact (@lem6196644 _123593 (term263 _123593 op k f) (term266 _123593 op k f)). Qed.
Lemma lem6196650 {_123593 : Type'} (op : type1400 _123593) (k : nat) (f : nat -> _123593) : (term223 _123593 op k f) = (term266 _123593 op k f).
Proof. exact (TRANS (@lem6196641 _123593 op k f) (@lem6196645 _123593 op k f)). Qed.
Lemma lem6196651 {_123593 : Type'} : (@eq _123593) = (@eq _123593).
Proof. exact (eq_refl (@eq _123593)). Qed.
Lemma lem6196652 {_123593 : Type'} (op : type1400 _123593) (k : nat) (f : nat -> _123593) : (term225 _123593 op k f) = (term268 _123593 op k f).
Proof. exact (MK_COMB (@lem6196651 _123593) (@lem6196650 _123593 op k f)). Qed.
Lemma lem6196657 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) (k : nat) : (term226 _123593 op f k) = (term226 _123593 op f k).
Proof. exact (eq_refl (term226 _123593 op f k)). Qed.
Lemma lem6196658 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) (k : nat) : ((term223 _123593 op k f) = (term226 _123593 op f k)) = ((term266 _123593 op k f) = (term226 _123593 op f k)).
Proof. exact (MK_COMB (@lem6196652 _123593 op k f) (@lem6196657 _123593 op f k)). Qed.
Lemma lem6196661 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) : (term228 _123593 op f) = (term269 _123593 op f).
Proof. exact (fun_ext (fun k : nat => @lem6196658 _123593 op f k)). Qed.
Lemma lem6196662 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6196663 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) : (term230 _123593 op f) = (term270 _123593 op f).
Proof. exact (MK_COMB (@lem6196662) (@lem6196661 _123593 op f)). Qed.
Lemma lem6196668 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) : (term235 _123593 op f) = (term271 _123593 op f).
Proof. exact (MK_COMB (@lem6196596 _123593 op) (@lem6196663 _123593 op f)). Qed.
Lemma lem6196671 {_123593 : Type'} (f : nat -> _123593) : (term237 _123593 f) = (term272 _123593 f).
Proof. exact (fun_ext (fun op : type1400 _123593 => @lem6196668 _123593 op f)). Qed.
Lemma lem6196672 {_123593 : Type'} : (@all (_123593 -> _123593 -> _123593)) = (@all (_123593 -> _123593 -> _123593)).
Proof. exact (eq_refl (@all (_123593 -> _123593 -> _123593))). Qed.
Lemma lem6196673 {_123593 : Type'} (f : nat -> _123593) : (term239 _123593 f) = (term273 _123593 f).
Proof. exact (MK_COMB (@lem6196672 _123593) (@lem6196671 _123593 f)). Qed.
Lemma lem6196678 {_123593 : Type'} (f : nat -> _123593) : (term273 _123593 f) = (term239 _123593 f).
Proof. exact (SYM (@lem6196673 _123593 f)). Qed.
Lemma lem6196680 (p : Prop) : p = (term274 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6196681 {_123593 : Type'} (f : nat -> _123593) : (term273 _123593 f) = (term275 _123593 f).
Proof. exact (@lem6196680 (term273 _123593 f)). Qed.
Lemma lem6196682 {_123593 : Type'} (f : nat -> _123593) : (term275 _123593 f) = (term273 _123593 f).
Proof. exact (SYM (@lem6196681 _123593 f)). Qed.
Lemma lem6196683 {_123593 : Type'} (f : nat -> _123593) (h1 : term276 _123593 f) : term276 _123593 f.
Proof. exact (h1). Qed.
Lemma lem6196686 {_123593 : Type'} (f : nat -> _123593) (h1 : term275 _123593 f) : term275 _123593 f.
Proof. exact (h1). Qed.
Lemma lem6196687 {_123593 : Type'} (f : nat -> _123593) : term277 _123593 f.
Proof. exact (fun h0 : term275 _123593 f => @lem6196686 _123593 f h0). Qed.
Lemma lem6196688 {_123593 : Type'} (f : nat -> _123593) (h1 : term277 _123593 f) : term277 _123593 f.
Proof. exact (h1). Qed.
Lemma lem6196689 {_123593 : Type'} (f : nat -> _123593) (h1 : term275 _123593 f) : term275 _123593 f.
Proof. exact (h1). Qed.
Lemma lem6196690 {_123593 : Type'} (f : nat -> _123593) (h1 : term275 _123593 f) (h2 : term277 _123593 f) : term275 _123593 f.
Proof. exact (@lem6196688 _123593 f h2 (@lem6196689 _123593 f h1)). Qed.
Lemma lem6196691 {_123593 : Type'} (f : nat -> _123593) (h1 : term275 _123593 f) : term278 _123593 f.
Proof. exact (fun h0 : term277 _123593 f => @lem6196690 _123593 f h1 h0). Qed.
Lemma lem6196692 {_123593 : Type'} (f : nat -> _123593) (h1 : term277 _123593 f) : term277 _123593 f.
Proof. exact (h1). Qed.
Lemma lem6196693 {_123593 : Type'} (f : nat -> _123593) (h1 : term275 _123593 f) (h2 : term277 _123593 f) : term275 _123593 f.
Proof. exact (@lem6196691 _123593 f h1 (@lem6196692 _123593 f h2)). Qed.
Lemma lem6196694 {_123593 : Type'} (f : nat -> _123593) (h1 : term277 _123593 f) : term277 _123593 f.
Proof. exact (fun h0 : term275 _123593 f => @lem6196693 _123593 f h0 h1). Qed.
Lemma lem6196695 {_123593 : Type'} (f : nat -> _123593) : term279 _123593 f.
Proof. exact (fun h0 : term277 _123593 f => @lem6196694 _123593 f h0). Qed.
Lemma lem6196698 {_123593 : Type'} (f : nat -> _123593) : term277 _123593 f.
Proof. exact (@lem6196695 _123593 f (@lem6196687 _123593 f)). Qed.
Lemma lem6196699 {_123593 : Type'} (f : nat -> _123593) : term277 _123593 f.
Proof. exact (@lem6196698 _123593 f). Qed.
Lemma lem6196705 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6196706 {_123593 : Type'} (f : nat -> _123593) : (term275 _123593 f) = (term280 _123593 f).
Proof. exact (@lem6196705 (term276 _123593 f)). Qed.
Lemma lem6196708 (t : Prop) : (term55 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6196709 {_123593 : Type'} (f : nat -> _123593) : (term280 _123593 f) = (term273 _123593 f).
Proof. exact (@lem6196708 (term273 _123593 f)). Qed.
Lemma lem6196714 {_123593 : Type'} (f : nat -> _123593) : (term275 _123593 f) = (term273 _123593 f).
Proof. exact (TRANS (@lem6196706 _123593 f) (@lem6196709 _123593 f)). Qed.
Lemma lem6196757 {_123593 : Type'} : (term281 _123593) = (term282 _123593).
Proof. exact (fun_ext (fun f : nat -> _123593 => @lem6196714 _123593 f)). Qed.
Lemma lem6196758 {_123593 : Type'} : (@all (nat -> _123593)) = (@all (nat -> _123593)).
Proof. exact (eq_refl (@all (nat -> _123593))). Qed.
Lemma lem6196765 {_123593 : Type'} : (term283 _123593) = (term284 _123593).
Proof. exact (MK_COMB (@lem6196758 _123593) (@lem6196757 _123593)). Qed.
Lemma lem6196766 (_78957 : type1605) (h1 : _78957 = term285) : _78957 = term285.
Proof. exact (h1). Qed.
Lemma lem6196767 (k : nat) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem6196768 (k : nat) (_78957 : type1605) (h1 : _78957 = term285) : (_78957 k) = (term286 k).
Proof. exact (MK_COMB (@lem6196766 _78957 h1) (@lem6196767 k)). Qed.
Lemma lem6196769 (k : nat) : (term286 k) = (term256 k).
Proof. exact (eq_refl (term286 k)). Qed.
Lemma lem6196770 (_78957 : type1605) (k : nat) : (term287 _78957 k) = (term287 _78957 k).
Proof. exact (eq_refl (term287 _78957 k)). Qed.
Lemma lem6196771 (_78957 : type1605) (k : nat) : ((_78957 k) = (term286 k)) = ((_78957 k) = (term256 k)).
Proof. exact (MK_COMB (@lem6196770 _78957 k) (@lem6196769 k)). Qed.
Lemma lem6196772 (k : nat) (_78957 : type1605) (h1 : _78957 = term285) : (_78957 k) = (term256 k).
Proof. exact (EQ_MP (@lem6196771 _78957 k) (@lem6196768 k _78957 h1)). Qed.
Lemma lem6196778 {_123593 : Type'} (f : nat -> _123593) (k : nat) : (term288 _123593 f k) = (term288 _123593 f k).
Proof. exact (eq_refl (term288 _123593 f k)). Qed.
Lemma lem6196779 {_123593 : Type'} (f : nat -> _123593) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6196781 (k : nat) (_78957 : type1605) (h1 : _78957 = term285) : (term256 k) = (_78957 k).
Proof. exact (SYM (@lem6196772 k _78957 h1)). Qed.
Lemma lem6196782 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem6196783 (k : nat) (_78957 : type1605) (h1 : _78957 = term285) : (term220 k) = (term289 _78957 k).
Proof. exact (MK_COMB (@lem6196782) (@lem6196781 k _78957 h1)). Qed.
Lemma lem6196786 {_123593 : Type'} (op : type1400 _123593) : (@iterate _123593 nat op) = (@iterate _123593 nat op).
Proof. exact (eq_refl (@iterate _123593 nat op)). Qed.
Lemma lem6196787 {_123593 : Type'} (op : type1400 _123593) (k : nat) (_78957 : type1605) (h1 : _78957 = term285) : (term290 _123593 op k) = (term291 _123593 op _78957 k).
Proof. exact (MK_COMB (@lem6196786 _123593 op) (@lem6196783 k _78957 h1)). Qed.
Lemma lem6196788 {_123593 : Type'} (op : type1400 _123593) (k : nat) (f : nat -> _123593) (_78957 : type1605) (h1 : _78957 = term285) : (term263 _123593 op k f) = (term292 _123593 op _78957 k f).
Proof. exact (MK_COMB (@lem6196787 _123593 op k _78957 h1) (@lem6196779 _123593 f)). Qed.
Lemma lem6196789 {_123593 : Type'} (op : type1400 _123593) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6196790 {_123593 : Type'} (op : type1400 _123593) (k : nat) (f : nat -> _123593) (_78957 : type1605) (h1 : _78957 = term285) : (term293 _123593 op k f) = (term294 _123593 op _78957 k f).
Proof. exact (MK_COMB (@lem6196789 _123593 op) (@lem6196788 _123593 op k f _78957 h1)). Qed.
Lemma lem6196791 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) (k : nat) (_78957 : type1605) (h1 : _78957 = term285) : (term226 _123593 op f k) = (term295 _123593 op _78957 f k).
Proof. exact (MK_COMB (@lem6196790 _123593 op k f _78957 h1) (@lem6196778 _123593 f k)). Qed.
Lemma lem6196792 {_123593 : Type'} (f : nat -> _123593) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6196794 (k : nat) (_78957 : type1605) (h1 : _78957 = term285) : (term256 k) = (_78957 k).
Proof. exact (SYM (@lem6196772 k _78957 h1)). Qed.
Lemma lem6196795 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem6196796 (k : nat) (_78957 : type1605) (h1 : _78957 = term285) : (term220 k) = (term289 _78957 k).
Proof. exact (MK_COMB (@lem6196795) (@lem6196794 k _78957 h1)). Qed.
Lemma lem6196799 {_123593 : Type'} (op : type1400 _123593) : (@iterate _123593 nat op) = (@iterate _123593 nat op).
Proof. exact (eq_refl (@iterate _123593 nat op)). Qed.
Lemma lem6196800 {_123593 : Type'} (op : type1400 _123593) (k : nat) (_78957 : type1605) (h1 : _78957 = term285) : (term290 _123593 op k) = (term291 _123593 op _78957 k).
Proof. exact (MK_COMB (@lem6196799 _123593 op) (@lem6196796 k _78957 h1)). Qed.
Lemma lem6196801 {_123593 : Type'} (op : type1400 _123593) (k : nat) (f : nat -> _123593) (_78957 : type1605) (h1 : _78957 = term285) : (term263 _123593 op k f) = (term292 _123593 op _78957 k f).
Proof. exact (MK_COMB (@lem6196800 _123593 op k _78957 h1) (@lem6196792 _123593 f)). Qed.
Lemma lem6196808 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) (k : nat) : (term296 _123593 op f k) = (term296 _123593 op f k).
Proof. exact (eq_refl (term296 _123593 op f k)). Qed.
Lemma lem6196809 {_123593 : Type'} (op : type1400 _123593) (k : nat) (f : nat -> _123593) (_78957 : type1605) (h1 : _78957 = term285) : (term266 _123593 op k f) = (term297 _123593 op _78957 k f).
Proof. exact (MK_COMB (@lem6196808 _123593 op f k) (@lem6196801 _123593 op k f _78957 h1)). Qed.
Lemma lem6196810 {_123593 : Type'} : (@eq _123593) = (@eq _123593).
Proof. exact (eq_refl (@eq _123593)). Qed.
Lemma lem6196811 {_123593 : Type'} (op : type1400 _123593) (k : nat) (f : nat -> _123593) (_78957 : type1605) (h1 : _78957 = term285) : (term268 _123593 op k f) = (term298 _123593 op _78957 k f).
Proof. exact (MK_COMB (@lem6196810 _123593) (@lem6196809 _123593 op k f _78957 h1)). Qed.
Lemma lem6196812 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) (k : nat) (_78957 : type1605) (h1 : _78957 = term285) : ((term266 _123593 op k f) = (term226 _123593 op f k)) = ((term297 _123593 op _78957 k f) = (term295 _123593 op _78957 f k)).
Proof. exact (MK_COMB (@lem6196811 _123593 op k f _78957 h1) (@lem6196791 _123593 op f k _78957 h1)). Qed.
Lemma lem6196813 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) (_78957 : type1605) (h1 : _78957 = term285) : (term269 _123593 op f) = (term299 _123593 op _78957 f).
Proof. exact (fun_ext (fun k : nat => @lem6196812 _123593 op f k _78957 h1)). Qed.
Lemma lem6196814 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6196815 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) (_78957 : type1605) (h1 : _78957 = term285) : (term270 _123593 op f) = (term300 _123593 op _78957 f).
Proof. exact (MK_COMB (@lem6196814) (@lem6196813 _123593 op f _78957 h1)). Qed.
Lemma lem6196826 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : ((term301 _123593 op x) = x) = ((term301 _123593 op x) = x).
Proof. exact (eq_refl ((term301 _123593 op x) = x)). Qed.
Lemma lem6196827 {_123593 : Type'} (op : type1400 _123593) : (term302 _123593 op) = (term302 _123593 op).
Proof. exact (fun_ext (fun x : _123593 => @lem6196826 _123593 op x)). Qed.
Lemma lem6196828 {_123593 : Type'} : (@all _123593) = (@all _123593).
Proof. exact (eq_refl (@all _123593)). Qed.
Lemma lem6196829 {_123593 : Type'} (op : type1400 _123593) : (term303 _123593 op) = (term303 _123593 op).
Proof. exact (MK_COMB (@lem6196828 _123593) (@lem6196827 _123593 op)). Qed.
Lemma lem6196850 {_123593 : Type'} (op : type1400 _123593) (x : _123593) (y : _123593) (z : _123593) : ((term304 _123593 x op y z) = (term305 _123593 op x y z)) = ((term304 _123593 x op y z) = (term305 _123593 op x y z)).
Proof. exact (eq_refl ((term304 _123593 x op y z) = (term305 _123593 op x y z))). Qed.
Lemma lem6196851 {_123593 : Type'} (op : type1400 _123593) (x : _123593) (y : _123593) : (term306 _123593 op x y) = (term306 _123593 op x y).
Proof. exact (fun_ext (fun z : _123593 => @lem6196850 _123593 op x y z)). Qed.
Lemma lem6196852 {_123593 : Type'} : (@all _123593) = (@all _123593).
Proof. exact (eq_refl (@all _123593)). Qed.
Lemma lem6196853 {_123593 : Type'} (op : type1400 _123593) (x : _123593) (y : _123593) : (term307 _123593 op x y) = (term307 _123593 op x y).
Proof. exact (MK_COMB (@lem6196852 _123593) (@lem6196851 _123593 op x y)). Qed.
Lemma lem6196854 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : (term308 _123593 op x) = (term308 _123593 op x).
Proof. exact (fun_ext (fun y : _123593 => @lem6196853 _123593 op x y)). Qed.
Lemma lem6196855 {_123593 : Type'} : (@all _123593) = (@all _123593).
Proof. exact (eq_refl (@all _123593)). Qed.
Lemma lem6196856 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : (term309 _123593 op x) = (term309 _123593 op x).
Proof. exact (MK_COMB (@lem6196855 _123593) (@lem6196854 _123593 op x)). Qed.
Lemma lem6196857 {_123593 : Type'} (op : type1400 _123593) : (term310 _123593 op) = (term310 _123593 op).
Proof. exact (fun_ext (fun x : _123593 => @lem6196856 _123593 op x)). Qed.
Lemma lem6196858 {_123593 : Type'} : (@all _123593) = (@all _123593).
Proof. exact (eq_refl (@all _123593)). Qed.
Lemma lem6196859 {_123593 : Type'} (op : type1400 _123593) : (term311 _123593 op) = (term311 _123593 op).
Proof. exact (MK_COMB (@lem6196858 _123593) (@lem6196857 _123593 op)). Qed.
Lemma lem6196860 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6196861 {_123593 : Type'} (op : type1400 _123593) : (term312 _123593 op) = (term312 _123593 op).
Proof. exact (MK_COMB (@lem6196860) (@lem6196859 _123593 op)). Qed.
Lemma lem6196862 {_123593 : Type'} (op : type1400 _123593) : (term313 _123593 op) = (term313 _123593 op).
Proof. exact (MK_COMB (@lem6196861 _123593 op) (@lem6196829 _123593 op)). Qed.
Lemma lem6196875 {_123593 : Type'} (op : type1400 _123593) (y : _123593) (x : _123593) : ((op x y) = (op y x)) = ((op x y) = (op y x)).
Proof. exact (eq_refl ((op x y) = (op y x))). Qed.
Lemma lem6196876 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : (term314 _123593 op x) = (term314 _123593 op x).
Proof. exact (fun_ext (fun y : _123593 => @lem6196875 _123593 op y x)). Qed.
Lemma lem6196877 {_123593 : Type'} : (@all _123593) = (@all _123593).
Proof. exact (eq_refl (@all _123593)). Qed.
Lemma lem6196878 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : (term315 _123593 op x) = (term315 _123593 op x).
Proof. exact (MK_COMB (@lem6196877 _123593) (@lem6196876 _123593 op x)). Qed.
Lemma lem6196879 {_123593 : Type'} (op : type1400 _123593) : (term316 _123593 op) = (term316 _123593 op).
Proof. exact (fun_ext (fun x : _123593 => @lem6196878 _123593 op x)). Qed.
Lemma lem6196880 {_123593 : Type'} : (@all _123593) = (@all _123593).
Proof. exact (eq_refl (@all _123593)). Qed.
Lemma lem6196881 {_123593 : Type'} (op : type1400 _123593) : (term317 _123593 op) = (term317 _123593 op).
Proof. exact (MK_COMB (@lem6196880 _123593) (@lem6196879 _123593 op)). Qed.
Lemma lem6196882 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6196883 {_123593 : Type'} (op : type1400 _123593) : (term318 _123593 op) = (term318 _123593 op).
Proof. exact (MK_COMB (@lem6196882) (@lem6196881 _123593 op)). Qed.
Lemma lem6196884 {_123593 : Type'} (op : type1400 _123593) : (term159 _123593 op) = (term159 _123593 op).
Proof. exact (MK_COMB (@lem6196883 _123593 op) (@lem6196862 _123593 op)). Qed.
Lemma lem6196885 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6196886 {_123593 : Type'} (op : type1400 _123593) : (term241 _123593 op) = (term241 _123593 op).
Proof. exact (MK_COMB (@lem6196885) (@lem6196884 _123593 op)). Qed.
Lemma lem6196887 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) (_78957 : type1605) (h1 : _78957 = term285) : (term271 _123593 op f) = (term319 _123593 op _78957 f).
Proof. exact (MK_COMB (@lem6196886 _123593 op) (@lem6196815 _123593 op f _78957 h1)). Qed.
Lemma lem6196888 {_123593 : Type'} (f : nat -> _123593) (_78957 : type1605) (h1 : _78957 = term285) : (term272 _123593 f) = (term320 _123593 _78957 f).
Proof. exact (fun_ext (fun op : type1400 _123593 => @lem6196887 _123593 op f _78957 h1)). Qed.
Lemma lem6196889 {_123593 : Type'} : (@all (_123593 -> _123593 -> _123593)) = (@all (_123593 -> _123593 -> _123593)).
Proof. exact (eq_refl (@all (_123593 -> _123593 -> _123593))). Qed.
Lemma lem6196890 {_123593 : Type'} (f : nat -> _123593) (_78957 : type1605) (h1 : _78957 = term285) : (term273 _123593 f) = (term321 _123593 _78957 f).
Proof. exact (MK_COMB (@lem6196889 _123593) (@lem6196888 _123593 f _78957 h1)). Qed.
Lemma lem6196891 {_123593 : Type'} (_78957 : type1605) (h1 : _78957 = term285) : (term282 _123593) = (term322 _123593 _78957).
Proof. exact (fun_ext (fun f : nat -> _123593 => @lem6196890 _123593 f _78957 h1)). Qed.
Lemma lem6196892 {_123593 : Type'} : (@all (nat -> _123593)) = (@all (nat -> _123593)).
Proof. exact (eq_refl (@all (nat -> _123593))). Qed.
Lemma lem6196893 {_123593 : Type'} (_78957 : type1605) (h1 : _78957 = term285) : (term284 _123593) = (term323 _123593 _78957).
Proof. exact (MK_COMB (@lem6196892 _123593) (@lem6196891 _123593 _78957 h1)). Qed.
Lemma lem6196894 {_123593 : Type'} (_78957 : type1605) : term324 _123593 _78957.
Proof. exact (fun h0 : _78957 = term285 => @lem6196893 _123593 _78957 h0). Qed.
Lemma lem6196895 {_123593 : Type'} : term325 _123593.
Proof. exact (fun _78957 : type1605 => @lem6196894 _123593 _78957). Qed.
Lemma lem6196897 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term326 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem6196898 (P : Prop) (c : type1605) (Q : type959) : term327 P c Q.
Proof. exact (@lem6196897 type1605 P c Q). Qed.
Lemma lem6196899 {_123593 : Type'} : term328 _123593.
Proof. exact (@lem6196898 (term284 _123593) term285 (term329 _123593)). Qed.
Lemma lem6196900 {_123593 : Type'} (_78957 : type1605) : (term330 _123593 _78957) = (term323 _123593 _78957).
Proof. exact (eq_refl (term330 _123593 _78957)). Qed.
Lemma lem6196901 {_123593 : Type'} : (term331 _123593) = (term331 _123593).
Proof. exact (eq_refl (term331 _123593)). Qed.
Lemma lem6196902 {_123593 : Type'} (_78957 : type1605) : ((term284 _123593) = (term330 _123593 _78957)) = ((term284 _123593) = (term323 _123593 _78957)).
Proof. exact (MK_COMB (@lem6196901 _123593) (@lem6196900 _123593 _78957)). Qed.
Lemma lem6196903 (_78957 : type1605) : (term332 _78957) = (term332 _78957).
Proof. exact (eq_refl (term332 _78957)). Qed.
Lemma lem6196904 {_123593 : Type'} (_78957 : type1605) : (term333 _123593 _78957) = (term324 _123593 _78957).
Proof. exact (MK_COMB (@lem6196903 _78957) (@lem6196902 _123593 _78957)). Qed.
Lemma lem6196905 {_123593 : Type'} : (term334 _123593) = (term335 _123593).
Proof. exact (fun_ext (fun _78957 : type1605 => @lem6196904 _123593 _78957)). Qed.
Lemma lem6196906 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem6196907 {_123593 : Type'} : (term336 _123593) = (term325 _123593).
Proof. exact (MK_COMB (@lem6196906) (@lem6196905 _123593)). Qed.
Lemma lem6196908 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6196909 {_123593 : Type'} : (term337 _123593) = (term338 _123593).
Proof. exact (MK_COMB (@lem6196908) (@lem6196907 _123593)). Qed.
Lemma lem6196910 {_123593 : Type'} (_78957 : type1605) : (term330 _123593 _78957) = (term323 _123593 _78957).
Proof. exact (eq_refl (term330 _123593 _78957)). Qed.
Lemma lem6196911 (_78957 : type1605) : (term332 _78957) = (term332 _78957).
Proof. exact (eq_refl (term332 _78957)). Qed.
Lemma lem6196912 {_123593 : Type'} (_78957 : type1605) : (term339 _123593 _78957) = (term340 _123593 _78957).
Proof. exact (MK_COMB (@lem6196911 _78957) (@lem6196910 _123593 _78957)). Qed.
Lemma lem6196913 {_123593 : Type'} : (term341 _123593) = (term342 _123593).
Proof. exact (fun_ext (fun _78957 : type1605 => @lem6196912 _123593 _78957)). Qed.
Lemma lem6196914 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem6196915 {_123593 : Type'} : (term343 _123593) = (term344 _123593).
Proof. exact (MK_COMB (@lem6196914) (@lem6196913 _123593)). Qed.
Lemma lem6196916 {_123593 : Type'} : (term331 _123593) = (term331 _123593).
Proof. exact (eq_refl (term331 _123593)). Qed.
Lemma lem6196917 {_123593 : Type'} : ((term284 _123593) = (term343 _123593)) = ((term284 _123593) = (term344 _123593)).
Proof. exact (MK_COMB (@lem6196916 _123593) (@lem6196915 _123593)). Qed.
Lemma lem6196918 {_123593 : Type'} : (term328 _123593) = (term345 _123593).
Proof. exact (MK_COMB (@lem6196909 _123593) (@lem6196917 _123593)). Qed.
Lemma lem6196919 {_123593 : Type'} : term345 _123593.
Proof. exact (EQ_MP (@lem6196918 _123593) (@lem6196899 _123593)). Qed.
Lemma lem6196920 {_123593 : Type'} : (term284 _123593) = (term344 _123593).
Proof. exact (@lem6196919 _123593 (@lem6196895 _123593)). Qed.
Lemma lem6196922 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term346 _3571 _3575 t)) = (term347 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem6196923 (s : type1605) (t : type1605) : (s = (term348 t)) = (term349 s t).
Proof. exact (@lem6196922 (nat -> Prop) nat s t). Qed.
Lemma lem6196924 (_78957 : type1605) : (_78957 = term350) = (term351 _78957).
Proof. exact (@lem6196923 _78957 term285). Qed.
Lemma lem6196925 (k : nat) : (term286 k) = (term256 k).
Proof. exact (eq_refl (term286 k)). Qed.
Lemma lem6196926 : term350 = term285.
Proof. exact (fun_ext (fun k : nat => @lem6196925 k)). Qed.
Lemma lem6196927 (_78957 : type1605) : (@eq (nat -> nat -> Prop) _78957) = (@eq (nat -> nat -> Prop) _78957).
Proof. exact (eq_refl (@eq (nat -> nat -> Prop) _78957)). Qed.
Lemma lem6196928 (_78957 : type1605) : (_78957 = term350) = (_78957 = term285).
Proof. exact (MK_COMB (@lem6196927 _78957) (@lem6196926)). Qed.
Lemma lem6196929 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6196930 (_78957 : type1605) : (term352 _78957) = (term353 _78957).
Proof. exact (MK_COMB (@lem6196929) (@lem6196928 _78957)). Qed.
Lemma lem6196931 (k : nat) : (term286 k) = (term256 k).
Proof. exact (eq_refl (term286 k)). Qed.
Lemma lem6196932 (_78957 : type1605) (k : nat) : (term287 _78957 k) = (term287 _78957 k).
Proof. exact (eq_refl (term287 _78957 k)). Qed.
Lemma lem6196933 (_78957 : type1605) (k : nat) : ((_78957 k) = (term286 k)) = ((_78957 k) = (term256 k)).
Proof. exact (MK_COMB (@lem6196932 _78957 k) (@lem6196931 k)). Qed.
Lemma lem6196934 (_78957 : type1605) : (term354 _78957) = (term355 _78957).
Proof. exact (fun_ext (fun k : nat => @lem6196933 _78957 k)). Qed.
Lemma lem6196935 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6196936 (_78957 : type1605) : (term351 _78957) = (term356 _78957).
Proof. exact (MK_COMB (@lem6196935) (@lem6196934 _78957)). Qed.
Lemma lem6196937 (_78957 : type1605) : ((_78957 = term350) = (term351 _78957)) = ((_78957 = term285) = (term356 _78957)).
Proof. exact (MK_COMB (@lem6196930 _78957) (@lem6196936 _78957)). Qed.
Lemma lem6196938 (_78957 : type1605) : (_78957 = term285) = (term356 _78957).
Proof. exact (EQ_MP (@lem6196937 _78957) (@lem6196924 _78957)). Qed.
Lemma lem6196940 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term346 _3571 _3575 t)) = (term347 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem6196941 (s : nat -> Prop) (t : nat -> Prop) : (s = (term357 t)) = (term358 s t).
Proof. exact (@lem6196940 Prop nat s t). Qed.
Lemma lem6196942 (_78957 : type1605) (k : nat) : ((_78957 k) = (term359 k)) = (term360 _78957 k).
Proof. exact (@lem6196941 (_78957 k) (term256 k)). Qed.
Lemma lem6196943 (GEN_PVAR_187 : nat) (k : nat) : (term361 k GEN_PVAR_187) = (term254 GEN_PVAR_187 k).
Proof. exact (eq_refl (term361 k GEN_PVAR_187)). Qed.
Lemma lem6196944 (k : nat) : (term359 k) = (term256 k).
Proof. exact (fun_ext (fun GEN_PVAR_187 : nat => @lem6196943 GEN_PVAR_187 k)). Qed.
Lemma lem6196945 (_78957 : type1605) (k : nat) : (term287 _78957 k) = (term287 _78957 k).
Proof. exact (eq_refl (term287 _78957 k)). Qed.
Lemma lem6196946 (_78957 : type1605) (k : nat) : ((_78957 k) = (term359 k)) = ((_78957 k) = (term256 k)).
Proof. exact (MK_COMB (@lem6196945 _78957 k) (@lem6196944 k)). Qed.
Lemma lem6196947 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6196948 (_78957 : type1605) (k : nat) : (term362 _78957 k) = (term363 _78957 k).
Proof. exact (MK_COMB (@lem6196947) (@lem6196946 _78957 k)). Qed.
Lemma lem6196949 (GEN_PVAR_187 : nat) (k : nat) : (term361 k GEN_PVAR_187) = (term254 GEN_PVAR_187 k).
Proof. exact (eq_refl (term361 k GEN_PVAR_187)). Qed.
Lemma lem6196950 (_78957 : type1605) (k : nat) (GEN_PVAR_187 : nat) : (term364 _78957 k GEN_PVAR_187) = (term364 _78957 k GEN_PVAR_187).
Proof. exact (eq_refl (term364 _78957 k GEN_PVAR_187)). Qed.
Lemma lem6196951 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) : ((_78957 k GEN_PVAR_187) = (term361 k GEN_PVAR_187)) = ((_78957 k GEN_PVAR_187) = (term254 GEN_PVAR_187 k)).
Proof. exact (MK_COMB (@lem6196950 _78957 k GEN_PVAR_187) (@lem6196949 GEN_PVAR_187 k)). Qed.
Lemma lem6196952 (_78957 : type1605) (k : nat) : (term365 _78957 k) = (term366 _78957 k).
Proof. exact (fun_ext (fun GEN_PVAR_187 : nat => @lem6196951 _78957 GEN_PVAR_187 k)). Qed.
Lemma lem6196953 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6196954 (_78957 : type1605) (k : nat) : (term360 _78957 k) = (term367 _78957 k).
Proof. exact (MK_COMB (@lem6196953) (@lem6196952 _78957 k)). Qed.
Lemma lem6196955 (_78957 : type1605) (k : nat) : (((_78957 k) = (term359 k)) = (term360 _78957 k)) = (((_78957 k) = (term256 k)) = (term367 _78957 k)).
Proof. exact (MK_COMB (@lem6196948 _78957 k) (@lem6196954 _78957 k)). Qed.
Lemma lem6196956 (_78957 : type1605) (k : nat) : ((_78957 k) = (term256 k)) = (term367 _78957 k).
Proof. exact (EQ_MP (@lem6196955 _78957 k) (@lem6196942 _78957 k)). Qed.
Lemma lem6196957 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) : ((_78957 k GEN_PVAR_187) = (term254 GEN_PVAR_187 k)) = ((_78957 k GEN_PVAR_187) = (term254 GEN_PVAR_187 k)).
Proof. exact (eq_refl ((_78957 k GEN_PVAR_187) = (term254 GEN_PVAR_187 k))). Qed.
Lemma lem6196958 (_78957 : type1605) (k : nat) : (term366 _78957 k) = (term366 _78957 k).
Proof. exact (fun_ext (fun GEN_PVAR_187 : nat => @lem6196957 _78957 GEN_PVAR_187 k)). Qed.
Lemma lem6196959 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6196960 (_78957 : type1605) (k : nat) : (term367 _78957 k) = (term367 _78957 k).
Proof. exact (MK_COMB (@lem6196959) (@lem6196958 _78957 k)). Qed.
Lemma lem6196961 (_78957 : type1605) (k : nat) : ((_78957 k) = (term256 k)) = (term367 _78957 k).
Proof. exact (TRANS (@lem6196956 _78957 k) (@lem6196960 _78957 k)). Qed.
Lemma lem6196962 (_78957 : type1605) : (term355 _78957) = (term368 _78957).
Proof. exact (fun_ext (fun k : nat => @lem6196961 _78957 k)). Qed.
Lemma lem6196963 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6196964 (_78957 : type1605) : (term356 _78957) = (term369 _78957).
Proof. exact (MK_COMB (@lem6196963) (@lem6196962 _78957)). Qed.
Lemma lem6196965 (_78957 : type1605) : (_78957 = term285) = (term369 _78957).
Proof. exact (TRANS (@lem6196938 _78957) (@lem6196964 _78957)). Qed.
Lemma lem6196966 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6196967 (_78957 : type1605) : (term332 _78957) = (term370 _78957).
Proof. exact (MK_COMB (@lem6196966) (@lem6196965 _78957)). Qed.
Lemma lem6196968 {_123593 : Type'} (_78957 : type1605) : (term323 _123593 _78957) = (term323 _123593 _78957).
Proof. exact (eq_refl (term323 _123593 _78957)). Qed.
Lemma lem6196969 {_123593 : Type'} (_78957 : type1605) : (term340 _123593 _78957) = (term371 _123593 _78957).
Proof. exact (MK_COMB (@lem6196967 _78957) (@lem6196968 _123593 _78957)). Qed.
Lemma lem6196970 {_123593 : Type'} : (term342 _123593) = (term372 _123593).
Proof. exact (fun_ext (fun _78957 : type1605 => @lem6196969 _123593 _78957)). Qed.
Lemma lem6196971 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem6196972 {_123593 : Type'} : (term344 _123593) = (term373 _123593).
Proof. exact (MK_COMB (@lem6196971) (@lem6196970 _123593)). Qed.
Lemma lem6196973 {_123593 : Type'} : (term331 _123593) = (term331 _123593).
Proof. exact (eq_refl (term331 _123593)). Qed.
Lemma lem6196974 {_123593 : Type'} : ((term284 _123593) = (term344 _123593)) = ((term284 _123593) = (term373 _123593)).
Proof. exact (MK_COMB (@lem6196973 _123593) (@lem6196972 _123593)). Qed.
Lemma lem6196977 {_123593 : Type'} : (term284 _123593) = (term373 _123593).
Proof. exact (EQ_MP (@lem6196974 _123593) (@lem6196920 _123593)). Qed.
Lemma lem6196978 {_123593 : Type'} : (term283 _123593) = (term373 _123593).
Proof. exact (TRANS (@lem6196765 _123593) (@lem6196977 _123593)). Qed.
Lemma lem6196979 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (f : nat -> _123593) (k : nat) : ((term297 _123593 op _78957 k f) = (term295 _123593 op _78957 f k)) = ((term297 _123593 op _78957 k f) = (term295 _123593 op _78957 f k)).
Proof. exact (eq_refl ((term297 _123593 op _78957 k f) = (term295 _123593 op _78957 f k))). Qed.
Lemma lem6196980 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (f : nat -> _123593) : (term299 _123593 op _78957 f) = (term299 _123593 op _78957 f).
Proof. exact (fun_ext (fun k : nat => @lem6196979 _123593 op _78957 f k)). Qed.
Lemma lem6196981 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6196982 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (f : nat -> _123593) : (term300 _123593 op _78957 f) = (term300 _123593 op _78957 f).
Proof. exact (MK_COMB (@lem6196981) (@lem6196980 _123593 op _78957 f)). Qed.
Lemma lem6196983 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : ((term301 _123593 op x) = x) = ((term301 _123593 op x) = x).
Proof. exact (eq_refl ((term301 _123593 op x) = x)). Qed.
Lemma lem6196984 {_123593 : Type'} (op : type1400 _123593) : (term302 _123593 op) = (term302 _123593 op).
Proof. exact (fun_ext (fun x : _123593 => @lem6196983 _123593 op x)). Qed.
Lemma lem6196985 {_123593 : Type'} : (@all _123593) = (@all _123593).
Proof. exact (eq_refl (@all _123593)). Qed.
Lemma lem6196986 {_123593 : Type'} (op : type1400 _123593) : (term303 _123593 op) = (term303 _123593 op).
Proof. exact (MK_COMB (@lem6196985 _123593) (@lem6196984 _123593 op)). Qed.
Lemma lem6196987 {_123593 : Type'} (op : type1400 _123593) (x : _123593) (y : _123593) (z : _123593) : ((term304 _123593 x op y z) = (term305 _123593 op x y z)) = ((term304 _123593 x op y z) = (term305 _123593 op x y z)).
Proof. exact (eq_refl ((term304 _123593 x op y z) = (term305 _123593 op x y z))). Qed.
Lemma lem6196988 {_123593 : Type'} (op : type1400 _123593) (x : _123593) (y : _123593) : (term306 _123593 op x y) = (term306 _123593 op x y).
Proof. exact (fun_ext (fun z : _123593 => @lem6196987 _123593 op x y z)). Qed.
Lemma lem6196989 {_123593 : Type'} : (@all _123593) = (@all _123593).
Proof. exact (eq_refl (@all _123593)). Qed.
Lemma lem6196990 {_123593 : Type'} (op : type1400 _123593) (x : _123593) (y : _123593) : (term307 _123593 op x y) = (term307 _123593 op x y).
Proof. exact (MK_COMB (@lem6196989 _123593) (@lem6196988 _123593 op x y)). Qed.
Lemma lem6196991 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : (term308 _123593 op x) = (term308 _123593 op x).
Proof. exact (fun_ext (fun y : _123593 => @lem6196990 _123593 op x y)). Qed.
Lemma lem6196992 {_123593 : Type'} : (@all _123593) = (@all _123593).
Proof. exact (eq_refl (@all _123593)). Qed.
Lemma lem6196993 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : (term309 _123593 op x) = (term309 _123593 op x).
Proof. exact (MK_COMB (@lem6196992 _123593) (@lem6196991 _123593 op x)). Qed.
Lemma lem6196994 {_123593 : Type'} (op : type1400 _123593) : (term310 _123593 op) = (term310 _123593 op).
Proof. exact (fun_ext (fun x : _123593 => @lem6196993 _123593 op x)). Qed.
Lemma lem6196995 {_123593 : Type'} : (@all _123593) = (@all _123593).
Proof. exact (eq_refl (@all _123593)). Qed.
Lemma lem6196996 {_123593 : Type'} (op : type1400 _123593) : (term311 _123593 op) = (term311 _123593 op).
Proof. exact (MK_COMB (@lem6196995 _123593) (@lem6196994 _123593 op)). Qed.
Lemma lem6196997 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6196998 {_123593 : Type'} (op : type1400 _123593) : (term312 _123593 op) = (term312 _123593 op).
Proof. exact (MK_COMB (@lem6196997) (@lem6196996 _123593 op)). Qed.
Lemma lem6196999 {_123593 : Type'} (op : type1400 _123593) : (term313 _123593 op) = (term313 _123593 op).
Proof. exact (MK_COMB (@lem6196998 _123593 op) (@lem6196986 _123593 op)). Qed.
Lemma lem6197000 {_123593 : Type'} (op : type1400 _123593) (y : _123593) (x : _123593) : ((op x y) = (op y x)) = ((op x y) = (op y x)).
Proof. exact (eq_refl ((op x y) = (op y x))). Qed.
Lemma lem6197001 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : (term314 _123593 op x) = (term314 _123593 op x).
Proof. exact (fun_ext (fun y : _123593 => @lem6197000 _123593 op y x)). Qed.
Lemma lem6197002 {_123593 : Type'} : (@all _123593) = (@all _123593).
Proof. exact (eq_refl (@all _123593)). Qed.
Lemma lem6197003 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : (term315 _123593 op x) = (term315 _123593 op x).
Proof. exact (MK_COMB (@lem6197002 _123593) (@lem6197001 _123593 op x)). Qed.
Lemma lem6197004 {_123593 : Type'} (op : type1400 _123593) : (term316 _123593 op) = (term316 _123593 op).
Proof. exact (fun_ext (fun x : _123593 => @lem6197003 _123593 op x)). Qed.
Lemma lem6197005 {_123593 : Type'} : (@all _123593) = (@all _123593).
Proof. exact (eq_refl (@all _123593)). Qed.
Lemma lem6197006 {_123593 : Type'} (op : type1400 _123593) : (term317 _123593 op) = (term317 _123593 op).
Proof. exact (MK_COMB (@lem6197005 _123593) (@lem6197004 _123593 op)). Qed.
Lemma lem6197007 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6197008 {_123593 : Type'} (op : type1400 _123593) : (term318 _123593 op) = (term318 _123593 op).
Proof. exact (MK_COMB (@lem6197007) (@lem6197006 _123593 op)). Qed.
Lemma lem6197009 {_123593 : Type'} (op : type1400 _123593) : (term159 _123593 op) = (term159 _123593 op).
Proof. exact (MK_COMB (@lem6197008 _123593 op) (@lem6196999 _123593 op)). Qed.
Lemma lem6197010 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6197011 {_123593 : Type'} (op : type1400 _123593) : (term241 _123593 op) = (term241 _123593 op).
Proof. exact (MK_COMB (@lem6197010) (@lem6197009 _123593 op)). Qed.
Lemma lem6197012 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (f : nat -> _123593) : (term319 _123593 op _78957 f) = (term319 _123593 op _78957 f).
Proof. exact (MK_COMB (@lem6197011 _123593 op) (@lem6196982 _123593 op _78957 f)). Qed.
Lemma lem6197013 {_123593 : Type'} (_78957 : type1605) (f : nat -> _123593) : (term320 _123593 _78957 f) = (term320 _123593 _78957 f).
Proof. exact (fun_ext (fun op : type1400 _123593 => @lem6197012 _123593 op _78957 f)). Qed.
Lemma lem6197014 {_123593 : Type'} : (@all (_123593 -> _123593 -> _123593)) = (@all (_123593 -> _123593 -> _123593)).
Proof. exact (eq_refl (@all (_123593 -> _123593 -> _123593))). Qed.
Lemma lem6197015 {_123593 : Type'} (_78957 : type1605) (f : nat -> _123593) : (term321 _123593 _78957 f) = (term321 _123593 _78957 f).
Proof. exact (MK_COMB (@lem6197014 _123593) (@lem6197013 _123593 _78957 f)). Qed.
Lemma lem6197016 {_123593 : Type'} (_78957 : type1605) : (term322 _123593 _78957) = (term322 _123593 _78957).
Proof. exact (fun_ext (fun f : nat -> _123593 => @lem6197015 _123593 _78957 f)). Qed.
Lemma lem6197017 {_123593 : Type'} : (@all (nat -> _123593)) = (@all (nat -> _123593)).
Proof. exact (eq_refl (@all (nat -> _123593))). Qed.
Lemma lem6197018 {_123593 : Type'} (_78957 : type1605) : (term323 _123593 _78957) = (term323 _123593 _78957).
Proof. exact (MK_COMB (@lem6197017 _123593) (@lem6197016 _123593 _78957)). Qed.
Lemma lem6197019 (GEN_PVAR_187 : nat) (k : nat) (i : nat) : (term250 GEN_PVAR_187 k i) = (term250 GEN_PVAR_187 k i).
Proof. exact (eq_refl (term250 GEN_PVAR_187 k i)). Qed.
Lemma lem6197020 (GEN_PVAR_187 : nat) (k : nat) : (term252 GEN_PVAR_187 k) = (term252 GEN_PVAR_187 k).
Proof. exact (fun_ext (fun i : nat => @lem6197019 GEN_PVAR_187 k i)). Qed.
Lemma lem6197021 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6197022 (GEN_PVAR_187 : nat) (k : nat) : (term254 GEN_PVAR_187 k) = (term254 GEN_PVAR_187 k).
Proof. exact (MK_COMB (@lem6197021) (@lem6197020 GEN_PVAR_187 k)). Qed.
Lemma lem6197025 (_78957 : type1605) (k : nat) (GEN_PVAR_187 : nat) : (term364 _78957 k GEN_PVAR_187) = (term364 _78957 k GEN_PVAR_187).
Proof. exact (eq_refl (term364 _78957 k GEN_PVAR_187)). Qed.
Lemma lem6197026 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) : ((_78957 k GEN_PVAR_187) = (term254 GEN_PVAR_187 k)) = ((_78957 k GEN_PVAR_187) = (term254 GEN_PVAR_187 k)).
Proof. exact (MK_COMB (@lem6197025 _78957 k GEN_PVAR_187) (@lem6197022 GEN_PVAR_187 k)). Qed.
Lemma lem6197027 (_78957 : type1605) (k : nat) : (term366 _78957 k) = (term366 _78957 k).
Proof. exact (fun_ext (fun GEN_PVAR_187 : nat => @lem6197026 _78957 GEN_PVAR_187 k)). Qed.
Lemma lem6197028 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6197029 (_78957 : type1605) (k : nat) : (term367 _78957 k) = (term367 _78957 k).
Proof. exact (MK_COMB (@lem6197028) (@lem6197027 _78957 k)). Qed.
Lemma lem6197030 (_78957 : type1605) : (term368 _78957) = (term368 _78957).
Proof. exact (fun_ext (fun k : nat => @lem6197029 _78957 k)). Qed.
Lemma lem6197031 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6197032 (_78957 : type1605) : (term369 _78957) = (term369 _78957).
Proof. exact (MK_COMB (@lem6197031) (@lem6197030 _78957)). Qed.
Lemma lem6197033 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6197034 (_78957 : type1605) : (term370 _78957) = (term370 _78957).
Proof. exact (MK_COMB (@lem6197033) (@lem6197032 _78957)). Qed.
Lemma lem6197035 {_123593 : Type'} (_78957 : type1605) : (term371 _123593 _78957) = (term371 _123593 _78957).
Proof. exact (MK_COMB (@lem6197034 _78957) (@lem6197018 _123593 _78957)). Qed.
Lemma lem6197036 {_123593 : Type'} : (term372 _123593) = (term372 _123593).
Proof. exact (fun_ext (fun _78957 : type1605 => @lem6197035 _123593 _78957)). Qed.
Lemma lem6197037 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem6197038 {_123593 : Type'} : (term373 _123593) = (term373 _123593).
Proof. exact (MK_COMB (@lem6197037) (@lem6197036 _123593)). Qed.
Lemma lem6197127 {_123593 : Type'} : (term283 _123593) = (term373 _123593).
Proof. exact (TRANS (@lem6196978 _123593) (@lem6197038 _123593)). Qed.
Lemma lem6197128 {_123593 : Type'} : (term373 _123593) = (term283 _123593).
Proof. exact (SYM (@lem6197127 _123593)). Qed.
Lemma lem6197129 (_78957 : type1605) (h1 : term369 _78957) : term369 _78957.
Proof. exact (h1). Qed.
Lemma lem6197130 {_123593 : Type'} (op : type1400 _123593) (h1 : term159 _123593 op) : term159 _123593 op.
Proof. exact (h1). Qed.
Lemma lem6197132 (p : Prop) : p = (term274 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6197133 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (f : nat -> _123593) (k : nat) : ((term297 _123593 op _78957 k f) = (term295 _123593 op _78957 f k)) = (term374 _123593 op _78957 f k).
Proof. exact (@lem6197132 ((term297 _123593 op _78957 k f) = (term295 _123593 op _78957 f k))). Qed.
Lemma lem6197134 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (f : nat -> _123593) (k : nat) : (term374 _123593 op _78957 f k) = ((term297 _123593 op _78957 k f) = (term295 _123593 op _78957 f k)).
Proof. exact (SYM (@lem6197133 _123593 op _78957 f k)). Qed.
Lemma lem6197135 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (f : nat -> _123593) (k : nat) (h1 : term375 _123593 op _78957 f k) : term375 _123593 op _78957 f k.
Proof. exact (h1). Qed.
Lemma lem6197139 (GEN_PVAR_187 : nat) (k : nat) (i : nat) : (term250 GEN_PVAR_187 k i) = (term250 GEN_PVAR_187 k i).
Proof. exact (eq_refl (term250 GEN_PVAR_187 k i)). Qed.
Lemma lem6197140 (P : nat -> Prop) : (term376 P) = (term377 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem6197141 (GEN_PVAR_187 : nat) (k : nat) : (term378 GEN_PVAR_187 k) = (term379 GEN_PVAR_187 k).
Proof. exact (@lem6197140 (term252 GEN_PVAR_187 k)). Qed.
Lemma lem6197142 (GEN_PVAR_187 : nat) (k : nat) (i : nat) : (term380 GEN_PVAR_187 k i) = (term250 GEN_PVAR_187 k i).
Proof. exact (eq_refl (term380 GEN_PVAR_187 k i)). Qed.
Lemma lem6197143 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6197145 (GEN_PVAR_187 : nat) (k : nat) (i : nat) : (term381 GEN_PVAR_187 k i) = (term382 GEN_PVAR_187 k i).
Proof. exact (MK_COMB (@lem6197143) (@lem6197142 GEN_PVAR_187 k i)). Qed.
Lemma lem6197146 (GEN_PVAR_187 : nat) (k : nat) : (term383 GEN_PVAR_187 k) = (term384 GEN_PVAR_187 k).
Proof. exact (fun_ext (fun i : nat => @lem6197145 GEN_PVAR_187 k i)). Qed.
Lemma lem6197147 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6197148 (GEN_PVAR_187 : nat) (k : nat) : (term379 GEN_PVAR_187 k) = (term385 GEN_PVAR_187 k).
Proof. exact (MK_COMB (@lem6197147) (@lem6197146 GEN_PVAR_187 k)). Qed.
Lemma lem6197149 (GEN_PVAR_187 : nat) (k : nat) : (term378 GEN_PVAR_187 k) = (term385 GEN_PVAR_187 k).
Proof. exact (TRANS (@lem6197141 GEN_PVAR_187 k) (@lem6197148 GEN_PVAR_187 k)). Qed.
Lemma lem6197150 (GEN_PVAR_187 : nat) (k : nat) : (term252 GEN_PVAR_187 k) = (term252 GEN_PVAR_187 k).
Proof. exact (fun_ext (fun i : nat => @lem6197139 GEN_PVAR_187 k i)). Qed.
Lemma lem6197151 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6197152 (GEN_PVAR_187 : nat) (k : nat) : (term254 GEN_PVAR_187 k) = (term254 GEN_PVAR_187 k).
Proof. exact (MK_COMB (@lem6197151) (@lem6197150 GEN_PVAR_187 k)). Qed.
Lemma lem6197154 (_78957 : type1605) (k : nat) (GEN_PVAR_187 : nat) : (term386 _78957 k GEN_PVAR_187) = (term386 _78957 k GEN_PVAR_187).
Proof. exact (eq_refl (term386 _78957 k GEN_PVAR_187)). Qed.
Lemma lem6197155 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) : (term387 _78957 GEN_PVAR_187 k) = (term387 _78957 GEN_PVAR_187 k).
Proof. exact (MK_COMB (@lem6197154 _78957 k GEN_PVAR_187) (@lem6197152 GEN_PVAR_187 k)). Qed.
Lemma lem6197157 (_78957 : type1605) (k : nat) (GEN_PVAR_187 : nat) : (term388 _78957 k GEN_PVAR_187) = (term388 _78957 k GEN_PVAR_187).
Proof. exact (eq_refl (term388 _78957 k GEN_PVAR_187)). Qed.
Lemma lem6197158 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) : (term389 _78957 GEN_PVAR_187 k) = (term390 _78957 GEN_PVAR_187 k).
Proof. exact (MK_COMB (@lem6197157 _78957 k GEN_PVAR_187) (@lem6197149 GEN_PVAR_187 k)). Qed.
Lemma lem6197159 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6197160 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) : (term391 _78957 GEN_PVAR_187 k) = (term392 _78957 GEN_PVAR_187 k).
Proof. exact (MK_COMB (@lem6197159) (@lem6197158 _78957 GEN_PVAR_187 k)). Qed.
Lemma lem6197161 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) : (term393 _78957 GEN_PVAR_187 k) = (term394 _78957 GEN_PVAR_187 k).
Proof. exact (MK_COMB (@lem6197160 _78957 GEN_PVAR_187 k) (@lem6197155 _78957 GEN_PVAR_187 k)). Qed.
Lemma lem6197162 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) : ((_78957 k GEN_PVAR_187) = (term254 GEN_PVAR_187 k)) = (term393 _78957 GEN_PVAR_187 k).
Proof. exact (@lem17784 (_78957 k GEN_PVAR_187) (term254 GEN_PVAR_187 k)). Qed.
Lemma lem6197163 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) : ((_78957 k GEN_PVAR_187) = (term254 GEN_PVAR_187 k)) = (term394 _78957 GEN_PVAR_187 k).
Proof. exact (TRANS (@lem6197162 _78957 GEN_PVAR_187 k) (@lem6197161 _78957 GEN_PVAR_187 k)). Qed.
Lemma lem6197164 (_78957 : type1605) (k : nat) : (term366 _78957 k) = (term395 _78957 k).
Proof. exact (fun_ext (fun GEN_PVAR_187 : nat => @lem6197163 _78957 GEN_PVAR_187 k)). Qed.
Lemma lem6197165 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6197166 (_78957 : type1605) (k : nat) : (term367 _78957 k) = (term396 _78957 k).
Proof. exact (MK_COMB (@lem6197165) (@lem6197164 _78957 k)). Qed.
Lemma lem6197167 (_78957 : type1605) : (term368 _78957) = (term397 _78957).
Proof. exact (fun_ext (fun k : nat => @lem6197166 _78957 k)). Qed.
Lemma lem6197168 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6197169 (_78957 : type1605) : (term369 _78957) = (term398 _78957).
Proof. exact (MK_COMB (@lem6197168) (@lem6197167 _78957)). Qed.
Lemma lem6197175 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term399 A P Q) = (term400 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6197176 (P : nat -> Prop) (Q : nat -> Prop) : (term401 P Q) = (term402 P Q).
Proof. exact (@lem6197175 nat P Q). Qed.
Lemma lem6197177 (_78957 : type1605) (k : nat) : (term403 _78957 k) = (term404 _78957 k).
Proof. exact (@lem6197176 (term405 _78957 k) (term406 _78957 k)). Qed.
Lemma lem6197178 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) : (term407 _78957 k GEN_PVAR_187) = (term390 _78957 GEN_PVAR_187 k).
Proof. exact (eq_refl (term407 _78957 k GEN_PVAR_187)). Qed.
Lemma lem6197179 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6197180 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) : (term408 _78957 k GEN_PVAR_187) = (term392 _78957 GEN_PVAR_187 k).
Proof. exact (MK_COMB (@lem6197179) (@lem6197178 _78957 GEN_PVAR_187 k)). Qed.
Lemma lem6197181 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) : (term409 _78957 k GEN_PVAR_187) = (term387 _78957 GEN_PVAR_187 k).
Proof. exact (eq_refl (term409 _78957 k GEN_PVAR_187)). Qed.
Lemma lem6197182 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) : (term410 _78957 k GEN_PVAR_187) = (term394 _78957 GEN_PVAR_187 k).
Proof. exact (MK_COMB (@lem6197180 _78957 GEN_PVAR_187 k) (@lem6197181 _78957 GEN_PVAR_187 k)). Qed.
Lemma lem6197183 (_78957 : type1605) (k : nat) : (term411 _78957 k) = (term395 _78957 k).
Proof. exact (fun_ext (fun GEN_PVAR_187 : nat => @lem6197182 _78957 GEN_PVAR_187 k)). Qed.
Lemma lem6197184 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6197185 (_78957 : type1605) (k : nat) : (term403 _78957 k) = (term396 _78957 k).
Proof. exact (MK_COMB (@lem6197184) (@lem6197183 _78957 k)). Qed.
Lemma lem6197186 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6197187 (_78957 : type1605) (k : nat) : (term412 _78957 k) = (term413 _78957 k).
Proof. exact (MK_COMB (@lem6197186) (@lem6197185 _78957 k)). Qed.
Lemma lem6197188 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) : (term407 _78957 k GEN_PVAR_187) = (term390 _78957 GEN_PVAR_187 k).
Proof. exact (eq_refl (term407 _78957 k GEN_PVAR_187)). Qed.
Lemma lem6197189 (_78957 : type1605) (k : nat) : (term414 _78957 k) = (term405 _78957 k).
Proof. exact (fun_ext (fun GEN_PVAR_187 : nat => @lem6197188 _78957 GEN_PVAR_187 k)). Qed.
Lemma lem6197190 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6197191 (_78957 : type1605) (k : nat) : (term415 _78957 k) = (term416 _78957 k).
Proof. exact (MK_COMB (@lem6197190) (@lem6197189 _78957 k)). Qed.
Lemma lem6197192 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6197193 (_78957 : type1605) (k : nat) : (term417 _78957 k) = (term418 _78957 k).
Proof. exact (MK_COMB (@lem6197192) (@lem6197191 _78957 k)). Qed.
Lemma lem6197194 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) : (term409 _78957 k GEN_PVAR_187) = (term387 _78957 GEN_PVAR_187 k).
Proof. exact (eq_refl (term409 _78957 k GEN_PVAR_187)). Qed.
Lemma lem6197195 (_78957 : type1605) (k : nat) : (term419 _78957 k) = (term406 _78957 k).
Proof. exact (fun_ext (fun GEN_PVAR_187 : nat => @lem6197194 _78957 GEN_PVAR_187 k)). Qed.
Lemma lem6197196 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6197197 (_78957 : type1605) (k : nat) : (term420 _78957 k) = (term421 _78957 k).
Proof. exact (MK_COMB (@lem6197196) (@lem6197195 _78957 k)). Qed.
Lemma lem6197198 (_78957 : type1605) (k : nat) : (term404 _78957 k) = (term422 _78957 k).
Proof. exact (MK_COMB (@lem6197193 _78957 k) (@lem6197197 _78957 k)). Qed.
Lemma lem6197199 (_78957 : type1605) (k : nat) : ((term403 _78957 k) = (term404 _78957 k)) = ((term396 _78957 k) = (term422 _78957 k)).
Proof. exact (MK_COMB (@lem6197187 _78957 k) (@lem6197198 _78957 k)). Qed.
Lemma lem6197200 (_78957 : type1605) (k : nat) : (term396 _78957 k) = (term422 _78957 k).
Proof. exact (EQ_MP (@lem6197199 _78957 k) (@lem6197177 _78957 k)). Qed.
Lemma lem6197305 (_78957 : type1605) : (term397 _78957) = (term423 _78957).
Proof. exact (fun_ext (fun k : nat => @lem6197200 _78957 k)). Qed.
Lemma lem6197306 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6197307 (_78957 : type1605) : (term398 _78957) = (term424 _78957).
Proof. exact (MK_COMB (@lem6197306) (@lem6197305 _78957)). Qed.
Lemma lem6197309 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term399 A P Q) = (term400 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6197310 (P : nat -> Prop) (Q : nat -> Prop) : (term401 P Q) = (term402 P Q).
Proof. exact (@lem6197309 nat P Q). Qed.
Lemma lem6197311 (_78957 : type1605) : (term425 _78957) = (term426 _78957).
Proof. exact (@lem6197310 (term427 _78957) (term428 _78957)). Qed.
Lemma lem6197312 (_78957 : type1605) (k : nat) : (term429 _78957 k) = (term416 _78957 k).
Proof. exact (eq_refl (term429 _78957 k)). Qed.
Lemma lem6197313 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6197314 (_78957 : type1605) (k : nat) : (term430 _78957 k) = (term418 _78957 k).
Proof. exact (MK_COMB (@lem6197313) (@lem6197312 _78957 k)). Qed.
Lemma lem6197315 (_78957 : type1605) (k : nat) : (term431 _78957 k) = (term421 _78957 k).
Proof. exact (eq_refl (term431 _78957 k)). Qed.
Lemma lem6197316 (_78957 : type1605) (k : nat) : (term432 _78957 k) = (term422 _78957 k).
Proof. exact (MK_COMB (@lem6197314 _78957 k) (@lem6197315 _78957 k)). Qed.
Lemma lem6197317 (_78957 : type1605) : (term433 _78957) = (term423 _78957).
Proof. exact (fun_ext (fun k : nat => @lem6197316 _78957 k)). Qed.
Lemma lem6197318 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6197319 (_78957 : type1605) : (term425 _78957) = (term424 _78957).
Proof. exact (MK_COMB (@lem6197318) (@lem6197317 _78957)). Qed.
Lemma lem6197320 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6197321 (_78957 : type1605) : (term434 _78957) = (term435 _78957).
Proof. exact (MK_COMB (@lem6197320) (@lem6197319 _78957)). Qed.
Lemma lem6197322 (_78957 : type1605) (k : nat) : (term429 _78957 k) = (term416 _78957 k).
Proof. exact (eq_refl (term429 _78957 k)). Qed.
Lemma lem6197323 (_78957 : type1605) : (term436 _78957) = (term427 _78957).
Proof. exact (fun_ext (fun k : nat => @lem6197322 _78957 k)). Qed.
Lemma lem6197324 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6197325 (_78957 : type1605) : (term437 _78957) = (term438 _78957).
Proof. exact (MK_COMB (@lem6197324) (@lem6197323 _78957)). Qed.
Lemma lem6197326 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6197327 (_78957 : type1605) : (term439 _78957) = (term440 _78957).
Proof. exact (MK_COMB (@lem6197326) (@lem6197325 _78957)). Qed.
Lemma lem6197328 (_78957 : type1605) (k : nat) : (term431 _78957 k) = (term421 _78957 k).
Proof. exact (eq_refl (term431 _78957 k)). Qed.
Lemma lem6197329 (_78957 : type1605) : (term441 _78957) = (term428 _78957).
Proof. exact (fun_ext (fun k : nat => @lem6197328 _78957 k)). Qed.
Lemma lem6197330 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6197331 (_78957 : type1605) : (term442 _78957) = (term443 _78957).
Proof. exact (MK_COMB (@lem6197330) (@lem6197329 _78957)). Qed.
Lemma lem6197332 (_78957 : type1605) : (term426 _78957) = (term444 _78957).
Proof. exact (MK_COMB (@lem6197327 _78957) (@lem6197331 _78957)). Qed.
Lemma lem6197333 (_78957 : type1605) : ((term425 _78957) = (term426 _78957)) = ((term424 _78957) = (term444 _78957)).
Proof. exact (MK_COMB (@lem6197321 _78957) (@lem6197332 _78957)). Qed.
Lemma lem6197334 (_78957 : type1605) : (term424 _78957) = (term444 _78957).
Proof. exact (EQ_MP (@lem6197333 _78957) (@lem6197311 _78957)). Qed.
Lemma lem6197447 (_78957 : type1605) : (term398 _78957) = (term444 _78957).
Proof. exact (TRANS (@lem6197307 _78957) (@lem6197334 _78957)). Qed.
Lemma lem6197449 {A : Type'} (P : Prop) (Q : A -> Prop) : (term445 A P Q) = (term446 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6197450 (P : Prop) (Q : nat -> Prop) : (term447 P Q) = (term448 P Q).
Proof. exact (@lem6197449 nat P Q). Qed.
Lemma lem6197451 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) : (term449 _78957 GEN_PVAR_187 k) = (term450 _78957 GEN_PVAR_187 k).
Proof. exact (@lem6197450 (term451 _78957 k GEN_PVAR_187) (term252 GEN_PVAR_187 k)). Qed.
Lemma lem6197452 (GEN_PVAR_187 : nat) (k : nat) (i : nat) : (term380 GEN_PVAR_187 k i) = (term250 GEN_PVAR_187 k i).
Proof. exact (eq_refl (term380 GEN_PVAR_187 k i)). Qed.
Lemma lem6197453 (GEN_PVAR_187 : nat) (k : nat) : (term452 GEN_PVAR_187 k) = (term252 GEN_PVAR_187 k).
Proof. exact (fun_ext (fun i : nat => @lem6197452 GEN_PVAR_187 k i)). Qed.
Lemma lem6197454 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6197455 (GEN_PVAR_187 : nat) (k : nat) : (term453 GEN_PVAR_187 k) = (term254 GEN_PVAR_187 k).
Proof. exact (MK_COMB (@lem6197454) (@lem6197453 GEN_PVAR_187 k)). Qed.
Lemma lem6197456 (_78957 : type1605) (k : nat) (GEN_PVAR_187 : nat) : (term386 _78957 k GEN_PVAR_187) = (term386 _78957 k GEN_PVAR_187).
Proof. exact (eq_refl (term386 _78957 k GEN_PVAR_187)). Qed.
Lemma lem6197457 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) : (term449 _78957 GEN_PVAR_187 k) = (term387 _78957 GEN_PVAR_187 k).
Proof. exact (MK_COMB (@lem6197456 _78957 k GEN_PVAR_187) (@lem6197455 GEN_PVAR_187 k)). Qed.
Lemma lem6197458 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6197459 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) : (term454 _78957 GEN_PVAR_187 k) = (term455 _78957 GEN_PVAR_187 k).
Proof. exact (MK_COMB (@lem6197458) (@lem6197457 _78957 GEN_PVAR_187 k)). Qed.
Lemma lem6197460 (GEN_PVAR_187 : nat) (k : nat) (i : nat) : (term380 GEN_PVAR_187 k i) = (term250 GEN_PVAR_187 k i).
Proof. exact (eq_refl (term380 GEN_PVAR_187 k i)). Qed.
Lemma lem6197461 (_78957 : type1605) (k : nat) (GEN_PVAR_187 : nat) : (term386 _78957 k GEN_PVAR_187) = (term386 _78957 k GEN_PVAR_187).
Proof. exact (eq_refl (term386 _78957 k GEN_PVAR_187)). Qed.
Lemma lem6197462 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) (i : nat) : (term456 _78957 GEN_PVAR_187 k i) = (term457 _78957 GEN_PVAR_187 k i).
Proof. exact (MK_COMB (@lem6197461 _78957 k GEN_PVAR_187) (@lem6197460 GEN_PVAR_187 k i)). Qed.
Lemma lem6197463 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) : (term458 _78957 GEN_PVAR_187 k) = (term459 _78957 GEN_PVAR_187 k).
Proof. exact (fun_ext (fun i : nat => @lem6197462 _78957 GEN_PVAR_187 k i)). Qed.
Lemma lem6197464 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6197465 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) : (term450 _78957 GEN_PVAR_187 k) = (term460 _78957 GEN_PVAR_187 k).
Proof. exact (MK_COMB (@lem6197464) (@lem6197463 _78957 GEN_PVAR_187 k)). Qed.
Lemma lem6197466 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) : ((term449 _78957 GEN_PVAR_187 k) = (term450 _78957 GEN_PVAR_187 k)) = ((term387 _78957 GEN_PVAR_187 k) = (term460 _78957 GEN_PVAR_187 k)).
Proof. exact (MK_COMB (@lem6197459 _78957 GEN_PVAR_187 k) (@lem6197465 _78957 GEN_PVAR_187 k)). Qed.
Lemma lem6197467 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) : (term387 _78957 GEN_PVAR_187 k) = (term460 _78957 GEN_PVAR_187 k).
Proof. exact (EQ_MP (@lem6197466 _78957 GEN_PVAR_187 k) (@lem6197451 _78957 GEN_PVAR_187 k)). Qed.
Lemma lem6197468 (_78957 : type1605) (k : nat) : (term406 _78957 k) = (term461 _78957 k).
Proof. exact (fun_ext (fun GEN_PVAR_187 : nat => @lem6197467 _78957 GEN_PVAR_187 k)). Qed.
Lemma lem6197469 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6197470 (_78957 : type1605) (k : nat) : (term421 _78957 k) = (term462 _78957 k).
Proof. exact (MK_COMB (@lem6197469) (@lem6197468 _78957 k)). Qed.
Lemma lem6197472 {A B : Type'} (P : type1413 A B) : (term463 A B P) = (term464 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6197473 (P : type1605) : (term465 P) = (term466 P).
Proof. exact (@lem6197472 nat nat P). Qed.
Lemma lem6197474 (_78957 : type1605) (k : nat) : (term467 _78957 k) = (term468 _78957 k).
Proof. exact (@lem6197473 (term469 _78957 k)). Qed.
Lemma lem6197475 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) : (term470 _78957 k GEN_PVAR_187) = (term459 _78957 GEN_PVAR_187 k).
Proof. exact (eq_refl (term470 _78957 k GEN_PVAR_187)). Qed.
Lemma lem6197476 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6197477 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) (i : nat) : (term471 _78957 k GEN_PVAR_187 i) = (term472 _78957 GEN_PVAR_187 k i).
Proof. exact (MK_COMB (@lem6197475 _78957 GEN_PVAR_187 k) (@lem6197476 i)). Qed.
Lemma lem6197478 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) (i : nat) : (term472 _78957 GEN_PVAR_187 k i) = (term457 _78957 GEN_PVAR_187 k i).
Proof. exact (eq_refl (term472 _78957 GEN_PVAR_187 k i)). Qed.
Lemma lem6197479 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) (i : nat) : (term471 _78957 k GEN_PVAR_187 i) = (term457 _78957 GEN_PVAR_187 k i).
Proof. exact (TRANS (@lem6197477 _78957 GEN_PVAR_187 k i) (@lem6197478 _78957 GEN_PVAR_187 k i)). Qed.
Lemma lem6197480 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) : (term473 _78957 k GEN_PVAR_187) = (term459 _78957 GEN_PVAR_187 k).
Proof. exact (fun_ext (fun i : nat => @lem6197479 _78957 GEN_PVAR_187 k i)). Qed.
Lemma lem6197481 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6197482 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) : (term474 _78957 k GEN_PVAR_187) = (term460 _78957 GEN_PVAR_187 k).
Proof. exact (MK_COMB (@lem6197481) (@lem6197480 _78957 GEN_PVAR_187 k)). Qed.
Lemma lem6197483 (_78957 : type1605) (k : nat) : (term475 _78957 k) = (term461 _78957 k).
Proof. exact (fun_ext (fun GEN_PVAR_187 : nat => @lem6197482 _78957 GEN_PVAR_187 k)). Qed.
Lemma lem6197484 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6197485 (_78957 : type1605) (k : nat) : (term467 _78957 k) = (term462 _78957 k).
Proof. exact (MK_COMB (@lem6197484) (@lem6197483 _78957 k)). Qed.
Lemma lem6197486 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6197487 (_78957 : type1605) (k : nat) : (term476 _78957 k) = (term477 _78957 k).
Proof. exact (MK_COMB (@lem6197486) (@lem6197485 _78957 k)). Qed.
Lemma lem6197488 (_78957 : type1605) (GEN_PVAR_187 : nat) (k : nat) : (term470 _78957 k GEN_PVAR_187) = (term459 _78957 GEN_PVAR_187 k).
Proof. exact (eq_refl (term470 _78957 k GEN_PVAR_187)). Qed.
Lemma lem6197489 (i : nat -> nat) (GEN_PVAR_187 : nat) : (i GEN_PVAR_187) = (i GEN_PVAR_187).
Proof. exact (eq_refl (i GEN_PVAR_187)). Qed.
Lemma lem6197490 (_78957 : type1605) (k : nat) (i : nat -> nat) (GEN_PVAR_187 : nat) : (term478 _78957 k i GEN_PVAR_187) = (term479 _78957 k i GEN_PVAR_187).
Proof. exact (MK_COMB (@lem6197488 _78957 GEN_PVAR_187 k) (@lem6197489 i GEN_PVAR_187)). Qed.
Lemma lem6197491 (_78957 : type1605) (k : nat) (i : nat -> nat) (GEN_PVAR_187 : nat) : (term479 _78957 k i GEN_PVAR_187) = (term480 _78957 k i GEN_PVAR_187).
Proof. exact (eq_refl (term479 _78957 k i GEN_PVAR_187)). Qed.
Lemma lem6197492 (_78957 : type1605) (k : nat) (i : nat -> nat) (GEN_PVAR_187 : nat) : (term478 _78957 k i GEN_PVAR_187) = (term480 _78957 k i GEN_PVAR_187).
Proof. exact (TRANS (@lem6197490 _78957 k i GEN_PVAR_187) (@lem6197491 _78957 k i GEN_PVAR_187)). Qed.
Lemma lem6197493 (_78957 : type1605) (k : nat) (i : nat -> nat) : (term481 _78957 k i) = (term482 _78957 k i).
Proof. exact (fun_ext (fun GEN_PVAR_187 : nat => @lem6197492 _78957 k i GEN_PVAR_187)). Qed.
Lemma lem6197494 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6197495 (_78957 : type1605) (k : nat) (i : nat -> nat) : (term483 _78957 k i) = (term484 _78957 k i).
Proof. exact (MK_COMB (@lem6197494) (@lem6197493 _78957 k i)). Qed.
Lemma lem6197496 (_78957 : type1605) (k : nat) : (term485 _78957 k) = (term486 _78957 k).
Proof. exact (fun_ext (fun i : nat -> nat => @lem6197495 _78957 k i)). Qed.
Lemma lem6197497 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem6197498 (_78957 : type1605) (k : nat) : (term468 _78957 k) = (term487 _78957 k).
Proof. exact (MK_COMB (@lem6197497) (@lem6197496 _78957 k)). Qed.
Lemma lem6197499 (_78957 : type1605) (k : nat) : ((term467 _78957 k) = (term468 _78957 k)) = ((term462 _78957 k) = (term487 _78957 k)).
Proof. exact (MK_COMB (@lem6197487 _78957 k) (@lem6197498 _78957 k)). Qed.
Lemma lem6197500 (_78957 : type1605) (k : nat) : (term462 _78957 k) = (term487 _78957 k).
Proof. exact (EQ_MP (@lem6197499 _78957 k) (@lem6197474 _78957 k)). Qed.
Lemma lem6197501 (_78957 : type1605) (k : nat) : (term421 _78957 k) = (term487 _78957 k).
Proof. exact (TRANS (@lem6197470 _78957 k) (@lem6197500 _78957 k)). Qed.
Lemma lem6197502 (_78957 : type1605) : (term428 _78957) = (term488 _78957).
Proof. exact (fun_ext (fun k : nat => @lem6197501 _78957 k)). Qed.
Lemma lem6197503 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6197504 (_78957 : type1605) : (term443 _78957) = (term489 _78957).
Proof. exact (MK_COMB (@lem6197503) (@lem6197502 _78957)). Qed.
Lemma lem6197506 {A B : Type'} (P : type1413 A B) : (term463 A B P) = (term464 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6197507 (P : type1586) : (term490 P) = (term491 P).
Proof. exact (@lem6197506 nat (nat -> nat) P). Qed.
Lemma lem6197508 (_78957 : type1605) : (term492 _78957) = (term493 _78957).
Proof. exact (@lem6197507 (term494 _78957)). Qed.
Lemma lem6197509 (_78957 : type1605) (k : nat) : (term495 _78957 k) = (term486 _78957 k).
Proof. exact (eq_refl (term495 _78957 k)). Qed.
Lemma lem6197510 (i : nat -> nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6197511 (_78957 : type1605) (k : nat) (i : nat -> nat) : (term496 _78957 k i) = (term497 _78957 k i).
Proof. exact (MK_COMB (@lem6197509 _78957 k) (@lem6197510 i)). Qed.
Lemma lem6197512 (_78957 : type1605) (k : nat) (i : nat -> nat) : (term497 _78957 k i) = (term484 _78957 k i).
Proof. exact (eq_refl (term497 _78957 k i)). Qed.
Lemma lem6197513 (_78957 : type1605) (k : nat) (i : nat -> nat) : (term496 _78957 k i) = (term484 _78957 k i).
Proof. exact (TRANS (@lem6197511 _78957 k i) (@lem6197512 _78957 k i)). Qed.
Lemma lem6197514 (_78957 : type1605) (k : nat) : (term498 _78957 k) = (term486 _78957 k).
Proof. exact (fun_ext (fun i : nat -> nat => @lem6197513 _78957 k i)). Qed.
Lemma lem6197515 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem6197516 (_78957 : type1605) (k : nat) : (term499 _78957 k) = (term487 _78957 k).
Proof. exact (MK_COMB (@lem6197515) (@lem6197514 _78957 k)). Qed.
Lemma lem6197517 (_78957 : type1605) : (term500 _78957) = (term488 _78957).
Proof. exact (fun_ext (fun k : nat => @lem6197516 _78957 k)). Qed.
Lemma lem6197518 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6197519 (_78957 : type1605) : (term492 _78957) = (term489 _78957).
Proof. exact (MK_COMB (@lem6197518) (@lem6197517 _78957)). Qed.
Lemma lem6197520 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6197521 (_78957 : type1605) : (term501 _78957) = (term502 _78957).
Proof. exact (MK_COMB (@lem6197520) (@lem6197519 _78957)). Qed.
Lemma lem6197522 (_78957 : type1605) (k : nat) : (term495 _78957 k) = (term486 _78957 k).
Proof. exact (eq_refl (term495 _78957 k)). Qed.
Lemma lem6197523 (i : type1606) (k : nat) : (i k) = (i k).
Proof. exact (eq_refl (i k)). Qed.
Lemma lem6197524 (_78957 : type1605) (i : type1606) (k : nat) : (term503 _78957 i k) = (term504 _78957 i k).
Proof. exact (MK_COMB (@lem6197522 _78957 k) (@lem6197523 i k)). Qed.
Lemma lem6197525 (_78957 : type1605) (i : type1606) (k : nat) : (term504 _78957 i k) = (term505 _78957 i k).
Proof. exact (eq_refl (term504 _78957 i k)). Qed.
Lemma lem6197526 (_78957 : type1605) (i : type1606) (k : nat) : (term503 _78957 i k) = (term505 _78957 i k).
Proof. exact (TRANS (@lem6197524 _78957 i k) (@lem6197525 _78957 i k)). Qed.
Lemma lem6197527 (_78957 : type1605) (i : type1606) : (term506 _78957 i) = (term507 _78957 i).
Proof. exact (fun_ext (fun k : nat => @lem6197526 _78957 i k)). Qed.
Lemma lem6197528 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6197529 (_78957 : type1605) (i : type1606) : (term508 _78957 i) = (term509 _78957 i).
Proof. exact (MK_COMB (@lem6197528) (@lem6197527 _78957 i)). Qed.
Lemma lem6197530 (_78957 : type1605) : (term510 _78957) = (term511 _78957).
Proof. exact (fun_ext (fun i : type1606 => @lem6197529 _78957 i)). Qed.
Lemma lem6197531 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem6197532 (_78957 : type1605) : (term493 _78957) = (term512 _78957).
Proof. exact (MK_COMB (@lem6197531) (@lem6197530 _78957)). Qed.
Lemma lem6197533 (_78957 : type1605) : ((term492 _78957) = (term493 _78957)) = ((term489 _78957) = (term512 _78957)).
Proof. exact (MK_COMB (@lem6197521 _78957) (@lem6197532 _78957)). Qed.
Lemma lem6197534 (_78957 : type1605) : (term489 _78957) = (term512 _78957).
Proof. exact (EQ_MP (@lem6197533 _78957) (@lem6197508 _78957)). Qed.
Lemma lem6197535 (_78957 : type1605) : (term443 _78957) = (term512 _78957).
Proof. exact (TRANS (@lem6197504 _78957) (@lem6197534 _78957)). Qed.
Lemma lem6197536 (_78957 : type1605) : (term440 _78957) = (term440 _78957).
Proof. exact (eq_refl (term440 _78957)). Qed.
Lemma lem6197537 (_78957 : type1605) : (term444 _78957) = (term513 _78957).
Proof. exact (MK_COMB (@lem6197536 _78957) (@lem6197535 _78957)). Qed.
Lemma lem6197539 {A : Type'} (P : Prop) (Q : A -> Prop) : (term514 A P Q) = (term515 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem6197540 (P : Prop) (Q : type961) : (term516 P Q) = (term517 P Q).
Proof. exact (@lem6197539 type1606 P Q). Qed.
Lemma lem6197541 (_78957 : type1605) : (term518 _78957) = (term519 _78957).
Proof. exact (@lem6197540 (term438 _78957) (term511 _78957)). Qed.
Lemma lem6197542 (_78957 : type1605) (i : type1606) : (term520 _78957 i) = (term509 _78957 i).
Proof. exact (eq_refl (term520 _78957 i)). Qed.
Lemma lem6197543 (_78957 : type1605) : (term521 _78957) = (term511 _78957).
Proof. exact (fun_ext (fun i : type1606 => @lem6197542 _78957 i)). Qed.
Lemma lem6197544 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem6197545 (_78957 : type1605) : (term522 _78957) = (term512 _78957).
Proof. exact (MK_COMB (@lem6197544) (@lem6197543 _78957)). Qed.
Lemma lem6197546 (_78957 : type1605) : (term440 _78957) = (term440 _78957).
Proof. exact (eq_refl (term440 _78957)). Qed.
Lemma lem6197547 (_78957 : type1605) : (term518 _78957) = (term513 _78957).
Proof. exact (MK_COMB (@lem6197546 _78957) (@lem6197545 _78957)). Qed.
Lemma lem6197548 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6197549 (_78957 : type1605) : (term523 _78957) = (term524 _78957).
Proof. exact (MK_COMB (@lem6197548) (@lem6197547 _78957)). Qed.
Lemma lem6197550 (_78957 : type1605) (i : type1606) : (term520 _78957 i) = (term509 _78957 i).
Proof. exact (eq_refl (term520 _78957 i)). Qed.
Lemma lem6197551 (_78957 : type1605) : (term440 _78957) = (term440 _78957).
Proof. exact (eq_refl (term440 _78957)). Qed.
Lemma lem6197552 (_78957 : type1605) (i : type1606) : (term525 _78957 i) = (term526 _78957 i).
Proof. exact (MK_COMB (@lem6197551 _78957) (@lem6197550 _78957 i)). Qed.
Lemma lem6197553 (_78957 : type1605) : (term527 _78957) = (term528 _78957).
Proof. exact (fun_ext (fun i : type1606 => @lem6197552 _78957 i)). Qed.
Lemma lem6197554 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem6197555 (_78957 : type1605) : (term519 _78957) = (term529 _78957).
Proof. exact (MK_COMB (@lem6197554) (@lem6197553 _78957)). Qed.
Lemma lem6197556 (_78957 : type1605) : ((term518 _78957) = (term519 _78957)) = ((term513 _78957) = (term529 _78957)).
Proof. exact (MK_COMB (@lem6197549 _78957) (@lem6197555 _78957)). Qed.
Lemma lem6197557 (_78957 : type1605) : (term513 _78957) = (term529 _78957).
Proof. exact (EQ_MP (@lem6197556 _78957) (@lem6197541 _78957)). Qed.
Lemma lem6197558 (_78957 : type1605) : (term444 _78957) = (term529 _78957).
Proof. exact (TRANS (@lem6197537 _78957) (@lem6197557 _78957)). Qed.
Lemma lem6197559 (_78957 : type1605) : (term398 _78957) = (term529 _78957).
Proof. exact (TRANS (@lem6197447 _78957) (@lem6197558 _78957)). Qed.
Lemma lem6197560 (_78957 : type1605) : (term369 _78957) = (term529 _78957).
Proof. exact (TRANS (@lem6197169 _78957) (@lem6197559 _78957)). Qed.
Lemma lem6197561 (_78957 : type1605) (h1 : term369 _78957) : term529 _78957.
Proof. exact (EQ_MP (@lem6197560 _78957) (@lem6197129 _78957 h1)). Qed.
Lemma lem6197562 {_123593 : Type'} (op : type1400 _123593) (y : _123593) (x : _123593) : ((op x y) = (op y x)) = ((op x y) = (op y x)).
Proof. exact (eq_refl ((op x y) = (op y x))). Qed.
Lemma lem6197563 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : (term314 _123593 op x) = (term314 _123593 op x).
Proof. exact (fun_ext (fun y : _123593 => @lem6197562 _123593 op y x)). Qed.
Lemma lem6197564 {_123593 : Type'} : (@all _123593) = (@all _123593).
Proof. exact (eq_refl (@all _123593)). Qed.
Lemma lem6197565 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : (term315 _123593 op x) = (term315 _123593 op x).
Proof. exact (MK_COMB (@lem6197564 _123593) (@lem6197563 _123593 op x)). Qed.
Lemma lem6197566 {_123593 : Type'} (op : type1400 _123593) : (term316 _123593 op) = (term316 _123593 op).
Proof. exact (fun_ext (fun x : _123593 => @lem6197565 _123593 op x)). Qed.
Lemma lem6197567 {_123593 : Type'} : (@all _123593) = (@all _123593).
Proof. exact (eq_refl (@all _123593)). Qed.
Lemma lem6197568 {_123593 : Type'} (op : type1400 _123593) : (term317 _123593 op) = (term317 _123593 op).
Proof. exact (MK_COMB (@lem6197567 _123593) (@lem6197566 _123593 op)). Qed.
Lemma lem6197569 {_123593 : Type'} (op : type1400 _123593) (x : _123593) (y : _123593) (z : _123593) : ((term304 _123593 x op y z) = (term305 _123593 op x y z)) = ((term304 _123593 x op y z) = (term305 _123593 op x y z)).
Proof. exact (eq_refl ((term304 _123593 x op y z) = (term305 _123593 op x y z))). Qed.
Lemma lem6197570 {_123593 : Type'} (op : type1400 _123593) (x : _123593) (y : _123593) : (term306 _123593 op x y) = (term306 _123593 op x y).
Proof. exact (fun_ext (fun z : _123593 => @lem6197569 _123593 op x y z)). Qed.
Lemma lem6197571 {_123593 : Type'} : (@all _123593) = (@all _123593).
Proof. exact (eq_refl (@all _123593)). Qed.
Lemma lem6197572 {_123593 : Type'} (op : type1400 _123593) (x : _123593) (y : _123593) : (term307 _123593 op x y) = (term307 _123593 op x y).
Proof. exact (MK_COMB (@lem6197571 _123593) (@lem6197570 _123593 op x y)). Qed.
Lemma lem6197573 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : (term308 _123593 op x) = (term308 _123593 op x).
Proof. exact (fun_ext (fun y : _123593 => @lem6197572 _123593 op x y)). Qed.
Lemma lem6197574 {_123593 : Type'} : (@all _123593) = (@all _123593).
Proof. exact (eq_refl (@all _123593)). Qed.
Lemma lem6197575 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : (term309 _123593 op x) = (term309 _123593 op x).
Proof. exact (MK_COMB (@lem6197574 _123593) (@lem6197573 _123593 op x)). Qed.
Lemma lem6197576 {_123593 : Type'} (op : type1400 _123593) : (term310 _123593 op) = (term310 _123593 op).
Proof. exact (fun_ext (fun x : _123593 => @lem6197575 _123593 op x)). Qed.
Lemma lem6197577 {_123593 : Type'} : (@all _123593) = (@all _123593).
Proof. exact (eq_refl (@all _123593)). Qed.
Lemma lem6197578 {_123593 : Type'} (op : type1400 _123593) : (term311 _123593 op) = (term311 _123593 op).
Proof. exact (MK_COMB (@lem6197577 _123593) (@lem6197576 _123593 op)). Qed.
Lemma lem6197579 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : ((term301 _123593 op x) = x) = ((term301 _123593 op x) = x).
Proof. exact (eq_refl ((term301 _123593 op x) = x)). Qed.
Lemma lem6197580 {_123593 : Type'} (op : type1400 _123593) : (term302 _123593 op) = (term302 _123593 op).
Proof. exact (fun_ext (fun x : _123593 => @lem6197579 _123593 op x)). Qed.
Lemma lem6197581 {_123593 : Type'} : (@all _123593) = (@all _123593).
Proof. exact (eq_refl (@all _123593)). Qed.
Lemma lem6197582 {_123593 : Type'} (op : type1400 _123593) : (term303 _123593 op) = (term303 _123593 op).
Proof. exact (MK_COMB (@lem6197581 _123593) (@lem6197580 _123593 op)). Qed.
Lemma lem6197583 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6197584 {_123593 : Type'} (op : type1400 _123593) : (term312 _123593 op) = (term312 _123593 op).
Proof. exact (MK_COMB (@lem6197583) (@lem6197578 _123593 op)). Qed.
Lemma lem6197585 {_123593 : Type'} (op : type1400 _123593) : (term313 _123593 op) = (term313 _123593 op).
Proof. exact (MK_COMB (@lem6197584 _123593 op) (@lem6197582 _123593 op)). Qed.
Lemma lem6197586 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6197587 {_123593 : Type'} (op : type1400 _123593) : (term318 _123593 op) = (term318 _123593 op).
Proof. exact (MK_COMB (@lem6197586) (@lem6197568 _123593 op)). Qed.
Lemma lem6197616 {_123593 : Type'} (op : type1400 _123593) : (term159 _123593 op) = (term159 _123593 op).
Proof. exact (MK_COMB (@lem6197587 _123593 op) (@lem6197585 _123593 op)). Qed.
Lemma lem6197617 {_123593 : Type'} (op : type1400 _123593) (h1 : term159 _123593 op) : term159 _123593 op.
Proof. exact (EQ_MP (@lem6197616 _123593 op) (@lem6197130 _123593 op h1)). Qed.
Lemma lem6197623 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (f : nat -> _123593) (k : nat) (h1 : term375 _123593 op _78957 f k) : term375 _123593 op _78957 f k.
Proof. exact (h1). Qed.
Lemma lem6197625 {_123593 : Type'} : (@eq _123593) = (@eq _123593).
Proof. exact (eq_refl (@eq _123593)). Qed.
Lemma lem6197634 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6197635 {_123593 : Type'} (f : type1400 _123593) (x : _123593) : (f x) = (@I (_123593 -> _123593 -> _123593) f x).
Proof. exact (@lem6197634 _123593 (_123593 -> _123593) f x). Qed.
Lemma lem6197636 {_123593 : Type'} (op : type1400 _123593) : (term530 _123593 op) = (term531 _123593 op).
Proof. exact (@lem6197635 _123593 op (@neutral _123593 op)). Qed.
Lemma lem6197637 {_123593 : Type'} (x : _123593) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6197638 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : (term301 _123593 op x) = (term532 _123593 op x).
Proof. exact (MK_COMB (@lem6197636 _123593 op) (@lem6197637 _123593 x)). Qed.
Lemma lem6197640 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6197641 {_123593 : Type'} (f : _123593 -> _123593) (x : _123593) : (f x) = (@I (_123593 -> _123593) f x).
Proof. exact (@lem6197640 _123593 _123593 f x). Qed.
Lemma lem6197642 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : (term532 _123593 op x) = (term533 _123593 op x).
Proof. exact (@lem6197641 _123593 (term531 _123593 op) x). Qed.
Lemma lem6197644 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : (term301 _123593 op x) = (term533 _123593 op x).
Proof. exact (TRANS (@lem6197638 _123593 op x) (@lem6197642 _123593 op x)). Qed.
Lemma lem6197645 {_123593 : Type'} (x : _123593) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6197646 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : (term534 _123593 op x) = (term535 _123593 op x).
Proof. exact (MK_COMB (@lem6197625 _123593) (@lem6197644 _123593 op x)). Qed.
Lemma lem6197647 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : ((term301 _123593 op x) = x) = ((term533 _123593 op x) = x).
Proof. exact (MK_COMB (@lem6197646 _123593 op x) (@lem6197645 _123593 x)). Qed.
Lemma lem6197648 {_123593 : Type'} (op : type1400 _123593) : (term302 _123593 op) = (term536 _123593 op).
Proof. exact (fun_ext (fun x : _123593 => @lem6197647 _123593 op x)). Qed.
Lemma lem6197649 {_123593 : Type'} : (@all _123593) = (@all _123593).
Proof. exact (eq_refl (@all _123593)). Qed.
Lemma lem6197650 {_123593 : Type'} (op : type1400 _123593) : (term303 _123593 op) = (term537 _123593 op).
Proof. exact (MK_COMB (@lem6197649 _123593) (@lem6197648 _123593 op)). Qed.
Lemma lem6197651 {_123593 : Type'} : (@eq _123593) = (@eq _123593).
Proof. exact (eq_refl (@eq _123593)). Qed.
Lemma lem6197660 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6197661 {_123593 : Type'} (f : type1400 _123593) (x : _123593) : (f x) = (@I (_123593 -> _123593 -> _123593) f x).
Proof. exact (@lem6197660 _123593 (_123593 -> _123593) f x). Qed.
Lemma lem6197662 {_123593 : Type'} (op : type1400 _123593) (y : _123593) : (op y) = (@I (_123593 -> _123593 -> _123593) op y).
Proof. exact (@lem6197661 _123593 op y). Qed.
Lemma lem6197663 {_123593 : Type'} (z : _123593) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem6197664 {_123593 : Type'} (op : type1400 _123593) (y : _123593) (z : _123593) : (op y z) = (@I (_123593 -> _123593 -> _123593) op y z).
Proof. exact (MK_COMB (@lem6197662 _123593 op y) (@lem6197663 _123593 z)). Qed.
Lemma lem6197666 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6197667 {_123593 : Type'} (f : _123593 -> _123593) (x : _123593) : (f x) = (@I (_123593 -> _123593) f x).
Proof. exact (@lem6197666 _123593 _123593 f x). Qed.
Lemma lem6197668 {_123593 : Type'} (op : type1400 _123593) (y : _123593) (z : _123593) : (@I (_123593 -> _123593 -> _123593) op y z) = (term538 _123593 op y z).
Proof. exact (@lem6197667 _123593 (@I (_123593 -> _123593 -> _123593) op y) z). Qed.
Lemma lem6197670 {_123593 : Type'} (op : type1400 _123593) (y : _123593) (z : _123593) : (op y z) = (term538 _123593 op y z).
Proof. exact (TRANS (@lem6197664 _123593 op y z) (@lem6197668 _123593 op y z)). Qed.
Lemma lem6197671 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : (op x) = (op x).
Proof. exact (eq_refl (op x)). Qed.
Lemma lem6197672 {_123593 : Type'} (x : _123593) (op : type1400 _123593) (y : _123593) (z : _123593) : (term304 _123593 x op y z) = (term539 _123593 x op y z).
Proof. exact (MK_COMB (@lem6197671 _123593 op x) (@lem6197670 _123593 op y z)). Qed.
Lemma lem6197674 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6197675 {_123593 : Type'} (f : type1400 _123593) (x : _123593) : (f x) = (@I (_123593 -> _123593 -> _123593) f x).
Proof. exact (@lem6197674 _123593 (_123593 -> _123593) f x). Qed.
Lemma lem6197676 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : (op x) = (@I (_123593 -> _123593 -> _123593) op x).
Proof. exact (@lem6197675 _123593 op x). Qed.
Lemma lem6197677 {_123593 : Type'} (op : type1400 _123593) (y : _123593) (z : _123593) : (term538 _123593 op y z) = (term538 _123593 op y z).
Proof. exact (eq_refl (term538 _123593 op y z)). Qed.
Lemma lem6197678 {_123593 : Type'} (x : _123593) (op : type1400 _123593) (y : _123593) (z : _123593) : (term539 _123593 x op y z) = (term540 _123593 x op y z).
Proof. exact (MK_COMB (@lem6197676 _123593 op x) (@lem6197677 _123593 op y z)). Qed.
Lemma lem6197680 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6197681 {_123593 : Type'} (f : _123593 -> _123593) (x : _123593) : (f x) = (@I (_123593 -> _123593) f x).
Proof. exact (@lem6197680 _123593 _123593 f x). Qed.
Lemma lem6197682 {_123593 : Type'} (x : _123593) (op : type1400 _123593) (y : _123593) (z : _123593) : (term540 _123593 x op y z) = (term541 _123593 x op y z).
Proof. exact (@lem6197681 _123593 (@I (_123593 -> _123593 -> _123593) op x) (term538 _123593 op y z)). Qed.
Lemma lem6197683 {_123593 : Type'} (x : _123593) (op : type1400 _123593) (y : _123593) (z : _123593) : (term539 _123593 x op y z) = (term541 _123593 x op y z).
Proof. exact (TRANS (@lem6197678 _123593 x op y z) (@lem6197682 _123593 x op y z)). Qed.
Lemma lem6197684 {_123593 : Type'} (x : _123593) (op : type1400 _123593) (y : _123593) (z : _123593) : (term304 _123593 x op y z) = (term541 _123593 x op y z).
Proof. exact (TRANS (@lem6197672 _123593 x op y z) (@lem6197683 _123593 x op y z)). Qed.
Lemma lem6197685 {_123593 : Type'} (op : type1400 _123593) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6197692 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6197693 {_123593 : Type'} (f : type1400 _123593) (x : _123593) : (f x) = (@I (_123593 -> _123593 -> _123593) f x).
Proof. exact (@lem6197692 _123593 (_123593 -> _123593) f x). Qed.
Lemma lem6197694 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : (op x) = (@I (_123593 -> _123593 -> _123593) op x).
Proof. exact (@lem6197693 _123593 op x). Qed.
Lemma lem6197695 {_123593 : Type'} (y : _123593) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6197696 {_123593 : Type'} (op : type1400 _123593) (x : _123593) (y : _123593) : (op x y) = (@I (_123593 -> _123593 -> _123593) op x y).
Proof. exact (MK_COMB (@lem6197694 _123593 op x) (@lem6197695 _123593 y)). Qed.
Lemma lem6197698 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6197699 {_123593 : Type'} (f : _123593 -> _123593) (x : _123593) : (f x) = (@I (_123593 -> _123593) f x).
Proof. exact (@lem6197698 _123593 _123593 f x). Qed.
Lemma lem6197700 {_123593 : Type'} (op : type1400 _123593) (x : _123593) (y : _123593) : (@I (_123593 -> _123593 -> _123593) op x y) = (term538 _123593 op x y).
Proof. exact (@lem6197699 _123593 (@I (_123593 -> _123593 -> _123593) op x) y). Qed.
Lemma lem6197702 {_123593 : Type'} (op : type1400 _123593) (x : _123593) (y : _123593) : (op x y) = (term538 _123593 op x y).
Proof. exact (TRANS (@lem6197696 _123593 op x y) (@lem6197700 _123593 op x y)). Qed.
Lemma lem6197703 {_123593 : Type'} (z : _123593) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem6197704 {_123593 : Type'} (op : type1400 _123593) (x : _123593) (y : _123593) : (term542 _123593 op x y) = (term543 _123593 op x y).
Proof. exact (MK_COMB (@lem6197685 _123593 op) (@lem6197702 _123593 op x y)). Qed.
Lemma lem6197705 {_123593 : Type'} (op : type1400 _123593) (x : _123593) (y : _123593) (z : _123593) : (term305 _123593 op x y z) = (term544 _123593 op x y z).
Proof. exact (MK_COMB (@lem6197704 _123593 op x y) (@lem6197703 _123593 z)). Qed.
Lemma lem6197707 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6197708 {_123593 : Type'} (f : type1400 _123593) (x : _123593) : (f x) = (@I (_123593 -> _123593 -> _123593) f x).
Proof. exact (@lem6197707 _123593 (_123593 -> _123593) f x). Qed.
Lemma lem6197709 {_123593 : Type'} (op : type1400 _123593) (x : _123593) (y : _123593) : (term543 _123593 op x y) = (term545 _123593 op x y).
Proof. exact (@lem6197708 _123593 op (term538 _123593 op x y)). Qed.
Lemma lem6197710 {_123593 : Type'} (z : _123593) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem6197711 {_123593 : Type'} (op : type1400 _123593) (x : _123593) (y : _123593) (z : _123593) : (term544 _123593 op x y z) = (term546 _123593 op x y z).
Proof. exact (MK_COMB (@lem6197709 _123593 op x y) (@lem6197710 _123593 z)). Qed.
Lemma lem6197713 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6197714 {_123593 : Type'} (f : _123593 -> _123593) (x : _123593) : (f x) = (@I (_123593 -> _123593) f x).
Proof. exact (@lem6197713 _123593 _123593 f x). Qed.
Lemma lem6197715 {_123593 : Type'} (op : type1400 _123593) (x : _123593) (y : _123593) (z : _123593) : (term546 _123593 op x y z) = (term547 _123593 op x y z).
Proof. exact (@lem6197714 _123593 (term545 _123593 op x y) z). Qed.
Lemma lem6197716 {_123593 : Type'} (op : type1400 _123593) (x : _123593) (y : _123593) (z : _123593) : (term544 _123593 op x y z) = (term547 _123593 op x y z).
Proof. exact (TRANS (@lem6197711 _123593 op x y z) (@lem6197715 _123593 op x y z)). Qed.
Lemma lem6197717 {_123593 : Type'} (op : type1400 _123593) (x : _123593) (y : _123593) (z : _123593) : (term305 _123593 op x y z) = (term547 _123593 op x y z).
Proof. exact (TRANS (@lem6197705 _123593 op x y z) (@lem6197716 _123593 op x y z)). Qed.
Lemma lem6197718 {_123593 : Type'} (x : _123593) (op : type1400 _123593) (y : _123593) (z : _123593) : (term548 _123593 x op y z) = (term549 _123593 x op y z).
Proof. exact (MK_COMB (@lem6197651 _123593) (@lem6197684 _123593 x op y z)). Qed.
Lemma lem6197719 {_123593 : Type'} (op : type1400 _123593) (x : _123593) (y : _123593) (z : _123593) : ((term304 _123593 x op y z) = (term305 _123593 op x y z)) = ((term541 _123593 x op y z) = (term547 _123593 op x y z)).
Proof. exact (MK_COMB (@lem6197718 _123593 x op y z) (@lem6197717 _123593 op x y z)). Qed.
Lemma lem6197720 {_123593 : Type'} (op : type1400 _123593) (x : _123593) (y : _123593) : (term306 _123593 op x y) = (term550 _123593 op x y).
Proof. exact (fun_ext (fun z : _123593 => @lem6197719 _123593 op x y z)). Qed.
Lemma lem6197721 {_123593 : Type'} : (@all _123593) = (@all _123593).
Proof. exact (eq_refl (@all _123593)). Qed.
Lemma lem6197722 {_123593 : Type'} (op : type1400 _123593) (x : _123593) (y : _123593) : (term307 _123593 op x y) = (term551 _123593 op x y).
Proof. exact (MK_COMB (@lem6197721 _123593) (@lem6197720 _123593 op x y)). Qed.
Lemma lem6197723 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : (term308 _123593 op x) = (term552 _123593 op x).
Proof. exact (fun_ext (fun y : _123593 => @lem6197722 _123593 op x y)). Qed.
Lemma lem6197724 {_123593 : Type'} : (@all _123593) = (@all _123593).
Proof. exact (eq_refl (@all _123593)). Qed.
Lemma lem6197725 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : (term309 _123593 op x) = (term553 _123593 op x).
Proof. exact (MK_COMB (@lem6197724 _123593) (@lem6197723 _123593 op x)). Qed.
Lemma lem6197726 {_123593 : Type'} (op : type1400 _123593) : (term310 _123593 op) = (term554 _123593 op).
Proof. exact (fun_ext (fun x : _123593 => @lem6197725 _123593 op x)). Qed.
Lemma lem6197727 {_123593 : Type'} : (@all _123593) = (@all _123593).
Proof. exact (eq_refl (@all _123593)). Qed.
Lemma lem6197728 {_123593 : Type'} (op : type1400 _123593) : (term311 _123593 op) = (term555 _123593 op).
Proof. exact (MK_COMB (@lem6197727 _123593) (@lem6197726 _123593 op)). Qed.
Lemma lem6197729 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6197730 {_123593 : Type'} (op : type1400 _123593) : (term312 _123593 op) = (term556 _123593 op).
Proof. exact (MK_COMB (@lem6197729) (@lem6197728 _123593 op)). Qed.
Lemma lem6197731 {_123593 : Type'} (op : type1400 _123593) : (term313 _123593 op) = (term557 _123593 op).
Proof. exact (MK_COMB (@lem6197730 _123593 op) (@lem6197650 _123593 op)). Qed.
Lemma lem6197732 {_123593 : Type'} : (@eq _123593) = (@eq _123593).
Proof. exact (eq_refl (@eq _123593)). Qed.
Lemma lem6197739 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6197740 {_123593 : Type'} (f : type1400 _123593) (x : _123593) : (f x) = (@I (_123593 -> _123593 -> _123593) f x).
Proof. exact (@lem6197739 _123593 (_123593 -> _123593) f x). Qed.
Lemma lem6197741 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : (op x) = (@I (_123593 -> _123593 -> _123593) op x).
Proof. exact (@lem6197740 _123593 op x). Qed.
Lemma lem6197742 {_123593 : Type'} (y : _123593) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6197743 {_123593 : Type'} (op : type1400 _123593) (x : _123593) (y : _123593) : (op x y) = (@I (_123593 -> _123593 -> _123593) op x y).
Proof. exact (MK_COMB (@lem6197741 _123593 op x) (@lem6197742 _123593 y)). Qed.
Lemma lem6197745 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6197746 {_123593 : Type'} (f : _123593 -> _123593) (x : _123593) : (f x) = (@I (_123593 -> _123593) f x).
Proof. exact (@lem6197745 _123593 _123593 f x). Qed.
Lemma lem6197747 {_123593 : Type'} (op : type1400 _123593) (x : _123593) (y : _123593) : (@I (_123593 -> _123593 -> _123593) op x y) = (term538 _123593 op x y).
Proof. exact (@lem6197746 _123593 (@I (_123593 -> _123593 -> _123593) op x) y). Qed.
Lemma lem6197749 {_123593 : Type'} (op : type1400 _123593) (x : _123593) (y : _123593) : (op x y) = (term538 _123593 op x y).
Proof. exact (TRANS (@lem6197743 _123593 op x y) (@lem6197747 _123593 op x y)). Qed.
Lemma lem6197756 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6197757 {_123593 : Type'} (f : type1400 _123593) (x : _123593) : (f x) = (@I (_123593 -> _123593 -> _123593) f x).
Proof. exact (@lem6197756 _123593 (_123593 -> _123593) f x). Qed.
Lemma lem6197758 {_123593 : Type'} (op : type1400 _123593) (y : _123593) : (op y) = (@I (_123593 -> _123593 -> _123593) op y).
Proof. exact (@lem6197757 _123593 op y). Qed.
Lemma lem6197759 {_123593 : Type'} (x : _123593) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6197760 {_123593 : Type'} (op : type1400 _123593) (y : _123593) (x : _123593) : (op y x) = (@I (_123593 -> _123593 -> _123593) op y x).
Proof. exact (MK_COMB (@lem6197758 _123593 op y) (@lem6197759 _123593 x)). Qed.
Lemma lem6197762 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6197763 {_123593 : Type'} (f : _123593 -> _123593) (x : _123593) : (f x) = (@I (_123593 -> _123593) f x).
Proof. exact (@lem6197762 _123593 _123593 f x). Qed.
Lemma lem6197764 {_123593 : Type'} (op : type1400 _123593) (y : _123593) (x : _123593) : (@I (_123593 -> _123593 -> _123593) op y x) = (term538 _123593 op y x).
Proof. exact (@lem6197763 _123593 (@I (_123593 -> _123593 -> _123593) op y) x). Qed.
Lemma lem6197766 {_123593 : Type'} (op : type1400 _123593) (y : _123593) (x : _123593) : (op y x) = (term538 _123593 op y x).
Proof. exact (TRANS (@lem6197760 _123593 op y x) (@lem6197764 _123593 op y x)). Qed.
Lemma lem6197767 {_123593 : Type'} (op : type1400 _123593) (x : _123593) (y : _123593) : (term558 _123593 op x y) = (term559 _123593 op x y).
Proof. exact (MK_COMB (@lem6197732 _123593) (@lem6197749 _123593 op x y)). Qed.
Lemma lem6197768 {_123593 : Type'} (op : type1400 _123593) (y : _123593) (x : _123593) : ((op x y) = (op y x)) = ((term538 _123593 op x y) = (term538 _123593 op y x)).
Proof. exact (MK_COMB (@lem6197767 _123593 op x y) (@lem6197766 _123593 op y x)). Qed.
Lemma lem6197769 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : (term314 _123593 op x) = (term560 _123593 op x).
Proof. exact (fun_ext (fun y : _123593 => @lem6197768 _123593 op y x)). Qed.
Lemma lem6197770 {_123593 : Type'} : (@all _123593) = (@all _123593).
Proof. exact (eq_refl (@all _123593)). Qed.
Lemma lem6197771 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : (term315 _123593 op x) = (term561 _123593 op x).
Proof. exact (MK_COMB (@lem6197770 _123593) (@lem6197769 _123593 op x)). Qed.
Lemma lem6197772 {_123593 : Type'} (op : type1400 _123593) : (term316 _123593 op) = (term562 _123593 op).
Proof. exact (fun_ext (fun x : _123593 => @lem6197771 _123593 op x)). Qed.
Lemma lem6197773 {_123593 : Type'} : (@all _123593) = (@all _123593).
Proof. exact (eq_refl (@all _123593)). Qed.
Lemma lem6197774 {_123593 : Type'} (op : type1400 _123593) : (term317 _123593 op) = (term563 _123593 op).
Proof. exact (MK_COMB (@lem6197773 _123593) (@lem6197772 _123593 op)). Qed.
Lemma lem6197775 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6197776 {_123593 : Type'} (op : type1400 _123593) : (term318 _123593 op) = (term564 _123593 op).
Proof. exact (MK_COMB (@lem6197775) (@lem6197774 _123593 op)). Qed.
Lemma lem6197777 {_123593 : Type'} (op : type1400 _123593) : (term159 _123593 op) = (term565 _123593 op).
Proof. exact (MK_COMB (@lem6197776 _123593 op) (@lem6197731 _123593 op)). Qed.
Lemma lem6197778 {_123593 : Type'} (op : type1400 _123593) (h1 : term159 _123593 op) : term565 _123593 op.
Proof. exact (EQ_MP (@lem6197777 _123593 op) (@lem6197617 _123593 op h1)). Qed.
Lemma lem6197779 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6197780 {_123593 : Type'} : (@eq _123593) = (@eq _123593).
Proof. exact (eq_refl (@eq _123593)). Qed.
Lemma lem6197781 {_123593 : Type'} (op : type1400 _123593) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6197788 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6197789 {_123593 : Type'} (f : nat -> _123593) (x : nat) : (f x) = (@I (nat -> _123593) f x).
Proof. exact (@lem6197788 nat _123593 f x). Qed.
Lemma lem6197791 {_123593 : Type'} (f : nat -> _123593) (k : nat) : (term288 _123593 f k) = (term566 _123593 f k).
Proof. exact (@lem6197789 _123593 f (S k)). Qed.
Lemma lem6197802 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (k : nat) (f : nat -> _123593) : (term292 _123593 op _78957 k f) = (term292 _123593 op _78957 k f).
Proof. exact (eq_refl (term292 _123593 op _78957 k f)). Qed.
Lemma lem6197803 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) (k : nat) : (term296 _123593 op f k) = (term567 _123593 op f k).
Proof. exact (MK_COMB (@lem6197781 _123593 op) (@lem6197791 _123593 f k)). Qed.
Lemma lem6197804 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (k : nat) (f : nat -> _123593) : (term297 _123593 op _78957 k f) = (term568 _123593 op _78957 k f).
Proof. exact (MK_COMB (@lem6197803 _123593 op f k) (@lem6197802 _123593 op _78957 k f)). Qed.
Lemma lem6197806 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6197807 {_123593 : Type'} (f : type1400 _123593) (x : _123593) : (f x) = (@I (_123593 -> _123593 -> _123593) f x).
Proof. exact (@lem6197806 _123593 (_123593 -> _123593) f x). Qed.
Lemma lem6197808 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) (k : nat) : (term567 _123593 op f k) = (term569 _123593 op f k).
Proof. exact (@lem6197807 _123593 op (term566 _123593 f k)). Qed.
Lemma lem6197809 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (k : nat) (f : nat -> _123593) : (term292 _123593 op _78957 k f) = (term292 _123593 op _78957 k f).
Proof. exact (eq_refl (term292 _123593 op _78957 k f)). Qed.
Lemma lem6197810 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (k : nat) (f : nat -> _123593) : (term568 _123593 op _78957 k f) = (term570 _123593 op _78957 k f).
Proof. exact (MK_COMB (@lem6197808 _123593 op f k) (@lem6197809 _123593 op _78957 k f)). Qed.
Lemma lem6197812 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6197813 {_123593 : Type'} (f : _123593 -> _123593) (x : _123593) : (f x) = (@I (_123593 -> _123593) f x).
Proof. exact (@lem6197812 _123593 _123593 f x). Qed.
Lemma lem6197814 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (k : nat) (f : nat -> _123593) : (term570 _123593 op _78957 k f) = (term571 _123593 op _78957 k f).
Proof. exact (@lem6197813 _123593 (term569 _123593 op f k) (term292 _123593 op _78957 k f)). Qed.
Lemma lem6197815 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (k : nat) (f : nat -> _123593) : (term568 _123593 op _78957 k f) = (term571 _123593 op _78957 k f).
Proof. exact (TRANS (@lem6197810 _123593 op _78957 k f) (@lem6197814 _123593 op _78957 k f)). Qed.
Lemma lem6197816 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (k : nat) (f : nat -> _123593) : (term297 _123593 op _78957 k f) = (term571 _123593 op _78957 k f).
Proof. exact (TRANS (@lem6197804 _123593 op _78957 k f) (@lem6197815 _123593 op _78957 k f)). Qed.
Lemma lem6197835 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6197836 {_123593 : Type'} (f : nat -> _123593) (x : nat) : (f x) = (@I (nat -> _123593) f x).
Proof. exact (@lem6197835 nat _123593 f x). Qed.
Lemma lem6197838 {_123593 : Type'} (f : nat -> _123593) (k : nat) : (term288 _123593 f k) = (term566 _123593 f k).
Proof. exact (@lem6197836 _123593 f (S k)). Qed.
Lemma lem6197839 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (k : nat) (f : nat -> _123593) : (term294 _123593 op _78957 k f) = (term294 _123593 op _78957 k f).
Proof. exact (eq_refl (term294 _123593 op _78957 k f)). Qed.
Lemma lem6197840 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (f : nat -> _123593) (k : nat) : (term295 _123593 op _78957 f k) = (term572 _123593 op _78957 f k).
Proof. exact (MK_COMB (@lem6197839 _123593 op _78957 k f) (@lem6197838 _123593 f k)). Qed.
Lemma lem6197842 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6197843 {_123593 : Type'} (f : type1400 _123593) (x : _123593) : (f x) = (@I (_123593 -> _123593 -> _123593) f x).
Proof. exact (@lem6197842 _123593 (_123593 -> _123593) f x). Qed.
Lemma lem6197844 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (k : nat) (f : nat -> _123593) : (term294 _123593 op _78957 k f) = (term573 _123593 op _78957 k f).
Proof. exact (@lem6197843 _123593 op (term292 _123593 op _78957 k f)). Qed.
Lemma lem6197845 {_123593 : Type'} (f : nat -> _123593) (k : nat) : (term566 _123593 f k) = (term566 _123593 f k).
Proof. exact (eq_refl (term566 _123593 f k)). Qed.
Lemma lem6197846 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (f : nat -> _123593) (k : nat) : (term572 _123593 op _78957 f k) = (term574 _123593 op _78957 f k).
Proof. exact (MK_COMB (@lem6197844 _123593 op _78957 k f) (@lem6197845 _123593 f k)). Qed.
Lemma lem6197848 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6197849 {_123593 : Type'} (f : _123593 -> _123593) (x : _123593) : (f x) = (@I (_123593 -> _123593) f x).
Proof. exact (@lem6197848 _123593 _123593 f x). Qed.
Lemma lem6197850 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (f : nat -> _123593) (k : nat) : (term574 _123593 op _78957 f k) = (term575 _123593 op _78957 f k).
Proof. exact (@lem6197849 _123593 (term573 _123593 op _78957 k f) (term566 _123593 f k)). Qed.
Lemma lem6197851 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (f : nat -> _123593) (k : nat) : (term572 _123593 op _78957 f k) = (term575 _123593 op _78957 f k).
Proof. exact (TRANS (@lem6197846 _123593 op _78957 f k) (@lem6197850 _123593 op _78957 f k)). Qed.
Lemma lem6197852 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (f : nat -> _123593) (k : nat) : (term295 _123593 op _78957 f k) = (term575 _123593 op _78957 f k).
Proof. exact (TRANS (@lem6197840 _123593 op _78957 f k) (@lem6197851 _123593 op _78957 f k)). Qed.
Lemma lem6197853 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (k : nat) (f : nat -> _123593) : (term298 _123593 op _78957 k f) = (term576 _123593 op _78957 k f).
Proof. exact (MK_COMB (@lem6197780 _123593) (@lem6197816 _123593 op _78957 k f)). Qed.
Lemma lem6197854 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (f : nat -> _123593) (k : nat) : ((term297 _123593 op _78957 k f) = (term295 _123593 op _78957 f k)) = ((term571 _123593 op _78957 k f) = (term575 _123593 op _78957 f k)).
Proof. exact (MK_COMB (@lem6197853 _123593 op _78957 k f) (@lem6197852 _123593 op _78957 f k)). Qed.
Lemma lem6197855 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (f : nat -> _123593) (k : nat) : (term375 _123593 op _78957 f k) = (term577 _123593 op _78957 f k).
Proof. exact (MK_COMB (@lem6197779) (@lem6197854 _123593 op _78957 f k)). Qed.
Lemma lem6197939 {_123593 : Type'} (op : type1400 _123593) (h1 : term159 _123593 op) : term563 _123593 op.
Proof. exact (proj1 (@lem6197778 _123593 op h1)). Qed.
Lemma lem6198007 {_123593 : Type'} (op : type1400 _123593) (y : _123593) (x : _123593) : ((term538 _123593 op x y) = (term538 _123593 op y x)) = ((term538 _123593 op x y) = (term538 _123593 op y x)).
Proof. exact (eq_refl ((term538 _123593 op x y) = (term538 _123593 op y x))). Qed.
Lemma lem6198008 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : (term560 _123593 op x) = (term560 _123593 op x).
Proof. exact (fun_ext (fun y : _123593 => @lem6198007 _123593 op y x)). Qed.
Lemma lem6198009 {_123593 : Type'} : (@all _123593) = (@all _123593).
Proof. exact (eq_refl (@all _123593)). Qed.
Lemma lem6198010 {_123593 : Type'} (op : type1400 _123593) (x : _123593) : (term561 _123593 op x) = (term561 _123593 op x).
Proof. exact (MK_COMB (@lem6198009 _123593) (@lem6198008 _123593 op x)). Qed.
Lemma lem6198011 {_123593 : Type'} (op : type1400 _123593) : (term562 _123593 op) = (term562 _123593 op).
Proof. exact (fun_ext (fun x : _123593 => @lem6198010 _123593 op x)). Qed.
Lemma lem6198012 {_123593 : Type'} : (@all _123593) = (@all _123593).
Proof. exact (eq_refl (@all _123593)). Qed.
Lemma lem6198014 {_123593 : Type'} (op : type1400 _123593) : (term563 _123593 op) = (term563 _123593 op).
Proof. exact (MK_COMB (@lem6198012 _123593) (@lem6198011 _123593 op)). Qed.
Lemma lem6198015 {_123593 : Type'} (op : type1400 _123593) (h1 : term159 _123593 op) : term563 _123593 op.
Proof. exact (EQ_MP (@lem6198014 _123593 op) (@lem6197939 _123593 op h1)). Qed.
Lemma lem6198051 {_123593 : Type'} (_78963 : _123593) (op : type1400 _123593) (h1 : term159 _123593 op) : term578 _123593 op _78963.
Proof. exact (@lem6198015 _123593 op h1 _78963). Qed.
Lemma lem6198052 {_123593 : Type'} (op : type1400 _123593) (_78963 : _123593) : (term578 _123593 op _78963) = (term561 _123593 op _78963).
Proof. exact (eq_refl (term578 _123593 op _78963)). Qed.
Lemma lem6198053 {_123593 : Type'} (_78963 : _123593) (op : type1400 _123593) (h1 : term159 _123593 op) : term561 _123593 op _78963.
Proof. exact (EQ_MP (@lem6198052 _123593 op _78963) (@lem6198051 _123593 _78963 op h1)). Qed.
Lemma lem6198054 {_123593 : Type'} (_78963 : _123593) (_78964 : _123593) (op : type1400 _123593) (h1 : term159 _123593 op) : term579 _123593 op _78963 _78964.
Proof. exact (@lem6198053 _123593 _78963 op h1 _78964). Qed.
Lemma lem6198055 {_123593 : Type'} (op : type1400 _123593) (_78964 : _123593) (_78963 : _123593) : (term579 _123593 op _78963 _78964) = ((term538 _123593 op _78963 _78964) = (term538 _123593 op _78964 _78963)).
Proof. exact (eq_refl (term579 _123593 op _78963 _78964)). Qed.
Lemma lem6198070 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (f : nat -> _123593) (k : nat) (h1 : term375 _123593 op _78957 f k) : term577 _123593 op _78957 f k.
Proof. exact (EQ_MP (@lem6197855 _123593 op _78957 f k) (@lem6197623 _123593 op _78957 f k h1)). Qed.
Lemma lem6198276 {_123593 : Type'} (_78964 : _123593) (_78963 : _123593) (op : type1400 _123593) (h1 : term159 _123593 op) : (term538 _123593 op _78963 _78964) = (term538 _123593 op _78964 _78963).
Proof. exact (EQ_MP (@lem6198055 _123593 op _78964 _78963) (@lem6198054 _123593 _78963 _78964 op h1)). Qed.
Lemma lem6198277 {_123593 : Type'} (_78964 : _123593) (_78963 : _123593) (op : type1400 _123593) (h1 : term159 _123593 op) : (term538 _123593 op _78963 _78964) = (term538 _123593 op _78964 _78963).
Proof. exact (@lem6198276 _123593 _78964 _78963 op h1). Qed.
Lemma lem6198278 {_123593 : Type'} (_78957 : type1605) (f : nat -> _123593) (k : nat) (op : type1400 _123593) (h1 : term159 _123593 op) : (term571 _123593 op _78957 k f) = (term575 _123593 op _78957 f k).
Proof. exact (@lem6198277 _123593 (term292 _123593 op _78957 k f) (term566 _123593 f k) op h1). Qed.
Lemma lem6198279 {_123593 : Type'} (_78957 : type1605) (f : nat -> _123593) (k : nat) (op : type1400 _123593) (h1 : term159 _123593 op) : term580 _123593 op _78957 f k.
Proof. exact (fun h0 : term577 _123593 op _78957 f k => @lem6198278 _123593 _78957 f k op h1). Qed.
Lemma lem6198281 (p : Prop) : (term581 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6198282 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (f : nat -> _123593) (k : nat) : (term580 _123593 op _78957 f k) = ((term571 _123593 op _78957 k f) = (term575 _123593 op _78957 f k)).
Proof. exact (@lem6198281 ((term571 _123593 op _78957 k f) = (term575 _123593 op _78957 f k))). Qed.
Lemma lem6198283 {_123593 : Type'} (_78957 : type1605) (f : nat -> _123593) (k : nat) (op : type1400 _123593) (h1 : term159 _123593 op) : (term571 _123593 op _78957 k f) = (term575 _123593 op _78957 f k).
Proof. exact (EQ_MP (@lem6198282 _123593 op _78957 f k) (@lem6198279 _123593 _78957 f k op h1)). Qed.
Lemma lem6198286 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6198288 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (f : nat -> _123593) (k : nat) : (term577 _123593 op _78957 f k) = (term582 _123593 op _78957 f k).
Proof. exact (@lem6198286 ((term571 _123593 op _78957 k f) = (term575 _123593 op _78957 f k))). Qed.
Lemma lem6198291 {_123593 : Type'} (op : type1400 _123593) (_78957 : type1605) (f : nat -> _123593) (k : nat) (h1 : term375 _123593 op _78957 f k) : term582 _123593 op _78957 f k.
Proof. exact (EQ_MP (@lem6198288 _123593 op _78957 f k) (@lem6198070 _123593 op _78957 f k h1)). Qed.
Lemma lem6198294 {_123593 : Type'} (_78957 : type1605) (f : nat -> _123593) (k : nat) (op : type1400 _123593) (h1 : term375 _123593 op _78957 f k) (h2 : term159 _123593 op) : False.
Proof. exact (@lem6198291 _123593 op _78957 f k h1 (@lem6198283 _123593 _78957 f k op h2)). Qed.
Lemma lem6198295 {_123593 : Type'} (_78957 : type1605) (f : nat -> _123593) (k : nat) (op : type1400 _123593) (h1 : term375 _123593 op _78957 f k) (h2 : term159 _123593 op) : term583.
Proof. exact (fun h0 : ~ False => @lem6198294 _123593 _78957 f k op h1 h2). Qed.
Lemma lem6198297 (p : Prop) : (term581 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6198298 : term583 = False.
Proof. exact (@lem6198297 False). Qed.
Lemma lem6198299 {_123593 : Type'} (_78957 : type1605) (f : nat -> _123593) (k : nat) (op : type1400 _123593) (h1 : term375 _123593 op _78957 f k) (h2 : term159 _123593 op) : False.
Proof. exact (EQ_MP (@lem6198298) (@lem6198295 _123593 _78957 f k op h1 h2)). Qed.
Lemma lem6198300 {_123593 : Type'} (_78957 : type1605) (f : nat -> _123593) (k : nat) (op : type1400 _123593) (h1 : term369 _78957) (h2 : term375 _123593 op _78957 f k) (h3 : term159 _123593 op) : False.
Proof. exact (ex_elim (@lem6197561 _78957 h1) (fun i : type1606 => fun h0 : term528 _78957 i => @lem6198299 _123593 _78957 f k op h2 h3)). Qed.
Lemma lem6198301 {_123593 : Type'} (_78957 : type1605) (f : nat -> _123593) (k : nat) (op : type1400 _123593) (h1 : term369 _78957) (h2 : term375 _123593 op _78957 f k) (h3 : term159 _123593 op) : (term375 _123593 op _78957 f k) = False.
Proof. exact (prop_ext (fun h4 : term375 _123593 op _78957 f k => @lem6198300 _123593 _78957 f k op h1 h2 h3) (fun h4 : False => @lem6197623 _123593 op _78957 f k h2)). Qed.
Lemma lem6198302 {_123593 : Type'} (_78957 : type1605) (f : nat -> _123593) (k : nat) (op : type1400 _123593) (h1 : term369 _78957) (h2 : term375 _123593 op _78957 f k) (h3 : term159 _123593 op) : False.
Proof. exact (EQ_MP (@lem6198301 _123593 _78957 f k op h1 h2 h3) (@lem6197623 _123593 op _78957 f k h2)). Qed.
Lemma lem6198303 {_123593 : Type'} (_78957 : type1605) (f : nat -> _123593) (k : nat) (op : type1400 _123593) (h1 : term369 _78957) (h2 : term375 _123593 op _78957 f k) (h3 : term159 _123593 op) : (term159 _123593 op) = False.
Proof. exact (prop_ext (fun h4 : term159 _123593 op => @lem6198302 _123593 _78957 f k op h1 h2 h3) (fun h4 : False => @lem6197617 _123593 op h3)). Qed.
Lemma lem6198304 {_123593 : Type'} (_78957 : type1605) (f : nat -> _123593) (k : nat) (op : type1400 _123593) (h1 : term369 _78957) (h2 : term375 _123593 op _78957 f k) (h3 : term159 _123593 op) : False.
Proof. exact (EQ_MP (@lem6198303 _123593 _78957 f k op h1 h2 h3) (@lem6197617 _123593 op h3)). Qed.
Lemma lem6198305 {_123593 : Type'} (_78957 : type1605) (f : nat -> _123593) (k : nat) (op : type1400 _123593) (h1 : term369 _78957) (h2 : term375 _123593 op _78957 f k) (h3 : term159 _123593 op) : (term375 _123593 op _78957 f k) = False.
Proof. exact (prop_ext (fun h4 : term375 _123593 op _78957 f k => @lem6198304 _123593 _78957 f k op h1 h2 h3) (fun h4 : False => @lem6197135 _123593 op _78957 f k h2)). Qed.
Lemma lem6198306 {_123593 : Type'} (_78957 : type1605) (f : nat -> _123593) (k : nat) (op : type1400 _123593) (h1 : term369 _78957) (h2 : term375 _123593 op _78957 f k) (h3 : term159 _123593 op) : False.
Proof. exact (EQ_MP (@lem6198305 _123593 _78957 f k op h1 h2 h3) (@lem6197135 _123593 op _78957 f k h2)). Qed.
Lemma lem6198307 {_123593 : Type'} (f : nat -> _123593) (k : nat) (_78957 : type1605) (op : type1400 _123593) (h1 : term369 _78957) (h2 : term159 _123593 op) : term374 _123593 op _78957 f k.
Proof. exact (fun h0 : term375 _123593 op _78957 f k => @lem6198306 _123593 _78957 f k op h1 h0 h2). Qed.
Lemma lem6198308 {_123593 : Type'} (f : nat -> _123593) (k : nat) (_78957 : type1605) (op : type1400 _123593) (h1 : term369 _78957) (h2 : term159 _123593 op) : (term297 _123593 op _78957 k f) = (term295 _123593 op _78957 f k).
Proof. exact (EQ_MP (@lem6197134 _123593 op _78957 f k) (@lem6198307 _123593 f k _78957 op h1 h2)). Qed.
Lemma lem6198313 {_123593 : Type'} (f : nat -> _123593) (_78957 : type1605) (op : type1400 _123593) (h1 : term369 _78957) (h2 : term159 _123593 op) : term300 _123593 op _78957 f.
Proof. exact (fun k : nat => @lem6198308 _123593 f k _78957 op h1 h2). Qed.
Lemma lem6198314 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) (_78957 : type1605) (h1 : term369 _78957) : term319 _123593 op _78957 f.
Proof. exact (fun h0 : term159 _123593 op => @lem6198313 _123593 f _78957 op h1 h0). Qed.
Lemma lem6198319 {_123593 : Type'} (f : nat -> _123593) (_78957 : type1605) (h1 : term369 _78957) : term321 _123593 _78957 f.
Proof. exact (fun op : type1400 _123593 => @lem6198314 _123593 op f _78957 h1). Qed.
Lemma lem6198324 {_123593 : Type'} (_78957 : type1605) (h1 : term369 _78957) : term323 _123593 _78957.
Proof. exact (fun f : nat -> _123593 => @lem6198319 _123593 f _78957 h1). Qed.
Lemma lem6198325 {_123593 : Type'} (_78957 : type1605) : term371 _123593 _78957.
Proof. exact (fun h0 : term369 _78957 => @lem6198324 _123593 _78957 h0). Qed.
Lemma lem6198330 {_123593 : Type'} : term373 _123593.
Proof. exact (fun _78957 : type1605 => @lem6198325 _123593 _78957). Qed.
Lemma lem6198331 {_123593 : Type'} : term283 _123593.
Proof. exact (EQ_MP (@lem6197128 _123593) (@lem6198330 _123593)). Qed.
Lemma lem6198332 {_123593 : Type'} (f : nat -> _123593) : term584 _123593 f.
Proof. exact (@lem6198331 _123593 f). Qed.
Lemma lem6198333 {_123593 : Type'} (f : nat -> _123593) : (term584 _123593 f) = (term275 _123593 f).
Proof. exact (eq_refl (term584 _123593 f)). Qed.
Lemma lem6198334 {_123593 : Type'} (f : nat -> _123593) : term275 _123593 f.
Proof. exact (EQ_MP (@lem6198333 _123593 f) (@lem6198332 _123593 f)). Qed.
Lemma lem6198336 {_123593 : Type'} (f : nat -> _123593) : term275 _123593 f.
Proof. exact (@lem6196699 _123593 f (@lem6198334 _123593 f)). Qed.
Lemma lem6198337 {_123593 : Type'} (f : nat -> _123593) (h1 : term276 _123593 f) : False.
Proof. exact (@lem6198336 _123593 f (@lem6196683 _123593 f h1)). Qed.
Lemma lem6198338 {_123593 : Type'} (f : nat -> _123593) (h1 : term276 _123593 f) : (term276 _123593 f) = False.
Proof. exact (prop_ext (fun h2 : term276 _123593 f => @lem6198337 _123593 f h1) (fun h2 : False => @lem6196683 _123593 f h1)). Qed.
Lemma lem6198339 {_123593 : Type'} (f : nat -> _123593) (h1 : term276 _123593 f) : False.
Proof. exact (EQ_MP (@lem6198338 _123593 f h1) (@lem6196683 _123593 f h1)). Qed.
Lemma lem6198340 {_123593 : Type'} (f : nat -> _123593) : term275 _123593 f.
Proof. exact (fun h0 : term276 _123593 f => @lem6198339 _123593 f h0). Qed.
Lemma lem6198341 {_123593 : Type'} (f : nat -> _123593) : term273 _123593 f.
Proof. exact (EQ_MP (@lem6196682 _123593 f) (@lem6198340 _123593 f)). Qed.
Lemma lem6198342 {_123593 : Type'} (f : nat -> _123593) : term239 _123593 f.
Proof. exact (EQ_MP (@lem6196678 _123593 f) (@lem6198341 _123593 f)). Qed.
Lemma lem6198343 {_123593 : Type'} (f : nat -> _123593) : term238 _123593 f.
Proof. exact (EQ_MP (@lem6196551 _123593 f) (@lem6198342 _123593 f)). Qed.
