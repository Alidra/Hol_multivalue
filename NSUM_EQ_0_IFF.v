Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_EQ_0_IFF_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import INT_POS_spec.
Require Import NSUM_EQ_0_spec.
Require Import NSUM_POS_BOUND_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
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
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17500_spec.
Require Import thm17784_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm18392_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
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
Require Import thm1982759_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988293_spec.
Require Import thm1988332_spec.
Require Import thm1988336_spec.
Require Import thm1988342_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
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
Require Import thm32_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem6949128 (n : nat) : ((n = (NUMERAL 0)) = (term0 n)) = (term1 n).
Proof. exact (@lem17500 (n = (NUMERAL 0)) (term0 n)). Qed.
Lemma lem6949130 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem6949131 (n : nat) : (n = (NUMERAL 0)) = ((int_of_num n) = term2).
Proof. exact (@lem6949130 n (NUMERAL 0)). Qed.
Lemma lem6949134 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6949135 (n : nat) : (term3 n) = (term4 n).
Proof. exact (MK_COMB (@lem6949134) (@lem6949131 n)). Qed.
Lemma lem6949137 (m : nat) (n : nat) : (Peano.le m n) = (term5 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem6949138 (n : nat) : (term0 n) = (term6 n).
Proof. exact (@lem6949137 n (NUMERAL 0)). Qed.
Lemma lem6949139 (n : nat) : (term7 n) = (term8 n).
Proof. exact (MK_COMB (@lem6949135 n) (@lem6949138 n)). Qed.
Lemma lem6949140 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6949141 (n : nat) : (term9 n) = (term10 n).
Proof. exact (MK_COMB (@lem6949140) (@lem6949139 n)). Qed.
Lemma lem6949143 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem6949144 (n : nat) : (n = (NUMERAL 0)) = ((int_of_num n) = term2).
Proof. exact (@lem6949143 n (NUMERAL 0)). Qed.
Lemma lem6949147 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6949148 (n : nat) : (term11 n) = (term12 n).
Proof. exact (MK_COMB (@lem6949147) (@lem6949144 n)). Qed.
Lemma lem6949149 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6949150 (n : nat) : (term13 n) = (term14 n).
Proof. exact (MK_COMB (@lem6949149) (@lem6949148 n)). Qed.
Lemma lem6949152 (m : nat) (n : nat) : (Peano.le m n) = (term5 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem6949153 (n : nat) : (term0 n) = (term6 n).
Proof. exact (@lem6949152 n (NUMERAL 0)). Qed.
Lemma lem6949154 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6949155 (n : nat) : (term15 n) = (term16 n).
Proof. exact (MK_COMB (@lem6949154) (@lem6949153 n)). Qed.
Lemma lem6949156 (n : nat) : (term17 n) = (term18 n).
Proof. exact (MK_COMB (@lem6949150 n) (@lem6949155 n)). Qed.
Lemma lem6949157 (n : nat) : (term1 n) = (term19 n).
Proof. exact (MK_COMB (@lem6949141 n) (@lem6949156 n)). Qed.
Lemma lem6949158 (n : nat) : ((n = (NUMERAL 0)) = (term0 n)) = (term19 n).
Proof. exact (TRANS (@lem6949128 n) (@lem6949157 n)). Qed.
Lemma lem6949159 (n : nat) : term20 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem6949160 (n : nat) : (term20 n) = (term21 n).
Proof. exact (eq_refl (term20 n)). Qed.
Lemma lem6949161 (n : nat) : term21 n.
Proof. exact (EQ_MP (@lem6949160 n) (@lem6949159 n)). Qed.
Lemma lem6949162 (_92591 : int) : (term22 _92591) = (term23 _92591).
Proof. exact (@lem2318604 (term23 _92591)). Qed.
Lemma lem6949183 (_92591 : int) : (term24 _92591) = (term25 _92591).
Proof. exact (@lem17045 (_92591 = term2) (term26 _92591)). Qed.
Lemma lem6949186 (_92591 : int) : (term27 _92591) = (_92591 = term2).
Proof. exact (@lem16933 (_92591 = term2)). Qed.
Lemma lem6949189 (_92591 : int) : (term28 _92591) = (term26 _92591).
Proof. exact (@lem16933 (term26 _92591)). Qed.
Lemma lem6949190 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6949191 (_92591 : int) : (term29 _92591) = (term30 _92591).
Proof. exact (MK_COMB (@lem6949190) (@lem6949186 _92591)). Qed.
Lemma lem6949192 (_92591 : int) : (term31 _92591) = (term32 _92591).
Proof. exact (MK_COMB (@lem6949191 _92591) (@lem6949189 _92591)). Qed.
Lemma lem6949193 (_92591 : int) : (term33 _92591) = (term31 _92591).
Proof. exact (@lem17045 (term34 _92591) (term35 _92591)). Qed.
Lemma lem6949194 (_92591 : int) : (term33 _92591) = (term32 _92591).
Proof. exact (TRANS (@lem6949193 _92591) (@lem6949192 _92591)). Qed.
Lemma lem6949195 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6949196 (_92591 : int) : (term36 _92591) = (term37 _92591).
Proof. exact (MK_COMB (@lem6949195) (@lem6949183 _92591)). Qed.
Lemma lem6949197 (_92591 : int) : (term38 _92591) = (term39 _92591).
Proof. exact (MK_COMB (@lem6949196 _92591) (@lem6949194 _92591)). Qed.
Lemma lem6949198 (_92591 : int) : (term40 _92591) = (term38 _92591).
Proof. exact (@lem17160 (term41 _92591) (term42 _92591)). Qed.
Lemma lem6949199 (_92591 : int) : (term40 _92591) = (term39 _92591).
Proof. exact (TRANS (@lem6949198 _92591) (@lem6949197 _92591)). Qed.
Lemma lem6949201 (_92591 : int) : (term43 _92591) = (term43 _92591).
Proof. exact (eq_refl (term43 _92591)). Qed.
Lemma lem6949202 (_92591 : int) : (term44 _92591) = (term45 _92591).
Proof. exact (MK_COMB (@lem6949201 _92591) (@lem6949199 _92591)). Qed.
Lemma lem6949203 (_92591 : int) : (term46 _92591) = (term44 _92591).
Proof. exact (@lem17362 (term47 _92591) (term48 _92591)). Qed.
Lemma lem6949227 (_92591 : int) : (term46 _92591) = (term45 _92591).
Proof. exact (TRANS (@lem6949203 _92591) (@lem6949202 _92591)). Qed.
Lemma lem6949230 (x : int) (y : int) : (int_le x y) = (term49 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6949231 (_92591 : int) : (term47 _92591) = (term50 _92591).
Proof. exact (@lem6949230 term2 _92591). Qed.
Lemma lem6949233 (n : nat) : (term51 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6949234 : term52 = term53.
Proof. exact (@lem6949233 (NUMERAL 0)). Qed.
Lemma lem6949235 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6949236 : term54 = term55.
Proof. exact (MK_COMB (@lem6949235) (@lem6949234)). Qed.
Lemma lem6949237 (_92591 : int) : (real_of_int _92591) = (real_of_int _92591).
Proof. exact (eq_refl (real_of_int _92591)). Qed.
Lemma lem6949238 (_92591 : int) : (term50 _92591) = (term56 _92591).
Proof. exact (MK_COMB (@lem6949236) (@lem6949237 _92591)). Qed.
Lemma lem6949240 (_92591 : int) : (term47 _92591) = (term56 _92591).
Proof. exact (TRANS (@lem6949231 _92591) (@lem6949238 _92591)). Qed.
Lemma lem6949242 (y : int) (x : int) : (term57 x y) = (term58 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem6949243 (_92591 : int) : (term34 _92591) = (term59 _92591).
Proof. exact (@lem6949242 term2 _92591). Qed.
Lemma lem6949245 (x : int) (y : int) : (int_le x y) = (term49 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6949246 (_92591 : int) : (term60 _92591) = (term61 _92591).
Proof. exact (@lem6949245 (term62 _92591) term2). Qed.
Lemma lem6949248 (x : int) (y : int) : (term63 x y) = (term64 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6949249 (_92591 : int) : (term65 _92591) = (term66 _92591).
Proof. exact (@lem6949248 _92591 term67). Qed.
Lemma lem6949251 (n : nat) : (term51 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6949252 : term68 = term69.
Proof. exact (@lem6949251 term70). Qed.
Lemma lem6949253 (_92591 : int) : (term71 _92591) = (term71 _92591).
Proof. exact (eq_refl (term71 _92591)). Qed.
Lemma lem6949254 (_92591 : int) : (term66 _92591) = (term72 _92591).
Proof. exact (MK_COMB (@lem6949253 _92591) (@lem6949252)). Qed.
Lemma lem6949255 (_92591 : int) : (term65 _92591) = (term72 _92591).
Proof. exact (TRANS (@lem6949249 _92591) (@lem6949254 _92591)). Qed.
Lemma lem6949256 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6949257 (_92591 : int) : (term73 _92591) = (term74 _92591).
Proof. exact (MK_COMB (@lem6949256) (@lem6949255 _92591)). Qed.
Lemma lem6949259 (n : nat) : (term51 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6949260 : term52 = term53.
Proof. exact (@lem6949259 (NUMERAL 0)). Qed.
Lemma lem6949261 (_92591 : int) : (term61 _92591) = (term75 _92591).
Proof. exact (MK_COMB (@lem6949257 _92591) (@lem6949260)). Qed.
Lemma lem6949262 (_92591 : int) : (term60 _92591) = (term75 _92591).
Proof. exact (TRANS (@lem6949246 _92591) (@lem6949261 _92591)). Qed.
Lemma lem6949263 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6949264 (_92591 : int) : (term76 _92591) = (term77 _92591).
Proof. exact (MK_COMB (@lem6949263) (@lem6949262 _92591)). Qed.
Lemma lem6949266 (x : int) (y : int) : (int_le x y) = (term49 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6949267 (_92591 : int) : (term78 _92591) = (term79 _92591).
Proof. exact (@lem6949266 term80 _92591). Qed.
Lemma lem6949269 (x : int) (y : int) : (term63 x y) = (term64 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6949270 : term81 = term82.
Proof. exact (@lem6949269 term2 term67). Qed.
Lemma lem6949272 (n : nat) : (term51 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6949273 : term52 = term53.
Proof. exact (@lem6949272 (NUMERAL 0)). Qed.
Lemma lem6949274 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6949275 : term83 = term84.
Proof. exact (MK_COMB (@lem6949274) (@lem6949273)). Qed.
Lemma lem6949277 (n : nat) : (term51 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6949278 : term68 = term69.
Proof. exact (@lem6949277 term70). Qed.
Lemma lem6949279 : term82 = term85.
Proof. exact (MK_COMB (@lem6949275) (@lem6949278)). Qed.
Lemma lem6949280 : term81 = term85.
Proof. exact (TRANS (@lem6949270) (@lem6949279)). Qed.
Lemma lem6949281 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6949282 : term86 = term87.
Proof. exact (MK_COMB (@lem6949281) (@lem6949280)). Qed.
Lemma lem6949283 (_92591 : int) : (real_of_int _92591) = (real_of_int _92591).
Proof. exact (eq_refl (real_of_int _92591)). Qed.
Lemma lem6949284 (_92591 : int) : (term79 _92591) = (term88 _92591).
Proof. exact (MK_COMB (@lem6949282) (@lem6949283 _92591)). Qed.
Lemma lem6949285 (_92591 : int) : (term78 _92591) = (term88 _92591).
Proof. exact (TRANS (@lem6949267 _92591) (@lem6949284 _92591)). Qed.
Lemma lem6949286 (_92591 : int) : (term59 _92591) = (term89 _92591).
Proof. exact (MK_COMB (@lem6949264 _92591) (@lem6949285 _92591)). Qed.
Lemma lem6949287 (_92591 : int) : (term34 _92591) = (term89 _92591).
Proof. exact (TRANS (@lem6949243 _92591) (@lem6949286 _92591)). Qed.
Lemma lem6949289 (y : int) (x : int) : (term90 x y) = (term91 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem6949290 (_92591 : int) : (term35 _92591) = (term78 _92591).
Proof. exact (@lem6949289 term2 _92591). Qed.
Lemma lem6949292 (x : int) (y : int) : (int_le x y) = (term49 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6949293 (_92591 : int) : (term78 _92591) = (term79 _92591).
Proof. exact (@lem6949292 term80 _92591). Qed.
Lemma lem6949295 (x : int) (y : int) : (term63 x y) = (term64 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6949296 : term81 = term82.
Proof. exact (@lem6949295 term2 term67). Qed.
Lemma lem6949298 (n : nat) : (term51 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6949299 : term52 = term53.
Proof. exact (@lem6949298 (NUMERAL 0)). Qed.
Lemma lem6949300 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6949301 : term83 = term84.
Proof. exact (MK_COMB (@lem6949300) (@lem6949299)). Qed.
Lemma lem6949303 (n : nat) : (term51 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6949304 : term68 = term69.
Proof. exact (@lem6949303 term70). Qed.
Lemma lem6949305 : term82 = term85.
Proof. exact (MK_COMB (@lem6949301) (@lem6949304)). Qed.
Lemma lem6949306 : term81 = term85.
Proof. exact (TRANS (@lem6949296) (@lem6949305)). Qed.
Lemma lem6949307 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6949308 : term86 = term87.
Proof. exact (MK_COMB (@lem6949307) (@lem6949306)). Qed.
Lemma lem6949309 (_92591 : int) : (real_of_int _92591) = (real_of_int _92591).
Proof. exact (eq_refl (real_of_int _92591)). Qed.
Lemma lem6949310 (_92591 : int) : (term79 _92591) = (term88 _92591).
Proof. exact (MK_COMB (@lem6949308) (@lem6949309 _92591)). Qed.
Lemma lem6949311 (_92591 : int) : (term78 _92591) = (term88 _92591).
Proof. exact (TRANS (@lem6949293 _92591) (@lem6949310 _92591)). Qed.
Lemma lem6949312 (_92591 : int) : (term35 _92591) = (term88 _92591).
Proof. exact (TRANS (@lem6949290 _92591) (@lem6949311 _92591)). Qed.
Lemma lem6949313 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6949314 (_92591 : int) : (term92 _92591) = (term93 _92591).
Proof. exact (MK_COMB (@lem6949313) (@lem6949287 _92591)). Qed.
Lemma lem6949315 (_92591 : int) : (term25 _92591) = (term94 _92591).
Proof. exact (MK_COMB (@lem6949314 _92591) (@lem6949312 _92591)). Qed.
Lemma lem6949318 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem6949319 (_92591 : int) : (_92591 = term2) = ((real_of_int _92591) = term52).
Proof. exact (@lem6949318 _92591 term2). Qed.
Lemma lem6949323 (n : nat) : (term51 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6949324 : term52 = term53.
Proof. exact (@lem6949323 (NUMERAL 0)). Qed.
Lemma lem6949325 (_92591 : int) : (term95 _92591) = (term95 _92591).
Proof. exact (eq_refl (term95 _92591)). Qed.
Lemma lem6949326 (_92591 : int) : ((real_of_int _92591) = term52) = ((real_of_int _92591) = term53).
Proof. exact (MK_COMB (@lem6949325 _92591) (@lem6949324)). Qed.
Lemma lem6949328 (_92591 : int) : (_92591 = term2) = ((real_of_int _92591) = term53).
Proof. exact (TRANS (@lem6949319 _92591) (@lem6949326 _92591)). Qed.
Lemma lem6949331 (x : int) (y : int) : (int_le x y) = (term49 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6949332 (_92591 : int) : (term26 _92591) = (term96 _92591).
Proof. exact (@lem6949331 _92591 term2). Qed.
Lemma lem6949334 (n : nat) : (term51 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6949335 : term52 = term53.
Proof. exact (@lem6949334 (NUMERAL 0)). Qed.
Lemma lem6949336 (_92591 : int) : (term97 _92591) = (term97 _92591).
Proof. exact (eq_refl (term97 _92591)). Qed.
Lemma lem6949337 (_92591 : int) : (term96 _92591) = (term98 _92591).
Proof. exact (MK_COMB (@lem6949336 _92591) (@lem6949335)). Qed.
Lemma lem6949339 (_92591 : int) : (term26 _92591) = (term98 _92591).
Proof. exact (TRANS (@lem6949332 _92591) (@lem6949337 _92591)). Qed.
Lemma lem6949340 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6949341 (_92591 : int) : (term30 _92591) = (term99 _92591).
Proof. exact (MK_COMB (@lem6949340) (@lem6949328 _92591)). Qed.
Lemma lem6949342 (_92591 : int) : (term32 _92591) = (term100 _92591).
Proof. exact (MK_COMB (@lem6949341 _92591) (@lem6949339 _92591)). Qed.
Lemma lem6949343 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6949344 (_92591 : int) : (term37 _92591) = (term101 _92591).
Proof. exact (MK_COMB (@lem6949343) (@lem6949315 _92591)). Qed.
Lemma lem6949345 (_92591 : int) : (term39 _92591) = (term102 _92591).
Proof. exact (MK_COMB (@lem6949344 _92591) (@lem6949342 _92591)). Qed.
Lemma lem6949346 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6949347 (_92591 : int) : (term43 _92591) = (term103 _92591).
Proof. exact (MK_COMB (@lem6949346) (@lem6949240 _92591)). Qed.
Lemma lem6949348 (_92591 : int) : (term45 _92591) = (term104 _92591).
Proof. exact (MK_COMB (@lem6949347 _92591) (@lem6949345 _92591)). Qed.
Lemma lem6949349 (_92591 : int) : (term46 _92591) = (term104 _92591).
Proof. exact (TRANS (@lem6949227 _92591) (@lem6949348 _92591)). Qed.
Lemma lem6949353 (t : Prop) : (term105 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6949409 (_92591 : int) : (term106 _92591) = (term104 _92591).
Proof. exact (@lem6949353 (term104 _92591)). Qed.
Lemma lem6949410 (_92591 : int) : (term56 _92591) = (term107 _92591).
Proof. exact (@lem1988287 (real_of_int _92591) term53). Qed.
Lemma lem6949416 (_92591 : int) : (term108 _92591) = (term109 _92591).
Proof. exact (@lem1982792 (real_of_int _92591) term53). Qed.
Lemma lem6949418 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6949419 : term53 = term111.
Proof. exact (@lem6949418 (NUMERAL 0)). Qed.
Lemma lem6949421 (x : nat) : (term112 x) = (term113 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6949422 : term114 = term115.
Proof. exact (@lem6949421 term70). Qed.
Lemma lem6949423 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6949424 : term116 = term117.
Proof. exact (MK_COMB (@lem6949423) (@lem6949422)). Qed.
Lemma lem6949425 : term118 = term119.
Proof. exact (MK_COMB (@lem6949424) (@lem6949419)). Qed.
Lemma lem6949426 : term119 = term120.
Proof. exact (@lem1981613 term114 term53 term69 term69). Qed.
Lemma lem6949428 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6949429 : term123 = term124.
Proof. exact (@lem6949428 term70 term70). Qed.
Lemma lem6949430 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6949431 : term126 = term70.
Proof. exact (EQ_MP (@lem6949430) (@lem940073)). Qed.
Lemma lem6949432 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6949433 : term124 = term69.
Proof. exact (MK_COMB (@lem6949432) (@lem6949431)). Qed.
Lemma lem6949434 : term123 = term69.
Proof. exact (TRANS (@lem6949429) (@lem6949433)). Qed.
Lemma lem6949436 (x : nat) : (term127 x) = term53.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6949437 : term118 = term53.
Proof. exact (@lem6949436 term70). Qed.
Lemma lem6949438 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6949439 : term128 = term129.
Proof. exact (MK_COMB (@lem6949438) (@lem6949437)). Qed.
Lemma lem6949440 : term120 = term111.
Proof. exact (MK_COMB (@lem6949439) (@lem6949434)). Qed.
Lemma lem6949441 : term119 = term111.
Proof. exact (TRANS (@lem6949426) (@lem6949440)). Qed.
Lemma lem6949442 : term118 = term111.
Proof. exact (TRANS (@lem6949425) (@lem6949441)). Qed.
Lemma lem6949444 (x : real) : (term130 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6949445 : term111 = term53.
Proof. exact (@lem6949444 term53). Qed.
Lemma lem6949446 : term118 = term53.
Proof. exact (TRANS (@lem6949442) (@lem6949445)). Qed.
Lemma lem6949447 (_92591 : int) : (term71 _92591) = (term71 _92591).
Proof. exact (eq_refl (term71 _92591)). Qed.
Lemma lem6949448 (_92591 : int) : (term109 _92591) = (term131 _92591).
Proof. exact (MK_COMB (@lem6949447 _92591) (@lem6949446)). Qed.
Lemma lem6949449 (_92591 : int) : (term131 _92591) = (real_of_int _92591).
Proof. exact (@lem1982723 (real_of_int _92591)). Qed.
Lemma lem6949450 (_92591 : int) : (term109 _92591) = (real_of_int _92591).
Proof. exact (TRANS (@lem6949448 _92591) (@lem6949449 _92591)). Qed.
Lemma lem6949452 (_92591 : int) : (term108 _92591) = (real_of_int _92591).
Proof. exact (TRANS (@lem6949416 _92591) (@lem6949450 _92591)). Qed.
Lemma lem6949453 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6949454 (_92591 : int) : (term132 _92591) = (term133 _92591).
Proof. exact (MK_COMB (@lem6949453) (@lem6949452 _92591)). Qed.
Lemma lem6949455 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem6949456 (_92591 : int) : (term107 _92591) = (term134 _92591).
Proof. exact (MK_COMB (@lem6949454 _92591) (@lem6949455)). Qed.
Lemma lem6949457 (_92591 : int) : (term56 _92591) = (term134 _92591).
Proof. exact (TRANS (@lem6949410 _92591) (@lem6949456 _92591)). Qed.
Lemma lem6949458 (_92591 : int) : (term75 _92591) = (term135 _92591).
Proof. exact (@lem1988287 term53 (term72 _92591)). Qed.
Lemma lem6949470 (_92591 : int) : (term136 _92591) = (term137 _92591).
Proof. exact (@lem1982792 term53 (term72 _92591)). Qed.
Lemma lem6949471 (_92591 : int) : (term138 _92591) = (term139 _92591).
Proof. exact (@lem1982781 (real_of_int _92591) term114 term69). Qed.
Lemma lem6949473 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6949474 : term69 = term140.
Proof. exact (@lem6949473 term70). Qed.
Lemma lem6949476 (x : nat) : (term112 x) = (term113 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6949477 : term114 = term115.
Proof. exact (@lem6949476 term70). Qed.
Lemma lem6949478 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6949479 : term116 = term117.
Proof. exact (MK_COMB (@lem6949478) (@lem6949477)). Qed.
Lemma lem6949480 : term141 = term142.
Proof. exact (MK_COMB (@lem6949479) (@lem6949474)). Qed.
Lemma lem6949481 : term142 = term143.
Proof. exact (@lem1981613 term114 term69 term69 term69). Qed.
Lemma lem6949483 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6949484 : term123 = term124.
Proof. exact (@lem6949483 term70 term70). Qed.
Lemma lem6949485 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6949486 : term126 = term70.
Proof. exact (EQ_MP (@lem6949485) (@lem940073)). Qed.
Lemma lem6949487 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6949488 : term124 = term69.
Proof. exact (MK_COMB (@lem6949487) (@lem6949486)). Qed.
Lemma lem6949489 : term123 = term69.
Proof. exact (TRANS (@lem6949484) (@lem6949488)). Qed.
Lemma lem6949491 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6949492 : term141 = term146.
Proof. exact (@lem6949491 term70 term70). Qed.
Lemma lem6949493 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6949494 : term126 = term70.
Proof. exact (EQ_MP (@lem6949493) (@lem940073)). Qed.
Lemma lem6949495 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6949496 : term124 = term69.
Proof. exact (MK_COMB (@lem6949495) (@lem6949494)). Qed.
Lemma lem6949497 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6949498 : term146 = term114.
Proof. exact (MK_COMB (@lem6949497) (@lem6949496)). Qed.
Lemma lem6949499 : term141 = term114.
Proof. exact (TRANS (@lem6949492) (@lem6949498)). Qed.
Lemma lem6949500 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6949501 : term147 = term148.
Proof. exact (MK_COMB (@lem6949500) (@lem6949499)). Qed.
Lemma lem6949502 : term143 = term115.
Proof. exact (MK_COMB (@lem6949501) (@lem6949489)). Qed.
Lemma lem6949503 : term142 = term115.
Proof. exact (TRANS (@lem6949481) (@lem6949502)). Qed.
Lemma lem6949504 : term141 = term115.
Proof. exact (TRANS (@lem6949480) (@lem6949503)). Qed.
Lemma lem6949506 (x : real) : (term130 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6949507 : term115 = term114.
Proof. exact (@lem6949506 term114). Qed.
Lemma lem6949508 : term141 = term114.
Proof. exact (TRANS (@lem6949504) (@lem6949507)). Qed.
Lemma lem6949511 (_92591 : int) : (term149 _92591) = (term149 _92591).
Proof. exact (eq_refl (term149 _92591)). Qed.
Lemma lem6949512 (_92591 : int) : (term139 _92591) = (term150 _92591).
Proof. exact (MK_COMB (@lem6949511 _92591) (@lem6949508)). Qed.
Lemma lem6949513 (_92591 : int) : (term138 _92591) = (term150 _92591).
Proof. exact (TRANS (@lem6949471 _92591) (@lem6949512 _92591)). Qed.
Lemma lem6949514 : term84 = term84.
Proof. exact (eq_refl term84). Qed.
Lemma lem6949515 (_92591 : int) : (term137 _92591) = (term151 _92591).
Proof. exact (MK_COMB (@lem6949514) (@lem6949513 _92591)). Qed.
Lemma lem6949516 (_92591 : int) : (term151 _92591) = (term150 _92591).
Proof. exact (@lem1982721 (term150 _92591)). Qed.
Lemma lem6949517 (_92591 : int) : (term137 _92591) = (term150 _92591).
Proof. exact (TRANS (@lem6949515 _92591) (@lem6949516 _92591)). Qed.
Lemma lem6949519 (_92591 : int) : (term136 _92591) = (term150 _92591).
Proof. exact (TRANS (@lem6949470 _92591) (@lem6949517 _92591)). Qed.
Lemma lem6949520 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6949521 (_92591 : int) : (term152 _92591) = (term153 _92591).
Proof. exact (MK_COMB (@lem6949520) (@lem6949519 _92591)). Qed.
Lemma lem6949522 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem6949523 (_92591 : int) : (term135 _92591) = (term154 _92591).
Proof. exact (MK_COMB (@lem6949521 _92591) (@lem6949522)). Qed.
Lemma lem6949524 (_92591 : int) : (term75 _92591) = (term154 _92591).
Proof. exact (TRANS (@lem6949458 _92591) (@lem6949523 _92591)). Qed.
Lemma lem6949525 (_92591 : int) : (term88 _92591) = (term155 _92591).
Proof. exact (@lem1988287 (real_of_int _92591) term85). Qed.
Lemma lem6949532 : term85 = term69.
Proof. exact (@lem1982721 term69). Qed.
Lemma lem6949535 (_92591 : int) : (term156 _92591) = (term156 _92591).
Proof. exact (eq_refl (term156 _92591)). Qed.
Lemma lem6949536 (_92591 : int) : (term157 _92591) = (term158 _92591).
Proof. exact (MK_COMB (@lem6949535 _92591) (@lem6949532)). Qed.
Lemma lem6949537 (_92591 : int) : (term158 _92591) = (term159 _92591).
Proof. exact (@lem1982792 (real_of_int _92591) term69). Qed.
Lemma lem6949539 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6949540 : term69 = term140.
Proof. exact (@lem6949539 term70). Qed.
Lemma lem6949542 (x : nat) : (term112 x) = (term113 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6949543 : term114 = term115.
Proof. exact (@lem6949542 term70). Qed.
Lemma lem6949544 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6949545 : term116 = term117.
Proof. exact (MK_COMB (@lem6949544) (@lem6949543)). Qed.
Lemma lem6949546 : term141 = term142.
Proof. exact (MK_COMB (@lem6949545) (@lem6949540)). Qed.
Lemma lem6949547 : term142 = term143.
Proof. exact (@lem1981613 term114 term69 term69 term69). Qed.
Lemma lem6949549 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6949550 : term123 = term124.
Proof. exact (@lem6949549 term70 term70). Qed.
Lemma lem6949551 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6949552 : term126 = term70.
Proof. exact (EQ_MP (@lem6949551) (@lem940073)). Qed.
Lemma lem6949553 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6949554 : term124 = term69.
Proof. exact (MK_COMB (@lem6949553) (@lem6949552)). Qed.
Lemma lem6949555 : term123 = term69.
Proof. exact (TRANS (@lem6949550) (@lem6949554)). Qed.
Lemma lem6949557 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6949558 : term141 = term146.
Proof. exact (@lem6949557 term70 term70). Qed.
Lemma lem6949559 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6949560 : term126 = term70.
Proof. exact (EQ_MP (@lem6949559) (@lem940073)). Qed.
Lemma lem6949561 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6949562 : term124 = term69.
Proof. exact (MK_COMB (@lem6949561) (@lem6949560)). Qed.
Lemma lem6949563 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6949564 : term146 = term114.
Proof. exact (MK_COMB (@lem6949563) (@lem6949562)). Qed.
Lemma lem6949565 : term141 = term114.
Proof. exact (TRANS (@lem6949558) (@lem6949564)). Qed.
Lemma lem6949566 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6949567 : term147 = term148.
Proof. exact (MK_COMB (@lem6949566) (@lem6949565)). Qed.
Lemma lem6949568 : term143 = term115.
Proof. exact (MK_COMB (@lem6949567) (@lem6949555)). Qed.
Lemma lem6949569 : term142 = term115.
Proof. exact (TRANS (@lem6949547) (@lem6949568)). Qed.
Lemma lem6949570 : term141 = term115.
Proof. exact (TRANS (@lem6949546) (@lem6949569)). Qed.
Lemma lem6949572 (x : real) : (term130 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6949573 : term115 = term114.
Proof. exact (@lem6949572 term114). Qed.
Lemma lem6949574 : term141 = term114.
Proof. exact (TRANS (@lem6949570) (@lem6949573)). Qed.
Lemma lem6949575 (_92591 : int) : (term71 _92591) = (term71 _92591).
Proof. exact (eq_refl (term71 _92591)). Qed.
Lemma lem6949578 (_92591 : int) : (term159 _92591) = (term160 _92591).
Proof. exact (MK_COMB (@lem6949575 _92591) (@lem6949574)). Qed.
Lemma lem6949579 (_92591 : int) : (term158 _92591) = (term160 _92591).
Proof. exact (TRANS (@lem6949537 _92591) (@lem6949578 _92591)). Qed.
Lemma lem6949580 (_92591 : int) : (term157 _92591) = (term160 _92591).
Proof. exact (TRANS (@lem6949536 _92591) (@lem6949579 _92591)). Qed.
Lemma lem6949581 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6949582 (_92591 : int) : (term161 _92591) = (term162 _92591).
Proof. exact (MK_COMB (@lem6949581) (@lem6949580 _92591)). Qed.
Lemma lem6949583 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem6949584 (_92591 : int) : (term155 _92591) = (term163 _92591).
Proof. exact (MK_COMB (@lem6949582 _92591) (@lem6949583)). Qed.
Lemma lem6949585 (_92591 : int) : (term88 _92591) = (term163 _92591).
Proof. exact (TRANS (@lem6949525 _92591) (@lem6949584 _92591)). Qed.
Lemma lem6949586 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6949587 (_92591 : int) : (term77 _92591) = (term164 _92591).
Proof. exact (MK_COMB (@lem6949586) (@lem6949524 _92591)). Qed.
Lemma lem6949588 (_92591 : int) : (term89 _92591) = (term165 _92591).
Proof. exact (MK_COMB (@lem6949587 _92591) (@lem6949585 _92591)). Qed.
Lemma lem6949589 (_92591 : int) : (term88 _92591) = (term155 _92591).
Proof. exact (@lem1988287 (real_of_int _92591) term85). Qed.
Lemma lem6949596 : term85 = term69.
Proof. exact (@lem1982721 term69). Qed.
Lemma lem6949599 (_92591 : int) : (term156 _92591) = (term156 _92591).
Proof. exact (eq_refl (term156 _92591)). Qed.
Lemma lem6949600 (_92591 : int) : (term157 _92591) = (term158 _92591).
Proof. exact (MK_COMB (@lem6949599 _92591) (@lem6949596)). Qed.
Lemma lem6949601 (_92591 : int) : (term158 _92591) = (term159 _92591).
Proof. exact (@lem1982792 (real_of_int _92591) term69). Qed.
Lemma lem6949603 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6949604 : term69 = term140.
Proof. exact (@lem6949603 term70). Qed.
Lemma lem6949606 (x : nat) : (term112 x) = (term113 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6949607 : term114 = term115.
Proof. exact (@lem6949606 term70). Qed.
Lemma lem6949608 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6949609 : term116 = term117.
Proof. exact (MK_COMB (@lem6949608) (@lem6949607)). Qed.
Lemma lem6949610 : term141 = term142.
Proof. exact (MK_COMB (@lem6949609) (@lem6949604)). Qed.
Lemma lem6949611 : term142 = term143.
Proof. exact (@lem1981613 term114 term69 term69 term69). Qed.
Lemma lem6949613 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6949614 : term123 = term124.
Proof. exact (@lem6949613 term70 term70). Qed.
Lemma lem6949615 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6949616 : term126 = term70.
Proof. exact (EQ_MP (@lem6949615) (@lem940073)). Qed.
Lemma lem6949617 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6949618 : term124 = term69.
Proof. exact (MK_COMB (@lem6949617) (@lem6949616)). Qed.
Lemma lem6949619 : term123 = term69.
Proof. exact (TRANS (@lem6949614) (@lem6949618)). Qed.
Lemma lem6949621 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6949622 : term141 = term146.
Proof. exact (@lem6949621 term70 term70). Qed.
Lemma lem6949623 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6949624 : term126 = term70.
Proof. exact (EQ_MP (@lem6949623) (@lem940073)). Qed.
Lemma lem6949625 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6949626 : term124 = term69.
Proof. exact (MK_COMB (@lem6949625) (@lem6949624)). Qed.
Lemma lem6949627 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6949628 : term146 = term114.
Proof. exact (MK_COMB (@lem6949627) (@lem6949626)). Qed.
Lemma lem6949629 : term141 = term114.
Proof. exact (TRANS (@lem6949622) (@lem6949628)). Qed.
Lemma lem6949630 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6949631 : term147 = term148.
Proof. exact (MK_COMB (@lem6949630) (@lem6949629)). Qed.
Lemma lem6949632 : term143 = term115.
Proof. exact (MK_COMB (@lem6949631) (@lem6949619)). Qed.
Lemma lem6949633 : term142 = term115.
Proof. exact (TRANS (@lem6949611) (@lem6949632)). Qed.
Lemma lem6949634 : term141 = term115.
Proof. exact (TRANS (@lem6949610) (@lem6949633)). Qed.
Lemma lem6949636 (x : real) : (term130 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6949637 : term115 = term114.
Proof. exact (@lem6949636 term114). Qed.
Lemma lem6949638 : term141 = term114.
Proof. exact (TRANS (@lem6949634) (@lem6949637)). Qed.
Lemma lem6949639 (_92591 : int) : (term71 _92591) = (term71 _92591).
Proof. exact (eq_refl (term71 _92591)). Qed.
Lemma lem6949642 (_92591 : int) : (term159 _92591) = (term160 _92591).
Proof. exact (MK_COMB (@lem6949639 _92591) (@lem6949638)). Qed.
Lemma lem6949643 (_92591 : int) : (term158 _92591) = (term160 _92591).
Proof. exact (TRANS (@lem6949601 _92591) (@lem6949642 _92591)). Qed.
Lemma lem6949644 (_92591 : int) : (term157 _92591) = (term160 _92591).
Proof. exact (TRANS (@lem6949600 _92591) (@lem6949643 _92591)). Qed.
Lemma lem6949645 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6949646 (_92591 : int) : (term161 _92591) = (term162 _92591).
Proof. exact (MK_COMB (@lem6949645) (@lem6949644 _92591)). Qed.
Lemma lem6949647 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem6949648 (_92591 : int) : (term155 _92591) = (term163 _92591).
Proof. exact (MK_COMB (@lem6949646 _92591) (@lem6949647)). Qed.
Lemma lem6949649 (_92591 : int) : (term88 _92591) = (term163 _92591).
Proof. exact (TRANS (@lem6949589 _92591) (@lem6949648 _92591)). Qed.
Lemma lem6949650 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6949651 (_92591 : int) : (term93 _92591) = (term166 _92591).
Proof. exact (MK_COMB (@lem6949650) (@lem6949588 _92591)). Qed.
Lemma lem6949652 (_92591 : int) : (term94 _92591) = (term167 _92591).
Proof. exact (MK_COMB (@lem6949651 _92591) (@lem6949649 _92591)). Qed.
Lemma lem6949653 (_92591 : int) : ((real_of_int _92591) = term53) = ((term108 _92591) = term53).
Proof. exact (@lem1988293 (real_of_int _92591) term53). Qed.
Lemma lem6949659 (_92591 : int) : (term108 _92591) = (term109 _92591).
Proof. exact (@lem1982792 (real_of_int _92591) term53). Qed.
Lemma lem6949661 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6949662 : term53 = term111.
Proof. exact (@lem6949661 (NUMERAL 0)). Qed.
Lemma lem6949664 (x : nat) : (term112 x) = (term113 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6949665 : term114 = term115.
Proof. exact (@lem6949664 term70). Qed.
Lemma lem6949666 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6949667 : term116 = term117.
Proof. exact (MK_COMB (@lem6949666) (@lem6949665)). Qed.
Lemma lem6949668 : term118 = term119.
Proof. exact (MK_COMB (@lem6949667) (@lem6949662)). Qed.
Lemma lem6949669 : term119 = term120.
Proof. exact (@lem1981613 term114 term53 term69 term69). Qed.
Lemma lem6949671 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6949672 : term123 = term124.
Proof. exact (@lem6949671 term70 term70). Qed.
Lemma lem6949673 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6949674 : term126 = term70.
Proof. exact (EQ_MP (@lem6949673) (@lem940073)). Qed.
Lemma lem6949675 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6949676 : term124 = term69.
Proof. exact (MK_COMB (@lem6949675) (@lem6949674)). Qed.
Lemma lem6949677 : term123 = term69.
Proof. exact (TRANS (@lem6949672) (@lem6949676)). Qed.
Lemma lem6949679 (x : nat) : (term127 x) = term53.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6949680 : term118 = term53.
Proof. exact (@lem6949679 term70). Qed.
Lemma lem6949681 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6949682 : term128 = term129.
Proof. exact (MK_COMB (@lem6949681) (@lem6949680)). Qed.
Lemma lem6949683 : term120 = term111.
Proof. exact (MK_COMB (@lem6949682) (@lem6949677)). Qed.
Lemma lem6949684 : term119 = term111.
Proof. exact (TRANS (@lem6949669) (@lem6949683)). Qed.
Lemma lem6949685 : term118 = term111.
Proof. exact (TRANS (@lem6949668) (@lem6949684)). Qed.
Lemma lem6949687 (x : real) : (term130 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6949688 : term111 = term53.
Proof. exact (@lem6949687 term53). Qed.
Lemma lem6949689 : term118 = term53.
Proof. exact (TRANS (@lem6949685) (@lem6949688)). Qed.
Lemma lem6949690 (_92591 : int) : (term71 _92591) = (term71 _92591).
Proof. exact (eq_refl (term71 _92591)). Qed.
Lemma lem6949691 (_92591 : int) : (term109 _92591) = (term131 _92591).
Proof. exact (MK_COMB (@lem6949690 _92591) (@lem6949689)). Qed.
Lemma lem6949692 (_92591 : int) : (term131 _92591) = (real_of_int _92591).
Proof. exact (@lem1982723 (real_of_int _92591)). Qed.
Lemma lem6949693 (_92591 : int) : (term109 _92591) = (real_of_int _92591).
Proof. exact (TRANS (@lem6949691 _92591) (@lem6949692 _92591)). Qed.
Lemma lem6949695 (_92591 : int) : (term108 _92591) = (real_of_int _92591).
Proof. exact (TRANS (@lem6949659 _92591) (@lem6949693 _92591)). Qed.
Lemma lem6949696 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6949697 (_92591 : int) : (term168 _92591) = (term95 _92591).
Proof. exact (MK_COMB (@lem6949696) (@lem6949695 _92591)). Qed.
Lemma lem6949698 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem6949699 (_92591 : int) : ((term108 _92591) = term53) = ((real_of_int _92591) = term53).
Proof. exact (MK_COMB (@lem6949697 _92591) (@lem6949698)). Qed.
Lemma lem6949700 (_92591 : int) : ((real_of_int _92591) = term53) = ((real_of_int _92591) = term53).
Proof. exact (TRANS (@lem6949653 _92591) (@lem6949699 _92591)). Qed.
Lemma lem6949701 (_92591 : int) : (term98 _92591) = (term169 _92591).
Proof. exact (@lem1988287 term53 (real_of_int _92591)). Qed.
Lemma lem6949707 (_92591 : int) : (term170 _92591) = (term171 _92591).
Proof. exact (@lem1982792 term53 (real_of_int _92591)). Qed.
Lemma lem6949712 (_92591 : int) : (term171 _92591) = (term172 _92591).
Proof. exact (@lem1982721 (term172 _92591)). Qed.
Lemma lem6949714 (_92591 : int) : (term170 _92591) = (term172 _92591).
Proof. exact (TRANS (@lem6949707 _92591) (@lem6949712 _92591)). Qed.
Lemma lem6949715 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6949716 (_92591 : int) : (term173 _92591) = (term174 _92591).
Proof. exact (MK_COMB (@lem6949715) (@lem6949714 _92591)). Qed.
Lemma lem6949717 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem6949718 (_92591 : int) : (term169 _92591) = (term175 _92591).
Proof. exact (MK_COMB (@lem6949716 _92591) (@lem6949717)). Qed.
Lemma lem6949719 (_92591 : int) : (term98 _92591) = (term175 _92591).
Proof. exact (TRANS (@lem6949701 _92591) (@lem6949718 _92591)). Qed.
Lemma lem6949720 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6949721 (_92591 : int) : (term99 _92591) = (term99 _92591).
Proof. exact (MK_COMB (@lem6949720) (@lem6949700 _92591)). Qed.
Lemma lem6949722 (_92591 : int) : (term100 _92591) = (term176 _92591).
Proof. exact (MK_COMB (@lem6949721 _92591) (@lem6949719 _92591)). Qed.
Lemma lem6949723 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6949724 (_92591 : int) : (term101 _92591) = (term177 _92591).
Proof. exact (MK_COMB (@lem6949723) (@lem6949652 _92591)). Qed.
Lemma lem6949725 (_92591 : int) : (term102 _92591) = (term178 _92591).
Proof. exact (MK_COMB (@lem6949724 _92591) (@lem6949722 _92591)). Qed.
Lemma lem6949726 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6949727 (_92591 : int) : (term103 _92591) = (term179 _92591).
Proof. exact (MK_COMB (@lem6949726) (@lem6949457 _92591)). Qed.
Lemma lem6949728 (_92591 : int) : (term104 _92591) = (term180 _92591).
Proof. exact (MK_COMB (@lem6949727 _92591) (@lem6949725 _92591)). Qed.
Lemma lem6949735 (_92591 : int) : (term106 _92591) = (term180 _92591).
Proof. exact (TRANS (@lem6949409 _92591) (@lem6949728 _92591)). Qed.
Lemma lem6949753 (_92591 : int) : (term178 _92591) = (term181 _92591).
Proof. exact (@lem19158 ((real_of_int _92591) = term53) (term167 _92591) (term175 _92591)). Qed.
Lemma lem6949754 (_92591 : int) : (term182 _92591) = (term183 _92591).
Proof. exact (@lem19367 (term165 _92591) (term163 _92591) (term175 _92591)). Qed.
Lemma lem6949755 (_92591 : int) : (term184 _92591) = (term184 _92591).
Proof. exact (eq_refl (term184 _92591)). Qed.
Lemma lem6949762 (_92591 : int) : (term185 _92591) = (term186 _92591).
Proof. exact (@lem19367 (term154 _92591) (term163 _92591) (term175 _92591)). Qed.
Lemma lem6949763 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6949764 (_92591 : int) : (term187 _92591) = (term188 _92591).
Proof. exact (MK_COMB (@lem6949763) (@lem6949762 _92591)). Qed.
Lemma lem6949765 (_92591 : int) : (term183 _92591) = (term189 _92591).
Proof. exact (MK_COMB (@lem6949764 _92591) (@lem6949755 _92591)). Qed.
Lemma lem6949766 (_92591 : int) : (term182 _92591) = (term189 _92591).
Proof. exact (TRANS (@lem6949754 _92591) (@lem6949765 _92591)). Qed.
Lemma lem6949767 (_92591 : int) : (term190 _92591) = (term191 _92591).
Proof. exact (@lem19367 (term165 _92591) (term163 _92591) ((real_of_int _92591) = term53)). Qed.
Lemma lem6949768 (_92591 : int) : (term192 _92591) = (term192 _92591).
Proof. exact (eq_refl (term192 _92591)). Qed.
Lemma lem6949775 (_92591 : int) : (term193 _92591) = (term194 _92591).
Proof. exact (@lem19367 (term154 _92591) (term163 _92591) ((real_of_int _92591) = term53)). Qed.
Lemma lem6949776 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6949777 (_92591 : int) : (term195 _92591) = (term196 _92591).
Proof. exact (MK_COMB (@lem6949776) (@lem6949775 _92591)). Qed.
Lemma lem6949778 (_92591 : int) : (term191 _92591) = (term197 _92591).
Proof. exact (MK_COMB (@lem6949777 _92591) (@lem6949768 _92591)). Qed.
Lemma lem6949779 (_92591 : int) : (term190 _92591) = (term197 _92591).
Proof. exact (TRANS (@lem6949767 _92591) (@lem6949778 _92591)). Qed.
Lemma lem6949780 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6949781 (_92591 : int) : (term198 _92591) = (term199 _92591).
Proof. exact (MK_COMB (@lem6949780) (@lem6949779 _92591)). Qed.
Lemma lem6949782 (_92591 : int) : (term181 _92591) = (term200 _92591).
Proof. exact (MK_COMB (@lem6949781 _92591) (@lem6949766 _92591)). Qed.
Lemma lem6949784 (_92591 : int) : (term178 _92591) = (term200 _92591).
Proof. exact (TRANS (@lem6949753 _92591) (@lem6949782 _92591)). Qed.
Lemma lem6949787 (_92591 : int) : (term179 _92591) = (term179 _92591).
Proof. exact (eq_refl (term179 _92591)). Qed.
Lemma lem6949788 (_92591 : int) : (term180 _92591) = (term201 _92591).
Proof. exact (MK_COMB (@lem6949787 _92591) (@lem6949784 _92591)). Qed.
Lemma lem6949789 (_92591 : int) : (term201 _92591) = (term202 _92591).
Proof. exact (@lem19158 (term197 _92591) (term134 _92591) (term189 _92591)). Qed.
Lemma lem6949790 (_92591 : int) : (term203 _92591) = (term204 _92591).
Proof. exact (@lem19158 (term186 _92591) (term134 _92591) (term184 _92591)). Qed.
Lemma lem6949791 (_92591 : int) : (term205 _92591) = (term205 _92591).
Proof. exact (eq_refl (term205 _92591)). Qed.
Lemma lem6949798 (_92591 : int) : (term206 _92591) = (term207 _92591).
Proof. exact (@lem19158 (term208 _92591) (term134 _92591) (term184 _92591)). Qed.
Lemma lem6949799 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6949800 (_92591 : int) : (term209 _92591) = (term210 _92591).
Proof. exact (MK_COMB (@lem6949799) (@lem6949798 _92591)). Qed.
Lemma lem6949801 (_92591 : int) : (term204 _92591) = (term211 _92591).
Proof. exact (MK_COMB (@lem6949800 _92591) (@lem6949791 _92591)). Qed.
Lemma lem6949802 (_92591 : int) : (term203 _92591) = (term211 _92591).
Proof. exact (TRANS (@lem6949790 _92591) (@lem6949801 _92591)). Qed.
Lemma lem6949803 (_92591 : int) : (term212 _92591) = (term213 _92591).
Proof. exact (@lem19158 (term194 _92591) (term134 _92591) (term192 _92591)). Qed.
Lemma lem6949804 (_92591 : int) : (term214 _92591) = (term214 _92591).
Proof. exact (eq_refl (term214 _92591)). Qed.
Lemma lem6949811 (_92591 : int) : (term215 _92591) = (term216 _92591).
Proof. exact (@lem19158 (term217 _92591) (term134 _92591) (term192 _92591)). Qed.
Lemma lem6949812 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6949813 (_92591 : int) : (term218 _92591) = (term219 _92591).
Proof. exact (MK_COMB (@lem6949812) (@lem6949811 _92591)). Qed.
Lemma lem6949814 (_92591 : int) : (term213 _92591) = (term220 _92591).
Proof. exact (MK_COMB (@lem6949813 _92591) (@lem6949804 _92591)). Qed.
Lemma lem6949815 (_92591 : int) : (term212 _92591) = (term220 _92591).
Proof. exact (TRANS (@lem6949803 _92591) (@lem6949814 _92591)). Qed.
Lemma lem6949816 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6949817 (_92591 : int) : (term221 _92591) = (term222 _92591).
Proof. exact (MK_COMB (@lem6949816) (@lem6949815 _92591)). Qed.
Lemma lem6949818 (_92591 : int) : (term202 _92591) = (term223 _92591).
Proof. exact (MK_COMB (@lem6949817 _92591) (@lem6949802 _92591)). Qed.
Lemma lem6949819 (_92591 : int) : (term201 _92591) = (term223 _92591).
Proof. exact (TRANS (@lem6949789 _92591) (@lem6949818 _92591)). Qed.
Lemma lem6949820 (_92591 : int) : (term180 _92591) = (term223 _92591).
Proof. exact (TRANS (@lem6949788 _92591) (@lem6949819 _92591)). Qed.
Lemma lem6949821 (_92591 : int) : (term106 _92591) = (term223 _92591).
Proof. exact (TRANS (@lem6949735 _92591) (@lem6949820 _92591)). Qed.
Lemma lem6949855 (_92591 : int) (h1 : term223 _92591) : term223 _92591.
Proof. exact (h1). Qed.
Lemma lem6949856 (_92591 : int) (h1 : term220 _92591) : term220 _92591.
Proof. exact (h1). Qed.
Lemma lem6949857 (_92591 : int) (h1 : term216 _92591) : term216 _92591.
Proof. exact (h1). Qed.
Lemma lem6949858 (_92591 : int) (h1 : term224 _92591) : term224 _92591.
Proof. exact (h1). Qed.
Lemma lem6949859 (_92591 : int) (h1 : term224 _92591) : term217 _92591.
Proof. exact (proj2 (@lem6949858 _92591 h1)). Qed.
Lemma lem6949861 (_92591 : int) (h1 : term224 _92591) : (real_of_int _92591) = term53.
Proof. exact (proj2 (@lem6949859 _92591 h1)). Qed.
Lemma lem6949862 (_92591 : int) (h1 : term224 _92591) : term154 _92591.
Proof. exact (proj1 (@lem6949859 _92591 h1)). Qed.
Lemma lem6949864 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6949865 : term225 = term226.
Proof. exact (@lem6949864 term53 term69). Qed.
Lemma lem6949867 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6949868 : term69 = term140.
Proof. exact (@lem6949867 term70). Qed.
Lemma lem6949870 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6949871 : term53 = term111.
Proof. exact (@lem6949870 (NUMERAL 0)). Qed.
Lemma lem6949872 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6949873 : term227 = term228.
Proof. exact (MK_COMB (@lem6949872) (@lem6949871)). Qed.
Lemma lem6949874 : term226 = term229.
Proof. exact (MK_COMB (@lem6949873) (@lem6949868)). Qed.
Lemma lem6949875 : term230.
Proof. exact (@lem1980255 term53 term69 term69 term69). Qed.
Lemma lem6949877 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6949878 : term226 = term232.
Proof. exact (@lem6949877 (NUMERAL 0) term70). Qed.
Lemma lem6949879 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6949880 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6949881 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6949880 h1) (fun h1 : term232 = True => @lem6949879)). Qed.
Lemma lem6949882 : term232 = True.
Proof. exact (EQ_MP (@lem6949881) (@lem6949879)). Qed.
Lemma lem6949883 : term226 = True.
Proof. exact (TRANS (@lem6949878) (@lem6949882)). Qed.
Lemma lem6949884 : True = term226.
Proof. exact (SYM (@lem6949883)). Qed.
Lemma lem6949885 : term226.
Proof. exact (EQ_MP (@lem6949884) (@lem0)). Qed.
Lemma lem6949886 : term234.
Proof. exact (@lem6949875 (@lem6949885)). Qed.
Lemma lem6949888 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6949889 : term226 = term232.
Proof. exact (@lem6949888 (NUMERAL 0) term70). Qed.
Lemma lem6949890 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6949891 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6949892 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6949891 h1) (fun h1 : term232 = True => @lem6949890)). Qed.
Lemma lem6949893 : term232 = True.
Proof. exact (EQ_MP (@lem6949892) (@lem6949890)). Qed.
Lemma lem6949894 : term226 = True.
Proof. exact (TRANS (@lem6949889) (@lem6949893)). Qed.
Lemma lem6949895 : True = term226.
Proof. exact (SYM (@lem6949894)). Qed.
Lemma lem6949896 : term226.
Proof. exact (EQ_MP (@lem6949895) (@lem0)). Qed.
Lemma lem6949897 : term229 = term235.
Proof. exact (@lem6949886 (@lem6949896)). Qed.
Lemma lem6949899 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6949900 : term123 = term124.
Proof. exact (@lem6949899 term70 term70). Qed.
Lemma lem6949901 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6949902 : term126 = term70.
Proof. exact (EQ_MP (@lem6949901) (@lem940073)). Qed.
Lemma lem6949903 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6949904 : term124 = term69.
Proof. exact (MK_COMB (@lem6949903) (@lem6949902)). Qed.
Lemma lem6949905 : term123 = term69.
Proof. exact (TRANS (@lem6949900) (@lem6949904)). Qed.
Lemma lem6949907 (x : nat) : (term236 x) = term53.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6949908 : term237 = term53.
Proof. exact (@lem6949907 term70). Qed.
Lemma lem6949909 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6949910 : term238 = term227.
Proof. exact (MK_COMB (@lem6949909) (@lem6949908)). Qed.
Lemma lem6949911 : term235 = term226.
Proof. exact (MK_COMB (@lem6949910) (@lem6949905)). Qed.
Lemma lem6949913 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6949914 : term226 = term232.
Proof. exact (@lem6949913 (NUMERAL 0) term70). Qed.
Lemma lem6949915 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6949916 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6949917 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6949916 h1) (fun h1 : term232 = True => @lem6949915)). Qed.
Lemma lem6949918 : term232 = True.
Proof. exact (EQ_MP (@lem6949917) (@lem6949915)). Qed.
Lemma lem6949919 : term226 = True.
Proof. exact (TRANS (@lem6949914) (@lem6949918)). Qed.
Lemma lem6949920 : term235 = True.
Proof. exact (TRANS (@lem6949911) (@lem6949919)). Qed.
Lemma lem6949921 : term229 = True.
Proof. exact (TRANS (@lem6949897) (@lem6949920)). Qed.
Lemma lem6949922 : term226 = True.
Proof. exact (TRANS (@lem6949874) (@lem6949921)). Qed.
Lemma lem6949923 : term225 = True.
Proof. exact (TRANS (@lem6949865) (@lem6949922)). Qed.
Lemma lem6949924 : True = term225.
Proof. exact (SYM (@lem6949923)). Qed.
Lemma lem6949925 : term225.
Proof. exact (EQ_MP (@lem6949924) (@lem0)). Qed.
Lemma lem6949926 (_92591 : int) (h1 : term224 _92591) : term239 _92591.
Proof. exact (conj (@lem6949925) (@lem6949862 _92591 h1)). Qed.
Lemma lem6949928 (x : real) (y : real) : term240 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6949929 (_92591 : int) : term241 _92591.
Proof. exact (@lem6949928 term69 (term150 _92591)). Qed.
Lemma lem6949930 (_92591 : int) (h1 : term224 _92591) : term242 _92591.
Proof. exact (@lem6949929 _92591 (@lem6949926 _92591 h1)). Qed.
Lemma lem6949931 (_92591 : int) : (term243 _92591) = (term150 _92591).
Proof. exact (@lem1982733 (term150 _92591)). Qed.
Lemma lem6949932 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6949933 (_92591 : int) : (term244 _92591) = (term153 _92591).
Proof. exact (MK_COMB (@lem6949932) (@lem6949931 _92591)). Qed.
Lemma lem6949934 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem6949935 (_92591 : int) : (term242 _92591) = (term154 _92591).
Proof. exact (MK_COMB (@lem6949933 _92591) (@lem6949934)). Qed.
Lemma lem6949936 (_92591 : int) (h1 : term224 _92591) : term154 _92591.
Proof. exact (EQ_MP (@lem6949935 _92591) (@lem6949930 _92591 h1)). Qed.
Lemma lem6949938 (y : real) : term245 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem6949939 (_92591 : int) : term246 _92591.
Proof. exact (@lem6949938 (real_of_int _92591)). Qed.
Lemma lem6949940 (_92591 : int) (h1 : term224 _92591) : term247 _92591.
Proof. exact (@lem6949939 _92591 (@lem6949861 _92591 h1)). Qed.
Lemma lem6949941 (_92591 : int) (h1 : term224 _92591) : term248 _92591.
Proof. exact (@lem6949940 _92591 h1 term69). Qed.
Lemma lem6949942 (_92591 : int) : (term248 _92591) = ((term249 _92591) = term53).
Proof. exact (eq_refl (term248 _92591)). Qed.
Lemma lem6949943 (_92591 : int) (h1 : term224 _92591) : (term249 _92591) = term53.
Proof. exact (EQ_MP (@lem6949942 _92591) (@lem6949941 _92591 h1)). Qed.
Lemma lem6949944 (_92591 : int) : (term249 _92591) = (real_of_int _92591).
Proof. exact (@lem1982733 (real_of_int _92591)). Qed.
Lemma lem6949945 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6949946 (_92591 : int) : (term250 _92591) = (term95 _92591).
Proof. exact (MK_COMB (@lem6949945) (@lem6949944 _92591)). Qed.
Lemma lem6949947 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem6949948 (_92591 : int) : ((term249 _92591) = term53) = ((real_of_int _92591) = term53).
Proof. exact (MK_COMB (@lem6949946 _92591) (@lem6949947)). Qed.
Lemma lem6949949 (_92591 : int) (h1 : term224 _92591) : (real_of_int _92591) = term53.
Proof. exact (EQ_MP (@lem6949948 _92591) (@lem6949943 _92591 h1)). Qed.
Lemma lem6949950 (_92591 : int) (h1 : term224 _92591) : term251 _92591.
Proof. exact (conj (@lem6949949 _92591 h1) (@lem6949936 _92591 h1)). Qed.
Lemma lem6949952 (x : real) (y : real) : term252 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem6949953 (_92591 : int) : term253 _92591.
Proof. exact (@lem6949952 (real_of_int _92591) (term150 _92591)). Qed.
Lemma lem6949954 (_92591 : int) (h1 : term224 _92591) : term254 _92591.
Proof. exact (@lem6949953 _92591 (@lem6949950 _92591 h1)). Qed.
Lemma lem6949955 (_92591 : int) : (term255 _92591) = (term256 _92591).
Proof. exact (@lem1982763 (real_of_int _92591) (term172 _92591) term114). Qed.
Lemma lem6949956 (_92591 : int) : (term257 _92591) = (term258 _92591).
Proof. exact (@lem1982715 term114 (real_of_int _92591)). Qed.
Lemma lem6949958 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6949959 : term69 = term140.
Proof. exact (@lem6949958 term70). Qed.
Lemma lem6949961 (x : nat) : (term112 x) = (term113 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6949962 : term114 = term115.
Proof. exact (@lem6949961 term70). Qed.
Lemma lem6949963 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6949964 : term259 = term260.
Proof. exact (MK_COMB (@lem6949963) (@lem6949962)). Qed.
Lemma lem6949965 : term261 = term262.
Proof. exact (MK_COMB (@lem6949964) (@lem6949959)). Qed.
Lemma lem6949966 : term263.
Proof. exact (@lem1981473 term114 term69 term69 term69 term53 term69). Qed.
Lemma lem6949968 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6949969 : term226 = term232.
Proof. exact (@lem6949968 (NUMERAL 0) term70). Qed.
Lemma lem6949970 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6949971 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6949972 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6949971 h1) (fun h1 : term232 = True => @lem6949970)). Qed.
Lemma lem6949973 : term232 = True.
Proof. exact (EQ_MP (@lem6949972) (@lem6949970)). Qed.
Lemma lem6949974 : term226 = True.
Proof. exact (TRANS (@lem6949969) (@lem6949973)). Qed.
Lemma lem6949975 : True = term226.
Proof. exact (SYM (@lem6949974)). Qed.
Lemma lem6949976 : term226.
Proof. exact (EQ_MP (@lem6949975) (@lem0)). Qed.
Lemma lem6949977 : term264.
Proof. exact (@lem6949966 (@lem6949976)). Qed.
Lemma lem6949979 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6949980 : term226 = term232.
Proof. exact (@lem6949979 (NUMERAL 0) term70). Qed.
Lemma lem6949981 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6949982 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6949983 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6949982 h1) (fun h1 : term232 = True => @lem6949981)). Qed.
Lemma lem6949984 : term232 = True.
Proof. exact (EQ_MP (@lem6949983) (@lem6949981)). Qed.
Lemma lem6949985 : term226 = True.
Proof. exact (TRANS (@lem6949980) (@lem6949984)). Qed.
Lemma lem6949986 : True = term226.
Proof. exact (SYM (@lem6949985)). Qed.
Lemma lem6949987 : term226.
Proof. exact (EQ_MP (@lem6949986) (@lem0)). Qed.
Lemma lem6949988 : term265.
Proof. exact (@lem6949977 (@lem6949987)). Qed.
Lemma lem6949990 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6949991 : term226 = term232.
Proof. exact (@lem6949990 (NUMERAL 0) term70). Qed.
Lemma lem6949992 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6949993 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6949994 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6949993 h1) (fun h1 : term232 = True => @lem6949992)). Qed.
Lemma lem6949995 : term232 = True.
Proof. exact (EQ_MP (@lem6949994) (@lem6949992)). Qed.
Lemma lem6949996 : term226 = True.
Proof. exact (TRANS (@lem6949991) (@lem6949995)). Qed.
Lemma lem6949997 : True = term226.
Proof. exact (SYM (@lem6949996)). Qed.
Lemma lem6949998 : term226.
Proof. exact (EQ_MP (@lem6949997) (@lem0)). Qed.
Lemma lem6949999 : term266.
Proof. exact (@lem6949988 (@lem6949998)). Qed.
Lemma lem6950001 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6950002 : term123 = term124.
Proof. exact (@lem6950001 term70 term70). Qed.
Lemma lem6950003 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6950004 : term126 = term70.
Proof. exact (EQ_MP (@lem6950003) (@lem940073)). Qed.
Lemma lem6950005 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6950006 : term124 = term69.
Proof. exact (MK_COMB (@lem6950005) (@lem6950004)). Qed.
Lemma lem6950007 : term123 = term69.
Proof. exact (TRANS (@lem6950002) (@lem6950006)). Qed.
Lemma lem6950009 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6950010 : term141 = term146.
Proof. exact (@lem6950009 term70 term70). Qed.
Lemma lem6950011 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6950012 : term126 = term70.
Proof. exact (EQ_MP (@lem6950011) (@lem940073)). Qed.
Lemma lem6950013 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6950014 : term124 = term69.
Proof. exact (MK_COMB (@lem6950013) (@lem6950012)). Qed.
Lemma lem6950015 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6950016 : term146 = term114.
Proof. exact (MK_COMB (@lem6950015) (@lem6950014)). Qed.
Lemma lem6950017 : term141 = term114.
Proof. exact (TRANS (@lem6950010) (@lem6950016)). Qed.
Lemma lem6950018 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6950019 : term267 = term259.
Proof. exact (MK_COMB (@lem6950018) (@lem6950017)). Qed.
Lemma lem6950020 : term268 = term261.
Proof. exact (MK_COMB (@lem6950019) (@lem6950007)). Qed.
Lemma lem6950022 (m : nat) : (term269 m) = term53.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6950023 : term261 = term53.
Proof. exact (@lem6950022 term70). Qed.
Lemma lem6950024 : term268 = term53.
Proof. exact (TRANS (@lem6950020) (@lem6950023)). Qed.
Lemma lem6950025 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6950026 : term270 = term271.
Proof. exact (MK_COMB (@lem6950025) (@lem6950024)). Qed.
Lemma lem6950027 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem6950028 : term272 = term237.
Proof. exact (MK_COMB (@lem6950026) (@lem6950027)). Qed.
Lemma lem6950030 (x : nat) : (term236 x) = term53.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6950031 : term237 = term53.
Proof. exact (@lem6950030 term70). Qed.
Lemma lem6950032 : term272 = term53.
Proof. exact (TRANS (@lem6950028) (@lem6950031)). Qed.
Lemma lem6950034 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6950035 : term123 = term124.
Proof. exact (@lem6950034 term70 term70). Qed.
Lemma lem6950036 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6950037 : term126 = term70.
Proof. exact (EQ_MP (@lem6950036) (@lem940073)). Qed.
Lemma lem6950038 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6950039 : term124 = term69.
Proof. exact (MK_COMB (@lem6950038) (@lem6950037)). Qed.
Lemma lem6950040 : term123 = term69.
Proof. exact (TRANS (@lem6950035) (@lem6950039)). Qed.
Lemma lem6950041 : term271 = term271.
Proof. exact (eq_refl term271). Qed.
Lemma lem6950042 : term273 = term237.
Proof. exact (MK_COMB (@lem6950041) (@lem6950040)). Qed.
Lemma lem6950044 (x : nat) : (term236 x) = term53.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6950045 : term237 = term53.
Proof. exact (@lem6950044 term70). Qed.
Lemma lem6950046 : term273 = term53.
Proof. exact (TRANS (@lem6950042) (@lem6950045)). Qed.
Lemma lem6950047 : term53 = term273.
Proof. exact (SYM (@lem6950046)). Qed.
Lemma lem6950048 : term272 = term273.
Proof. exact (TRANS (@lem6950032) (@lem6950047)). Qed.
Lemma lem6950049 : term262 = term111.
Proof. exact (@lem6949999 (@lem6950048)). Qed.
Lemma lem6950050 : term261 = term111.
Proof. exact (TRANS (@lem6949965) (@lem6950049)). Qed.
Lemma lem6950052 (x : real) : (term130 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6950053 : term111 = term53.
Proof. exact (@lem6950052 term53). Qed.
Lemma lem6950054 : term261 = term53.
Proof. exact (TRANS (@lem6950050) (@lem6950053)). Qed.
Lemma lem6950055 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6950056 : term274 = term271.
Proof. exact (MK_COMB (@lem6950055) (@lem6950054)). Qed.
Lemma lem6950057 (_92591 : int) : (real_of_int _92591) = (real_of_int _92591).
Proof. exact (eq_refl (real_of_int _92591)). Qed.
Lemma lem6950058 (_92591 : int) : (term258 _92591) = (term275 _92591).
Proof. exact (MK_COMB (@lem6950056) (@lem6950057 _92591)). Qed.
Lemma lem6950059 (_92591 : int) : (term257 _92591) = (term275 _92591).
Proof. exact (TRANS (@lem6949956 _92591) (@lem6950058 _92591)). Qed.
Lemma lem6950060 (_92591 : int) : (term275 _92591) = term53.
Proof. exact (@lem1982719 (real_of_int _92591)). Qed.
Lemma lem6950061 (_92591 : int) : (term257 _92591) = term53.
Proof. exact (TRANS (@lem6950059 _92591) (@lem6950060 _92591)). Qed.
Lemma lem6950062 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6950063 (_92591 : int) : (term276 _92591) = term84.
Proof. exact (MK_COMB (@lem6950062) (@lem6950061 _92591)). Qed.
Lemma lem6950064 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem6950065 (_92591 : int) : (term256 _92591) = term277.
Proof. exact (MK_COMB (@lem6950063 _92591) (@lem6950064)). Qed.
Lemma lem6950066 (_92591 : int) : (term255 _92591) = term277.
Proof. exact (TRANS (@lem6949955 _92591) (@lem6950065 _92591)). Qed.
Lemma lem6950067 : term277 = term114.
Proof. exact (@lem1982721 term114). Qed.
Lemma lem6950068 (_92591 : int) : (term255 _92591) = term114.
Proof. exact (TRANS (@lem6950066 _92591) (@lem6950067)). Qed.
Lemma lem6950069 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6950070 (_92591 : int) : (term278 _92591) = term279.
Proof. exact (MK_COMB (@lem6950069) (@lem6950068 _92591)). Qed.
Lemma lem6950071 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem6950072 (_92591 : int) : (term254 _92591) = term280.
Proof. exact (MK_COMB (@lem6950070 _92591) (@lem6950071)). Qed.
Lemma lem6950073 (_92591 : int) (h1 : term224 _92591) : term280.
Proof. exact (EQ_MP (@lem6950072 _92591) (@lem6949954 _92591 h1)). Qed.
Lemma lem6950075 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6950076 : term280 = term281.
Proof. exact (@lem6950075 term53 term114). Qed.
Lemma lem6950078 (x : nat) : (term112 x) = (term113 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6950079 : term114 = term115.
Proof. exact (@lem6950078 term70). Qed.
Lemma lem6950081 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6950082 : term53 = term111.
Proof. exact (@lem6950081 (NUMERAL 0)). Qed.
Lemma lem6950083 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6950084 : term55 = term282.
Proof. exact (MK_COMB (@lem6950083) (@lem6950082)). Qed.
Lemma lem6950085 : term281 = term283.
Proof. exact (MK_COMB (@lem6950084) (@lem6950079)). Qed.
Lemma lem6950086 : term284.
Proof. exact (@lem1980026 term53 term69 term114 term69). Qed.
Lemma lem6950088 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6950089 : term226 = term232.
Proof. exact (@lem6950088 (NUMERAL 0) term70). Qed.
Lemma lem6950090 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950091 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6950092 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950091 h1) (fun h1 : term232 = True => @lem6950090)). Qed.
Lemma lem6950093 : term232 = True.
Proof. exact (EQ_MP (@lem6950092) (@lem6950090)). Qed.
Lemma lem6950094 : term226 = True.
Proof. exact (TRANS (@lem6950089) (@lem6950093)). Qed.
Lemma lem6950095 : True = term226.
Proof. exact (SYM (@lem6950094)). Qed.
Lemma lem6950096 : term226.
Proof. exact (EQ_MP (@lem6950095) (@lem0)). Qed.
Lemma lem6950097 : term285.
Proof. exact (@lem6950086 (@lem6950096)). Qed.
Lemma lem6950099 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6950100 : term226 = term232.
Proof. exact (@lem6950099 (NUMERAL 0) term70). Qed.
Lemma lem6950101 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950102 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6950103 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950102 h1) (fun h1 : term232 = True => @lem6950101)). Qed.
Lemma lem6950104 : term232 = True.
Proof. exact (EQ_MP (@lem6950103) (@lem6950101)). Qed.
Lemma lem6950105 : term226 = True.
Proof. exact (TRANS (@lem6950100) (@lem6950104)). Qed.
Lemma lem6950106 : True = term226.
Proof. exact (SYM (@lem6950105)). Qed.
Lemma lem6950107 : term226.
Proof. exact (EQ_MP (@lem6950106) (@lem0)). Qed.
Lemma lem6950108 : term283 = term286.
Proof. exact (@lem6950097 (@lem6950107)). Qed.
Lemma lem6950110 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6950111 : term141 = term146.
Proof. exact (@lem6950110 term70 term70). Qed.
Lemma lem6950112 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6950113 : term126 = term70.
Proof. exact (EQ_MP (@lem6950112) (@lem940073)). Qed.
Lemma lem6950114 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6950115 : term124 = term69.
Proof. exact (MK_COMB (@lem6950114) (@lem6950113)). Qed.
Lemma lem6950116 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6950117 : term146 = term114.
Proof. exact (MK_COMB (@lem6950116) (@lem6950115)). Qed.
Lemma lem6950118 : term141 = term114.
Proof. exact (TRANS (@lem6950111) (@lem6950117)). Qed.
Lemma lem6950120 (x : nat) : (term236 x) = term53.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6950121 : term237 = term53.
Proof. exact (@lem6950120 term70). Qed.
Lemma lem6950122 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6950123 : term287 = term55.
Proof. exact (MK_COMB (@lem6950122) (@lem6950121)). Qed.
Lemma lem6950124 : term286 = term281.
Proof. exact (MK_COMB (@lem6950123) (@lem6950118)). Qed.
Lemma lem6950126 (m : nat) (n : nat) : (term288 m n) = (term289 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6950127 : term281 = term290.
Proof. exact (@lem6950126 (NUMERAL 0) term70). Qed.
Lemma lem6950128 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950129 (h1 : term233 = (BIT1 0)) : (term70 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6950130 : (term233 = (BIT1 0)) = ((term70 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950129 h1) (fun h1 : (term70 = (NUMERAL 0)) = False => @lem6950128)). Qed.
Lemma lem6950131 : (term70 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6950130) (@lem6950128)). Qed.
Lemma lem6950132 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6950133 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6950134 : term291 = (and True).
Proof. exact (MK_COMB (@lem6950133) (@lem6950132)). Qed.
Lemma lem6950135 : term290 = (True /\ False).
Proof. exact (MK_COMB (@lem6950134) (@lem6950131)). Qed.
Lemma lem6950137 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6950138 : term290 = False.
Proof. exact (TRANS (@lem6950135) (@lem6950137)). Qed.
Lemma lem6950139 : term281 = False.
Proof. exact (TRANS (@lem6950127) (@lem6950138)). Qed.
Lemma lem6950140 : term286 = False.
Proof. exact (TRANS (@lem6950124) (@lem6950139)). Qed.
Lemma lem6950141 : term283 = False.
Proof. exact (TRANS (@lem6950108) (@lem6950140)). Qed.
Lemma lem6950142 : term281 = False.
Proof. exact (TRANS (@lem6950085) (@lem6950141)). Qed.
Lemma lem6950143 : term280 = False.
Proof. exact (TRANS (@lem6950076) (@lem6950142)). Qed.
Lemma lem6950144 (_92591 : int) (h1 : term224 _92591) : False.
Proof. exact (EQ_MP (@lem6950143) (@lem6950073 _92591 h1)). Qed.
Lemma lem6950145 (_92591 : int) (h1 : term214 _92591) : term214 _92591.
Proof. exact (h1). Qed.
Lemma lem6950146 (_92591 : int) (h1 : term214 _92591) : term192 _92591.
Proof. exact (proj2 (@lem6950145 _92591 h1)). Qed.
Lemma lem6950148 (_92591 : int) (h1 : term214 _92591) : (real_of_int _92591) = term53.
Proof. exact (proj2 (@lem6950146 _92591 h1)). Qed.
Lemma lem6950149 (_92591 : int) (h1 : term214 _92591) : term163 _92591.
Proof. exact (proj1 (@lem6950146 _92591 h1)). Qed.
Lemma lem6950151 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6950152 : term225 = term226.
Proof. exact (@lem6950151 term53 term69). Qed.
Lemma lem6950154 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6950155 : term69 = term140.
Proof. exact (@lem6950154 term70). Qed.
Lemma lem6950157 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6950158 : term53 = term111.
Proof. exact (@lem6950157 (NUMERAL 0)). Qed.
Lemma lem6950159 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6950160 : term227 = term228.
Proof. exact (MK_COMB (@lem6950159) (@lem6950158)). Qed.
Lemma lem6950161 : term226 = term229.
Proof. exact (MK_COMB (@lem6950160) (@lem6950155)). Qed.
Lemma lem6950162 : term230.
Proof. exact (@lem1980255 term53 term69 term69 term69). Qed.
Lemma lem6950164 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6950165 : term226 = term232.
Proof. exact (@lem6950164 (NUMERAL 0) term70). Qed.
Lemma lem6950166 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950167 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6950168 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950167 h1) (fun h1 : term232 = True => @lem6950166)). Qed.
Lemma lem6950169 : term232 = True.
Proof. exact (EQ_MP (@lem6950168) (@lem6950166)). Qed.
Lemma lem6950170 : term226 = True.
Proof. exact (TRANS (@lem6950165) (@lem6950169)). Qed.
Lemma lem6950171 : True = term226.
Proof. exact (SYM (@lem6950170)). Qed.
Lemma lem6950172 : term226.
Proof. exact (EQ_MP (@lem6950171) (@lem0)). Qed.
Lemma lem6950173 : term234.
Proof. exact (@lem6950162 (@lem6950172)). Qed.
Lemma lem6950175 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6950176 : term226 = term232.
Proof. exact (@lem6950175 (NUMERAL 0) term70). Qed.
Lemma lem6950177 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950178 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6950179 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950178 h1) (fun h1 : term232 = True => @lem6950177)). Qed.
Lemma lem6950180 : term232 = True.
Proof. exact (EQ_MP (@lem6950179) (@lem6950177)). Qed.
Lemma lem6950181 : term226 = True.
Proof. exact (TRANS (@lem6950176) (@lem6950180)). Qed.
Lemma lem6950182 : True = term226.
Proof. exact (SYM (@lem6950181)). Qed.
Lemma lem6950183 : term226.
Proof. exact (EQ_MP (@lem6950182) (@lem0)). Qed.
Lemma lem6950184 : term229 = term235.
Proof. exact (@lem6950173 (@lem6950183)). Qed.
Lemma lem6950186 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6950187 : term123 = term124.
Proof. exact (@lem6950186 term70 term70). Qed.
Lemma lem6950188 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6950189 : term126 = term70.
Proof. exact (EQ_MP (@lem6950188) (@lem940073)). Qed.
Lemma lem6950190 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6950191 : term124 = term69.
Proof. exact (MK_COMB (@lem6950190) (@lem6950189)). Qed.
Lemma lem6950192 : term123 = term69.
Proof. exact (TRANS (@lem6950187) (@lem6950191)). Qed.
Lemma lem6950194 (x : nat) : (term236 x) = term53.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6950195 : term237 = term53.
Proof. exact (@lem6950194 term70). Qed.
Lemma lem6950196 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6950197 : term238 = term227.
Proof. exact (MK_COMB (@lem6950196) (@lem6950195)). Qed.
Lemma lem6950198 : term235 = term226.
Proof. exact (MK_COMB (@lem6950197) (@lem6950192)). Qed.
Lemma lem6950200 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6950201 : term226 = term232.
Proof. exact (@lem6950200 (NUMERAL 0) term70). Qed.
Lemma lem6950202 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950203 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6950204 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950203 h1) (fun h1 : term232 = True => @lem6950202)). Qed.
Lemma lem6950205 : term232 = True.
Proof. exact (EQ_MP (@lem6950204) (@lem6950202)). Qed.
Lemma lem6950206 : term226 = True.
Proof. exact (TRANS (@lem6950201) (@lem6950205)). Qed.
Lemma lem6950207 : term235 = True.
Proof. exact (TRANS (@lem6950198) (@lem6950206)). Qed.
Lemma lem6950208 : term229 = True.
Proof. exact (TRANS (@lem6950184) (@lem6950207)). Qed.
Lemma lem6950209 : term226 = True.
Proof. exact (TRANS (@lem6950161) (@lem6950208)). Qed.
Lemma lem6950210 : term225 = True.
Proof. exact (TRANS (@lem6950152) (@lem6950209)). Qed.
Lemma lem6950211 : True = term225.
Proof. exact (SYM (@lem6950210)). Qed.
Lemma lem6950212 : term225.
Proof. exact (EQ_MP (@lem6950211) (@lem0)). Qed.
Lemma lem6950213 (_92591 : int) (h1 : term214 _92591) : term292 _92591.
Proof. exact (conj (@lem6950212) (@lem6950149 _92591 h1)). Qed.
Lemma lem6950215 (x : real) (y : real) : term240 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6950216 (_92591 : int) : term293 _92591.
Proof. exact (@lem6950215 term69 (term160 _92591)). Qed.
Lemma lem6950217 (_92591 : int) (h1 : term214 _92591) : term294 _92591.
Proof. exact (@lem6950216 _92591 (@lem6950213 _92591 h1)). Qed.
Lemma lem6950218 (_92591 : int) : (term295 _92591) = (term160 _92591).
Proof. exact (@lem1982733 (term160 _92591)). Qed.
Lemma lem6950219 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6950220 (_92591 : int) : (term296 _92591) = (term162 _92591).
Proof. exact (MK_COMB (@lem6950219) (@lem6950218 _92591)). Qed.
Lemma lem6950221 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem6950222 (_92591 : int) : (term294 _92591) = (term163 _92591).
Proof. exact (MK_COMB (@lem6950220 _92591) (@lem6950221)). Qed.
Lemma lem6950223 (_92591 : int) (h1 : term214 _92591) : term163 _92591.
Proof. exact (EQ_MP (@lem6950222 _92591) (@lem6950217 _92591 h1)). Qed.
Lemma lem6950225 (y : real) : term245 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem6950226 (_92591 : int) : term246 _92591.
Proof. exact (@lem6950225 (real_of_int _92591)). Qed.
Lemma lem6950227 (_92591 : int) (h1 : term214 _92591) : term247 _92591.
Proof. exact (@lem6950226 _92591 (@lem6950148 _92591 h1)). Qed.
Lemma lem6950228 (_92591 : int) (h1 : term214 _92591) : term297 _92591.
Proof. exact (@lem6950227 _92591 h1 term114). Qed.
Lemma lem6950229 (_92591 : int) : (term297 _92591) = ((term172 _92591) = term53).
Proof. exact (eq_refl (term297 _92591)). Qed.
Lemma lem6950236 (_92591 : int) (h1 : term214 _92591) : (term172 _92591) = term53.
Proof. exact (EQ_MP (@lem6950229 _92591) (@lem6950228 _92591 h1)). Qed.
Lemma lem6950237 (_92591 : int) (h1 : term214 _92591) : term298 _92591.
Proof. exact (conj (@lem6950236 _92591 h1) (@lem6950223 _92591 h1)). Qed.
Lemma lem6950239 (x : real) (y : real) : term252 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem6950240 (_92591 : int) : term299 _92591.
Proof. exact (@lem6950239 (term172 _92591) (term160 _92591)). Qed.
Lemma lem6950241 (_92591 : int) (h1 : term214 _92591) : term300 _92591.
Proof. exact (@lem6950240 _92591 (@lem6950237 _92591 h1)). Qed.
Lemma lem6950242 (_92591 : int) : (term301 _92591) = (term302 _92591).
Proof. exact (@lem1982763 (term172 _92591) (real_of_int _92591) term114). Qed.
Lemma lem6950243 (_92591 : int) : (term303 _92591) = (term258 _92591).
Proof. exact (@lem1982713 term114 (real_of_int _92591)). Qed.
Lemma lem6950245 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6950246 : term69 = term140.
Proof. exact (@lem6950245 term70). Qed.
Lemma lem6950248 (x : nat) : (term112 x) = (term113 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6950249 : term114 = term115.
Proof. exact (@lem6950248 term70). Qed.
Lemma lem6950250 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6950251 : term259 = term260.
Proof. exact (MK_COMB (@lem6950250) (@lem6950249)). Qed.
Lemma lem6950252 : term261 = term262.
Proof. exact (MK_COMB (@lem6950251) (@lem6950246)). Qed.
Lemma lem6950253 : term263.
Proof. exact (@lem1981473 term114 term69 term69 term69 term53 term69). Qed.
Lemma lem6950255 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6950256 : term226 = term232.
Proof. exact (@lem6950255 (NUMERAL 0) term70). Qed.
Lemma lem6950257 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950258 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6950259 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950258 h1) (fun h1 : term232 = True => @lem6950257)). Qed.
Lemma lem6950260 : term232 = True.
Proof. exact (EQ_MP (@lem6950259) (@lem6950257)). Qed.
Lemma lem6950261 : term226 = True.
Proof. exact (TRANS (@lem6950256) (@lem6950260)). Qed.
Lemma lem6950262 : True = term226.
Proof. exact (SYM (@lem6950261)). Qed.
Lemma lem6950263 : term226.
Proof. exact (EQ_MP (@lem6950262) (@lem0)). Qed.
Lemma lem6950264 : term264.
Proof. exact (@lem6950253 (@lem6950263)). Qed.
Lemma lem6950266 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6950267 : term226 = term232.
Proof. exact (@lem6950266 (NUMERAL 0) term70). Qed.
Lemma lem6950268 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950269 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6950270 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950269 h1) (fun h1 : term232 = True => @lem6950268)). Qed.
Lemma lem6950271 : term232 = True.
Proof. exact (EQ_MP (@lem6950270) (@lem6950268)). Qed.
Lemma lem6950272 : term226 = True.
Proof. exact (TRANS (@lem6950267) (@lem6950271)). Qed.
Lemma lem6950273 : True = term226.
Proof. exact (SYM (@lem6950272)). Qed.
Lemma lem6950274 : term226.
Proof. exact (EQ_MP (@lem6950273) (@lem0)). Qed.
Lemma lem6950275 : term265.
Proof. exact (@lem6950264 (@lem6950274)). Qed.
Lemma lem6950277 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6950278 : term226 = term232.
Proof. exact (@lem6950277 (NUMERAL 0) term70). Qed.
Lemma lem6950279 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950280 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6950281 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950280 h1) (fun h1 : term232 = True => @lem6950279)). Qed.
Lemma lem6950282 : term232 = True.
Proof. exact (EQ_MP (@lem6950281) (@lem6950279)). Qed.
Lemma lem6950283 : term226 = True.
Proof. exact (TRANS (@lem6950278) (@lem6950282)). Qed.
Lemma lem6950284 : True = term226.
Proof. exact (SYM (@lem6950283)). Qed.
Lemma lem6950285 : term226.
Proof. exact (EQ_MP (@lem6950284) (@lem0)). Qed.
Lemma lem6950286 : term266.
Proof. exact (@lem6950275 (@lem6950285)). Qed.
Lemma lem6950288 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6950289 : term123 = term124.
Proof. exact (@lem6950288 term70 term70). Qed.
Lemma lem6950290 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6950291 : term126 = term70.
Proof. exact (EQ_MP (@lem6950290) (@lem940073)). Qed.
Lemma lem6950292 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6950293 : term124 = term69.
Proof. exact (MK_COMB (@lem6950292) (@lem6950291)). Qed.
Lemma lem6950294 : term123 = term69.
Proof. exact (TRANS (@lem6950289) (@lem6950293)). Qed.
Lemma lem6950296 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6950297 : term141 = term146.
Proof. exact (@lem6950296 term70 term70). Qed.
Lemma lem6950298 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6950299 : term126 = term70.
Proof. exact (EQ_MP (@lem6950298) (@lem940073)). Qed.
Lemma lem6950300 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6950301 : term124 = term69.
Proof. exact (MK_COMB (@lem6950300) (@lem6950299)). Qed.
Lemma lem6950302 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6950303 : term146 = term114.
Proof. exact (MK_COMB (@lem6950302) (@lem6950301)). Qed.
Lemma lem6950304 : term141 = term114.
Proof. exact (TRANS (@lem6950297) (@lem6950303)). Qed.
Lemma lem6950305 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6950306 : term267 = term259.
Proof. exact (MK_COMB (@lem6950305) (@lem6950304)). Qed.
Lemma lem6950307 : term268 = term261.
Proof. exact (MK_COMB (@lem6950306) (@lem6950294)). Qed.
Lemma lem6950309 (m : nat) : (term269 m) = term53.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6950310 : term261 = term53.
Proof. exact (@lem6950309 term70). Qed.
Lemma lem6950311 : term268 = term53.
Proof. exact (TRANS (@lem6950307) (@lem6950310)). Qed.
Lemma lem6950312 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6950313 : term270 = term271.
Proof. exact (MK_COMB (@lem6950312) (@lem6950311)). Qed.
Lemma lem6950314 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem6950315 : term272 = term237.
Proof. exact (MK_COMB (@lem6950313) (@lem6950314)). Qed.
Lemma lem6950317 (x : nat) : (term236 x) = term53.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6950318 : term237 = term53.
Proof. exact (@lem6950317 term70). Qed.
Lemma lem6950319 : term272 = term53.
Proof. exact (TRANS (@lem6950315) (@lem6950318)). Qed.
Lemma lem6950321 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6950322 : term123 = term124.
Proof. exact (@lem6950321 term70 term70). Qed.
Lemma lem6950323 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6950324 : term126 = term70.
Proof. exact (EQ_MP (@lem6950323) (@lem940073)). Qed.
Lemma lem6950325 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6950326 : term124 = term69.
Proof. exact (MK_COMB (@lem6950325) (@lem6950324)). Qed.
Lemma lem6950327 : term123 = term69.
Proof. exact (TRANS (@lem6950322) (@lem6950326)). Qed.
Lemma lem6950328 : term271 = term271.
Proof. exact (eq_refl term271). Qed.
Lemma lem6950329 : term273 = term237.
Proof. exact (MK_COMB (@lem6950328) (@lem6950327)). Qed.
Lemma lem6950331 (x : nat) : (term236 x) = term53.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6950332 : term237 = term53.
Proof. exact (@lem6950331 term70). Qed.
Lemma lem6950333 : term273 = term53.
Proof. exact (TRANS (@lem6950329) (@lem6950332)). Qed.
Lemma lem6950334 : term53 = term273.
Proof. exact (SYM (@lem6950333)). Qed.
Lemma lem6950335 : term272 = term273.
Proof. exact (TRANS (@lem6950319) (@lem6950334)). Qed.
Lemma lem6950336 : term262 = term111.
Proof. exact (@lem6950286 (@lem6950335)). Qed.
Lemma lem6950337 : term261 = term111.
Proof. exact (TRANS (@lem6950252) (@lem6950336)). Qed.
Lemma lem6950339 (x : real) : (term130 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6950340 : term111 = term53.
Proof. exact (@lem6950339 term53). Qed.
Lemma lem6950341 : term261 = term53.
Proof. exact (TRANS (@lem6950337) (@lem6950340)). Qed.
Lemma lem6950342 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6950343 : term274 = term271.
Proof. exact (MK_COMB (@lem6950342) (@lem6950341)). Qed.
Lemma lem6950344 (_92591 : int) : (real_of_int _92591) = (real_of_int _92591).
Proof. exact (eq_refl (real_of_int _92591)). Qed.
Lemma lem6950345 (_92591 : int) : (term258 _92591) = (term275 _92591).
Proof. exact (MK_COMB (@lem6950343) (@lem6950344 _92591)). Qed.
Lemma lem6950346 (_92591 : int) : (term303 _92591) = (term275 _92591).
Proof. exact (TRANS (@lem6950243 _92591) (@lem6950345 _92591)). Qed.
Lemma lem6950347 (_92591 : int) : (term275 _92591) = term53.
Proof. exact (@lem1982719 (real_of_int _92591)). Qed.
Lemma lem6950348 (_92591 : int) : (term303 _92591) = term53.
Proof. exact (TRANS (@lem6950346 _92591) (@lem6950347 _92591)). Qed.
Lemma lem6950349 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6950350 (_92591 : int) : (term304 _92591) = term84.
Proof. exact (MK_COMB (@lem6950349) (@lem6950348 _92591)). Qed.
Lemma lem6950351 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem6950352 (_92591 : int) : (term302 _92591) = term277.
Proof. exact (MK_COMB (@lem6950350 _92591) (@lem6950351)). Qed.
Lemma lem6950353 (_92591 : int) : (term301 _92591) = term277.
Proof. exact (TRANS (@lem6950242 _92591) (@lem6950352 _92591)). Qed.
Lemma lem6950354 : term277 = term114.
Proof. exact (@lem1982721 term114). Qed.
Lemma lem6950355 (_92591 : int) : (term301 _92591) = term114.
Proof. exact (TRANS (@lem6950353 _92591) (@lem6950354)). Qed.
Lemma lem6950356 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6950357 (_92591 : int) : (term305 _92591) = term279.
Proof. exact (MK_COMB (@lem6950356) (@lem6950355 _92591)). Qed.
Lemma lem6950358 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem6950359 (_92591 : int) : (term300 _92591) = term280.
Proof. exact (MK_COMB (@lem6950357 _92591) (@lem6950358)). Qed.
Lemma lem6950360 (_92591 : int) (h1 : term214 _92591) : term280.
Proof. exact (EQ_MP (@lem6950359 _92591) (@lem6950241 _92591 h1)). Qed.
Lemma lem6950362 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6950363 : term280 = term281.
Proof. exact (@lem6950362 term53 term114). Qed.
Lemma lem6950365 (x : nat) : (term112 x) = (term113 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6950366 : term114 = term115.
Proof. exact (@lem6950365 term70). Qed.
Lemma lem6950368 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6950369 : term53 = term111.
Proof. exact (@lem6950368 (NUMERAL 0)). Qed.
Lemma lem6950370 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6950371 : term55 = term282.
Proof. exact (MK_COMB (@lem6950370) (@lem6950369)). Qed.
Lemma lem6950372 : term281 = term283.
Proof. exact (MK_COMB (@lem6950371) (@lem6950366)). Qed.
Lemma lem6950373 : term284.
Proof. exact (@lem1980026 term53 term69 term114 term69). Qed.
Lemma lem6950375 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6950376 : term226 = term232.
Proof. exact (@lem6950375 (NUMERAL 0) term70). Qed.
Lemma lem6950377 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950378 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6950379 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950378 h1) (fun h1 : term232 = True => @lem6950377)). Qed.
Lemma lem6950380 : term232 = True.
Proof. exact (EQ_MP (@lem6950379) (@lem6950377)). Qed.
Lemma lem6950381 : term226 = True.
Proof. exact (TRANS (@lem6950376) (@lem6950380)). Qed.
Lemma lem6950382 : True = term226.
Proof. exact (SYM (@lem6950381)). Qed.
Lemma lem6950383 : term226.
Proof. exact (EQ_MP (@lem6950382) (@lem0)). Qed.
Lemma lem6950384 : term285.
Proof. exact (@lem6950373 (@lem6950383)). Qed.
Lemma lem6950386 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6950387 : term226 = term232.
Proof. exact (@lem6950386 (NUMERAL 0) term70). Qed.
Lemma lem6950388 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950389 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6950390 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950389 h1) (fun h1 : term232 = True => @lem6950388)). Qed.
Lemma lem6950391 : term232 = True.
Proof. exact (EQ_MP (@lem6950390) (@lem6950388)). Qed.
Lemma lem6950392 : term226 = True.
Proof. exact (TRANS (@lem6950387) (@lem6950391)). Qed.
Lemma lem6950393 : True = term226.
Proof. exact (SYM (@lem6950392)). Qed.
Lemma lem6950394 : term226.
Proof. exact (EQ_MP (@lem6950393) (@lem0)). Qed.
Lemma lem6950395 : term283 = term286.
Proof. exact (@lem6950384 (@lem6950394)). Qed.
Lemma lem6950397 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6950398 : term141 = term146.
Proof. exact (@lem6950397 term70 term70). Qed.
Lemma lem6950399 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6950400 : term126 = term70.
Proof. exact (EQ_MP (@lem6950399) (@lem940073)). Qed.
Lemma lem6950401 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6950402 : term124 = term69.
Proof. exact (MK_COMB (@lem6950401) (@lem6950400)). Qed.
Lemma lem6950403 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6950404 : term146 = term114.
Proof. exact (MK_COMB (@lem6950403) (@lem6950402)). Qed.
Lemma lem6950405 : term141 = term114.
Proof. exact (TRANS (@lem6950398) (@lem6950404)). Qed.
Lemma lem6950407 (x : nat) : (term236 x) = term53.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6950408 : term237 = term53.
Proof. exact (@lem6950407 term70). Qed.
Lemma lem6950409 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6950410 : term287 = term55.
Proof. exact (MK_COMB (@lem6950409) (@lem6950408)). Qed.
Lemma lem6950411 : term286 = term281.
Proof. exact (MK_COMB (@lem6950410) (@lem6950405)). Qed.
Lemma lem6950413 (m : nat) (n : nat) : (term288 m n) = (term289 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6950414 : term281 = term290.
Proof. exact (@lem6950413 (NUMERAL 0) term70). Qed.
Lemma lem6950415 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950416 (h1 : term233 = (BIT1 0)) : (term70 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6950417 : (term233 = (BIT1 0)) = ((term70 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950416 h1) (fun h1 : (term70 = (NUMERAL 0)) = False => @lem6950415)). Qed.
Lemma lem6950418 : (term70 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6950417) (@lem6950415)). Qed.
Lemma lem6950419 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6950420 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6950421 : term291 = (and True).
Proof. exact (MK_COMB (@lem6950420) (@lem6950419)). Qed.
Lemma lem6950422 : term290 = (True /\ False).
Proof. exact (MK_COMB (@lem6950421) (@lem6950418)). Qed.
Lemma lem6950424 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6950425 : term290 = False.
Proof. exact (TRANS (@lem6950422) (@lem6950424)). Qed.
Lemma lem6950426 : term281 = False.
Proof. exact (TRANS (@lem6950414) (@lem6950425)). Qed.
Lemma lem6950427 : term286 = False.
Proof. exact (TRANS (@lem6950411) (@lem6950426)). Qed.
Lemma lem6950428 : term283 = False.
Proof. exact (TRANS (@lem6950395) (@lem6950427)). Qed.
Lemma lem6950429 : term281 = False.
Proof. exact (TRANS (@lem6950372) (@lem6950428)). Qed.
Lemma lem6950430 : term280 = False.
Proof. exact (TRANS (@lem6950363) (@lem6950429)). Qed.
Lemma lem6950431 (_92591 : int) (h1 : term214 _92591) : False.
Proof. exact (EQ_MP (@lem6950430) (@lem6950360 _92591 h1)). Qed.
Lemma lem6950432 (_92591 : int) (h1 : term216 _92591) : False.
Proof. exact (or_elim (@lem6949857 _92591 h1) (fun h0 : term224 _92591 => @lem6950144 _92591 h0) (fun h0 : term214 _92591 => @lem6950431 _92591 h0)). Qed.
Lemma lem6950433 (_92591 : int) (h1 : term214 _92591) : term214 _92591.
Proof. exact (h1). Qed.
Lemma lem6950434 (_92591 : int) (h1 : term214 _92591) : term192 _92591.
Proof. exact (proj2 (@lem6950433 _92591 h1)). Qed.
Lemma lem6950436 (_92591 : int) (h1 : term214 _92591) : (real_of_int _92591) = term53.
Proof. exact (proj2 (@lem6950434 _92591 h1)). Qed.
Lemma lem6950437 (_92591 : int) (h1 : term214 _92591) : term163 _92591.
Proof. exact (proj1 (@lem6950434 _92591 h1)). Qed.
Lemma lem6950439 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6950440 : term225 = term226.
Proof. exact (@lem6950439 term53 term69). Qed.
Lemma lem6950442 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6950443 : term69 = term140.
Proof. exact (@lem6950442 term70). Qed.
Lemma lem6950445 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6950446 : term53 = term111.
Proof. exact (@lem6950445 (NUMERAL 0)). Qed.
Lemma lem6950447 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6950448 : term227 = term228.
Proof. exact (MK_COMB (@lem6950447) (@lem6950446)). Qed.
Lemma lem6950449 : term226 = term229.
Proof. exact (MK_COMB (@lem6950448) (@lem6950443)). Qed.
Lemma lem6950450 : term230.
Proof. exact (@lem1980255 term53 term69 term69 term69). Qed.
Lemma lem6950452 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6950453 : term226 = term232.
Proof. exact (@lem6950452 (NUMERAL 0) term70). Qed.
Lemma lem6950454 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950455 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6950456 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950455 h1) (fun h1 : term232 = True => @lem6950454)). Qed.
Lemma lem6950457 : term232 = True.
Proof. exact (EQ_MP (@lem6950456) (@lem6950454)). Qed.
Lemma lem6950458 : term226 = True.
Proof. exact (TRANS (@lem6950453) (@lem6950457)). Qed.
Lemma lem6950459 : True = term226.
Proof. exact (SYM (@lem6950458)). Qed.
Lemma lem6950460 : term226.
Proof. exact (EQ_MP (@lem6950459) (@lem0)). Qed.
Lemma lem6950461 : term234.
Proof. exact (@lem6950450 (@lem6950460)). Qed.
Lemma lem6950463 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6950464 : term226 = term232.
Proof. exact (@lem6950463 (NUMERAL 0) term70). Qed.
Lemma lem6950465 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950466 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6950467 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950466 h1) (fun h1 : term232 = True => @lem6950465)). Qed.
Lemma lem6950468 : term232 = True.
Proof. exact (EQ_MP (@lem6950467) (@lem6950465)). Qed.
Lemma lem6950469 : term226 = True.
Proof. exact (TRANS (@lem6950464) (@lem6950468)). Qed.
Lemma lem6950470 : True = term226.
Proof. exact (SYM (@lem6950469)). Qed.
Lemma lem6950471 : term226.
Proof. exact (EQ_MP (@lem6950470) (@lem0)). Qed.
Lemma lem6950472 : term229 = term235.
Proof. exact (@lem6950461 (@lem6950471)). Qed.
Lemma lem6950474 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6950475 : term123 = term124.
Proof. exact (@lem6950474 term70 term70). Qed.
Lemma lem6950476 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6950477 : term126 = term70.
Proof. exact (EQ_MP (@lem6950476) (@lem940073)). Qed.
Lemma lem6950478 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6950479 : term124 = term69.
Proof. exact (MK_COMB (@lem6950478) (@lem6950477)). Qed.
Lemma lem6950480 : term123 = term69.
Proof. exact (TRANS (@lem6950475) (@lem6950479)). Qed.
Lemma lem6950482 (x : nat) : (term236 x) = term53.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6950483 : term237 = term53.
Proof. exact (@lem6950482 term70). Qed.
Lemma lem6950484 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6950485 : term238 = term227.
Proof. exact (MK_COMB (@lem6950484) (@lem6950483)). Qed.
Lemma lem6950486 : term235 = term226.
Proof. exact (MK_COMB (@lem6950485) (@lem6950480)). Qed.
Lemma lem6950488 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6950489 : term226 = term232.
Proof. exact (@lem6950488 (NUMERAL 0) term70). Qed.
Lemma lem6950490 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950491 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6950492 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950491 h1) (fun h1 : term232 = True => @lem6950490)). Qed.
Lemma lem6950493 : term232 = True.
Proof. exact (EQ_MP (@lem6950492) (@lem6950490)). Qed.
Lemma lem6950494 : term226 = True.
Proof. exact (TRANS (@lem6950489) (@lem6950493)). Qed.
Lemma lem6950495 : term235 = True.
Proof. exact (TRANS (@lem6950486) (@lem6950494)). Qed.
Lemma lem6950496 : term229 = True.
Proof. exact (TRANS (@lem6950472) (@lem6950495)). Qed.
Lemma lem6950497 : term226 = True.
Proof. exact (TRANS (@lem6950449) (@lem6950496)). Qed.
Lemma lem6950498 : term225 = True.
Proof. exact (TRANS (@lem6950440) (@lem6950497)). Qed.
Lemma lem6950499 : True = term225.
Proof. exact (SYM (@lem6950498)). Qed.
Lemma lem6950500 : term225.
Proof. exact (EQ_MP (@lem6950499) (@lem0)). Qed.
Lemma lem6950501 (_92591 : int) (h1 : term214 _92591) : term292 _92591.
Proof. exact (conj (@lem6950500) (@lem6950437 _92591 h1)). Qed.
Lemma lem6950503 (x : real) (y : real) : term240 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6950504 (_92591 : int) : term293 _92591.
Proof. exact (@lem6950503 term69 (term160 _92591)). Qed.
Lemma lem6950505 (_92591 : int) (h1 : term214 _92591) : term294 _92591.
Proof. exact (@lem6950504 _92591 (@lem6950501 _92591 h1)). Qed.
Lemma lem6950506 (_92591 : int) : (term295 _92591) = (term160 _92591).
Proof. exact (@lem1982733 (term160 _92591)). Qed.
Lemma lem6950507 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6950508 (_92591 : int) : (term296 _92591) = (term162 _92591).
Proof. exact (MK_COMB (@lem6950507) (@lem6950506 _92591)). Qed.
Lemma lem6950509 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem6950510 (_92591 : int) : (term294 _92591) = (term163 _92591).
Proof. exact (MK_COMB (@lem6950508 _92591) (@lem6950509)). Qed.
Lemma lem6950511 (_92591 : int) (h1 : term214 _92591) : term163 _92591.
Proof. exact (EQ_MP (@lem6950510 _92591) (@lem6950505 _92591 h1)). Qed.
Lemma lem6950513 (y : real) : term245 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem6950514 (_92591 : int) : term246 _92591.
Proof. exact (@lem6950513 (real_of_int _92591)). Qed.
Lemma lem6950515 (_92591 : int) (h1 : term214 _92591) : term247 _92591.
Proof. exact (@lem6950514 _92591 (@lem6950436 _92591 h1)). Qed.
Lemma lem6950516 (_92591 : int) (h1 : term214 _92591) : term297 _92591.
Proof. exact (@lem6950515 _92591 h1 term114). Qed.
Lemma lem6950517 (_92591 : int) : (term297 _92591) = ((term172 _92591) = term53).
Proof. exact (eq_refl (term297 _92591)). Qed.
Lemma lem6950524 (_92591 : int) (h1 : term214 _92591) : (term172 _92591) = term53.
Proof. exact (EQ_MP (@lem6950517 _92591) (@lem6950516 _92591 h1)). Qed.
Lemma lem6950525 (_92591 : int) (h1 : term214 _92591) : term298 _92591.
Proof. exact (conj (@lem6950524 _92591 h1) (@lem6950511 _92591 h1)). Qed.
Lemma lem6950527 (x : real) (y : real) : term252 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem6950528 (_92591 : int) : term299 _92591.
Proof. exact (@lem6950527 (term172 _92591) (term160 _92591)). Qed.
Lemma lem6950529 (_92591 : int) (h1 : term214 _92591) : term300 _92591.
Proof. exact (@lem6950528 _92591 (@lem6950525 _92591 h1)). Qed.
Lemma lem6950530 (_92591 : int) : (term301 _92591) = (term302 _92591).
Proof. exact (@lem1982763 (term172 _92591) (real_of_int _92591) term114). Qed.
Lemma lem6950531 (_92591 : int) : (term303 _92591) = (term258 _92591).
Proof. exact (@lem1982713 term114 (real_of_int _92591)). Qed.
Lemma lem6950533 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6950534 : term69 = term140.
Proof. exact (@lem6950533 term70). Qed.
Lemma lem6950536 (x : nat) : (term112 x) = (term113 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6950537 : term114 = term115.
Proof. exact (@lem6950536 term70). Qed.
Lemma lem6950538 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6950539 : term259 = term260.
Proof. exact (MK_COMB (@lem6950538) (@lem6950537)). Qed.
Lemma lem6950540 : term261 = term262.
Proof. exact (MK_COMB (@lem6950539) (@lem6950534)). Qed.
Lemma lem6950541 : term263.
Proof. exact (@lem1981473 term114 term69 term69 term69 term53 term69). Qed.
Lemma lem6950543 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6950544 : term226 = term232.
Proof. exact (@lem6950543 (NUMERAL 0) term70). Qed.
Lemma lem6950545 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950546 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6950547 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950546 h1) (fun h1 : term232 = True => @lem6950545)). Qed.
Lemma lem6950548 : term232 = True.
Proof. exact (EQ_MP (@lem6950547) (@lem6950545)). Qed.
Lemma lem6950549 : term226 = True.
Proof. exact (TRANS (@lem6950544) (@lem6950548)). Qed.
Lemma lem6950550 : True = term226.
Proof. exact (SYM (@lem6950549)). Qed.
Lemma lem6950551 : term226.
Proof. exact (EQ_MP (@lem6950550) (@lem0)). Qed.
Lemma lem6950552 : term264.
Proof. exact (@lem6950541 (@lem6950551)). Qed.
Lemma lem6950554 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6950555 : term226 = term232.
Proof. exact (@lem6950554 (NUMERAL 0) term70). Qed.
Lemma lem6950556 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950557 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6950558 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950557 h1) (fun h1 : term232 = True => @lem6950556)). Qed.
Lemma lem6950559 : term232 = True.
Proof. exact (EQ_MP (@lem6950558) (@lem6950556)). Qed.
Lemma lem6950560 : term226 = True.
Proof. exact (TRANS (@lem6950555) (@lem6950559)). Qed.
Lemma lem6950561 : True = term226.
Proof. exact (SYM (@lem6950560)). Qed.
Lemma lem6950562 : term226.
Proof. exact (EQ_MP (@lem6950561) (@lem0)). Qed.
Lemma lem6950563 : term265.
Proof. exact (@lem6950552 (@lem6950562)). Qed.
Lemma lem6950565 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6950566 : term226 = term232.
Proof. exact (@lem6950565 (NUMERAL 0) term70). Qed.
Lemma lem6950567 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950568 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6950569 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950568 h1) (fun h1 : term232 = True => @lem6950567)). Qed.
Lemma lem6950570 : term232 = True.
Proof. exact (EQ_MP (@lem6950569) (@lem6950567)). Qed.
Lemma lem6950571 : term226 = True.
Proof. exact (TRANS (@lem6950566) (@lem6950570)). Qed.
Lemma lem6950572 : True = term226.
Proof. exact (SYM (@lem6950571)). Qed.
Lemma lem6950573 : term226.
Proof. exact (EQ_MP (@lem6950572) (@lem0)). Qed.
Lemma lem6950574 : term266.
Proof. exact (@lem6950563 (@lem6950573)). Qed.
Lemma lem6950576 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6950577 : term123 = term124.
Proof. exact (@lem6950576 term70 term70). Qed.
Lemma lem6950578 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6950579 : term126 = term70.
Proof. exact (EQ_MP (@lem6950578) (@lem940073)). Qed.
Lemma lem6950580 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6950581 : term124 = term69.
Proof. exact (MK_COMB (@lem6950580) (@lem6950579)). Qed.
Lemma lem6950582 : term123 = term69.
Proof. exact (TRANS (@lem6950577) (@lem6950581)). Qed.
Lemma lem6950584 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6950585 : term141 = term146.
Proof. exact (@lem6950584 term70 term70). Qed.
Lemma lem6950586 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6950587 : term126 = term70.
Proof. exact (EQ_MP (@lem6950586) (@lem940073)). Qed.
Lemma lem6950588 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6950589 : term124 = term69.
Proof. exact (MK_COMB (@lem6950588) (@lem6950587)). Qed.
Lemma lem6950590 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6950591 : term146 = term114.
Proof. exact (MK_COMB (@lem6950590) (@lem6950589)). Qed.
Lemma lem6950592 : term141 = term114.
Proof. exact (TRANS (@lem6950585) (@lem6950591)). Qed.
Lemma lem6950593 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6950594 : term267 = term259.
Proof. exact (MK_COMB (@lem6950593) (@lem6950592)). Qed.
Lemma lem6950595 : term268 = term261.
Proof. exact (MK_COMB (@lem6950594) (@lem6950582)). Qed.
Lemma lem6950597 (m : nat) : (term269 m) = term53.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6950598 : term261 = term53.
Proof. exact (@lem6950597 term70). Qed.
Lemma lem6950599 : term268 = term53.
Proof. exact (TRANS (@lem6950595) (@lem6950598)). Qed.
Lemma lem6950600 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6950601 : term270 = term271.
Proof. exact (MK_COMB (@lem6950600) (@lem6950599)). Qed.
Lemma lem6950602 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem6950603 : term272 = term237.
Proof. exact (MK_COMB (@lem6950601) (@lem6950602)). Qed.
Lemma lem6950605 (x : nat) : (term236 x) = term53.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6950606 : term237 = term53.
Proof. exact (@lem6950605 term70). Qed.
Lemma lem6950607 : term272 = term53.
Proof. exact (TRANS (@lem6950603) (@lem6950606)). Qed.
Lemma lem6950609 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6950610 : term123 = term124.
Proof. exact (@lem6950609 term70 term70). Qed.
Lemma lem6950611 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6950612 : term126 = term70.
Proof. exact (EQ_MP (@lem6950611) (@lem940073)). Qed.
Lemma lem6950613 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6950614 : term124 = term69.
Proof. exact (MK_COMB (@lem6950613) (@lem6950612)). Qed.
Lemma lem6950615 : term123 = term69.
Proof. exact (TRANS (@lem6950610) (@lem6950614)). Qed.
Lemma lem6950616 : term271 = term271.
Proof. exact (eq_refl term271). Qed.
Lemma lem6950617 : term273 = term237.
Proof. exact (MK_COMB (@lem6950616) (@lem6950615)). Qed.
Lemma lem6950619 (x : nat) : (term236 x) = term53.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6950620 : term237 = term53.
Proof. exact (@lem6950619 term70). Qed.
Lemma lem6950621 : term273 = term53.
Proof. exact (TRANS (@lem6950617) (@lem6950620)). Qed.
Lemma lem6950622 : term53 = term273.
Proof. exact (SYM (@lem6950621)). Qed.
Lemma lem6950623 : term272 = term273.
Proof. exact (TRANS (@lem6950607) (@lem6950622)). Qed.
Lemma lem6950624 : term262 = term111.
Proof. exact (@lem6950574 (@lem6950623)). Qed.
Lemma lem6950625 : term261 = term111.
Proof. exact (TRANS (@lem6950540) (@lem6950624)). Qed.
Lemma lem6950627 (x : real) : (term130 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6950628 : term111 = term53.
Proof. exact (@lem6950627 term53). Qed.
Lemma lem6950629 : term261 = term53.
Proof. exact (TRANS (@lem6950625) (@lem6950628)). Qed.
Lemma lem6950630 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6950631 : term274 = term271.
Proof. exact (MK_COMB (@lem6950630) (@lem6950629)). Qed.
Lemma lem6950632 (_92591 : int) : (real_of_int _92591) = (real_of_int _92591).
Proof. exact (eq_refl (real_of_int _92591)). Qed.
Lemma lem6950633 (_92591 : int) : (term258 _92591) = (term275 _92591).
Proof. exact (MK_COMB (@lem6950631) (@lem6950632 _92591)). Qed.
Lemma lem6950634 (_92591 : int) : (term303 _92591) = (term275 _92591).
Proof. exact (TRANS (@lem6950531 _92591) (@lem6950633 _92591)). Qed.
Lemma lem6950635 (_92591 : int) : (term275 _92591) = term53.
Proof. exact (@lem1982719 (real_of_int _92591)). Qed.
Lemma lem6950636 (_92591 : int) : (term303 _92591) = term53.
Proof. exact (TRANS (@lem6950634 _92591) (@lem6950635 _92591)). Qed.
Lemma lem6950637 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6950638 (_92591 : int) : (term304 _92591) = term84.
Proof. exact (MK_COMB (@lem6950637) (@lem6950636 _92591)). Qed.
Lemma lem6950639 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem6950640 (_92591 : int) : (term302 _92591) = term277.
Proof. exact (MK_COMB (@lem6950638 _92591) (@lem6950639)). Qed.
Lemma lem6950641 (_92591 : int) : (term301 _92591) = term277.
Proof. exact (TRANS (@lem6950530 _92591) (@lem6950640 _92591)). Qed.
Lemma lem6950642 : term277 = term114.
Proof. exact (@lem1982721 term114). Qed.
Lemma lem6950643 (_92591 : int) : (term301 _92591) = term114.
Proof. exact (TRANS (@lem6950641 _92591) (@lem6950642)). Qed.
Lemma lem6950644 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6950645 (_92591 : int) : (term305 _92591) = term279.
Proof. exact (MK_COMB (@lem6950644) (@lem6950643 _92591)). Qed.
Lemma lem6950646 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem6950647 (_92591 : int) : (term300 _92591) = term280.
Proof. exact (MK_COMB (@lem6950645 _92591) (@lem6950646)). Qed.
Lemma lem6950648 (_92591 : int) (h1 : term214 _92591) : term280.
Proof. exact (EQ_MP (@lem6950647 _92591) (@lem6950529 _92591 h1)). Qed.
Lemma lem6950650 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6950651 : term280 = term281.
Proof. exact (@lem6950650 term53 term114). Qed.
Lemma lem6950653 (x : nat) : (term112 x) = (term113 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6950654 : term114 = term115.
Proof. exact (@lem6950653 term70). Qed.
Lemma lem6950656 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6950657 : term53 = term111.
Proof. exact (@lem6950656 (NUMERAL 0)). Qed.
Lemma lem6950658 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6950659 : term55 = term282.
Proof. exact (MK_COMB (@lem6950658) (@lem6950657)). Qed.
Lemma lem6950660 : term281 = term283.
Proof. exact (MK_COMB (@lem6950659) (@lem6950654)). Qed.
Lemma lem6950661 : term284.
Proof. exact (@lem1980026 term53 term69 term114 term69). Qed.
Lemma lem6950663 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6950664 : term226 = term232.
Proof. exact (@lem6950663 (NUMERAL 0) term70). Qed.
Lemma lem6950665 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950666 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6950667 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950666 h1) (fun h1 : term232 = True => @lem6950665)). Qed.
Lemma lem6950668 : term232 = True.
Proof. exact (EQ_MP (@lem6950667) (@lem6950665)). Qed.
Lemma lem6950669 : term226 = True.
Proof. exact (TRANS (@lem6950664) (@lem6950668)). Qed.
Lemma lem6950670 : True = term226.
Proof. exact (SYM (@lem6950669)). Qed.
Lemma lem6950671 : term226.
Proof. exact (EQ_MP (@lem6950670) (@lem0)). Qed.
Lemma lem6950672 : term285.
Proof. exact (@lem6950661 (@lem6950671)). Qed.
Lemma lem6950674 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6950675 : term226 = term232.
Proof. exact (@lem6950674 (NUMERAL 0) term70). Qed.
Lemma lem6950676 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950677 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6950678 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950677 h1) (fun h1 : term232 = True => @lem6950676)). Qed.
Lemma lem6950679 : term232 = True.
Proof. exact (EQ_MP (@lem6950678) (@lem6950676)). Qed.
Lemma lem6950680 : term226 = True.
Proof. exact (TRANS (@lem6950675) (@lem6950679)). Qed.
Lemma lem6950681 : True = term226.
Proof. exact (SYM (@lem6950680)). Qed.
Lemma lem6950682 : term226.
Proof. exact (EQ_MP (@lem6950681) (@lem0)). Qed.
Lemma lem6950683 : term283 = term286.
Proof. exact (@lem6950672 (@lem6950682)). Qed.
Lemma lem6950685 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6950686 : term141 = term146.
Proof. exact (@lem6950685 term70 term70). Qed.
Lemma lem6950687 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6950688 : term126 = term70.
Proof. exact (EQ_MP (@lem6950687) (@lem940073)). Qed.
Lemma lem6950689 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6950690 : term124 = term69.
Proof. exact (MK_COMB (@lem6950689) (@lem6950688)). Qed.
Lemma lem6950691 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6950692 : term146 = term114.
Proof. exact (MK_COMB (@lem6950691) (@lem6950690)). Qed.
Lemma lem6950693 : term141 = term114.
Proof. exact (TRANS (@lem6950686) (@lem6950692)). Qed.
Lemma lem6950695 (x : nat) : (term236 x) = term53.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6950696 : term237 = term53.
Proof. exact (@lem6950695 term70). Qed.
Lemma lem6950697 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6950698 : term287 = term55.
Proof. exact (MK_COMB (@lem6950697) (@lem6950696)). Qed.
Lemma lem6950699 : term286 = term281.
Proof. exact (MK_COMB (@lem6950698) (@lem6950693)). Qed.
Lemma lem6950701 (m : nat) (n : nat) : (term288 m n) = (term289 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6950702 : term281 = term290.
Proof. exact (@lem6950701 (NUMERAL 0) term70). Qed.
Lemma lem6950703 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950704 (h1 : term233 = (BIT1 0)) : (term70 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6950705 : (term233 = (BIT1 0)) = ((term70 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950704 h1) (fun h1 : (term70 = (NUMERAL 0)) = False => @lem6950703)). Qed.
Lemma lem6950706 : (term70 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6950705) (@lem6950703)). Qed.
Lemma lem6950707 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6950708 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6950709 : term291 = (and True).
Proof. exact (MK_COMB (@lem6950708) (@lem6950707)). Qed.
Lemma lem6950710 : term290 = (True /\ False).
Proof. exact (MK_COMB (@lem6950709) (@lem6950706)). Qed.
Lemma lem6950712 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6950713 : term290 = False.
Proof. exact (TRANS (@lem6950710) (@lem6950712)). Qed.
Lemma lem6950714 : term281 = False.
Proof. exact (TRANS (@lem6950702) (@lem6950713)). Qed.
Lemma lem6950715 : term286 = False.
Proof. exact (TRANS (@lem6950699) (@lem6950714)). Qed.
Lemma lem6950716 : term283 = False.
Proof. exact (TRANS (@lem6950683) (@lem6950715)). Qed.
Lemma lem6950717 : term281 = False.
Proof. exact (TRANS (@lem6950660) (@lem6950716)). Qed.
Lemma lem6950718 : term280 = False.
Proof. exact (TRANS (@lem6950651) (@lem6950717)). Qed.
Lemma lem6950719 (_92591 : int) (h1 : term214 _92591) : False.
Proof. exact (EQ_MP (@lem6950718) (@lem6950648 _92591 h1)). Qed.
Lemma lem6950720 (_92591 : int) (h1 : term220 _92591) : False.
Proof. exact (or_elim (@lem6949856 _92591 h1) (fun h0 : term216 _92591 => @lem6950432 _92591 h0) (fun h0 : term214 _92591 => @lem6950719 _92591 h0)). Qed.
Lemma lem6950721 (_92591 : int) (h1 : term211 _92591) : term211 _92591.
Proof. exact (h1). Qed.
Lemma lem6950722 (_92591 : int) (h1 : term207 _92591) : term207 _92591.
Proof. exact (h1). Qed.
Lemma lem6950723 (_92591 : int) (h1 : term306 _92591) : term306 _92591.
Proof. exact (h1). Qed.
Lemma lem6950724 (_92591 : int) (h1 : term306 _92591) : term208 _92591.
Proof. exact (proj2 (@lem6950723 _92591 h1)). Qed.
Lemma lem6950725 (_92591 : int) (h1 : term306 _92591) : term134 _92591.
Proof. exact (proj1 (@lem6950723 _92591 h1)). Qed.
Lemma lem6950727 (_92591 : int) (h1 : term306 _92591) : term154 _92591.
Proof. exact (proj1 (@lem6950724 _92591 h1)). Qed.
Lemma lem6950729 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6950730 : term225 = term226.
Proof. exact (@lem6950729 term53 term69). Qed.
Lemma lem6950732 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6950733 : term69 = term140.
Proof. exact (@lem6950732 term70). Qed.
Lemma lem6950735 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6950736 : term53 = term111.
Proof. exact (@lem6950735 (NUMERAL 0)). Qed.
Lemma lem6950737 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6950738 : term227 = term228.
Proof. exact (MK_COMB (@lem6950737) (@lem6950736)). Qed.
Lemma lem6950739 : term226 = term229.
Proof. exact (MK_COMB (@lem6950738) (@lem6950733)). Qed.
Lemma lem6950740 : term230.
Proof. exact (@lem1980255 term53 term69 term69 term69). Qed.
Lemma lem6950742 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6950743 : term226 = term232.
Proof. exact (@lem6950742 (NUMERAL 0) term70). Qed.
Lemma lem6950744 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950745 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6950746 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950745 h1) (fun h1 : term232 = True => @lem6950744)). Qed.
Lemma lem6950747 : term232 = True.
Proof. exact (EQ_MP (@lem6950746) (@lem6950744)). Qed.
Lemma lem6950748 : term226 = True.
Proof. exact (TRANS (@lem6950743) (@lem6950747)). Qed.
Lemma lem6950749 : True = term226.
Proof. exact (SYM (@lem6950748)). Qed.
Lemma lem6950750 : term226.
Proof. exact (EQ_MP (@lem6950749) (@lem0)). Qed.
Lemma lem6950751 : term234.
Proof. exact (@lem6950740 (@lem6950750)). Qed.
Lemma lem6950753 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6950754 : term226 = term232.
Proof. exact (@lem6950753 (NUMERAL 0) term70). Qed.
Lemma lem6950755 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950756 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6950757 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950756 h1) (fun h1 : term232 = True => @lem6950755)). Qed.
Lemma lem6950758 : term232 = True.
Proof. exact (EQ_MP (@lem6950757) (@lem6950755)). Qed.
Lemma lem6950759 : term226 = True.
Proof. exact (TRANS (@lem6950754) (@lem6950758)). Qed.
Lemma lem6950760 : True = term226.
Proof. exact (SYM (@lem6950759)). Qed.
Lemma lem6950761 : term226.
Proof. exact (EQ_MP (@lem6950760) (@lem0)). Qed.
Lemma lem6950762 : term229 = term235.
Proof. exact (@lem6950751 (@lem6950761)). Qed.
Lemma lem6950764 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6950765 : term123 = term124.
Proof. exact (@lem6950764 term70 term70). Qed.
Lemma lem6950766 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6950767 : term126 = term70.
Proof. exact (EQ_MP (@lem6950766) (@lem940073)). Qed.
Lemma lem6950768 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6950769 : term124 = term69.
Proof. exact (MK_COMB (@lem6950768) (@lem6950767)). Qed.
Lemma lem6950770 : term123 = term69.
Proof. exact (TRANS (@lem6950765) (@lem6950769)). Qed.
Lemma lem6950772 (x : nat) : (term236 x) = term53.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6950773 : term237 = term53.
Proof. exact (@lem6950772 term70). Qed.
Lemma lem6950774 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6950775 : term238 = term227.
Proof. exact (MK_COMB (@lem6950774) (@lem6950773)). Qed.
Lemma lem6950776 : term235 = term226.
Proof. exact (MK_COMB (@lem6950775) (@lem6950770)). Qed.
Lemma lem6950778 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6950779 : term226 = term232.
Proof. exact (@lem6950778 (NUMERAL 0) term70). Qed.
Lemma lem6950780 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950781 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6950782 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950781 h1) (fun h1 : term232 = True => @lem6950780)). Qed.
Lemma lem6950783 : term232 = True.
Proof. exact (EQ_MP (@lem6950782) (@lem6950780)). Qed.
Lemma lem6950784 : term226 = True.
Proof. exact (TRANS (@lem6950779) (@lem6950783)). Qed.
Lemma lem6950785 : term235 = True.
Proof. exact (TRANS (@lem6950776) (@lem6950784)). Qed.
Lemma lem6950786 : term229 = True.
Proof. exact (TRANS (@lem6950762) (@lem6950785)). Qed.
Lemma lem6950787 : term226 = True.
Proof. exact (TRANS (@lem6950739) (@lem6950786)). Qed.
Lemma lem6950788 : term225 = True.
Proof. exact (TRANS (@lem6950730) (@lem6950787)). Qed.
Lemma lem6950789 : True = term225.
Proof. exact (SYM (@lem6950788)). Qed.
Lemma lem6950790 : term225.
Proof. exact (EQ_MP (@lem6950789) (@lem0)). Qed.
Lemma lem6950791 (_92591 : int) (h1 : term306 _92591) : term307 _92591.
Proof. exact (conj (@lem6950790) (@lem6950725 _92591 h1)). Qed.
Lemma lem6950793 (x : real) (y : real) : term240 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6950794 (_92591 : int) : term308 _92591.
Proof. exact (@lem6950793 term69 (real_of_int _92591)). Qed.
Lemma lem6950795 (_92591 : int) (h1 : term306 _92591) : term309 _92591.
Proof. exact (@lem6950794 _92591 (@lem6950791 _92591 h1)). Qed.
Lemma lem6950796 (_92591 : int) : (term249 _92591) = (real_of_int _92591).
Proof. exact (@lem1982733 (real_of_int _92591)). Qed.
Lemma lem6950797 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6950798 (_92591 : int) : (term310 _92591) = (term133 _92591).
Proof. exact (MK_COMB (@lem6950797) (@lem6950796 _92591)). Qed.
Lemma lem6950799 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem6950800 (_92591 : int) : (term309 _92591) = (term134 _92591).
Proof. exact (MK_COMB (@lem6950798 _92591) (@lem6950799)). Qed.
Lemma lem6950801 (_92591 : int) (h1 : term306 _92591) : term134 _92591.
Proof. exact (EQ_MP (@lem6950800 _92591) (@lem6950795 _92591 h1)). Qed.
Lemma lem6950803 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6950804 : term225 = term226.
Proof. exact (@lem6950803 term53 term69). Qed.
Lemma lem6950806 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6950807 : term69 = term140.
Proof. exact (@lem6950806 term70). Qed.
Lemma lem6950809 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6950810 : term53 = term111.
Proof. exact (@lem6950809 (NUMERAL 0)). Qed.
Lemma lem6950811 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6950812 : term227 = term228.
Proof. exact (MK_COMB (@lem6950811) (@lem6950810)). Qed.
Lemma lem6950813 : term226 = term229.
Proof. exact (MK_COMB (@lem6950812) (@lem6950807)). Qed.
Lemma lem6950814 : term230.
Proof. exact (@lem1980255 term53 term69 term69 term69). Qed.
Lemma lem6950816 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6950817 : term226 = term232.
Proof. exact (@lem6950816 (NUMERAL 0) term70). Qed.
Lemma lem6950818 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950819 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6950820 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950819 h1) (fun h1 : term232 = True => @lem6950818)). Qed.
Lemma lem6950821 : term232 = True.
Proof. exact (EQ_MP (@lem6950820) (@lem6950818)). Qed.
Lemma lem6950822 : term226 = True.
Proof. exact (TRANS (@lem6950817) (@lem6950821)). Qed.
Lemma lem6950823 : True = term226.
Proof. exact (SYM (@lem6950822)). Qed.
Lemma lem6950824 : term226.
Proof. exact (EQ_MP (@lem6950823) (@lem0)). Qed.
Lemma lem6950825 : term234.
Proof. exact (@lem6950814 (@lem6950824)). Qed.
Lemma lem6950827 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6950828 : term226 = term232.
Proof. exact (@lem6950827 (NUMERAL 0) term70). Qed.
Lemma lem6950829 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950830 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6950831 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950830 h1) (fun h1 : term232 = True => @lem6950829)). Qed.
Lemma lem6950832 : term232 = True.
Proof. exact (EQ_MP (@lem6950831) (@lem6950829)). Qed.
Lemma lem6950833 : term226 = True.
Proof. exact (TRANS (@lem6950828) (@lem6950832)). Qed.
Lemma lem6950834 : True = term226.
Proof. exact (SYM (@lem6950833)). Qed.
Lemma lem6950835 : term226.
Proof. exact (EQ_MP (@lem6950834) (@lem0)). Qed.
Lemma lem6950836 : term229 = term235.
Proof. exact (@lem6950825 (@lem6950835)). Qed.
Lemma lem6950838 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6950839 : term123 = term124.
Proof. exact (@lem6950838 term70 term70). Qed.
Lemma lem6950840 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6950841 : term126 = term70.
Proof. exact (EQ_MP (@lem6950840) (@lem940073)). Qed.
Lemma lem6950842 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6950843 : term124 = term69.
Proof. exact (MK_COMB (@lem6950842) (@lem6950841)). Qed.
Lemma lem6950844 : term123 = term69.
Proof. exact (TRANS (@lem6950839) (@lem6950843)). Qed.
Lemma lem6950846 (x : nat) : (term236 x) = term53.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6950847 : term237 = term53.
Proof. exact (@lem6950846 term70). Qed.
Lemma lem6950848 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6950849 : term238 = term227.
Proof. exact (MK_COMB (@lem6950848) (@lem6950847)). Qed.
Lemma lem6950850 : term235 = term226.
Proof. exact (MK_COMB (@lem6950849) (@lem6950844)). Qed.
Lemma lem6950852 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6950853 : term226 = term232.
Proof. exact (@lem6950852 (NUMERAL 0) term70). Qed.
Lemma lem6950854 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950855 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6950856 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950855 h1) (fun h1 : term232 = True => @lem6950854)). Qed.
Lemma lem6950857 : term232 = True.
Proof. exact (EQ_MP (@lem6950856) (@lem6950854)). Qed.
Lemma lem6950858 : term226 = True.
Proof. exact (TRANS (@lem6950853) (@lem6950857)). Qed.
Lemma lem6950859 : term235 = True.
Proof. exact (TRANS (@lem6950850) (@lem6950858)). Qed.
Lemma lem6950860 : term229 = True.
Proof. exact (TRANS (@lem6950836) (@lem6950859)). Qed.
Lemma lem6950861 : term226 = True.
Proof. exact (TRANS (@lem6950813) (@lem6950860)). Qed.
Lemma lem6950862 : term225 = True.
Proof. exact (TRANS (@lem6950804) (@lem6950861)). Qed.
Lemma lem6950863 : True = term225.
Proof. exact (SYM (@lem6950862)). Qed.
Lemma lem6950864 : term225.
Proof. exact (EQ_MP (@lem6950863) (@lem0)). Qed.
Lemma lem6950865 (_92591 : int) (h1 : term306 _92591) : term239 _92591.
Proof. exact (conj (@lem6950864) (@lem6950727 _92591 h1)). Qed.
Lemma lem6950867 (x : real) (y : real) : term240 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6950868 (_92591 : int) : term241 _92591.
Proof. exact (@lem6950867 term69 (term150 _92591)). Qed.
Lemma lem6950869 (_92591 : int) (h1 : term306 _92591) : term242 _92591.
Proof. exact (@lem6950868 _92591 (@lem6950865 _92591 h1)). Qed.
Lemma lem6950870 (_92591 : int) : (term243 _92591) = (term150 _92591).
Proof. exact (@lem1982733 (term150 _92591)). Qed.
Lemma lem6950871 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6950872 (_92591 : int) : (term244 _92591) = (term153 _92591).
Proof. exact (MK_COMB (@lem6950871) (@lem6950870 _92591)). Qed.
Lemma lem6950873 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem6950874 (_92591 : int) : (term242 _92591) = (term154 _92591).
Proof. exact (MK_COMB (@lem6950872 _92591) (@lem6950873)). Qed.
Lemma lem6950875 (_92591 : int) (h1 : term306 _92591) : term154 _92591.
Proof. exact (EQ_MP (@lem6950874 _92591) (@lem6950869 _92591 h1)). Qed.
Lemma lem6950876 (_92591 : int) (h1 : term306 _92591) : term311 _92591.
Proof. exact (conj (@lem6950875 _92591 h1) (@lem6950801 _92591 h1)). Qed.
Lemma lem6950878 (x : real) (y : real) : term312 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem6950879 (_92591 : int) : term313 _92591.
Proof. exact (@lem6950878 (term150 _92591) (real_of_int _92591)). Qed.
Lemma lem6950880 (_92591 : int) (h1 : term306 _92591) : term314 _92591.
Proof. exact (@lem6950879 _92591 (@lem6950876 _92591 h1)). Qed.
Lemma lem6950881 (_92591 : int) : (term315 _92591) = (term302 _92591).
Proof. exact (@lem1982759 (term172 _92591) (real_of_int _92591) term114). Qed.
Lemma lem6950882 (_92591 : int) : (term303 _92591) = (term258 _92591).
Proof. exact (@lem1982713 term114 (real_of_int _92591)). Qed.
Lemma lem6950884 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6950885 : term69 = term140.
Proof. exact (@lem6950884 term70). Qed.
Lemma lem6950887 (x : nat) : (term112 x) = (term113 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6950888 : term114 = term115.
Proof. exact (@lem6950887 term70). Qed.
Lemma lem6950889 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6950890 : term259 = term260.
Proof. exact (MK_COMB (@lem6950889) (@lem6950888)). Qed.
Lemma lem6950891 : term261 = term262.
Proof. exact (MK_COMB (@lem6950890) (@lem6950885)). Qed.
Lemma lem6950892 : term263.
Proof. exact (@lem1981473 term114 term69 term69 term69 term53 term69). Qed.
Lemma lem6950894 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6950895 : term226 = term232.
Proof. exact (@lem6950894 (NUMERAL 0) term70). Qed.
Lemma lem6950896 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950897 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6950898 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950897 h1) (fun h1 : term232 = True => @lem6950896)). Qed.
Lemma lem6950899 : term232 = True.
Proof. exact (EQ_MP (@lem6950898) (@lem6950896)). Qed.
Lemma lem6950900 : term226 = True.
Proof. exact (TRANS (@lem6950895) (@lem6950899)). Qed.
Lemma lem6950901 : True = term226.
Proof. exact (SYM (@lem6950900)). Qed.
Lemma lem6950902 : term226.
Proof. exact (EQ_MP (@lem6950901) (@lem0)). Qed.
Lemma lem6950903 : term264.
Proof. exact (@lem6950892 (@lem6950902)). Qed.
Lemma lem6950905 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6950906 : term226 = term232.
Proof. exact (@lem6950905 (NUMERAL 0) term70). Qed.
Lemma lem6950907 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950908 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6950909 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950908 h1) (fun h1 : term232 = True => @lem6950907)). Qed.
Lemma lem6950910 : term232 = True.
Proof. exact (EQ_MP (@lem6950909) (@lem6950907)). Qed.
Lemma lem6950911 : term226 = True.
Proof. exact (TRANS (@lem6950906) (@lem6950910)). Qed.
Lemma lem6950912 : True = term226.
Proof. exact (SYM (@lem6950911)). Qed.
Lemma lem6950913 : term226.
Proof. exact (EQ_MP (@lem6950912) (@lem0)). Qed.
Lemma lem6950914 : term265.
Proof. exact (@lem6950903 (@lem6950913)). Qed.
Lemma lem6950916 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6950917 : term226 = term232.
Proof. exact (@lem6950916 (NUMERAL 0) term70). Qed.
Lemma lem6950918 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6950919 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6950920 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6950919 h1) (fun h1 : term232 = True => @lem6950918)). Qed.
Lemma lem6950921 : term232 = True.
Proof. exact (EQ_MP (@lem6950920) (@lem6950918)). Qed.
Lemma lem6950922 : term226 = True.
Proof. exact (TRANS (@lem6950917) (@lem6950921)). Qed.
Lemma lem6950923 : True = term226.
Proof. exact (SYM (@lem6950922)). Qed.
Lemma lem6950924 : term226.
Proof. exact (EQ_MP (@lem6950923) (@lem0)). Qed.
Lemma lem6950925 : term266.
Proof. exact (@lem6950914 (@lem6950924)). Qed.
Lemma lem6950927 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6950928 : term123 = term124.
Proof. exact (@lem6950927 term70 term70). Qed.
Lemma lem6950929 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6950930 : term126 = term70.
Proof. exact (EQ_MP (@lem6950929) (@lem940073)). Qed.
Lemma lem6950931 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6950932 : term124 = term69.
Proof. exact (MK_COMB (@lem6950931) (@lem6950930)). Qed.
Lemma lem6950933 : term123 = term69.
Proof. exact (TRANS (@lem6950928) (@lem6950932)). Qed.
Lemma lem6950935 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6950936 : term141 = term146.
Proof. exact (@lem6950935 term70 term70). Qed.
Lemma lem6950937 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6950938 : term126 = term70.
Proof. exact (EQ_MP (@lem6950937) (@lem940073)). Qed.
Lemma lem6950939 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6950940 : term124 = term69.
Proof. exact (MK_COMB (@lem6950939) (@lem6950938)). Qed.
Lemma lem6950941 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6950942 : term146 = term114.
Proof. exact (MK_COMB (@lem6950941) (@lem6950940)). Qed.
Lemma lem6950943 : term141 = term114.
Proof. exact (TRANS (@lem6950936) (@lem6950942)). Qed.
Lemma lem6950944 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6950945 : term267 = term259.
Proof. exact (MK_COMB (@lem6950944) (@lem6950943)). Qed.
Lemma lem6950946 : term268 = term261.
Proof. exact (MK_COMB (@lem6950945) (@lem6950933)). Qed.
Lemma lem6950948 (m : nat) : (term269 m) = term53.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6950949 : term261 = term53.
Proof. exact (@lem6950948 term70). Qed.
Lemma lem6950950 : term268 = term53.
Proof. exact (TRANS (@lem6950946) (@lem6950949)). Qed.
Lemma lem6950951 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6950952 : term270 = term271.
Proof. exact (MK_COMB (@lem6950951) (@lem6950950)). Qed.
Lemma lem6950953 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem6950954 : term272 = term237.
Proof. exact (MK_COMB (@lem6950952) (@lem6950953)). Qed.
Lemma lem6950956 (x : nat) : (term236 x) = term53.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6950957 : term237 = term53.
Proof. exact (@lem6950956 term70). Qed.
Lemma lem6950958 : term272 = term53.
Proof. exact (TRANS (@lem6950954) (@lem6950957)). Qed.
Lemma lem6950960 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6950961 : term123 = term124.
Proof. exact (@lem6950960 term70 term70). Qed.
Lemma lem6950962 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6950963 : term126 = term70.
Proof. exact (EQ_MP (@lem6950962) (@lem940073)). Qed.
Lemma lem6950964 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6950965 : term124 = term69.
Proof. exact (MK_COMB (@lem6950964) (@lem6950963)). Qed.
Lemma lem6950966 : term123 = term69.
Proof. exact (TRANS (@lem6950961) (@lem6950965)). Qed.
Lemma lem6950967 : term271 = term271.
Proof. exact (eq_refl term271). Qed.
Lemma lem6950968 : term273 = term237.
Proof. exact (MK_COMB (@lem6950967) (@lem6950966)). Qed.
Lemma lem6950970 (x : nat) : (term236 x) = term53.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6950971 : term237 = term53.
Proof. exact (@lem6950970 term70). Qed.
Lemma lem6950972 : term273 = term53.
Proof. exact (TRANS (@lem6950968) (@lem6950971)). Qed.
Lemma lem6950973 : term53 = term273.
Proof. exact (SYM (@lem6950972)). Qed.
Lemma lem6950974 : term272 = term273.
Proof. exact (TRANS (@lem6950958) (@lem6950973)). Qed.
Lemma lem6950975 : term262 = term111.
Proof. exact (@lem6950925 (@lem6950974)). Qed.
Lemma lem6950976 : term261 = term111.
Proof. exact (TRANS (@lem6950891) (@lem6950975)). Qed.
Lemma lem6950978 (x : real) : (term130 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6950979 : term111 = term53.
Proof. exact (@lem6950978 term53). Qed.
Lemma lem6950980 : term261 = term53.
Proof. exact (TRANS (@lem6950976) (@lem6950979)). Qed.
Lemma lem6950981 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6950982 : term274 = term271.
Proof. exact (MK_COMB (@lem6950981) (@lem6950980)). Qed.
Lemma lem6950983 (_92591 : int) : (real_of_int _92591) = (real_of_int _92591).
Proof. exact (eq_refl (real_of_int _92591)). Qed.
Lemma lem6950984 (_92591 : int) : (term258 _92591) = (term275 _92591).
Proof. exact (MK_COMB (@lem6950982) (@lem6950983 _92591)). Qed.
Lemma lem6950985 (_92591 : int) : (term303 _92591) = (term275 _92591).
Proof. exact (TRANS (@lem6950882 _92591) (@lem6950984 _92591)). Qed.
Lemma lem6950986 (_92591 : int) : (term275 _92591) = term53.
Proof. exact (@lem1982719 (real_of_int _92591)). Qed.
Lemma lem6950987 (_92591 : int) : (term303 _92591) = term53.
Proof. exact (TRANS (@lem6950985 _92591) (@lem6950986 _92591)). Qed.
Lemma lem6950988 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6950989 (_92591 : int) : (term304 _92591) = term84.
Proof. exact (MK_COMB (@lem6950988) (@lem6950987 _92591)). Qed.
Lemma lem6950990 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem6950991 (_92591 : int) : (term302 _92591) = term277.
Proof. exact (MK_COMB (@lem6950989 _92591) (@lem6950990)). Qed.
Lemma lem6950992 (_92591 : int) : (term315 _92591) = term277.
Proof. exact (TRANS (@lem6950881 _92591) (@lem6950991 _92591)). Qed.
Lemma lem6950993 : term277 = term114.
Proof. exact (@lem1982721 term114). Qed.
Lemma lem6950994 (_92591 : int) : (term315 _92591) = term114.
Proof. exact (TRANS (@lem6950992 _92591) (@lem6950993)). Qed.
Lemma lem6950995 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6950996 (_92591 : int) : (term316 _92591) = term279.
Proof. exact (MK_COMB (@lem6950995) (@lem6950994 _92591)). Qed.
Lemma lem6950997 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem6950998 (_92591 : int) : (term314 _92591) = term280.
Proof. exact (MK_COMB (@lem6950996 _92591) (@lem6950997)). Qed.
Lemma lem6950999 (_92591 : int) (h1 : term306 _92591) : term280.
Proof. exact (EQ_MP (@lem6950998 _92591) (@lem6950880 _92591 h1)). Qed.
Lemma lem6951001 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6951002 : term280 = term281.
Proof. exact (@lem6951001 term53 term114). Qed.
Lemma lem6951004 (x : nat) : (term112 x) = (term113 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6951005 : term114 = term115.
Proof. exact (@lem6951004 term70). Qed.
Lemma lem6951007 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6951008 : term53 = term111.
Proof. exact (@lem6951007 (NUMERAL 0)). Qed.
Lemma lem6951009 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6951010 : term55 = term282.
Proof. exact (MK_COMB (@lem6951009) (@lem6951008)). Qed.
Lemma lem6951011 : term281 = term283.
Proof. exact (MK_COMB (@lem6951010) (@lem6951005)). Qed.
Lemma lem6951012 : term284.
Proof. exact (@lem1980026 term53 term69 term114 term69). Qed.
Lemma lem6951014 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6951015 : term226 = term232.
Proof. exact (@lem6951014 (NUMERAL 0) term70). Qed.
Lemma lem6951016 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6951017 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6951018 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6951017 h1) (fun h1 : term232 = True => @lem6951016)). Qed.
Lemma lem6951019 : term232 = True.
Proof. exact (EQ_MP (@lem6951018) (@lem6951016)). Qed.
Lemma lem6951020 : term226 = True.
Proof. exact (TRANS (@lem6951015) (@lem6951019)). Qed.
Lemma lem6951021 : True = term226.
Proof. exact (SYM (@lem6951020)). Qed.
Lemma lem6951022 : term226.
Proof. exact (EQ_MP (@lem6951021) (@lem0)). Qed.
Lemma lem6951023 : term285.
Proof. exact (@lem6951012 (@lem6951022)). Qed.
Lemma lem6951025 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6951026 : term226 = term232.
Proof. exact (@lem6951025 (NUMERAL 0) term70). Qed.
Lemma lem6951027 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6951028 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6951029 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6951028 h1) (fun h1 : term232 = True => @lem6951027)). Qed.
Lemma lem6951030 : term232 = True.
Proof. exact (EQ_MP (@lem6951029) (@lem6951027)). Qed.
Lemma lem6951031 : term226 = True.
Proof. exact (TRANS (@lem6951026) (@lem6951030)). Qed.
Lemma lem6951032 : True = term226.
Proof. exact (SYM (@lem6951031)). Qed.
Lemma lem6951033 : term226.
Proof. exact (EQ_MP (@lem6951032) (@lem0)). Qed.
Lemma lem6951034 : term283 = term286.
Proof. exact (@lem6951023 (@lem6951033)). Qed.
Lemma lem6951036 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6951037 : term141 = term146.
Proof. exact (@lem6951036 term70 term70). Qed.
Lemma lem6951038 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6951039 : term126 = term70.
Proof. exact (EQ_MP (@lem6951038) (@lem940073)). Qed.
Lemma lem6951040 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6951041 : term124 = term69.
Proof. exact (MK_COMB (@lem6951040) (@lem6951039)). Qed.
Lemma lem6951042 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6951043 : term146 = term114.
Proof. exact (MK_COMB (@lem6951042) (@lem6951041)). Qed.
Lemma lem6951044 : term141 = term114.
Proof. exact (TRANS (@lem6951037) (@lem6951043)). Qed.
Lemma lem6951046 (x : nat) : (term236 x) = term53.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6951047 : term237 = term53.
Proof. exact (@lem6951046 term70). Qed.
Lemma lem6951048 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6951049 : term287 = term55.
Proof. exact (MK_COMB (@lem6951048) (@lem6951047)). Qed.
Lemma lem6951050 : term286 = term281.
Proof. exact (MK_COMB (@lem6951049) (@lem6951044)). Qed.
Lemma lem6951052 (m : nat) (n : nat) : (term288 m n) = (term289 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6951053 : term281 = term290.
Proof. exact (@lem6951052 (NUMERAL 0) term70). Qed.
Lemma lem6951054 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6951055 (h1 : term233 = (BIT1 0)) : (term70 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6951056 : (term233 = (BIT1 0)) = ((term70 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6951055 h1) (fun h1 : (term70 = (NUMERAL 0)) = False => @lem6951054)). Qed.
Lemma lem6951057 : (term70 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6951056) (@lem6951054)). Qed.
Lemma lem6951058 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6951059 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6951060 : term291 = (and True).
Proof. exact (MK_COMB (@lem6951059) (@lem6951058)). Qed.
Lemma lem6951061 : term290 = (True /\ False).
Proof. exact (MK_COMB (@lem6951060) (@lem6951057)). Qed.
Lemma lem6951063 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6951064 : term290 = False.
Proof. exact (TRANS (@lem6951061) (@lem6951063)). Qed.
Lemma lem6951065 : term281 = False.
Proof. exact (TRANS (@lem6951053) (@lem6951064)). Qed.
Lemma lem6951066 : term286 = False.
Proof. exact (TRANS (@lem6951050) (@lem6951065)). Qed.
Lemma lem6951067 : term283 = False.
Proof. exact (TRANS (@lem6951034) (@lem6951066)). Qed.
Lemma lem6951068 : term281 = False.
Proof. exact (TRANS (@lem6951011) (@lem6951067)). Qed.
Lemma lem6951069 : term280 = False.
Proof. exact (TRANS (@lem6951002) (@lem6951068)). Qed.
Lemma lem6951070 (_92591 : int) (h1 : term306 _92591) : False.
Proof. exact (EQ_MP (@lem6951069) (@lem6950999 _92591 h1)). Qed.
Lemma lem6951071 (_92591 : int) (h1 : term205 _92591) : term205 _92591.
Proof. exact (h1). Qed.
Lemma lem6951072 (_92591 : int) (h1 : term205 _92591) : term184 _92591.
Proof. exact (proj2 (@lem6951071 _92591 h1)). Qed.
Lemma lem6951074 (_92591 : int) (h1 : term205 _92591) : term175 _92591.
Proof. exact (proj2 (@lem6951072 _92591 h1)). Qed.
Lemma lem6951075 (_92591 : int) (h1 : term205 _92591) : term163 _92591.
Proof. exact (proj1 (@lem6951072 _92591 h1)). Qed.
Lemma lem6951077 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6951078 : term225 = term226.
Proof. exact (@lem6951077 term53 term69). Qed.
Lemma lem6951080 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6951081 : term69 = term140.
Proof. exact (@lem6951080 term70). Qed.
Lemma lem6951083 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6951084 : term53 = term111.
Proof. exact (@lem6951083 (NUMERAL 0)). Qed.
Lemma lem6951085 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6951086 : term227 = term228.
Proof. exact (MK_COMB (@lem6951085) (@lem6951084)). Qed.
Lemma lem6951087 : term226 = term229.
Proof. exact (MK_COMB (@lem6951086) (@lem6951081)). Qed.
Lemma lem6951088 : term230.
Proof. exact (@lem1980255 term53 term69 term69 term69). Qed.
Lemma lem6951090 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6951091 : term226 = term232.
Proof. exact (@lem6951090 (NUMERAL 0) term70). Qed.
Lemma lem6951092 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6951093 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6951094 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6951093 h1) (fun h1 : term232 = True => @lem6951092)). Qed.
Lemma lem6951095 : term232 = True.
Proof. exact (EQ_MP (@lem6951094) (@lem6951092)). Qed.
Lemma lem6951096 : term226 = True.
Proof. exact (TRANS (@lem6951091) (@lem6951095)). Qed.
Lemma lem6951097 : True = term226.
Proof. exact (SYM (@lem6951096)). Qed.
Lemma lem6951098 : term226.
Proof. exact (EQ_MP (@lem6951097) (@lem0)). Qed.
Lemma lem6951099 : term234.
Proof. exact (@lem6951088 (@lem6951098)). Qed.
Lemma lem6951101 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6951102 : term226 = term232.
Proof. exact (@lem6951101 (NUMERAL 0) term70). Qed.
Lemma lem6951103 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6951104 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6951105 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6951104 h1) (fun h1 : term232 = True => @lem6951103)). Qed.
Lemma lem6951106 : term232 = True.
Proof. exact (EQ_MP (@lem6951105) (@lem6951103)). Qed.
Lemma lem6951107 : term226 = True.
Proof. exact (TRANS (@lem6951102) (@lem6951106)). Qed.
Lemma lem6951108 : True = term226.
Proof. exact (SYM (@lem6951107)). Qed.
Lemma lem6951109 : term226.
Proof. exact (EQ_MP (@lem6951108) (@lem0)). Qed.
Lemma lem6951110 : term229 = term235.
Proof. exact (@lem6951099 (@lem6951109)). Qed.
Lemma lem6951112 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6951113 : term123 = term124.
Proof. exact (@lem6951112 term70 term70). Qed.
Lemma lem6951114 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6951115 : term126 = term70.
Proof. exact (EQ_MP (@lem6951114) (@lem940073)). Qed.
Lemma lem6951116 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6951117 : term124 = term69.
Proof. exact (MK_COMB (@lem6951116) (@lem6951115)). Qed.
Lemma lem6951118 : term123 = term69.
Proof. exact (TRANS (@lem6951113) (@lem6951117)). Qed.
Lemma lem6951120 (x : nat) : (term236 x) = term53.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6951121 : term237 = term53.
Proof. exact (@lem6951120 term70). Qed.
Lemma lem6951122 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6951123 : term238 = term227.
Proof. exact (MK_COMB (@lem6951122) (@lem6951121)). Qed.
Lemma lem6951124 : term235 = term226.
Proof. exact (MK_COMB (@lem6951123) (@lem6951118)). Qed.
Lemma lem6951126 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6951127 : term226 = term232.
Proof. exact (@lem6951126 (NUMERAL 0) term70). Qed.
Lemma lem6951128 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6951129 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6951130 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6951129 h1) (fun h1 : term232 = True => @lem6951128)). Qed.
Lemma lem6951131 : term232 = True.
Proof. exact (EQ_MP (@lem6951130) (@lem6951128)). Qed.
Lemma lem6951132 : term226 = True.
Proof. exact (TRANS (@lem6951127) (@lem6951131)). Qed.
Lemma lem6951133 : term235 = True.
Proof. exact (TRANS (@lem6951124) (@lem6951132)). Qed.
Lemma lem6951134 : term229 = True.
Proof. exact (TRANS (@lem6951110) (@lem6951133)). Qed.
Lemma lem6951135 : term226 = True.
Proof. exact (TRANS (@lem6951087) (@lem6951134)). Qed.
Lemma lem6951136 : term225 = True.
Proof. exact (TRANS (@lem6951078) (@lem6951135)). Qed.
Lemma lem6951137 : True = term225.
Proof. exact (SYM (@lem6951136)). Qed.
Lemma lem6951138 : term225.
Proof. exact (EQ_MP (@lem6951137) (@lem0)). Qed.
Lemma lem6951139 (_92591 : int) (h1 : term205 _92591) : term292 _92591.
Proof. exact (conj (@lem6951138) (@lem6951075 _92591 h1)). Qed.
Lemma lem6951141 (x : real) (y : real) : term240 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6951142 (_92591 : int) : term293 _92591.
Proof. exact (@lem6951141 term69 (term160 _92591)). Qed.
Lemma lem6951143 (_92591 : int) (h1 : term205 _92591) : term294 _92591.
Proof. exact (@lem6951142 _92591 (@lem6951139 _92591 h1)). Qed.
Lemma lem6951144 (_92591 : int) : (term295 _92591) = (term160 _92591).
Proof. exact (@lem1982733 (term160 _92591)). Qed.
Lemma lem6951145 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6951146 (_92591 : int) : (term296 _92591) = (term162 _92591).
Proof. exact (MK_COMB (@lem6951145) (@lem6951144 _92591)). Qed.
Lemma lem6951147 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem6951148 (_92591 : int) : (term294 _92591) = (term163 _92591).
Proof. exact (MK_COMB (@lem6951146 _92591) (@lem6951147)). Qed.
Lemma lem6951149 (_92591 : int) (h1 : term205 _92591) : term163 _92591.
Proof. exact (EQ_MP (@lem6951148 _92591) (@lem6951143 _92591 h1)). Qed.
Lemma lem6951151 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6951152 : term225 = term226.
Proof. exact (@lem6951151 term53 term69). Qed.
Lemma lem6951154 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6951155 : term69 = term140.
Proof. exact (@lem6951154 term70). Qed.
Lemma lem6951157 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6951158 : term53 = term111.
Proof. exact (@lem6951157 (NUMERAL 0)). Qed.
Lemma lem6951159 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6951160 : term227 = term228.
Proof. exact (MK_COMB (@lem6951159) (@lem6951158)). Qed.
Lemma lem6951161 : term226 = term229.
Proof. exact (MK_COMB (@lem6951160) (@lem6951155)). Qed.
Lemma lem6951162 : term230.
Proof. exact (@lem1980255 term53 term69 term69 term69). Qed.
Lemma lem6951164 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6951165 : term226 = term232.
Proof. exact (@lem6951164 (NUMERAL 0) term70). Qed.
Lemma lem6951166 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6951167 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6951168 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6951167 h1) (fun h1 : term232 = True => @lem6951166)). Qed.
Lemma lem6951169 : term232 = True.
Proof. exact (EQ_MP (@lem6951168) (@lem6951166)). Qed.
Lemma lem6951170 : term226 = True.
Proof. exact (TRANS (@lem6951165) (@lem6951169)). Qed.
Lemma lem6951171 : True = term226.
Proof. exact (SYM (@lem6951170)). Qed.
Lemma lem6951172 : term226.
Proof. exact (EQ_MP (@lem6951171) (@lem0)). Qed.
Lemma lem6951173 : term234.
Proof. exact (@lem6951162 (@lem6951172)). Qed.
Lemma lem6951175 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6951176 : term226 = term232.
Proof. exact (@lem6951175 (NUMERAL 0) term70). Qed.
Lemma lem6951177 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6951178 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6951179 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6951178 h1) (fun h1 : term232 = True => @lem6951177)). Qed.
Lemma lem6951180 : term232 = True.
Proof. exact (EQ_MP (@lem6951179) (@lem6951177)). Qed.
Lemma lem6951181 : term226 = True.
Proof. exact (TRANS (@lem6951176) (@lem6951180)). Qed.
Lemma lem6951182 : True = term226.
Proof. exact (SYM (@lem6951181)). Qed.
Lemma lem6951183 : term226.
Proof. exact (EQ_MP (@lem6951182) (@lem0)). Qed.
Lemma lem6951184 : term229 = term235.
Proof. exact (@lem6951173 (@lem6951183)). Qed.
Lemma lem6951186 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6951187 : term123 = term124.
Proof. exact (@lem6951186 term70 term70). Qed.
Lemma lem6951188 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6951189 : term126 = term70.
Proof. exact (EQ_MP (@lem6951188) (@lem940073)). Qed.
Lemma lem6951190 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6951191 : term124 = term69.
Proof. exact (MK_COMB (@lem6951190) (@lem6951189)). Qed.
Lemma lem6951192 : term123 = term69.
Proof. exact (TRANS (@lem6951187) (@lem6951191)). Qed.
Lemma lem6951194 (x : nat) : (term236 x) = term53.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6951195 : term237 = term53.
Proof. exact (@lem6951194 term70). Qed.
Lemma lem6951196 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6951197 : term238 = term227.
Proof. exact (MK_COMB (@lem6951196) (@lem6951195)). Qed.
Lemma lem6951198 : term235 = term226.
Proof. exact (MK_COMB (@lem6951197) (@lem6951192)). Qed.
Lemma lem6951200 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6951201 : term226 = term232.
Proof. exact (@lem6951200 (NUMERAL 0) term70). Qed.
Lemma lem6951202 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6951203 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6951204 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6951203 h1) (fun h1 : term232 = True => @lem6951202)). Qed.
Lemma lem6951205 : term232 = True.
Proof. exact (EQ_MP (@lem6951204) (@lem6951202)). Qed.
Lemma lem6951206 : term226 = True.
Proof. exact (TRANS (@lem6951201) (@lem6951205)). Qed.
Lemma lem6951207 : term235 = True.
Proof. exact (TRANS (@lem6951198) (@lem6951206)). Qed.
Lemma lem6951208 : term229 = True.
Proof. exact (TRANS (@lem6951184) (@lem6951207)). Qed.
Lemma lem6951209 : term226 = True.
Proof. exact (TRANS (@lem6951161) (@lem6951208)). Qed.
Lemma lem6951210 : term225 = True.
Proof. exact (TRANS (@lem6951152) (@lem6951209)). Qed.
Lemma lem6951211 : True = term225.
Proof. exact (SYM (@lem6951210)). Qed.
Lemma lem6951212 : term225.
Proof. exact (EQ_MP (@lem6951211) (@lem0)). Qed.
Lemma lem6951213 (_92591 : int) (h1 : term205 _92591) : term317 _92591.
Proof. exact (conj (@lem6951212) (@lem6951074 _92591 h1)). Qed.
Lemma lem6951215 (x : real) (y : real) : term240 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6951216 (_92591 : int) : term318 _92591.
Proof. exact (@lem6951215 term69 (term172 _92591)). Qed.
Lemma lem6951217 (_92591 : int) (h1 : term205 _92591) : term319 _92591.
Proof. exact (@lem6951216 _92591 (@lem6951213 _92591 h1)). Qed.
Lemma lem6951218 (_92591 : int) : (term320 _92591) = (term172 _92591).
Proof. exact (@lem1982733 (term172 _92591)). Qed.
Lemma lem6951219 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6951220 (_92591 : int) : (term321 _92591) = (term174 _92591).
Proof. exact (MK_COMB (@lem6951219) (@lem6951218 _92591)). Qed.
Lemma lem6951221 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem6951222 (_92591 : int) : (term319 _92591) = (term175 _92591).
Proof. exact (MK_COMB (@lem6951220 _92591) (@lem6951221)). Qed.
Lemma lem6951223 (_92591 : int) (h1 : term205 _92591) : term175 _92591.
Proof. exact (EQ_MP (@lem6951222 _92591) (@lem6951217 _92591 h1)). Qed.
Lemma lem6951224 (_92591 : int) (h1 : term205 _92591) : term322 _92591.
Proof. exact (conj (@lem6951223 _92591 h1) (@lem6951149 _92591 h1)). Qed.
Lemma lem6951226 (x : real) (y : real) : term312 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem6951227 (_92591 : int) : term323 _92591.
Proof. exact (@lem6951226 (term172 _92591) (term160 _92591)). Qed.
Lemma lem6951228 (_92591 : int) (h1 : term205 _92591) : term300 _92591.
Proof. exact (@lem6951227 _92591 (@lem6951224 _92591 h1)). Qed.
Lemma lem6951229 (_92591 : int) : (term301 _92591) = (term302 _92591).
Proof. exact (@lem1982763 (term172 _92591) (real_of_int _92591) term114). Qed.
Lemma lem6951230 (_92591 : int) : (term303 _92591) = (term258 _92591).
Proof. exact (@lem1982713 term114 (real_of_int _92591)). Qed.
Lemma lem6951232 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6951233 : term69 = term140.
Proof. exact (@lem6951232 term70). Qed.
Lemma lem6951235 (x : nat) : (term112 x) = (term113 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6951236 : term114 = term115.
Proof. exact (@lem6951235 term70). Qed.
Lemma lem6951237 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6951238 : term259 = term260.
Proof. exact (MK_COMB (@lem6951237) (@lem6951236)). Qed.
Lemma lem6951239 : term261 = term262.
Proof. exact (MK_COMB (@lem6951238) (@lem6951233)). Qed.
Lemma lem6951240 : term263.
Proof. exact (@lem1981473 term114 term69 term69 term69 term53 term69). Qed.
Lemma lem6951242 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6951243 : term226 = term232.
Proof. exact (@lem6951242 (NUMERAL 0) term70). Qed.
Lemma lem6951244 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6951245 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6951246 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6951245 h1) (fun h1 : term232 = True => @lem6951244)). Qed.
Lemma lem6951247 : term232 = True.
Proof. exact (EQ_MP (@lem6951246) (@lem6951244)). Qed.
Lemma lem6951248 : term226 = True.
Proof. exact (TRANS (@lem6951243) (@lem6951247)). Qed.
Lemma lem6951249 : True = term226.
Proof. exact (SYM (@lem6951248)). Qed.
Lemma lem6951250 : term226.
Proof. exact (EQ_MP (@lem6951249) (@lem0)). Qed.
Lemma lem6951251 : term264.
Proof. exact (@lem6951240 (@lem6951250)). Qed.
Lemma lem6951253 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6951254 : term226 = term232.
Proof. exact (@lem6951253 (NUMERAL 0) term70). Qed.
Lemma lem6951255 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6951256 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6951257 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6951256 h1) (fun h1 : term232 = True => @lem6951255)). Qed.
Lemma lem6951258 : term232 = True.
Proof. exact (EQ_MP (@lem6951257) (@lem6951255)). Qed.
Lemma lem6951259 : term226 = True.
Proof. exact (TRANS (@lem6951254) (@lem6951258)). Qed.
Lemma lem6951260 : True = term226.
Proof. exact (SYM (@lem6951259)). Qed.
Lemma lem6951261 : term226.
Proof. exact (EQ_MP (@lem6951260) (@lem0)). Qed.
Lemma lem6951262 : term265.
Proof. exact (@lem6951251 (@lem6951261)). Qed.
Lemma lem6951264 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6951265 : term226 = term232.
Proof. exact (@lem6951264 (NUMERAL 0) term70). Qed.
Lemma lem6951266 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6951267 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6951268 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6951267 h1) (fun h1 : term232 = True => @lem6951266)). Qed.
Lemma lem6951269 : term232 = True.
Proof. exact (EQ_MP (@lem6951268) (@lem6951266)). Qed.
Lemma lem6951270 : term226 = True.
Proof. exact (TRANS (@lem6951265) (@lem6951269)). Qed.
Lemma lem6951271 : True = term226.
Proof. exact (SYM (@lem6951270)). Qed.
Lemma lem6951272 : term226.
Proof. exact (EQ_MP (@lem6951271) (@lem0)). Qed.
Lemma lem6951273 : term266.
Proof. exact (@lem6951262 (@lem6951272)). Qed.
Lemma lem6951275 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6951276 : term123 = term124.
Proof. exact (@lem6951275 term70 term70). Qed.
Lemma lem6951277 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6951278 : term126 = term70.
Proof. exact (EQ_MP (@lem6951277) (@lem940073)). Qed.
Lemma lem6951279 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6951280 : term124 = term69.
Proof. exact (MK_COMB (@lem6951279) (@lem6951278)). Qed.
Lemma lem6951281 : term123 = term69.
Proof. exact (TRANS (@lem6951276) (@lem6951280)). Qed.
Lemma lem6951283 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6951284 : term141 = term146.
Proof. exact (@lem6951283 term70 term70). Qed.
Lemma lem6951285 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6951286 : term126 = term70.
Proof. exact (EQ_MP (@lem6951285) (@lem940073)). Qed.
Lemma lem6951287 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6951288 : term124 = term69.
Proof. exact (MK_COMB (@lem6951287) (@lem6951286)). Qed.
Lemma lem6951289 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6951290 : term146 = term114.
Proof. exact (MK_COMB (@lem6951289) (@lem6951288)). Qed.
Lemma lem6951291 : term141 = term114.
Proof. exact (TRANS (@lem6951284) (@lem6951290)). Qed.
Lemma lem6951292 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6951293 : term267 = term259.
Proof. exact (MK_COMB (@lem6951292) (@lem6951291)). Qed.
Lemma lem6951294 : term268 = term261.
Proof. exact (MK_COMB (@lem6951293) (@lem6951281)). Qed.
Lemma lem6951296 (m : nat) : (term269 m) = term53.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6951297 : term261 = term53.
Proof. exact (@lem6951296 term70). Qed.
Lemma lem6951298 : term268 = term53.
Proof. exact (TRANS (@lem6951294) (@lem6951297)). Qed.
Lemma lem6951299 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6951300 : term270 = term271.
Proof. exact (MK_COMB (@lem6951299) (@lem6951298)). Qed.
Lemma lem6951301 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem6951302 : term272 = term237.
Proof. exact (MK_COMB (@lem6951300) (@lem6951301)). Qed.
Lemma lem6951304 (x : nat) : (term236 x) = term53.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6951305 : term237 = term53.
Proof. exact (@lem6951304 term70). Qed.
Lemma lem6951306 : term272 = term53.
Proof. exact (TRANS (@lem6951302) (@lem6951305)). Qed.
Lemma lem6951308 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6951309 : term123 = term124.
Proof. exact (@lem6951308 term70 term70). Qed.
Lemma lem6951310 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6951311 : term126 = term70.
Proof. exact (EQ_MP (@lem6951310) (@lem940073)). Qed.
Lemma lem6951312 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6951313 : term124 = term69.
Proof. exact (MK_COMB (@lem6951312) (@lem6951311)). Qed.
Lemma lem6951314 : term123 = term69.
Proof. exact (TRANS (@lem6951309) (@lem6951313)). Qed.
Lemma lem6951315 : term271 = term271.
Proof. exact (eq_refl term271). Qed.
Lemma lem6951316 : term273 = term237.
Proof. exact (MK_COMB (@lem6951315) (@lem6951314)). Qed.
Lemma lem6951318 (x : nat) : (term236 x) = term53.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6951319 : term237 = term53.
Proof. exact (@lem6951318 term70). Qed.
Lemma lem6951320 : term273 = term53.
Proof. exact (TRANS (@lem6951316) (@lem6951319)). Qed.
Lemma lem6951321 : term53 = term273.
Proof. exact (SYM (@lem6951320)). Qed.
Lemma lem6951322 : term272 = term273.
Proof. exact (TRANS (@lem6951306) (@lem6951321)). Qed.
Lemma lem6951323 : term262 = term111.
Proof. exact (@lem6951273 (@lem6951322)). Qed.
Lemma lem6951324 : term261 = term111.
Proof. exact (TRANS (@lem6951239) (@lem6951323)). Qed.
Lemma lem6951326 (x : real) : (term130 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6951327 : term111 = term53.
Proof. exact (@lem6951326 term53). Qed.
Lemma lem6951328 : term261 = term53.
Proof. exact (TRANS (@lem6951324) (@lem6951327)). Qed.
Lemma lem6951329 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6951330 : term274 = term271.
Proof. exact (MK_COMB (@lem6951329) (@lem6951328)). Qed.
Lemma lem6951331 (_92591 : int) : (real_of_int _92591) = (real_of_int _92591).
Proof. exact (eq_refl (real_of_int _92591)). Qed.
Lemma lem6951332 (_92591 : int) : (term258 _92591) = (term275 _92591).
Proof. exact (MK_COMB (@lem6951330) (@lem6951331 _92591)). Qed.
Lemma lem6951333 (_92591 : int) : (term303 _92591) = (term275 _92591).
Proof. exact (TRANS (@lem6951230 _92591) (@lem6951332 _92591)). Qed.
Lemma lem6951334 (_92591 : int) : (term275 _92591) = term53.
Proof. exact (@lem1982719 (real_of_int _92591)). Qed.
Lemma lem6951335 (_92591 : int) : (term303 _92591) = term53.
Proof. exact (TRANS (@lem6951333 _92591) (@lem6951334 _92591)). Qed.
Lemma lem6951336 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6951337 (_92591 : int) : (term304 _92591) = term84.
Proof. exact (MK_COMB (@lem6951336) (@lem6951335 _92591)). Qed.
Lemma lem6951338 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem6951339 (_92591 : int) : (term302 _92591) = term277.
Proof. exact (MK_COMB (@lem6951337 _92591) (@lem6951338)). Qed.
Lemma lem6951340 (_92591 : int) : (term301 _92591) = term277.
Proof. exact (TRANS (@lem6951229 _92591) (@lem6951339 _92591)). Qed.
Lemma lem6951341 : term277 = term114.
Proof. exact (@lem1982721 term114). Qed.
Lemma lem6951342 (_92591 : int) : (term301 _92591) = term114.
Proof. exact (TRANS (@lem6951340 _92591) (@lem6951341)). Qed.
Lemma lem6951343 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6951344 (_92591 : int) : (term305 _92591) = term279.
Proof. exact (MK_COMB (@lem6951343) (@lem6951342 _92591)). Qed.
Lemma lem6951345 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem6951346 (_92591 : int) : (term300 _92591) = term280.
Proof. exact (MK_COMB (@lem6951344 _92591) (@lem6951345)). Qed.
Lemma lem6951347 (_92591 : int) (h1 : term205 _92591) : term280.
Proof. exact (EQ_MP (@lem6951346 _92591) (@lem6951228 _92591 h1)). Qed.
Lemma lem6951349 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6951350 : term280 = term281.
Proof. exact (@lem6951349 term53 term114). Qed.
Lemma lem6951352 (x : nat) : (term112 x) = (term113 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6951353 : term114 = term115.
Proof. exact (@lem6951352 term70). Qed.
Lemma lem6951355 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6951356 : term53 = term111.
Proof. exact (@lem6951355 (NUMERAL 0)). Qed.
Lemma lem6951357 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6951358 : term55 = term282.
Proof. exact (MK_COMB (@lem6951357) (@lem6951356)). Qed.
Lemma lem6951359 : term281 = term283.
Proof. exact (MK_COMB (@lem6951358) (@lem6951353)). Qed.
Lemma lem6951360 : term284.
Proof. exact (@lem1980026 term53 term69 term114 term69). Qed.
Lemma lem6951362 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6951363 : term226 = term232.
Proof. exact (@lem6951362 (NUMERAL 0) term70). Qed.
Lemma lem6951364 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6951365 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6951366 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6951365 h1) (fun h1 : term232 = True => @lem6951364)). Qed.
Lemma lem6951367 : term232 = True.
Proof. exact (EQ_MP (@lem6951366) (@lem6951364)). Qed.
Lemma lem6951368 : term226 = True.
Proof. exact (TRANS (@lem6951363) (@lem6951367)). Qed.
Lemma lem6951369 : True = term226.
Proof. exact (SYM (@lem6951368)). Qed.
Lemma lem6951370 : term226.
Proof. exact (EQ_MP (@lem6951369) (@lem0)). Qed.
Lemma lem6951371 : term285.
Proof. exact (@lem6951360 (@lem6951370)). Qed.
Lemma lem6951373 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6951374 : term226 = term232.
Proof. exact (@lem6951373 (NUMERAL 0) term70). Qed.
Lemma lem6951375 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6951376 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6951377 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6951376 h1) (fun h1 : term232 = True => @lem6951375)). Qed.
Lemma lem6951378 : term232 = True.
Proof. exact (EQ_MP (@lem6951377) (@lem6951375)). Qed.
Lemma lem6951379 : term226 = True.
Proof. exact (TRANS (@lem6951374) (@lem6951378)). Qed.
Lemma lem6951380 : True = term226.
Proof. exact (SYM (@lem6951379)). Qed.
Lemma lem6951381 : term226.
Proof. exact (EQ_MP (@lem6951380) (@lem0)). Qed.
Lemma lem6951382 : term283 = term286.
Proof. exact (@lem6951371 (@lem6951381)). Qed.
Lemma lem6951384 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6951385 : term141 = term146.
Proof. exact (@lem6951384 term70 term70). Qed.
Lemma lem6951386 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6951387 : term126 = term70.
Proof. exact (EQ_MP (@lem6951386) (@lem940073)). Qed.
Lemma lem6951388 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6951389 : term124 = term69.
Proof. exact (MK_COMB (@lem6951388) (@lem6951387)). Qed.
Lemma lem6951390 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6951391 : term146 = term114.
Proof. exact (MK_COMB (@lem6951390) (@lem6951389)). Qed.
Lemma lem6951392 : term141 = term114.
Proof. exact (TRANS (@lem6951385) (@lem6951391)). Qed.
Lemma lem6951394 (x : nat) : (term236 x) = term53.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6951395 : term237 = term53.
Proof. exact (@lem6951394 term70). Qed.
Lemma lem6951396 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6951397 : term287 = term55.
Proof. exact (MK_COMB (@lem6951396) (@lem6951395)). Qed.
Lemma lem6951398 : term286 = term281.
Proof. exact (MK_COMB (@lem6951397) (@lem6951392)). Qed.
Lemma lem6951400 (m : nat) (n : nat) : (term288 m n) = (term289 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6951401 : term281 = term290.
Proof. exact (@lem6951400 (NUMERAL 0) term70). Qed.
Lemma lem6951402 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6951403 (h1 : term233 = (BIT1 0)) : (term70 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6951404 : (term233 = (BIT1 0)) = ((term70 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6951403 h1) (fun h1 : (term70 = (NUMERAL 0)) = False => @lem6951402)). Qed.
Lemma lem6951405 : (term70 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6951404) (@lem6951402)). Qed.
Lemma lem6951406 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6951407 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6951408 : term291 = (and True).
Proof. exact (MK_COMB (@lem6951407) (@lem6951406)). Qed.
Lemma lem6951409 : term290 = (True /\ False).
Proof. exact (MK_COMB (@lem6951408) (@lem6951405)). Qed.
Lemma lem6951411 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6951412 : term290 = False.
Proof. exact (TRANS (@lem6951409) (@lem6951411)). Qed.
Lemma lem6951413 : term281 = False.
Proof. exact (TRANS (@lem6951401) (@lem6951412)). Qed.
Lemma lem6951414 : term286 = False.
Proof. exact (TRANS (@lem6951398) (@lem6951413)). Qed.
Lemma lem6951415 : term283 = False.
Proof. exact (TRANS (@lem6951382) (@lem6951414)). Qed.
Lemma lem6951416 : term281 = False.
Proof. exact (TRANS (@lem6951359) (@lem6951415)). Qed.
Lemma lem6951417 : term280 = False.
Proof. exact (TRANS (@lem6951350) (@lem6951416)). Qed.
Lemma lem6951418 (_92591 : int) (h1 : term205 _92591) : False.
Proof. exact (EQ_MP (@lem6951417) (@lem6951347 _92591 h1)). Qed.
Lemma lem6951419 (_92591 : int) (h1 : term207 _92591) : False.
Proof. exact (or_elim (@lem6950722 _92591 h1) (fun h0 : term306 _92591 => @lem6951070 _92591 h0) (fun h0 : term205 _92591 => @lem6951418 _92591 h0)). Qed.
Lemma lem6951420 (_92591 : int) (h1 : term205 _92591) : term205 _92591.
Proof. exact (h1). Qed.
Lemma lem6951421 (_92591 : int) (h1 : term205 _92591) : term184 _92591.
Proof. exact (proj2 (@lem6951420 _92591 h1)). Qed.
Lemma lem6951423 (_92591 : int) (h1 : term205 _92591) : term175 _92591.
Proof. exact (proj2 (@lem6951421 _92591 h1)). Qed.
Lemma lem6951424 (_92591 : int) (h1 : term205 _92591) : term163 _92591.
Proof. exact (proj1 (@lem6951421 _92591 h1)). Qed.
Lemma lem6951426 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6951427 : term225 = term226.
Proof. exact (@lem6951426 term53 term69). Qed.
Lemma lem6951429 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6951430 : term69 = term140.
Proof. exact (@lem6951429 term70). Qed.
Lemma lem6951432 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6951433 : term53 = term111.
Proof. exact (@lem6951432 (NUMERAL 0)). Qed.
Lemma lem6951434 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6951435 : term227 = term228.
Proof. exact (MK_COMB (@lem6951434) (@lem6951433)). Qed.
Lemma lem6951436 : term226 = term229.
Proof. exact (MK_COMB (@lem6951435) (@lem6951430)). Qed.
Lemma lem6951437 : term230.
Proof. exact (@lem1980255 term53 term69 term69 term69). Qed.
Lemma lem6951439 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6951440 : term226 = term232.
Proof. exact (@lem6951439 (NUMERAL 0) term70). Qed.
Lemma lem6951441 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6951442 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6951443 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6951442 h1) (fun h1 : term232 = True => @lem6951441)). Qed.
Lemma lem6951444 : term232 = True.
Proof. exact (EQ_MP (@lem6951443) (@lem6951441)). Qed.
Lemma lem6951445 : term226 = True.
Proof. exact (TRANS (@lem6951440) (@lem6951444)). Qed.
Lemma lem6951446 : True = term226.
Proof. exact (SYM (@lem6951445)). Qed.
Lemma lem6951447 : term226.
Proof. exact (EQ_MP (@lem6951446) (@lem0)). Qed.
Lemma lem6951448 : term234.
Proof. exact (@lem6951437 (@lem6951447)). Qed.
Lemma lem6951450 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6951451 : term226 = term232.
Proof. exact (@lem6951450 (NUMERAL 0) term70). Qed.
Lemma lem6951452 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6951453 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6951454 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6951453 h1) (fun h1 : term232 = True => @lem6951452)). Qed.
Lemma lem6951455 : term232 = True.
Proof. exact (EQ_MP (@lem6951454) (@lem6951452)). Qed.
Lemma lem6951456 : term226 = True.
Proof. exact (TRANS (@lem6951451) (@lem6951455)). Qed.
Lemma lem6951457 : True = term226.
Proof. exact (SYM (@lem6951456)). Qed.
Lemma lem6951458 : term226.
Proof. exact (EQ_MP (@lem6951457) (@lem0)). Qed.
Lemma lem6951459 : term229 = term235.
Proof. exact (@lem6951448 (@lem6951458)). Qed.
Lemma lem6951461 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6951462 : term123 = term124.
Proof. exact (@lem6951461 term70 term70). Qed.
Lemma lem6951463 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6951464 : term126 = term70.
Proof. exact (EQ_MP (@lem6951463) (@lem940073)). Qed.
Lemma lem6951465 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6951466 : term124 = term69.
Proof. exact (MK_COMB (@lem6951465) (@lem6951464)). Qed.
Lemma lem6951467 : term123 = term69.
Proof. exact (TRANS (@lem6951462) (@lem6951466)). Qed.
Lemma lem6951469 (x : nat) : (term236 x) = term53.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6951470 : term237 = term53.
Proof. exact (@lem6951469 term70). Qed.
Lemma lem6951471 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6951472 : term238 = term227.
Proof. exact (MK_COMB (@lem6951471) (@lem6951470)). Qed.
Lemma lem6951473 : term235 = term226.
Proof. exact (MK_COMB (@lem6951472) (@lem6951467)). Qed.
Lemma lem6951475 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6951476 : term226 = term232.
Proof. exact (@lem6951475 (NUMERAL 0) term70). Qed.
Lemma lem6951477 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6951478 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6951479 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6951478 h1) (fun h1 : term232 = True => @lem6951477)). Qed.
Lemma lem6951480 : term232 = True.
Proof. exact (EQ_MP (@lem6951479) (@lem6951477)). Qed.
Lemma lem6951481 : term226 = True.
Proof. exact (TRANS (@lem6951476) (@lem6951480)). Qed.
Lemma lem6951482 : term235 = True.
Proof. exact (TRANS (@lem6951473) (@lem6951481)). Qed.
Lemma lem6951483 : term229 = True.
Proof. exact (TRANS (@lem6951459) (@lem6951482)). Qed.
Lemma lem6951484 : term226 = True.
Proof. exact (TRANS (@lem6951436) (@lem6951483)). Qed.
Lemma lem6951485 : term225 = True.
Proof. exact (TRANS (@lem6951427) (@lem6951484)). Qed.
Lemma lem6951486 : True = term225.
Proof. exact (SYM (@lem6951485)). Qed.
Lemma lem6951487 : term225.
Proof. exact (EQ_MP (@lem6951486) (@lem0)). Qed.
Lemma lem6951488 (_92591 : int) (h1 : term205 _92591) : term292 _92591.
Proof. exact (conj (@lem6951487) (@lem6951424 _92591 h1)). Qed.
Lemma lem6951490 (x : real) (y : real) : term240 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6951491 (_92591 : int) : term293 _92591.
Proof. exact (@lem6951490 term69 (term160 _92591)). Qed.
Lemma lem6951492 (_92591 : int) (h1 : term205 _92591) : term294 _92591.
Proof. exact (@lem6951491 _92591 (@lem6951488 _92591 h1)). Qed.
Lemma lem6951493 (_92591 : int) : (term295 _92591) = (term160 _92591).
Proof. exact (@lem1982733 (term160 _92591)). Qed.
Lemma lem6951494 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6951495 (_92591 : int) : (term296 _92591) = (term162 _92591).
Proof. exact (MK_COMB (@lem6951494) (@lem6951493 _92591)). Qed.
Lemma lem6951496 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem6951497 (_92591 : int) : (term294 _92591) = (term163 _92591).
Proof. exact (MK_COMB (@lem6951495 _92591) (@lem6951496)). Qed.
Lemma lem6951498 (_92591 : int) (h1 : term205 _92591) : term163 _92591.
Proof. exact (EQ_MP (@lem6951497 _92591) (@lem6951492 _92591 h1)). Qed.
Lemma lem6951500 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6951501 : term225 = term226.
Proof. exact (@lem6951500 term53 term69). Qed.
Lemma lem6951503 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6951504 : term69 = term140.
Proof. exact (@lem6951503 term70). Qed.
Lemma lem6951506 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6951507 : term53 = term111.
Proof. exact (@lem6951506 (NUMERAL 0)). Qed.
Lemma lem6951508 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6951509 : term227 = term228.
Proof. exact (MK_COMB (@lem6951508) (@lem6951507)). Qed.
Lemma lem6951510 : term226 = term229.
Proof. exact (MK_COMB (@lem6951509) (@lem6951504)). Qed.
Lemma lem6951511 : term230.
Proof. exact (@lem1980255 term53 term69 term69 term69). Qed.
Lemma lem6951513 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6951514 : term226 = term232.
Proof. exact (@lem6951513 (NUMERAL 0) term70). Qed.
Lemma lem6951515 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6951516 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6951517 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6951516 h1) (fun h1 : term232 = True => @lem6951515)). Qed.
Lemma lem6951518 : term232 = True.
Proof. exact (EQ_MP (@lem6951517) (@lem6951515)). Qed.
Lemma lem6951519 : term226 = True.
Proof. exact (TRANS (@lem6951514) (@lem6951518)). Qed.
Lemma lem6951520 : True = term226.
Proof. exact (SYM (@lem6951519)). Qed.
Lemma lem6951521 : term226.
Proof. exact (EQ_MP (@lem6951520) (@lem0)). Qed.
Lemma lem6951522 : term234.
Proof. exact (@lem6951511 (@lem6951521)). Qed.
Lemma lem6951524 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6951525 : term226 = term232.
Proof. exact (@lem6951524 (NUMERAL 0) term70). Qed.
Lemma lem6951526 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6951527 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6951528 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6951527 h1) (fun h1 : term232 = True => @lem6951526)). Qed.
Lemma lem6951529 : term232 = True.
Proof. exact (EQ_MP (@lem6951528) (@lem6951526)). Qed.
Lemma lem6951530 : term226 = True.
Proof. exact (TRANS (@lem6951525) (@lem6951529)). Qed.
Lemma lem6951531 : True = term226.
Proof. exact (SYM (@lem6951530)). Qed.
Lemma lem6951532 : term226.
Proof. exact (EQ_MP (@lem6951531) (@lem0)). Qed.
Lemma lem6951533 : term229 = term235.
Proof. exact (@lem6951522 (@lem6951532)). Qed.
Lemma lem6951535 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6951536 : term123 = term124.
Proof. exact (@lem6951535 term70 term70). Qed.
Lemma lem6951537 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6951538 : term126 = term70.
Proof. exact (EQ_MP (@lem6951537) (@lem940073)). Qed.
Lemma lem6951539 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6951540 : term124 = term69.
Proof. exact (MK_COMB (@lem6951539) (@lem6951538)). Qed.
Lemma lem6951541 : term123 = term69.
Proof. exact (TRANS (@lem6951536) (@lem6951540)). Qed.
Lemma lem6951543 (x : nat) : (term236 x) = term53.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6951544 : term237 = term53.
Proof. exact (@lem6951543 term70). Qed.
Lemma lem6951545 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6951546 : term238 = term227.
Proof. exact (MK_COMB (@lem6951545) (@lem6951544)). Qed.
Lemma lem6951547 : term235 = term226.
Proof. exact (MK_COMB (@lem6951546) (@lem6951541)). Qed.
Lemma lem6951549 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6951550 : term226 = term232.
Proof. exact (@lem6951549 (NUMERAL 0) term70). Qed.
Lemma lem6951551 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6951552 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6951553 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6951552 h1) (fun h1 : term232 = True => @lem6951551)). Qed.
Lemma lem6951554 : term232 = True.
Proof. exact (EQ_MP (@lem6951553) (@lem6951551)). Qed.
Lemma lem6951555 : term226 = True.
Proof. exact (TRANS (@lem6951550) (@lem6951554)). Qed.
Lemma lem6951556 : term235 = True.
Proof. exact (TRANS (@lem6951547) (@lem6951555)). Qed.
Lemma lem6951557 : term229 = True.
Proof. exact (TRANS (@lem6951533) (@lem6951556)). Qed.
Lemma lem6951558 : term226 = True.
Proof. exact (TRANS (@lem6951510) (@lem6951557)). Qed.
Lemma lem6951559 : term225 = True.
Proof. exact (TRANS (@lem6951501) (@lem6951558)). Qed.
Lemma lem6951560 : True = term225.
Proof. exact (SYM (@lem6951559)). Qed.
Lemma lem6951561 : term225.
Proof. exact (EQ_MP (@lem6951560) (@lem0)). Qed.
Lemma lem6951562 (_92591 : int) (h1 : term205 _92591) : term317 _92591.
Proof. exact (conj (@lem6951561) (@lem6951423 _92591 h1)). Qed.
Lemma lem6951564 (x : real) (y : real) : term240 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6951565 (_92591 : int) : term318 _92591.
Proof. exact (@lem6951564 term69 (term172 _92591)). Qed.
Lemma lem6951566 (_92591 : int) (h1 : term205 _92591) : term319 _92591.
Proof. exact (@lem6951565 _92591 (@lem6951562 _92591 h1)). Qed.
Lemma lem6951567 (_92591 : int) : (term320 _92591) = (term172 _92591).
Proof. exact (@lem1982733 (term172 _92591)). Qed.
Lemma lem6951568 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6951569 (_92591 : int) : (term321 _92591) = (term174 _92591).
Proof. exact (MK_COMB (@lem6951568) (@lem6951567 _92591)). Qed.
Lemma lem6951570 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem6951571 (_92591 : int) : (term319 _92591) = (term175 _92591).
Proof. exact (MK_COMB (@lem6951569 _92591) (@lem6951570)). Qed.
Lemma lem6951572 (_92591 : int) (h1 : term205 _92591) : term175 _92591.
Proof. exact (EQ_MP (@lem6951571 _92591) (@lem6951566 _92591 h1)). Qed.
Lemma lem6951573 (_92591 : int) (h1 : term205 _92591) : term322 _92591.
Proof. exact (conj (@lem6951572 _92591 h1) (@lem6951498 _92591 h1)). Qed.
Lemma lem6951575 (x : real) (y : real) : term312 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem6951576 (_92591 : int) : term323 _92591.
Proof. exact (@lem6951575 (term172 _92591) (term160 _92591)). Qed.
Lemma lem6951577 (_92591 : int) (h1 : term205 _92591) : term300 _92591.
Proof. exact (@lem6951576 _92591 (@lem6951573 _92591 h1)). Qed.
Lemma lem6951578 (_92591 : int) : (term301 _92591) = (term302 _92591).
Proof. exact (@lem1982763 (term172 _92591) (real_of_int _92591) term114). Qed.
Lemma lem6951579 (_92591 : int) : (term303 _92591) = (term258 _92591).
Proof. exact (@lem1982713 term114 (real_of_int _92591)). Qed.
Lemma lem6951581 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6951582 : term69 = term140.
Proof. exact (@lem6951581 term70). Qed.
Lemma lem6951584 (x : nat) : (term112 x) = (term113 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6951585 : term114 = term115.
Proof. exact (@lem6951584 term70). Qed.
Lemma lem6951586 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6951587 : term259 = term260.
Proof. exact (MK_COMB (@lem6951586) (@lem6951585)). Qed.
Lemma lem6951588 : term261 = term262.
Proof. exact (MK_COMB (@lem6951587) (@lem6951582)). Qed.
Lemma lem6951589 : term263.
Proof. exact (@lem1981473 term114 term69 term69 term69 term53 term69). Qed.
Lemma lem6951591 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6951592 : term226 = term232.
Proof. exact (@lem6951591 (NUMERAL 0) term70). Qed.
Lemma lem6951593 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6951594 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6951595 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6951594 h1) (fun h1 : term232 = True => @lem6951593)). Qed.
Lemma lem6951596 : term232 = True.
Proof. exact (EQ_MP (@lem6951595) (@lem6951593)). Qed.
Lemma lem6951597 : term226 = True.
Proof. exact (TRANS (@lem6951592) (@lem6951596)). Qed.
Lemma lem6951598 : True = term226.
Proof. exact (SYM (@lem6951597)). Qed.
Lemma lem6951599 : term226.
Proof. exact (EQ_MP (@lem6951598) (@lem0)). Qed.
Lemma lem6951600 : term264.
Proof. exact (@lem6951589 (@lem6951599)). Qed.
Lemma lem6951602 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6951603 : term226 = term232.
Proof. exact (@lem6951602 (NUMERAL 0) term70). Qed.
Lemma lem6951604 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6951605 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6951606 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6951605 h1) (fun h1 : term232 = True => @lem6951604)). Qed.
Lemma lem6951607 : term232 = True.
Proof. exact (EQ_MP (@lem6951606) (@lem6951604)). Qed.
Lemma lem6951608 : term226 = True.
Proof. exact (TRANS (@lem6951603) (@lem6951607)). Qed.
Lemma lem6951609 : True = term226.
Proof. exact (SYM (@lem6951608)). Qed.
Lemma lem6951610 : term226.
Proof. exact (EQ_MP (@lem6951609) (@lem0)). Qed.
Lemma lem6951611 : term265.
Proof. exact (@lem6951600 (@lem6951610)). Qed.
Lemma lem6951613 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6951614 : term226 = term232.
Proof. exact (@lem6951613 (NUMERAL 0) term70). Qed.
Lemma lem6951615 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6951616 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6951617 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6951616 h1) (fun h1 : term232 = True => @lem6951615)). Qed.
Lemma lem6951618 : term232 = True.
Proof. exact (EQ_MP (@lem6951617) (@lem6951615)). Qed.
Lemma lem6951619 : term226 = True.
Proof. exact (TRANS (@lem6951614) (@lem6951618)). Qed.
Lemma lem6951620 : True = term226.
Proof. exact (SYM (@lem6951619)). Qed.
Lemma lem6951621 : term226.
Proof. exact (EQ_MP (@lem6951620) (@lem0)). Qed.
Lemma lem6951622 : term266.
Proof. exact (@lem6951611 (@lem6951621)). Qed.
Lemma lem6951624 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6951625 : term123 = term124.
Proof. exact (@lem6951624 term70 term70). Qed.
Lemma lem6951626 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6951627 : term126 = term70.
Proof. exact (EQ_MP (@lem6951626) (@lem940073)). Qed.
Lemma lem6951628 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6951629 : term124 = term69.
Proof. exact (MK_COMB (@lem6951628) (@lem6951627)). Qed.
Lemma lem6951630 : term123 = term69.
Proof. exact (TRANS (@lem6951625) (@lem6951629)). Qed.
Lemma lem6951632 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6951633 : term141 = term146.
Proof. exact (@lem6951632 term70 term70). Qed.
Lemma lem6951634 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6951635 : term126 = term70.
Proof. exact (EQ_MP (@lem6951634) (@lem940073)). Qed.
Lemma lem6951636 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6951637 : term124 = term69.
Proof. exact (MK_COMB (@lem6951636) (@lem6951635)). Qed.
Lemma lem6951638 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6951639 : term146 = term114.
Proof. exact (MK_COMB (@lem6951638) (@lem6951637)). Qed.
Lemma lem6951640 : term141 = term114.
Proof. exact (TRANS (@lem6951633) (@lem6951639)). Qed.
Lemma lem6951641 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6951642 : term267 = term259.
Proof. exact (MK_COMB (@lem6951641) (@lem6951640)). Qed.
Lemma lem6951643 : term268 = term261.
Proof. exact (MK_COMB (@lem6951642) (@lem6951630)). Qed.
Lemma lem6951645 (m : nat) : (term269 m) = term53.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6951646 : term261 = term53.
Proof. exact (@lem6951645 term70). Qed.
Lemma lem6951647 : term268 = term53.
Proof. exact (TRANS (@lem6951643) (@lem6951646)). Qed.
Lemma lem6951648 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6951649 : term270 = term271.
Proof. exact (MK_COMB (@lem6951648) (@lem6951647)). Qed.
Lemma lem6951650 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem6951651 : term272 = term237.
Proof. exact (MK_COMB (@lem6951649) (@lem6951650)). Qed.
Lemma lem6951653 (x : nat) : (term236 x) = term53.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6951654 : term237 = term53.
Proof. exact (@lem6951653 term70). Qed.
Lemma lem6951655 : term272 = term53.
Proof. exact (TRANS (@lem6951651) (@lem6951654)). Qed.
Lemma lem6951657 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6951658 : term123 = term124.
Proof. exact (@lem6951657 term70 term70). Qed.
Lemma lem6951659 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6951660 : term126 = term70.
Proof. exact (EQ_MP (@lem6951659) (@lem940073)). Qed.
Lemma lem6951661 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6951662 : term124 = term69.
Proof. exact (MK_COMB (@lem6951661) (@lem6951660)). Qed.
Lemma lem6951663 : term123 = term69.
Proof. exact (TRANS (@lem6951658) (@lem6951662)). Qed.
Lemma lem6951664 : term271 = term271.
Proof. exact (eq_refl term271). Qed.
Lemma lem6951665 : term273 = term237.
Proof. exact (MK_COMB (@lem6951664) (@lem6951663)). Qed.
Lemma lem6951667 (x : nat) : (term236 x) = term53.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6951668 : term237 = term53.
Proof. exact (@lem6951667 term70). Qed.
Lemma lem6951669 : term273 = term53.
Proof. exact (TRANS (@lem6951665) (@lem6951668)). Qed.
Lemma lem6951670 : term53 = term273.
Proof. exact (SYM (@lem6951669)). Qed.
Lemma lem6951671 : term272 = term273.
Proof. exact (TRANS (@lem6951655) (@lem6951670)). Qed.
Lemma lem6951672 : term262 = term111.
Proof. exact (@lem6951622 (@lem6951671)). Qed.
Lemma lem6951673 : term261 = term111.
Proof. exact (TRANS (@lem6951588) (@lem6951672)). Qed.
Lemma lem6951675 (x : real) : (term130 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6951676 : term111 = term53.
Proof. exact (@lem6951675 term53). Qed.
Lemma lem6951677 : term261 = term53.
Proof. exact (TRANS (@lem6951673) (@lem6951676)). Qed.
Lemma lem6951678 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6951679 : term274 = term271.
Proof. exact (MK_COMB (@lem6951678) (@lem6951677)). Qed.
Lemma lem6951680 (_92591 : int) : (real_of_int _92591) = (real_of_int _92591).
Proof. exact (eq_refl (real_of_int _92591)). Qed.
Lemma lem6951681 (_92591 : int) : (term258 _92591) = (term275 _92591).
Proof. exact (MK_COMB (@lem6951679) (@lem6951680 _92591)). Qed.
Lemma lem6951682 (_92591 : int) : (term303 _92591) = (term275 _92591).
Proof. exact (TRANS (@lem6951579 _92591) (@lem6951681 _92591)). Qed.
Lemma lem6951683 (_92591 : int) : (term275 _92591) = term53.
Proof. exact (@lem1982719 (real_of_int _92591)). Qed.
Lemma lem6951684 (_92591 : int) : (term303 _92591) = term53.
Proof. exact (TRANS (@lem6951682 _92591) (@lem6951683 _92591)). Qed.
Lemma lem6951685 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6951686 (_92591 : int) : (term304 _92591) = term84.
Proof. exact (MK_COMB (@lem6951685) (@lem6951684 _92591)). Qed.
Lemma lem6951687 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem6951688 (_92591 : int) : (term302 _92591) = term277.
Proof. exact (MK_COMB (@lem6951686 _92591) (@lem6951687)). Qed.
Lemma lem6951689 (_92591 : int) : (term301 _92591) = term277.
Proof. exact (TRANS (@lem6951578 _92591) (@lem6951688 _92591)). Qed.
Lemma lem6951690 : term277 = term114.
Proof. exact (@lem1982721 term114). Qed.
Lemma lem6951691 (_92591 : int) : (term301 _92591) = term114.
Proof. exact (TRANS (@lem6951689 _92591) (@lem6951690)). Qed.
Lemma lem6951692 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6951693 (_92591 : int) : (term305 _92591) = term279.
Proof. exact (MK_COMB (@lem6951692) (@lem6951691 _92591)). Qed.
Lemma lem6951694 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem6951695 (_92591 : int) : (term300 _92591) = term280.
Proof. exact (MK_COMB (@lem6951693 _92591) (@lem6951694)). Qed.
Lemma lem6951696 (_92591 : int) (h1 : term205 _92591) : term280.
Proof. exact (EQ_MP (@lem6951695 _92591) (@lem6951577 _92591 h1)). Qed.
Lemma lem6951698 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6951699 : term280 = term281.
Proof. exact (@lem6951698 term53 term114). Qed.
Lemma lem6951701 (x : nat) : (term112 x) = (term113 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6951702 : term114 = term115.
Proof. exact (@lem6951701 term70). Qed.
Lemma lem6951704 (x : nat) : (real_of_num x) = (term110 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6951705 : term53 = term111.
Proof. exact (@lem6951704 (NUMERAL 0)). Qed.
Lemma lem6951706 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6951707 : term55 = term282.
Proof. exact (MK_COMB (@lem6951706) (@lem6951705)). Qed.
Lemma lem6951708 : term281 = term283.
Proof. exact (MK_COMB (@lem6951707) (@lem6951702)). Qed.
Lemma lem6951709 : term284.
Proof. exact (@lem1980026 term53 term69 term114 term69). Qed.
Lemma lem6951711 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6951712 : term226 = term232.
Proof. exact (@lem6951711 (NUMERAL 0) term70). Qed.
Lemma lem6951713 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6951714 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6951715 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6951714 h1) (fun h1 : term232 = True => @lem6951713)). Qed.
Lemma lem6951716 : term232 = True.
Proof. exact (EQ_MP (@lem6951715) (@lem6951713)). Qed.
Lemma lem6951717 : term226 = True.
Proof. exact (TRANS (@lem6951712) (@lem6951716)). Qed.
Lemma lem6951718 : True = term226.
Proof. exact (SYM (@lem6951717)). Qed.
Lemma lem6951719 : term226.
Proof. exact (EQ_MP (@lem6951718) (@lem0)). Qed.
Lemma lem6951720 : term285.
Proof. exact (@lem6951709 (@lem6951719)). Qed.
Lemma lem6951722 (m : nat) (n : nat) : (term231 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6951723 : term226 = term232.
Proof. exact (@lem6951722 (NUMERAL 0) term70). Qed.
Lemma lem6951724 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6951725 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6951726 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6951725 h1) (fun h1 : term232 = True => @lem6951724)). Qed.
Lemma lem6951727 : term232 = True.
Proof. exact (EQ_MP (@lem6951726) (@lem6951724)). Qed.
Lemma lem6951728 : term226 = True.
Proof. exact (TRANS (@lem6951723) (@lem6951727)). Qed.
Lemma lem6951729 : True = term226.
Proof. exact (SYM (@lem6951728)). Qed.
Lemma lem6951730 : term226.
Proof. exact (EQ_MP (@lem6951729) (@lem0)). Qed.
Lemma lem6951731 : term283 = term286.
Proof. exact (@lem6951720 (@lem6951730)). Qed.
Lemma lem6951733 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6951734 : term141 = term146.
Proof. exact (@lem6951733 term70 term70). Qed.
Lemma lem6951735 : (term125 = (BIT1 0)) = (term126 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6951736 : term126 = term70.
Proof. exact (EQ_MP (@lem6951735) (@lem940073)). Qed.
Lemma lem6951737 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6951738 : term124 = term69.
Proof. exact (MK_COMB (@lem6951737) (@lem6951736)). Qed.
Lemma lem6951739 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6951740 : term146 = term114.
Proof. exact (MK_COMB (@lem6951739) (@lem6951738)). Qed.
Lemma lem6951741 : term141 = term114.
Proof. exact (TRANS (@lem6951734) (@lem6951740)). Qed.
Lemma lem6951743 (x : nat) : (term236 x) = term53.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6951744 : term237 = term53.
Proof. exact (@lem6951743 term70). Qed.
Lemma lem6951745 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6951746 : term287 = term55.
Proof. exact (MK_COMB (@lem6951745) (@lem6951744)). Qed.
Lemma lem6951747 : term286 = term281.
Proof. exact (MK_COMB (@lem6951746) (@lem6951741)). Qed.
Lemma lem6951749 (m : nat) (n : nat) : (term288 m n) = (term289 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6951750 : term281 = term290.
Proof. exact (@lem6951749 (NUMERAL 0) term70). Qed.
Lemma lem6951751 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6951752 (h1 : term233 = (BIT1 0)) : (term70 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6951753 : (term233 = (BIT1 0)) = ((term70 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem6951752 h1) (fun h1 : (term70 = (NUMERAL 0)) = False => @lem6951751)). Qed.
Lemma lem6951754 : (term70 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6951753) (@lem6951751)). Qed.
Lemma lem6951755 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6951756 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6951757 : term291 = (and True).
Proof. exact (MK_COMB (@lem6951756) (@lem6951755)). Qed.
Lemma lem6951758 : term290 = (True /\ False).
Proof. exact (MK_COMB (@lem6951757) (@lem6951754)). Qed.
Lemma lem6951760 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6951761 : term290 = False.
Proof. exact (TRANS (@lem6951758) (@lem6951760)). Qed.
Lemma lem6951762 : term281 = False.
Proof. exact (TRANS (@lem6951750) (@lem6951761)). Qed.
Lemma lem6951763 : term286 = False.
Proof. exact (TRANS (@lem6951747) (@lem6951762)). Qed.
Lemma lem6951764 : term283 = False.
Proof. exact (TRANS (@lem6951731) (@lem6951763)). Qed.
Lemma lem6951765 : term281 = False.
Proof. exact (TRANS (@lem6951708) (@lem6951764)). Qed.
Lemma lem6951766 : term280 = False.
Proof. exact (TRANS (@lem6951699) (@lem6951765)). Qed.
Lemma lem6951767 (_92591 : int) (h1 : term205 _92591) : False.
Proof. exact (EQ_MP (@lem6951766) (@lem6951696 _92591 h1)). Qed.
Lemma lem6951768 (_92591 : int) (h1 : term211 _92591) : False.
Proof. exact (or_elim (@lem6950721 _92591 h1) (fun h0 : term207 _92591 => @lem6951419 _92591 h0) (fun h0 : term205 _92591 => @lem6951767 _92591 h0)). Qed.
Lemma lem6951769 (_92591 : int) (h1 : term223 _92591) : False.
Proof. exact (or_elim (@lem6949855 _92591 h1) (fun h0 : term220 _92591 => @lem6950720 _92591 h0) (fun h0 : term211 _92591 => @lem6951768 _92591 h0)). Qed.
Lemma lem6951771 (_92591 : int) (h1 : term223 _92591) : term223 _92591.
Proof. exact (h1). Qed.
Lemma lem6951772 (_92591 : int) (h1 : term223 _92591) : (term223 _92591) = False.
Proof. exact (prop_ext (fun h2 : term223 _92591 => @lem6951769 _92591 h1) (fun h2 : False => @lem6951771 _92591 h1)). Qed.
Lemma lem6951773 (_92591 : int) (h1 : term223 _92591) : False.
Proof. exact (EQ_MP (@lem6951772 _92591 h1) (@lem6951771 _92591 h1)). Qed.
Lemma lem6951774 (_92591 : int) (h1 : term106 _92591) : term106 _92591.
Proof. exact (h1). Qed.
Lemma lem6951775 (_92591 : int) (h1 : term106 _92591) : term223 _92591.
Proof. exact (EQ_MP (@lem6949821 _92591) (@lem6951774 _92591 h1)). Qed.
Lemma lem6951776 (_92591 : int) (h1 : term106 _92591) : (term223 _92591) = False.
Proof. exact (prop_ext (fun h2 : term223 _92591 => @lem6951773 _92591 h2) (fun h2 : False => @lem6951775 _92591 h1)). Qed.
Lemma lem6951777 (_92591 : int) (h1 : term106 _92591) : False.
Proof. exact (EQ_MP (@lem6951776 _92591 h1) (@lem6951775 _92591 h1)). Qed.
Lemma lem6951778 (_92591 : int) : term324 _92591.
Proof. exact (fun h0 : term106 _92591 => @lem6951777 _92591 h0). Qed.
Lemma lem6951779 (_92591 : int) : term325 _92591.
Proof. exact (@lem1386578 (term326 _92591)). Qed.
Lemma lem6951782 (_92591 : int) : term326 _92591.
Proof. exact (@lem6951779 _92591 (@lem6951778 _92591)). Qed.
Lemma lem6951783 (_92591 : int) : (term104 _92591) = (term46 _92591).
Proof. exact (SYM (@lem6949349 _92591)). Qed.
Lemma lem6951784 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6951785 (_92591 : int) : (term326 _92591) = (term22 _92591).
Proof. exact (MK_COMB (@lem6951784) (@lem6951783 _92591)). Qed.
Lemma lem6951786 (_92591 : int) : term22 _92591.
Proof. exact (EQ_MP (@lem6951785 _92591) (@lem6951782 _92591)). Qed.
Lemma lem6951787 (_92591 : int) : term23 _92591.
Proof. exact (EQ_MP (@lem6949162 _92591) (@lem6951786 _92591)). Qed.
Lemma lem6951788 (n : nat) : term327 n.
Proof. exact (@lem6951787 (int_of_num n)). Qed.
Lemma lem6951789 (n : nat) : term19 n.
Proof. exact (@lem6951788 n (@lem6949161 n)). Qed.
Lemma lem6951790 (n : nat) : (term19 n) = ((n = (NUMERAL 0)) = (term0 n)).
Proof. exact (SYM (@lem6949158 n)). Qed.
Lemma lem6951791 (n : nat) : (n = (NUMERAL 0)) = (term0 n).
Proof. exact (EQ_MP (@lem6951790 n) (@lem6951789 n)). Qed.
Lemma lem6951792 (t1 : Prop) : term328 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem6951793 (t1 : Prop) : (term328 t1) = (term329 t1).
Proof. exact (eq_refl (term328 t1)). Qed.
Lemma lem6951794 (t1 : Prop) : term329 t1.
Proof. exact (EQ_MP (@lem6951793 t1) (@lem6951792 t1)). Qed.
Lemma lem6951795 (t1 : Prop) (t2 : Prop) : term330 t1 t2.
Proof. exact (@lem6951794 t1 t2). Qed.
Lemma lem6951796 (t1 : Prop) (t2 : Prop) : (term330 t1 t2) = (term331 t1 t2).
Proof. exact (eq_refl (term330 t1 t2)). Qed.
Lemma lem6951797 (t1 : Prop) (t2 : Prop) : term331 t1 t2.
Proof. exact (EQ_MP (@lem6951796 t1 t2) (@lem6951795 t1 t2)). Qed.
Lemma lem6951798 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term332 t1 t2 t3.
Proof. exact (@lem6951797 t1 t2 t3). Qed.
Lemma lem6951799 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term332 t1 t2 t3) = ((term333 t1 t2 t3) = (term334 t1 t2 t3)).
Proof. exact (eq_refl (term332 t1 t2 t3)). Qed.
Lemma lem6951800 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term333 t1 t2 t3) = (term334 t1 t2 t3).
Proof. exact (EQ_MP (@lem6951799 t1 t2 t3) (@lem6951798 t1 t2 t3)). Qed.
Lemma lem6951801 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term334 t1 t2 t3) = (term333 t1 t2 t3).
Proof. exact (SYM (@lem6951800 t1 t2 t3)). Qed.
Lemma lem6951802 : term335.
Proof. exact (fun n : nat => @lem6951791 n). Qed.
Lemma lem6951803 {_127305 : Type'} (s : _127305 -> Prop) (h1 : @FINITE _127305 s) : @FINITE _127305 s.
Proof. exact (h1). Qed.
Lemma lem6951982 {A : Type'} (f : A -> nat) : term336 A f.
Proof. exact (@lem6930973 A f). Qed.
Lemma lem6951983 {A : Type'} (f : A -> nat) : (term336 A f) = (term337 A f).
Proof. exact (eq_refl (term336 A f)). Qed.
Lemma lem6951984 {A : Type'} (f : A -> nat) : term337 A f.
Proof. exact (EQ_MP (@lem6951983 A f) (@lem6951982 A f)). Qed.
Lemma lem6951985 {A : Type'} (f : A -> nat) (s : A -> Prop) : term338 A f s.
Proof. exact (@lem6951984 A f s). Qed.
Lemma lem6951986 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term338 A f s) = (term339 A s f).
Proof. exact (eq_refl (term338 A f s)). Qed.
Lemma lem6951987 {A : Type'} (s : A -> Prop) (f : A -> nat) : term339 A s f.
Proof. exact (EQ_MP (@lem6951986 A s f) (@lem6951985 A f s)). Qed.
Lemma lem6951988 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term340 A s f) : term340 A s f.
Proof. exact (h1). Qed.
Lemma lem6951989 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term340 A s f) : (@nsum A s f) = (NUMERAL 0).
Proof. exact (@lem6951987 A s f (@lem6951988 A s f h1)). Qed.
Lemma lem6952000 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term341 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6952001 (p : Prop) (q : Prop) (p' : Prop) : term342 p q p'.
Proof. exact (fun q' : Prop => @lem6952000 p q p' q'). Qed.
Lemma lem6952002 (p : Prop) (q : Prop) : term343 p q.
Proof. exact (fun p' : Prop => @lem6952001 p q p'). Qed.
Lemma lem6952003 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : term344 _127305 s f.
Proof. exact (@lem6952002 (term340 _127305 s f) ((@nsum _127305 s f) = (NUMERAL 0))). Qed.
Lemma lem6952004 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (p' : Prop) : term345 _127305 s f p'.
Proof. exact (@lem6952003 _127305 s f p'). Qed.
Lemma lem6952005 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (p' : Prop) : (term345 _127305 s f p') = (term346 _127305 s f p').
Proof. exact (eq_refl (term345 _127305 s f p')). Qed.
Lemma lem6952006 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (p' : Prop) : term346 _127305 s f p'.
Proof. exact (EQ_MP (@lem6952005 _127305 s f p') (@lem6952004 _127305 s f p')). Qed.
Lemma lem6952007 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (p' : Prop) (q' : Prop) : term347 _127305 s f p' q'.
Proof. exact (@lem6952006 _127305 s f p' q'). Qed.
Lemma lem6952008 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (p' : Prop) (q' : Prop) : (term347 _127305 s f p' q') = (term348 _127305 s f p' q').
Proof. exact (eq_refl (term347 _127305 s f p' q')). Qed.
Lemma lem6952009 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (p' : Prop) (q' : Prop) : term348 _127305 s f p' q'.
Proof. exact (EQ_MP (@lem6952008 _127305 s f p' q') (@lem6952007 _127305 s f p' q')). Qed.
Lemma lem6952041 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term340 _127305 s f) = (term340 _127305 s f).
Proof. exact (eq_refl (term340 _127305 s f)). Qed.
Lemma lem6952042 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (q' : Prop) : term349 _127305 s f q'.
Proof. exact (@lem6952009 _127305 s f (term340 _127305 s f) q'). Qed.
Lemma lem6952043 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (q' : Prop) : term350 _127305 s f q'.
Proof. exact (@lem6952042 _127305 s f q' (@lem6952041 _127305 s f)). Qed.
Lemma lem6952044 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term340 _127305 s f) : term340 _127305 s f.
Proof. exact (h1). Qed.
Lemma lem6952045 {_127305 : Type'} (x : _127305) (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term340 _127305 s f) : term351 _127305 s f x.
Proof. exact (@lem6952044 _127305 s f h1 x). Qed.
Lemma lem6952046 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) : (term351 _127305 s f x) = (term352 _127305 s f x).
Proof. exact (eq_refl (term351 _127305 s f x)). Qed.
Lemma lem6952047 {_127305 : Type'} (x : _127305) (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term340 _127305 s f) : term352 _127305 s f x.
Proof. exact (EQ_MP (@lem6952046 _127305 s f x) (@lem6952045 _127305 x s f h1)). Qed.
Lemma lem6952048 {_127305 : Type'} (x : _127305) (s : _127305 -> Prop) (h1 : @IN _127305 x s) : @IN _127305 x s.
Proof. exact (h1). Qed.
Lemma lem6952049 {_127305 : Type'} (f : _127305 -> nat) (x : _127305) (s : _127305 -> Prop) (h1 : term340 _127305 s f) (h2 : @IN _127305 x s) : (f x) = (NUMERAL 0).
Proof. exact (@lem6952047 _127305 x s f h1 (@lem6952048 _127305 x s h2)). Qed.
Lemma lem6952058 {A : Type'} (s : A -> Prop) (f : A -> nat) : term339 A s f.
Proof. exact (fun h0 : term340 A s f => @lem6951989 A s f h0). Qed.
Lemma lem6952059 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : term339 _127305 s f.
Proof. exact (@lem6952058 _127305 s f). Qed.
Lemma lem6952067 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term341 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6952068 (p : Prop) (q : Prop) (p' : Prop) : term342 p q p'.
Proof. exact (fun q' : Prop => @lem6952067 p q p' q'). Qed.
Lemma lem6952069 (p : Prop) (q : Prop) : term343 p q.
Proof. exact (fun p' : Prop => @lem6952068 p q p'). Qed.
Lemma lem6952070 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) : term353 _127305 s f x.
Proof. exact (@lem6952069 (@IN _127305 x s) ((f x) = (NUMERAL 0))). Qed.
Lemma lem6952071 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (p' : Prop) : term354 _127305 s f x p'.
Proof. exact (@lem6952070 _127305 s f x p'). Qed.
Lemma lem6952072 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (p' : Prop) : (term354 _127305 s f x p') = (term355 _127305 s f x p').
Proof. exact (eq_refl (term354 _127305 s f x p')). Qed.
Lemma lem6952073 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (p' : Prop) : term355 _127305 s f x p'.
Proof. exact (EQ_MP (@lem6952072 _127305 s f x p') (@lem6952071 _127305 s f x p')). Qed.
Lemma lem6952074 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (p' : Prop) (q' : Prop) : term356 _127305 s f x p' q'.
Proof. exact (@lem6952073 _127305 s f x p' q'). Qed.
Lemma lem6952075 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (p' : Prop) (q' : Prop) : (term356 _127305 s f x p' q') = (term357 _127305 s f x p' q').
Proof. exact (eq_refl (term356 _127305 s f x p' q')). Qed.
Lemma lem6952076 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (p' : Prop) (q' : Prop) : term357 _127305 s f x p' q'.
Proof. exact (EQ_MP (@lem6952075 _127305 s f x p' q') (@lem6952074 _127305 s f x p' q')). Qed.
Lemma lem6952077 {_127305 : Type'} (x : _127305) (s : _127305 -> Prop) : (@IN _127305 x s) = (@IN _127305 x s).
Proof. exact (eq_refl (@IN _127305 x s)). Qed.
Lemma lem6952078 {_127305 : Type'} (f : _127305 -> nat) (x : _127305) (s : _127305 -> Prop) (q' : Prop) : term358 _127305 f x s q'.
Proof. exact (@lem6952076 _127305 s f x (@IN _127305 x s) q'). Qed.
Lemma lem6952079 {_127305 : Type'} (f : _127305 -> nat) (x : _127305) (s : _127305 -> Prop) (q' : Prop) : term359 _127305 f x s q'.
Proof. exact (@lem6952078 _127305 f x s q' (@lem6952077 _127305 x s)). Qed.
Lemma lem6952080 {_127305 : Type'} (x : _127305) (s : _127305 -> Prop) (h1 : @IN _127305 x s) : @IN _127305 x s.
Proof. exact (h1). Qed.
Lemma lem6952081 {_127305 : Type'} (x : _127305) (s : _127305 -> Prop) : (@IN _127305 x s) = ((@IN _127305 x s) = True).
Proof. exact (@lem7 (@IN _127305 x s)). Qed.
Lemma lem6952086 {_127305 : Type'} (x : _127305) (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term340 _127305 s f) : term352 _127305 s f x.
Proof. exact (fun h0 : @IN _127305 x s => @lem6952049 _127305 f x s h1 h0). Qed.
Lemma lem6952087 {_127305 : Type'} (x : _127305) (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term340 _127305 s f) : term352 _127305 s f x.
Proof. exact (@lem6952086 _127305 x s f h1). Qed.
Lemma lem6952089 {_127305 : Type'} (x : _127305) (s : _127305 -> Prop) (h1 : @IN _127305 x s) : (@IN _127305 x s) = True.
Proof. exact (EQ_MP (@lem6952081 _127305 x s) (@lem6952080 _127305 x s h1)). Qed.
Lemma lem6952090 {_127305 : Type'} (x : _127305) (s : _127305 -> Prop) (h1 : @IN _127305 x s) : True = (@IN _127305 x s).
Proof. exact (SYM (@lem6952089 _127305 x s h1)). Qed.
Lemma lem6952091 {_127305 : Type'} (x : _127305) (s : _127305 -> Prop) (h1 : @IN _127305 x s) : @IN _127305 x s.
Proof. exact (EQ_MP (@lem6952090 _127305 x s h1) (@lem0)). Qed.
Lemma lem6952092 {_127305 : Type'} (f : _127305 -> nat) (x : _127305) (s : _127305 -> Prop) (h1 : term340 _127305 s f) (h2 : @IN _127305 x s) : (f x) = (NUMERAL 0).
Proof. exact (@lem6952087 _127305 x s f h1 (@lem6952091 _127305 x s h2)). Qed.
Lemma lem6952093 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6952094 {_127305 : Type'} (f : _127305 -> nat) (x : _127305) (s : _127305 -> Prop) (h1 : term340 _127305 s f) (h2 : @IN _127305 x s) : (term360 _127305 f x) = term361.
Proof. exact (MK_COMB (@lem6952093) (@lem6952092 _127305 f x s h1 h2)). Qed.
Lemma lem6952095 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem6952096 {_127305 : Type'} (f : _127305 -> nat) (x : _127305) (s : _127305 -> Prop) (h1 : term340 _127305 s f) (h2 : @IN _127305 x s) : ((f x) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem6952094 _127305 f x s h1 h2) (@lem6952095)). Qed.
Lemma lem6952098 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6952099 (x : nat) : (x = x) = True.
Proof. exact (@lem6952098 nat x). Qed.
Lemma lem6952100 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem6952099 (NUMERAL 0)). Qed.
Lemma lem6952101 {_127305 : Type'} (f : _127305 -> nat) (x : _127305) (s : _127305 -> Prop) (h1 : term340 _127305 s f) (h2 : @IN _127305 x s) : ((f x) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem6952096 _127305 f x s h1 h2) (@lem6952100)). Qed.
Lemma lem6952102 {_127305 : Type'} (x : _127305) (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term340 _127305 s f) : term362 _127305 s f x.
Proof. exact (fun h0 : @IN _127305 x s => @lem6952101 _127305 f x s h1 h0). Qed.
Lemma lem6952103 {_127305 : Type'} (f : _127305 -> nat) (x : _127305) (s : _127305 -> Prop) : term363 _127305 f x s.
Proof. exact (@lem6952079 _127305 f x s True). Qed.
Lemma lem6952104 {_127305 : Type'} (x : _127305) (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term340 _127305 s f) : (term352 _127305 s f x) = (term364 _127305 x s).
Proof. exact (@lem6952103 _127305 f x s (@lem6952102 _127305 x s f h1)). Qed.
Lemma lem6952106 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6952107 {_127305 : Type'} (x : _127305) (s : _127305 -> Prop) : (term364 _127305 x s) = True.
Proof. exact (@lem6952106 (@IN _127305 x s)). Qed.
Lemma lem6952108 {_127305 : Type'} (x : _127305) (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term340 _127305 s f) : (term352 _127305 s f x) = True.
Proof. exact (TRANS (@lem6952104 _127305 x s f h1) (@lem6952107 _127305 x s)). Qed.
Lemma lem6952109 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term340 _127305 s f) : (term365 _127305 s f) = (term366 _127305).
Proof. exact (fun_ext (fun x : _127305 => @lem6952108 _127305 x s f h1)). Qed.
Lemma lem6952110 {_127305 : Type'} : (@all _127305) = (@all _127305).
Proof. exact (eq_refl (@all _127305)). Qed.
Lemma lem6952111 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term340 _127305 s f) : (term340 _127305 s f) = (term367 _127305).
Proof. exact (MK_COMB (@lem6952110 _127305) (@lem6952109 _127305 s f h1)). Qed.
Lemma lem6952113 {A : Type'} (t : Prop) : (term368 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6952114 {_127305 : Type'} (t : Prop) : (term368 _127305 t) = t.
Proof. exact (@lem6952113 _127305 t). Qed.
Lemma lem6952115 {_127305 : Type'} : (term367 _127305) = True.
Proof. exact (@lem6952114 _127305 True). Qed.
Lemma lem6952116 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term340 _127305 s f) : (term340 _127305 s f) = True.
Proof. exact (TRANS (@lem6952111 _127305 s f h1) (@lem6952115 _127305)). Qed.
Lemma lem6952117 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term340 _127305 s f) : True = (term340 _127305 s f).
Proof. exact (SYM (@lem6952116 _127305 s f h1)). Qed.
Lemma lem6952118 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term340 _127305 s f) : term340 _127305 s f.
Proof. exact (EQ_MP (@lem6952117 _127305 s f h1) (@lem0)). Qed.
Lemma lem6952119 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term340 _127305 s f) : (@nsum _127305 s f) = (NUMERAL 0).
Proof. exact (@lem6952059 _127305 s f (@lem6952118 _127305 s f h1)). Qed.
Lemma lem6952120 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6952121 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term340 _127305 s f) : (term369 _127305 s f) = term361.
Proof. exact (MK_COMB (@lem6952120) (@lem6952119 _127305 s f h1)). Qed.
Lemma lem6952122 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem6952123 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term340 _127305 s f) : ((@nsum _127305 s f) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem6952121 _127305 s f h1) (@lem6952122)). Qed.
Lemma lem6952125 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6952126 (x : nat) : (x = x) = True.
Proof. exact (@lem6952125 nat x). Qed.
Lemma lem6952127 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem6952126 (NUMERAL 0)). Qed.
Lemma lem6952128 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term340 _127305 s f) : ((@nsum _127305 s f) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem6952123 _127305 s f h1) (@lem6952127)). Qed.
Lemma lem6952129 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : term370 _127305 s f.
Proof. exact (fun h0 : term340 _127305 s f => @lem6952128 _127305 s f h0). Qed.
Lemma lem6952130 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : term371 _127305 s f.
Proof. exact (@lem6952043 _127305 s f True). Qed.
Lemma lem6952131 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term339 _127305 s f) = (term372 _127305 s f).
Proof. exact (@lem6952130 _127305 s f (@lem6952129 _127305 s f)). Qed.
Lemma lem6952133 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6952134 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term372 _127305 s f) = True.
Proof. exact (@lem6952133 (term340 _127305 s f)). Qed.
Lemma lem6952135 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term339 _127305 s f) = True.
Proof. exact (TRANS (@lem6952131 _127305 s f) (@lem6952134 _127305 s f)). Qed.
Lemma lem6952136 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : True = (term339 _127305 s f).
Proof. exact (SYM (@lem6952135 _127305 s f)). Qed.
Lemma lem6952137 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : term339 _127305 s f.
Proof. exact (EQ_MP (@lem6952136 _127305 s f) (@lem0)). Qed.
Lemma lem6952139 (p : Prop) : p = (term373 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6952140 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term374 _127305 s f) = (term375 _127305 s f).
Proof. exact (@lem6952139 (term374 _127305 s f)). Qed.
Lemma lem6952141 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term375 _127305 s f) = (term374 _127305 s f).
Proof. exact (SYM (@lem6952140 _127305 s f)). Qed.
Lemma lem6952142 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term376 _127305 s f) : term376 _127305 s f.
Proof. exact (h1). Qed.
Lemma lem6952143 {_127305 : Type'} : term377 _127305.
Proof. exact (@lem6949047 _127305). Qed.
Lemma lem6952148 {_127305 A : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term378 _127305 A s f) : term378 _127305 A s f.
Proof. exact (h1). Qed.
Lemma lem6952149 {_127305 A : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : term379 _127305 A s f.
Proof. exact (fun h0 : term378 _127305 A s f => @lem6952148 _127305 A s f h0). Qed.
Lemma lem6952150 {_127305 A : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term379 _127305 A s f) : term379 _127305 A s f.
Proof. exact (h1). Qed.
Lemma lem6952151 {_127305 A : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term378 _127305 A s f) : term378 _127305 A s f.
Proof. exact (h1). Qed.
Lemma lem6952152 {_127305 A : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term378 _127305 A s f) (h2 : term379 _127305 A s f) : term378 _127305 A s f.
Proof. exact (@lem6952150 _127305 A s f h2 (@lem6952151 _127305 A s f h1)). Qed.
Lemma lem6952153 {_127305 A : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term378 _127305 A s f) : term380 _127305 A s f.
Proof. exact (fun h0 : term379 _127305 A s f => @lem6952152 _127305 A s f h1 h0). Qed.
Lemma lem6952154 {_127305 A : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term379 _127305 A s f) : term379 _127305 A s f.
Proof. exact (h1). Qed.
Lemma lem6952155 {_127305 A : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term378 _127305 A s f) (h2 : term379 _127305 A s f) : term378 _127305 A s f.
Proof. exact (@lem6952153 _127305 A s f h1 (@lem6952154 _127305 A s f h2)). Qed.
Lemma lem6952156 {_127305 A : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term379 _127305 A s f) : term379 _127305 A s f.
Proof. exact (fun h0 : term378 _127305 A s f => @lem6952155 _127305 A s f h0 h1). Qed.
Lemma lem6952157 {_127305 A : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : term381 _127305 A s f.
Proof. exact (fun h0 : term379 _127305 A s f => @lem6952156 _127305 A s f h0). Qed.
Lemma lem6952160 {_127305 A : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : term379 _127305 A s f.
Proof. exact (@lem6952157 _127305 A s f (@lem6952149 _127305 A s f)). Qed.
Lemma lem6952161 {_127305 A : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : term379 _127305 A s f.
Proof. exact (@lem6952160 _127305 A s f). Qed.
Lemma lem6952231 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6952232 : term382 = term383.
Proof. exact (@lem6952231 term335). Qed.
Lemma lem6952237 {A : Type'} : (term384 A) = (term384 A).
Proof. exact (eq_refl (term384 A)). Qed.
Lemma lem6952238 {A : Type'} : (term385 A) = (term386 A).
Proof. exact (MK_COMB (@lem6952237 A) (@lem6952232)). Qed.
Lemma lem6952241 {_127305 : Type'} : (term384 _127305) = (term384 _127305).
Proof. exact (eq_refl (term384 _127305)). Qed.
Lemma lem6952242 {_127305 A : Type'} : (term387 _127305 A) = (term388 _127305 A).
Proof. exact (MK_COMB (@lem6952241 _127305) (@lem6952238 A)). Qed.
Lemma lem6952245 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term389 _127305 s f) = (term389 _127305 s f).
Proof. exact (eq_refl (term389 _127305 s f)). Qed.
Lemma lem6952246 {_127305 A : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term390 _127305 A s f) = (term391 _127305 A s f).
Proof. exact (MK_COMB (@lem6952245 _127305 s f) (@lem6952242 _127305 A)). Qed.
Lemma lem6952249 {_127305 : Type'} (s : _127305 -> Prop) : (term392 _127305 s) = (term392 _127305 s).
Proof. exact (eq_refl (term392 _127305 s)). Qed.
Lemma lem6952250 {_127305 A : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term378 _127305 A s f) = (term393 _127305 A s f).
Proof. exact (MK_COMB (@lem6952249 _127305 s) (@lem6952246 _127305 A s f)). Qed.
Lemma lem6952253 {_127305 A : Type'} (f : _127305 -> nat) : (term394 _127305 A f) = (term395 _127305 A f).
Proof. exact (fun_ext (fun s : _127305 -> Prop => @lem6952250 _127305 A s f)). Qed.
Lemma lem6952254 {_127305 : Type'} : (@all (_127305 -> Prop)) = (@all (_127305 -> Prop)).
Proof. exact (eq_refl (@all (_127305 -> Prop))). Qed.
Lemma lem6952255 {_127305 A : Type'} (f : _127305 -> nat) : (term396 _127305 A f) = (term397 _127305 A f).
Proof. exact (MK_COMB (@lem6952254 _127305) (@lem6952253 _127305 A f)). Qed.
Lemma lem6952260 {_127305 A : Type'} : (term398 _127305 A) = (term399 _127305 A).
Proof. exact (fun_ext (fun f : _127305 -> nat => @lem6952255 _127305 A f)). Qed.
Lemma lem6952261 {_127305 : Type'} : (@all (_127305 -> nat)) = (@all (_127305 -> nat)).
Proof. exact (eq_refl (@all (_127305 -> nat))). Qed.
Lemma lem6952270 {_127305 A : Type'} : (term400 _127305 A) = (term401 _127305 A).
Proof. exact (MK_COMB (@lem6952261 _127305) (@lem6952260 _127305 A)). Qed.
Lemma lem6952275 (n : nat) : ((n = (NUMERAL 0)) = (term0 n)) = ((n = (NUMERAL 0)) = (term0 n)).
Proof. exact (eq_refl ((n = (NUMERAL 0)) = (term0 n))). Qed.
Lemma lem6952276 : term402 = term402.
Proof. exact (fun_ext (fun n : nat => @lem6952275 n)). Qed.
Lemma lem6952277 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6952278 : term335 = term335.
Proof. exact (MK_COMB (@lem6952277) (@lem6952276)). Qed.
Lemma lem6952279 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6952280 : term383 = term383.
Proof. exact (MK_COMB (@lem6952279) (@lem6952278)). Qed.
Lemma lem6952285 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term403 A s f x b) = (term403 A s f x b).
Proof. exact (eq_refl (term403 A s f x b)). Qed.
Lemma lem6952286 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term404 A s f b) = (term404 A s f b).
Proof. exact (fun_ext (fun x : A => @lem6952285 A s f x b)). Qed.
Lemma lem6952287 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6952288 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term405 A s f b) = (term405 A s f b).
Proof. exact (MK_COMB (@lem6952287 A) (@lem6952286 A s f b)). Qed.
Lemma lem6952295 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term406 A s f b) = (term406 A s f b).
Proof. exact (eq_refl (term406 A s f b)). Qed.
Lemma lem6952296 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term407 A s f b) = (term407 A s f b).
Proof. exact (MK_COMB (@lem6952295 A s f b) (@lem6952288 A s f b)). Qed.
Lemma lem6952297 {A : Type'} (f : A -> nat) (b : nat) : (term408 A f b) = (term408 A f b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6952296 A s f b)). Qed.
Lemma lem6952298 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6952299 {A : Type'} (f : A -> nat) (b : nat) : (term409 A f b) = (term409 A f b).
Proof. exact (MK_COMB (@lem6952298 A) (@lem6952297 A f b)). Qed.
Lemma lem6952300 {A : Type'} (f : A -> nat) : (term410 A f) = (term410 A f).
Proof. exact (fun_ext (fun b : nat => @lem6952299 A f b)). Qed.
Lemma lem6952301 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6952302 {A : Type'} (f : A -> nat) : (term411 A f) = (term411 A f).
Proof. exact (MK_COMB (@lem6952301) (@lem6952300 A f)). Qed.
Lemma lem6952303 {A : Type'} : (term412 A) = (term412 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6952302 A f)). Qed.
Lemma lem6952304 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6952305 {A : Type'} : (term377 A) = (term377 A).
Proof. exact (MK_COMB (@lem6952304 A) (@lem6952303 A)). Qed.
Lemma lem6952306 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6952307 {A : Type'} : (term384 A) = (term384 A).
Proof. exact (MK_COMB (@lem6952306) (@lem6952305 A)). Qed.
Lemma lem6952308 {A : Type'} : (term386 A) = (term386 A).
Proof. exact (MK_COMB (@lem6952307 A) (@lem6952280)). Qed.
Lemma lem6952313 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (b : nat) : (term403 _127305 s f x b) = (term403 _127305 s f x b).
Proof. exact (eq_refl (term403 _127305 s f x b)). Qed.
Lemma lem6952314 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term404 _127305 s f b) = (term404 _127305 s f b).
Proof. exact (fun_ext (fun x : _127305 => @lem6952313 _127305 s f x b)). Qed.
Lemma lem6952315 {_127305 : Type'} : (@all _127305) = (@all _127305).
Proof. exact (eq_refl (@all _127305)). Qed.
Lemma lem6952316 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term405 _127305 s f b) = (term405 _127305 s f b).
Proof. exact (MK_COMB (@lem6952315 _127305) (@lem6952314 _127305 s f b)). Qed.
Lemma lem6952323 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term406 _127305 s f b) = (term406 _127305 s f b).
Proof. exact (eq_refl (term406 _127305 s f b)). Qed.
Lemma lem6952324 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term407 _127305 s f b) = (term407 _127305 s f b).
Proof. exact (MK_COMB (@lem6952323 _127305 s f b) (@lem6952316 _127305 s f b)). Qed.
Lemma lem6952325 {_127305 : Type'} (f : _127305 -> nat) (b : nat) : (term408 _127305 f b) = (term408 _127305 f b).
Proof. exact (fun_ext (fun s : _127305 -> Prop => @lem6952324 _127305 s f b)). Qed.
Lemma lem6952326 {_127305 : Type'} : (@all (_127305 -> Prop)) = (@all (_127305 -> Prop)).
Proof. exact (eq_refl (@all (_127305 -> Prop))). Qed.
Lemma lem6952327 {_127305 : Type'} (f : _127305 -> nat) (b : nat) : (term409 _127305 f b) = (term409 _127305 f b).
Proof. exact (MK_COMB (@lem6952326 _127305) (@lem6952325 _127305 f b)). Qed.
Lemma lem6952328 {_127305 : Type'} (f : _127305 -> nat) : (term410 _127305 f) = (term410 _127305 f).
Proof. exact (fun_ext (fun b : nat => @lem6952327 _127305 f b)). Qed.
Lemma lem6952329 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6952330 {_127305 : Type'} (f : _127305 -> nat) : (term411 _127305 f) = (term411 _127305 f).
Proof. exact (MK_COMB (@lem6952329) (@lem6952328 _127305 f)). Qed.
Lemma lem6952331 {_127305 : Type'} : (term412 _127305) = (term412 _127305).
Proof. exact (fun_ext (fun f : _127305 -> nat => @lem6952330 _127305 f)). Qed.
Lemma lem6952332 {_127305 : Type'} : (@all (_127305 -> nat)) = (@all (_127305 -> nat)).
Proof. exact (eq_refl (@all (_127305 -> nat))). Qed.
Lemma lem6952333 {_127305 : Type'} : (term377 _127305) = (term377 _127305).
Proof. exact (MK_COMB (@lem6952332 _127305) (@lem6952331 _127305)). Qed.
Lemma lem6952334 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6952335 {_127305 : Type'} : (term384 _127305) = (term384 _127305).
Proof. exact (MK_COMB (@lem6952334) (@lem6952333 _127305)). Qed.
Lemma lem6952336 {_127305 A : Type'} : (term388 _127305 A) = (term388 _127305 A).
Proof. exact (MK_COMB (@lem6952335 _127305) (@lem6952308 A)). Qed.
Lemma lem6952341 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) : (term352 _127305 s f x) = (term352 _127305 s f x).
Proof. exact (eq_refl (term352 _127305 s f x)). Qed.
Lemma lem6952342 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term365 _127305 s f) = (term365 _127305 s f).
Proof. exact (fun_ext (fun x : _127305 => @lem6952341 _127305 s f x)). Qed.
Lemma lem6952343 {_127305 : Type'} : (@all _127305) = (@all _127305).
Proof. exact (eq_refl (@all _127305)). Qed.
Lemma lem6952344 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term340 _127305 s f) = (term340 _127305 s f).
Proof. exact (MK_COMB (@lem6952343 _127305) (@lem6952342 _127305 s f)). Qed.
Lemma lem6952347 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term413 _127305 s f) = (term413 _127305 s f).
Proof. exact (eq_refl (term413 _127305 s f)). Qed.
Lemma lem6952348 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term374 _127305 s f) = (term374 _127305 s f).
Proof. exact (MK_COMB (@lem6952347 _127305 s f) (@lem6952344 _127305 s f)). Qed.
Lemma lem6952349 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6952350 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term376 _127305 s f) = (term376 _127305 s f).
Proof. exact (MK_COMB (@lem6952349) (@lem6952348 _127305 s f)). Qed.
Lemma lem6952351 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6952352 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term389 _127305 s f) = (term389 _127305 s f).
Proof. exact (MK_COMB (@lem6952351) (@lem6952350 _127305 s f)). Qed.
Lemma lem6952353 {_127305 A : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term391 _127305 A s f) = (term391 _127305 A s f).
Proof. exact (MK_COMB (@lem6952352 _127305 s f) (@lem6952336 _127305 A)). Qed.
Lemma lem6952356 {_127305 : Type'} (s : _127305 -> Prop) : (term392 _127305 s) = (term392 _127305 s).
Proof. exact (eq_refl (term392 _127305 s)). Qed.
Lemma lem6952357 {_127305 A : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term393 _127305 A s f) = (term393 _127305 A s f).
Proof. exact (MK_COMB (@lem6952356 _127305 s) (@lem6952353 _127305 A s f)). Qed.
Lemma lem6952358 {_127305 A : Type'} (f : _127305 -> nat) : (term395 _127305 A f) = (term395 _127305 A f).
Proof. exact (fun_ext (fun s : _127305 -> Prop => @lem6952357 _127305 A s f)). Qed.
Lemma lem6952359 {_127305 : Type'} : (@all (_127305 -> Prop)) = (@all (_127305 -> Prop)).
Proof. exact (eq_refl (@all (_127305 -> Prop))). Qed.
Lemma lem6952360 {_127305 A : Type'} (f : _127305 -> nat) : (term397 _127305 A f) = (term397 _127305 A f).
Proof. exact (MK_COMB (@lem6952359 _127305) (@lem6952358 _127305 A f)). Qed.
Lemma lem6952361 {_127305 A : Type'} : (term399 _127305 A) = (term399 _127305 A).
Proof. exact (fun_ext (fun f : _127305 -> nat => @lem6952360 _127305 A f)). Qed.
Lemma lem6952362 {_127305 : Type'} : (@all (_127305 -> nat)) = (@all (_127305 -> nat)).
Proof. exact (eq_refl (@all (_127305 -> nat))). Qed.
Lemma lem6952363 {_127305 A : Type'} : (term401 _127305 A) = (term401 _127305 A).
Proof. exact (MK_COMB (@lem6952362 _127305) (@lem6952361 _127305 A)). Qed.
Lemma lem6952462 {_127305 A : Type'} : (term400 _127305 A) = (term401 _127305 A).
Proof. exact (TRANS (@lem6952270 _127305 A) (@lem6952363 _127305 A)). Qed.
Lemma lem6952463 {_127305 A : Type'} : (term401 _127305 A) = (term400 _127305 A).
Proof. exact (SYM (@lem6952462 _127305 A)). Qed.
Lemma lem6952465 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term376 _127305 s f) : term376 _127305 s f.
Proof. exact (h1). Qed.
Lemma lem6952466 {_127305 : Type'} (h1 : term377 _127305) : term377 _127305.
Proof. exact (h1). Qed.
Lemma lem6952468 (h1 : term335) : term335.
Proof. exact (h1). Qed.
Lemma lem6952474 {_127305 : Type'} (s : _127305 -> Prop) (h1 : @FINITE _127305 s) : @FINITE _127305 s.
Proof. exact (h1). Qed.
Lemma lem6952482 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) : (term414 _127305 s f x) = (term415 _127305 s f x).
Proof. exact (@lem17362 (@IN _127305 x s) ((f x) = (NUMERAL 0))). Qed.
Lemma lem6952483 {_127305 : Type'} (P : _127305 -> Prop) : (term416 _127305 P) = (term417 _127305 P).
Proof. exact (@lem18392 _127305 P). Qed.
Lemma lem6952484 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term418 _127305 s f) = (term419 _127305 s f).
Proof. exact (@lem6952483 _127305 (term365 _127305 s f)). Qed.
Lemma lem6952485 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) : (term351 _127305 s f x) = (term352 _127305 s f x).
Proof. exact (eq_refl (term351 _127305 s f x)). Qed.
Lemma lem6952486 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6952487 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) : (term420 _127305 s f x) = (term414 _127305 s f x).
Proof. exact (MK_COMB (@lem6952486) (@lem6952485 _127305 s f x)). Qed.
Lemma lem6952488 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) : (term420 _127305 s f x) = (term415 _127305 s f x).
Proof. exact (TRANS (@lem6952487 _127305 s f x) (@lem6952482 _127305 s f x)). Qed.
Lemma lem6952489 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term421 _127305 s f) = (term422 _127305 s f).
Proof. exact (fun_ext (fun x : _127305 => @lem6952488 _127305 s f x)). Qed.
Lemma lem6952490 {_127305 : Type'} : (@ex _127305) = (@ex _127305).
Proof. exact (eq_refl (@ex _127305)). Qed.
Lemma lem6952491 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term419 _127305 s f) = (term423 _127305 s f).
Proof. exact (MK_COMB (@lem6952490 _127305) (@lem6952489 _127305 s f)). Qed.
Lemma lem6952492 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term418 _127305 s f) = (term423 _127305 s f).
Proof. exact (TRANS (@lem6952484 _127305 s f) (@lem6952491 _127305 s f)). Qed.
Lemma lem6952494 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term424 _127305 s f) = (term424 _127305 s f).
Proof. exact (eq_refl (term424 _127305 s f)). Qed.
Lemma lem6952495 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term425 _127305 s f) = (term426 _127305 s f).
Proof. exact (MK_COMB (@lem6952494 _127305 s f) (@lem6952492 _127305 s f)). Qed.
Lemma lem6952496 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term376 _127305 s f) = (term425 _127305 s f).
Proof. exact (@lem17362 ((@nsum _127305 s f) = (NUMERAL 0)) (term340 _127305 s f)). Qed.
Lemma lem6952497 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term376 _127305 s f) = (term426 _127305 s f).
Proof. exact (TRANS (@lem6952496 _127305 s f) (@lem6952495 _127305 s f)). Qed.
Lemma lem6952548 {A : Type'} (P : Prop) (Q : A -> Prop) : (term427 A P Q) = (term428 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem6952549 {_127305 : Type'} (P : Prop) (Q : _127305 -> Prop) : (term427 _127305 P Q) = (term428 _127305 P Q).
Proof. exact (@lem6952548 _127305 P Q). Qed.
Lemma lem6952550 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term429 _127305 s f) = (term430 _127305 s f).
Proof. exact (@lem6952549 _127305 ((@nsum _127305 s f) = (NUMERAL 0)) (term422 _127305 s f)). Qed.
Lemma lem6952551 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) : (term431 _127305 s f x) = (term415 _127305 s f x).
Proof. exact (eq_refl (term431 _127305 s f x)). Qed.
Lemma lem6952552 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term432 _127305 s f) = (term422 _127305 s f).
Proof. exact (fun_ext (fun x : _127305 => @lem6952551 _127305 s f x)). Qed.
Lemma lem6952553 {_127305 : Type'} : (@ex _127305) = (@ex _127305).
Proof. exact (eq_refl (@ex _127305)). Qed.
Lemma lem6952554 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term433 _127305 s f) = (term423 _127305 s f).
Proof. exact (MK_COMB (@lem6952553 _127305) (@lem6952552 _127305 s f)). Qed.
Lemma lem6952555 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term424 _127305 s f) = (term424 _127305 s f).
Proof. exact (eq_refl (term424 _127305 s f)). Qed.
Lemma lem6952556 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term429 _127305 s f) = (term426 _127305 s f).
Proof. exact (MK_COMB (@lem6952555 _127305 s f) (@lem6952554 _127305 s f)). Qed.
Lemma lem6952557 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6952558 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term434 _127305 s f) = (term435 _127305 s f).
Proof. exact (MK_COMB (@lem6952557) (@lem6952556 _127305 s f)). Qed.
Lemma lem6952559 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) : (term431 _127305 s f x) = (term415 _127305 s f x).
Proof. exact (eq_refl (term431 _127305 s f x)). Qed.
Lemma lem6952560 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term424 _127305 s f) = (term424 _127305 s f).
Proof. exact (eq_refl (term424 _127305 s f)). Qed.
Lemma lem6952561 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) : (term436 _127305 s f x) = (term437 _127305 s f x).
Proof. exact (MK_COMB (@lem6952560 _127305 s f) (@lem6952559 _127305 s f x)). Qed.
Lemma lem6952562 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term438 _127305 s f) = (term439 _127305 s f).
Proof. exact (fun_ext (fun x : _127305 => @lem6952561 _127305 s f x)). Qed.
Lemma lem6952563 {_127305 : Type'} : (@ex _127305) = (@ex _127305).
Proof. exact (eq_refl (@ex _127305)). Qed.
Lemma lem6952564 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term430 _127305 s f) = (term440 _127305 s f).
Proof. exact (MK_COMB (@lem6952563 _127305) (@lem6952562 _127305 s f)). Qed.
Lemma lem6952565 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : ((term429 _127305 s f) = (term430 _127305 s f)) = ((term426 _127305 s f) = (term440 _127305 s f)).
Proof. exact (MK_COMB (@lem6952558 _127305 s f) (@lem6952564 _127305 s f)). Qed.
Lemma lem6952567 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term426 _127305 s f) = (term440 _127305 s f).
Proof. exact (EQ_MP (@lem6952565 _127305 s f) (@lem6952550 _127305 s f)). Qed.
Lemma lem6952568 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term376 _127305 s f) = (term440 _127305 s f).
Proof. exact (TRANS (@lem6952497 _127305 s f) (@lem6952567 _127305 s f)). Qed.
Lemma lem6952569 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term376 _127305 s f) : term440 _127305 s f.
Proof. exact (EQ_MP (@lem6952568 _127305 s f) (@lem6952465 _127305 s f h1)). Qed.
Lemma lem6952576 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term441 _127305 s f b) = (term442 _127305 s f b).
Proof. exact (@lem17045 (@FINITE _127305 s) (term443 _127305 s f b)). Qed.
Lemma lem6952583 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (b : nat) : (term403 _127305 s f x b) = (term444 _127305 s f x b).
Proof. exact (@lem17265 (@IN _127305 x s) (term445 _127305 f x b)). Qed.
Lemma lem6952584 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term404 _127305 s f b) = (term446 _127305 s f b).
Proof. exact (fun_ext (fun x : _127305 => @lem6952583 _127305 s f x b)). Qed.
Lemma lem6952585 {_127305 : Type'} : (@all _127305) = (@all _127305).
Proof. exact (eq_refl (@all _127305)). Qed.
Lemma lem6952586 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term405 _127305 s f b) = (term447 _127305 s f b).
Proof. exact (MK_COMB (@lem6952585 _127305) (@lem6952584 _127305 s f b)). Qed.
Lemma lem6952587 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6952588 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term448 _127305 s f b) = (term449 _127305 s f b).
Proof. exact (MK_COMB (@lem6952587) (@lem6952576 _127305 s f b)). Qed.
Lemma lem6952589 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term450 _127305 s f b) = (term451 _127305 s f b).
Proof. exact (MK_COMB (@lem6952588 _127305 s f b) (@lem6952586 _127305 s f b)). Qed.
Lemma lem6952590 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term407 _127305 s f b) = (term450 _127305 s f b).
Proof. exact (@lem17265 (term452 _127305 s f b) (term405 _127305 s f b)). Qed.
Lemma lem6952591 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term407 _127305 s f b) = (term451 _127305 s f b).
Proof. exact (TRANS (@lem6952590 _127305 s f b) (@lem6952589 _127305 s f b)). Qed.
Lemma lem6952592 {_127305 : Type'} (f : _127305 -> nat) (b : nat) : (term408 _127305 f b) = (term453 _127305 f b).
Proof. exact (fun_ext (fun s : _127305 -> Prop => @lem6952591 _127305 s f b)). Qed.
Lemma lem6952593 {_127305 : Type'} : (@all (_127305 -> Prop)) = (@all (_127305 -> Prop)).
Proof. exact (eq_refl (@all (_127305 -> Prop))). Qed.
Lemma lem6952594 {_127305 : Type'} (f : _127305 -> nat) (b : nat) : (term409 _127305 f b) = (term454 _127305 f b).
Proof. exact (MK_COMB (@lem6952593 _127305) (@lem6952592 _127305 f b)). Qed.
Lemma lem6952595 {_127305 : Type'} (f : _127305 -> nat) : (term410 _127305 f) = (term455 _127305 f).
Proof. exact (fun_ext (fun b : nat => @lem6952594 _127305 f b)). Qed.
Lemma lem6952596 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6952597 {_127305 : Type'} (f : _127305 -> nat) : (term411 _127305 f) = (term456 _127305 f).
Proof. exact (MK_COMB (@lem6952596) (@lem6952595 _127305 f)). Qed.
Lemma lem6952598 {_127305 : Type'} : (term412 _127305) = (term457 _127305).
Proof. exact (fun_ext (fun f : _127305 -> nat => @lem6952597 _127305 f)). Qed.
Lemma lem6952599 {_127305 : Type'} : (@all (_127305 -> nat)) = (@all (_127305 -> nat)).
Proof. exact (eq_refl (@all (_127305 -> nat))). Qed.
Lemma lem6952708 {_127305 : Type'} : (term377 _127305) = (term458 _127305).
Proof. exact (MK_COMB (@lem6952599 _127305) (@lem6952598 _127305)). Qed.
Lemma lem6952709 {_127305 : Type'} (h1 : term377 _127305) : term458 _127305.
Proof. exact (EQ_MP (@lem6952708 _127305) (@lem6952466 _127305 h1)). Qed.
Lemma lem6952864 (n : nat) : ((n = (NUMERAL 0)) = (term0 n)) = (term459 n).
Proof. exact (@lem17784 (n = (NUMERAL 0)) (term0 n)). Qed.
Lemma lem6952865 : term402 = term460.
Proof. exact (fun_ext (fun n : nat => @lem6952864 n)). Qed.
Lemma lem6952866 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6952867 : term335 = term461.
Proof. exact (MK_COMB (@lem6952866) (@lem6952865)). Qed.
Lemma lem6952869 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term462 A P Q) = (term463 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6952870 (P : nat -> Prop) (Q : nat -> Prop) : (term464 P Q) = (term465 P Q).
Proof. exact (@lem6952869 nat P Q). Qed.
Lemma lem6952871 : term466 = term467.
Proof. exact (@lem6952870 term468 term469). Qed.
Lemma lem6952872 (n : nat) : (term470 n) = (term471 n).
Proof. exact (eq_refl (term470 n)). Qed.
Lemma lem6952873 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6952874 (n : nat) : (term472 n) = (term473 n).
Proof. exact (MK_COMB (@lem6952873) (@lem6952872 n)). Qed.
Lemma lem6952875 (n : nat) : (term474 n) = (term475 n).
Proof. exact (eq_refl (term474 n)). Qed.
Lemma lem6952876 (n : nat) : (term476 n) = (term459 n).
Proof. exact (MK_COMB (@lem6952874 n) (@lem6952875 n)). Qed.
Lemma lem6952877 : term477 = term460.
Proof. exact (fun_ext (fun n : nat => @lem6952876 n)). Qed.
Lemma lem6952878 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6952879 : term466 = term461.
Proof. exact (MK_COMB (@lem6952878) (@lem6952877)). Qed.
Lemma lem6952880 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6952881 : term478 = term479.
Proof. exact (MK_COMB (@lem6952880) (@lem6952879)). Qed.
Lemma lem6952882 (n : nat) : (term470 n) = (term471 n).
Proof. exact (eq_refl (term470 n)). Qed.
Lemma lem6952883 : term480 = term468.
Proof. exact (fun_ext (fun n : nat => @lem6952882 n)). Qed.
Lemma lem6952884 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6952885 : term481 = term482.
Proof. exact (MK_COMB (@lem6952884) (@lem6952883)). Qed.
Lemma lem6952886 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6952887 : term483 = term484.
Proof. exact (MK_COMB (@lem6952886) (@lem6952885)). Qed.
Lemma lem6952888 (n : nat) : (term474 n) = (term475 n).
Proof. exact (eq_refl (term474 n)). Qed.
Lemma lem6952889 : term485 = term469.
Proof. exact (fun_ext (fun n : nat => @lem6952888 n)). Qed.
Lemma lem6952890 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6952891 : term486 = term487.
Proof. exact (MK_COMB (@lem6952890) (@lem6952889)). Qed.
Lemma lem6952892 : term467 = term488.
Proof. exact (MK_COMB (@lem6952887) (@lem6952891)). Qed.
Lemma lem6952893 : (term466 = term467) = (term461 = term488).
Proof. exact (MK_COMB (@lem6952881) (@lem6952892)). Qed.
Lemma lem6952992 : term461 = term488.
Proof. exact (EQ_MP (@lem6952893) (@lem6952871)). Qed.
Lemma lem6952993 : term335 = term488.
Proof. exact (TRANS (@lem6952867) (@lem6952992)). Qed.
Lemma lem6952994 (h1 : term335) : term488.
Proof. exact (EQ_MP (@lem6952993) (@lem6952468 h1)). Qed.
Lemma lem6952995 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (h1 : term437 _127305 s f x) : term437 _127305 s f x.
Proof. exact (h1). Qed.
Lemma lem6953000 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6953001 {_127305 : Type'} (f : type686 _127305) (x : _127305 -> Prop) : (f x) = (@I ((_127305 -> Prop) -> Prop) f x).
Proof. exact (@lem6953000 (_127305 -> Prop) Prop f x). Qed.
Lemma lem6953003 {_127305 : Type'} (s : _127305 -> Prop) : (@FINITE _127305 s) = (@I ((_127305 -> Prop) -> Prop) (@FINITE _127305) s).
Proof. exact (@lem6953001 _127305 (@FINITE _127305) s). Qed.
Lemma lem6953005 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem6953010 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6953012 {_127305 : Type'} (f : _127305 -> nat) (x : _127305) : (f x) = (@I (_127305 -> nat) f x).
Proof. exact (@lem6953010 _127305 nat f x). Qed.
Lemma lem6953013 (b : nat) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem6953014 {_127305 : Type'} (f : _127305 -> nat) (x : _127305) : (term489 _127305 f x) = (term490 _127305 f x).
Proof. exact (MK_COMB (@lem6953005) (@lem6953012 _127305 f x)). Qed.
Lemma lem6953015 {_127305 : Type'} (f : _127305 -> nat) (x : _127305) (b : nat) : (term445 _127305 f x b) = (term491 _127305 f x b).
Proof. exact (MK_COMB (@lem6953014 _127305 f x) (@lem6953013 b)). Qed.
Lemma lem6953017 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6953018 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem6953017 nat (nat -> Prop) f x). Qed.
Lemma lem6953019 {_127305 : Type'} (f : _127305 -> nat) (x : _127305) : (term490 _127305 f x) = (term492 _127305 f x).
Proof. exact (@lem6953018 Peano.le (@I (_127305 -> nat) f x)). Qed.
Lemma lem6953020 (b : nat) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem6953021 {_127305 : Type'} (f : _127305 -> nat) (x : _127305) (b : nat) : (term491 _127305 f x b) = (term493 _127305 f x b).
Proof. exact (MK_COMB (@lem6953019 _127305 f x) (@lem6953020 b)). Qed.
Lemma lem6953023 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6953024 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem6953023 nat Prop f x). Qed.
Lemma lem6953025 {_127305 : Type'} (f : _127305 -> nat) (x : _127305) (b : nat) : (term493 _127305 f x b) = (term494 _127305 f x b).
Proof. exact (@lem6953024 (term492 _127305 f x) b). Qed.
Lemma lem6953026 {_127305 : Type'} (f : _127305 -> nat) (x : _127305) (b : nat) : (term491 _127305 f x b) = (term494 _127305 f x b).
Proof. exact (TRANS (@lem6953021 _127305 f x b) (@lem6953025 _127305 f x b)). Qed.
Lemma lem6953027 {_127305 : Type'} (f : _127305 -> nat) (x : _127305) (b : nat) : (term445 _127305 f x b) = (term494 _127305 f x b).
Proof. exact (TRANS (@lem6953015 _127305 f x b) (@lem6953026 _127305 f x b)). Qed.
Lemma lem6953028 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6953035 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6953036 {_127305 : Type'} (f : type1364 _127305) (x : _127305) : (f x) = (@I (_127305 -> (_127305 -> Prop) -> Prop) f x).
Proof. exact (@lem6953035 _127305 (type686 _127305) f x). Qed.
Lemma lem6953037 {_127305 : Type'} (x : _127305) : (@IN _127305 x) = (@I (_127305 -> (_127305 -> Prop) -> Prop) (@IN _127305) x).
Proof. exact (@lem6953036 _127305 (@IN _127305) x). Qed.
Lemma lem6953038 {_127305 : Type'} (s : _127305 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6953039 {_127305 : Type'} (x : _127305) (s : _127305 -> Prop) : (@IN _127305 x s) = (@I (_127305 -> (_127305 -> Prop) -> Prop) (@IN _127305) x s).
Proof. exact (MK_COMB (@lem6953037 _127305 x) (@lem6953038 _127305 s)). Qed.
Lemma lem6953041 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6953042 {_127305 : Type'} (f : type686 _127305) (x : _127305 -> Prop) : (f x) = (@I ((_127305 -> Prop) -> Prop) f x).
Proof. exact (@lem6953041 (_127305 -> Prop) Prop f x). Qed.
Lemma lem6953043 {_127305 : Type'} (x : _127305) (s : _127305 -> Prop) : (@I (_127305 -> (_127305 -> Prop) -> Prop) (@IN _127305) x s) = (term495 _127305 x s).
Proof. exact (@lem6953042 _127305 (@I (_127305 -> (_127305 -> Prop) -> Prop) (@IN _127305) x) s). Qed.
Lemma lem6953045 {_127305 : Type'} (x : _127305) (s : _127305 -> Prop) : (@IN _127305 x s) = (term495 _127305 x s).
Proof. exact (TRANS (@lem6953039 _127305 x s) (@lem6953043 _127305 x s)). Qed.
Lemma lem6953046 {_127305 : Type'} (x : _127305) (s : _127305 -> Prop) : (term496 _127305 x s) = (term497 _127305 x s).
Proof. exact (MK_COMB (@lem6953028) (@lem6953045 _127305 x s)). Qed.
Lemma lem6953047 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6953048 {_127305 : Type'} (x : _127305) (s : _127305 -> Prop) : (term498 _127305 x s) = (term499 _127305 x s).
Proof. exact (MK_COMB (@lem6953047) (@lem6953046 _127305 x s)). Qed.
Lemma lem6953049 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (b : nat) : (term444 _127305 s f x b) = (term500 _127305 s f x b).
Proof. exact (MK_COMB (@lem6953048 _127305 x s) (@lem6953027 _127305 f x b)). Qed.
Lemma lem6953050 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term446 _127305 s f b) = (term501 _127305 s f b).
Proof. exact (fun_ext (fun x : _127305 => @lem6953049 _127305 s f x b)). Qed.
Lemma lem6953051 {_127305 : Type'} : (@all _127305) = (@all _127305).
Proof. exact (eq_refl (@all _127305)). Qed.
Lemma lem6953052 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term447 _127305 s f b) = (term502 _127305 s f b).
Proof. exact (MK_COMB (@lem6953051 _127305) (@lem6953050 _127305 s f b)). Qed.
Lemma lem6953053 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6953054 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem6953061 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6953062 {_127305 : Type'} (f : type644 _127305) (x : _127305 -> Prop) : (f x) = (@I ((_127305 -> Prop) -> (_127305 -> nat) -> nat) f x).
Proof. exact (@lem6953061 (_127305 -> Prop) (type705 _127305) f x). Qed.
Lemma lem6953063 {_127305 : Type'} (s : _127305 -> Prop) : (@nsum _127305 s) = (@I ((_127305 -> Prop) -> (_127305 -> nat) -> nat) (@nsum _127305) s).
Proof. exact (@lem6953062 _127305 (@nsum _127305) s). Qed.
Lemma lem6953064 {_127305 : Type'} (f : _127305 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6953065 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (@nsum _127305 s f) = (@I ((_127305 -> Prop) -> (_127305 -> nat) -> nat) (@nsum _127305) s f).
Proof. exact (MK_COMB (@lem6953063 _127305 s) (@lem6953064 _127305 f)). Qed.
Lemma lem6953067 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6953068 {_127305 : Type'} (f : type705 _127305) (x : _127305 -> nat) : (f x) = (@I ((_127305 -> nat) -> nat) f x).
Proof. exact (@lem6953067 (_127305 -> nat) nat f x). Qed.
Lemma lem6953069 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (@I ((_127305 -> Prop) -> (_127305 -> nat) -> nat) (@nsum _127305) s f) = (term503 _127305 s f).
Proof. exact (@lem6953068 _127305 (@I ((_127305 -> Prop) -> (_127305 -> nat) -> nat) (@nsum _127305) s) f). Qed.
Lemma lem6953071 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (@nsum _127305 s f) = (term503 _127305 s f).
Proof. exact (TRANS (@lem6953065 _127305 s f) (@lem6953069 _127305 s f)). Qed.
Lemma lem6953072 (b : nat) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem6953073 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term504 _127305 s f) = (term505 _127305 s f).
Proof. exact (MK_COMB (@lem6953054) (@lem6953071 _127305 s f)). Qed.
Lemma lem6953074 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term443 _127305 s f b) = (term506 _127305 s f b).
Proof. exact (MK_COMB (@lem6953073 _127305 s f) (@lem6953072 b)). Qed.
Lemma lem6953076 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6953077 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem6953076 nat (nat -> Prop) f x). Qed.
Lemma lem6953078 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term505 _127305 s f) = (term507 _127305 s f).
Proof. exact (@lem6953077 Peano.le (term503 _127305 s f)). Qed.
Lemma lem6953079 (b : nat) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem6953080 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term506 _127305 s f b) = (term508 _127305 s f b).
Proof. exact (MK_COMB (@lem6953078 _127305 s f) (@lem6953079 b)). Qed.
Lemma lem6953082 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6953083 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem6953082 nat Prop f x). Qed.
Lemma lem6953084 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term508 _127305 s f b) = (term509 _127305 s f b).
Proof. exact (@lem6953083 (term507 _127305 s f) b). Qed.
Lemma lem6953085 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term506 _127305 s f b) = (term509 _127305 s f b).
Proof. exact (TRANS (@lem6953080 _127305 s f b) (@lem6953084 _127305 s f b)). Qed.
Lemma lem6953086 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term443 _127305 s f b) = (term509 _127305 s f b).
Proof. exact (TRANS (@lem6953074 _127305 s f b) (@lem6953085 _127305 s f b)). Qed.
Lemma lem6953087 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term510 _127305 s f b) = (term511 _127305 s f b).
Proof. exact (MK_COMB (@lem6953053) (@lem6953086 _127305 s f b)). Qed.
Lemma lem6953088 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6953093 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6953094 {_127305 : Type'} (f : type686 _127305) (x : _127305 -> Prop) : (f x) = (@I ((_127305 -> Prop) -> Prop) f x).
Proof. exact (@lem6953093 (_127305 -> Prop) Prop f x). Qed.
Lemma lem6953096 {_127305 : Type'} (s : _127305 -> Prop) : (@FINITE _127305 s) = (@I ((_127305 -> Prop) -> Prop) (@FINITE _127305) s).
Proof. exact (@lem6953094 _127305 (@FINITE _127305) s). Qed.
Lemma lem6953097 {_127305 : Type'} (s : _127305 -> Prop) : (term512 _127305 s) = (term513 _127305 s).
Proof. exact (MK_COMB (@lem6953088) (@lem6953096 _127305 s)). Qed.
Lemma lem6953098 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6953099 {_127305 : Type'} (s : _127305 -> Prop) : (term514 _127305 s) = (term515 _127305 s).
Proof. exact (MK_COMB (@lem6953098) (@lem6953097 _127305 s)). Qed.
Lemma lem6953100 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term442 _127305 s f b) = (term516 _127305 s f b).
Proof. exact (MK_COMB (@lem6953099 _127305 s) (@lem6953087 _127305 s f b)). Qed.
Lemma lem6953101 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6953102 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term449 _127305 s f b) = (term517 _127305 s f b).
Proof. exact (MK_COMB (@lem6953101) (@lem6953100 _127305 s f b)). Qed.
Lemma lem6953103 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term451 _127305 s f b) = (term518 _127305 s f b).
Proof. exact (MK_COMB (@lem6953102 _127305 s f b) (@lem6953052 _127305 s f b)). Qed.
Lemma lem6953104 {_127305 : Type'} (f : _127305 -> nat) (b : nat) : (term453 _127305 f b) = (term519 _127305 f b).
Proof. exact (fun_ext (fun s : _127305 -> Prop => @lem6953103 _127305 s f b)). Qed.
Lemma lem6953105 {_127305 : Type'} : (@all (_127305 -> Prop)) = (@all (_127305 -> Prop)).
Proof. exact (eq_refl (@all (_127305 -> Prop))). Qed.
Lemma lem6953106 {_127305 : Type'} (f : _127305 -> nat) (b : nat) : (term454 _127305 f b) = (term520 _127305 f b).
Proof. exact (MK_COMB (@lem6953105 _127305) (@lem6953104 _127305 f b)). Qed.
Lemma lem6953107 {_127305 : Type'} (f : _127305 -> nat) : (term455 _127305 f) = (term521 _127305 f).
Proof. exact (fun_ext (fun b : nat => @lem6953106 _127305 f b)). Qed.
Lemma lem6953108 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6953109 {_127305 : Type'} (f : _127305 -> nat) : (term456 _127305 f) = (term522 _127305 f).
Proof. exact (MK_COMB (@lem6953108) (@lem6953107 _127305 f)). Qed.
Lemma lem6953110 {_127305 : Type'} : (term457 _127305) = (term523 _127305).
Proof. exact (fun_ext (fun f : _127305 -> nat => @lem6953109 _127305 f)). Qed.
Lemma lem6953111 {_127305 : Type'} : (@all (_127305 -> nat)) = (@all (_127305 -> nat)).
Proof. exact (eq_refl (@all (_127305 -> nat))). Qed.
Lemma lem6953112 {_127305 : Type'} : (term458 _127305) = (term524 _127305).
Proof. exact (MK_COMB (@lem6953111 _127305) (@lem6953110 _127305)). Qed.
Lemma lem6953113 {_127305 : Type'} (h1 : term377 _127305) : term524 _127305.
Proof. exact (EQ_MP (@lem6953112 _127305) (@lem6952709 _127305 h1)). Qed.
Lemma lem6953229 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6953230 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem6953229 nat nat f x). Qed.
Lemma lem6953232 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem6953230 NUMERAL 0). Qed.
Lemma lem6953233 (n : nat) : (Peano.le n) = (Peano.le n).
Proof. exact (eq_refl (Peano.le n)). Qed.
Lemma lem6953234 (n : nat) : (term0 n) = (term525 n).
Proof. exact (MK_COMB (@lem6953233 n) (@lem6953232)). Qed.
Lemma lem6953236 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6953237 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem6953236 nat (nat -> Prop) f x). Qed.
Lemma lem6953238 (n : nat) : (Peano.le n) = (@I (nat -> nat -> Prop) Peano.le n).
Proof. exact (@lem6953237 Peano.le n). Qed.
Lemma lem6953239 : (@I (nat -> nat) NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (eq_refl (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem6953240 (n : nat) : (term525 n) = (term526 n).
Proof. exact (MK_COMB (@lem6953238 n) (@lem6953239)). Qed.
Lemma lem6953242 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6953243 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem6953242 nat Prop f x). Qed.
Lemma lem6953244 (n : nat) : (term526 n) = (term527 n).
Proof. exact (@lem6953243 (@I (nat -> nat -> Prop) Peano.le n) (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem6953245 (n : nat) : (term525 n) = (term527 n).
Proof. exact (TRANS (@lem6953240 n) (@lem6953244 n)). Qed.
Lemma lem6953246 (n : nat) : (term0 n) = (term527 n).
Proof. exact (TRANS (@lem6953234 n) (@lem6953245 n)). Qed.
Lemma lem6953247 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6953254 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6953255 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem6953254 nat nat f x). Qed.
Lemma lem6953257 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem6953255 NUMERAL 0). Qed.
Lemma lem6953258 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem6953259 (n : nat) : (n = (NUMERAL 0)) = (n = (@I (nat -> nat) NUMERAL 0)).
Proof. exact (MK_COMB (@lem6953258 n) (@lem6953257)). Qed.
Lemma lem6953260 (n : nat) : (term11 n) = (term528 n).
Proof. exact (MK_COMB (@lem6953247) (@lem6953259 n)). Qed.
Lemma lem6953261 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6953262 (n : nat) : (term529 n) = (term530 n).
Proof. exact (MK_COMB (@lem6953261) (@lem6953260 n)). Qed.
Lemma lem6953263 (n : nat) : (term475 n) = (term531 n).
Proof. exact (MK_COMB (@lem6953262 n) (@lem6953246 n)). Qed.
Lemma lem6953264 : term469 = term532.
Proof. exact (fun_ext (fun n : nat => @lem6953263 n)). Qed.
Lemma lem6953265 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6953266 : term487 = term533.
Proof. exact (MK_COMB (@lem6953265) (@lem6953264)). Qed.
Lemma lem6953267 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6953274 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6953275 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem6953274 nat nat f x). Qed.
Lemma lem6953277 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem6953275 NUMERAL 0). Qed.
Lemma lem6953278 (n : nat) : (Peano.le n) = (Peano.le n).
Proof. exact (eq_refl (Peano.le n)). Qed.
Lemma lem6953279 (n : nat) : (term0 n) = (term525 n).
Proof. exact (MK_COMB (@lem6953278 n) (@lem6953277)). Qed.
Lemma lem6953281 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6953282 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem6953281 nat (nat -> Prop) f x). Qed.
Lemma lem6953283 (n : nat) : (Peano.le n) = (@I (nat -> nat -> Prop) Peano.le n).
Proof. exact (@lem6953282 Peano.le n). Qed.
Lemma lem6953284 : (@I (nat -> nat) NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (eq_refl (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem6953285 (n : nat) : (term525 n) = (term526 n).
Proof. exact (MK_COMB (@lem6953283 n) (@lem6953284)). Qed.
Lemma lem6953287 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6953288 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem6953287 nat Prop f x). Qed.
Lemma lem6953289 (n : nat) : (term526 n) = (term527 n).
Proof. exact (@lem6953288 (@I (nat -> nat -> Prop) Peano.le n) (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem6953290 (n : nat) : (term525 n) = (term527 n).
Proof. exact (TRANS (@lem6953285 n) (@lem6953289 n)). Qed.
Lemma lem6953291 (n : nat) : (term0 n) = (term527 n).
Proof. exact (TRANS (@lem6953279 n) (@lem6953290 n)). Qed.
Lemma lem6953292 (n : nat) : (term15 n) = (term534 n).
Proof. exact (MK_COMB (@lem6953267) (@lem6953291 n)). Qed.
Lemma lem6953299 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6953300 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem6953299 nat nat f x). Qed.
Lemma lem6953302 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem6953300 NUMERAL 0). Qed.
Lemma lem6953303 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem6953304 (n : nat) : (n = (NUMERAL 0)) = (n = (@I (nat -> nat) NUMERAL 0)).
Proof. exact (MK_COMB (@lem6953303 n) (@lem6953302)). Qed.
Lemma lem6953305 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6953306 (n : nat) : (term535 n) = (term536 n).
Proof. exact (MK_COMB (@lem6953305) (@lem6953304 n)). Qed.
Lemma lem6953307 (n : nat) : (term471 n) = (term537 n).
Proof. exact (MK_COMB (@lem6953306 n) (@lem6953292 n)). Qed.
Lemma lem6953308 : term468 = term538.
Proof. exact (fun_ext (fun n : nat => @lem6953307 n)). Qed.
Lemma lem6953309 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6953310 : term482 = term539.
Proof. exact (MK_COMB (@lem6953309) (@lem6953308)). Qed.
Lemma lem6953311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6953312 : term484 = term540.
Proof. exact (MK_COMB (@lem6953311) (@lem6953310)). Qed.
Lemma lem6953313 : term488 = term541.
Proof. exact (MK_COMB (@lem6953312) (@lem6953266)). Qed.
Lemma lem6953314 (h1 : term335) : term541.
Proof. exact (EQ_MP (@lem6953313) (@lem6952994 h1)). Qed.
Lemma lem6953315 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6953316 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6953321 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6953323 {_127305 : Type'} (f : _127305 -> nat) (x : _127305) : (f x) = (@I (_127305 -> nat) f x).
Proof. exact (@lem6953321 _127305 nat f x). Qed.
Lemma lem6953328 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6953329 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem6953328 nat nat f x). Qed.
Lemma lem6953331 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem6953329 NUMERAL 0). Qed.
Lemma lem6953332 {_127305 : Type'} (f : _127305 -> nat) (x : _127305) : (term360 _127305 f x) = (term542 _127305 f x).
Proof. exact (MK_COMB (@lem6953316) (@lem6953323 _127305 f x)). Qed.
Lemma lem6953333 {_127305 : Type'} (f : _127305 -> nat) (x : _127305) : ((f x) = (NUMERAL 0)) = ((@I (_127305 -> nat) f x) = (@I (nat -> nat) NUMERAL 0)).
Proof. exact (MK_COMB (@lem6953332 _127305 f x) (@lem6953331)). Qed.
Lemma lem6953334 {_127305 : Type'} (f : _127305 -> nat) (x : _127305) : (term543 _127305 f x) = (term544 _127305 f x).
Proof. exact (MK_COMB (@lem6953315) (@lem6953333 _127305 f x)). Qed.
Lemma lem6953341 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6953342 {_127305 : Type'} (f : type1364 _127305) (x : _127305) : (f x) = (@I (_127305 -> (_127305 -> Prop) -> Prop) f x).
Proof. exact (@lem6953341 _127305 (type686 _127305) f x). Qed.
Lemma lem6953343 {_127305 : Type'} (x : _127305) : (@IN _127305 x) = (@I (_127305 -> (_127305 -> Prop) -> Prop) (@IN _127305) x).
Proof. exact (@lem6953342 _127305 (@IN _127305) x). Qed.
Lemma lem6953344 {_127305 : Type'} (s : _127305 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6953345 {_127305 : Type'} (x : _127305) (s : _127305 -> Prop) : (@IN _127305 x s) = (@I (_127305 -> (_127305 -> Prop) -> Prop) (@IN _127305) x s).
Proof. exact (MK_COMB (@lem6953343 _127305 x) (@lem6953344 _127305 s)). Qed.
Lemma lem6953347 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6953348 {_127305 : Type'} (f : type686 _127305) (x : _127305 -> Prop) : (f x) = (@I ((_127305 -> Prop) -> Prop) f x).
Proof. exact (@lem6953347 (_127305 -> Prop) Prop f x). Qed.
Lemma lem6953349 {_127305 : Type'} (x : _127305) (s : _127305 -> Prop) : (@I (_127305 -> (_127305 -> Prop) -> Prop) (@IN _127305) x s) = (term495 _127305 x s).
Proof. exact (@lem6953348 _127305 (@I (_127305 -> (_127305 -> Prop) -> Prop) (@IN _127305) x) s). Qed.
Lemma lem6953351 {_127305 : Type'} (x : _127305) (s : _127305 -> Prop) : (@IN _127305 x s) = (term495 _127305 x s).
Proof. exact (TRANS (@lem6953345 _127305 x s) (@lem6953349 _127305 x s)). Qed.
Lemma lem6953352 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6953353 {_127305 : Type'} (x : _127305) (s : _127305 -> Prop) : (term545 _127305 x s) = (term546 _127305 x s).
Proof. exact (MK_COMB (@lem6953352) (@lem6953351 _127305 x s)). Qed.
Lemma lem6953354 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) : (term415 _127305 s f x) = (term547 _127305 s f x).
Proof. exact (MK_COMB (@lem6953353 _127305 x s) (@lem6953334 _127305 f x)). Qed.
Lemma lem6953355 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6953362 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6953363 {_127305 : Type'} (f : type644 _127305) (x : _127305 -> Prop) : (f x) = (@I ((_127305 -> Prop) -> (_127305 -> nat) -> nat) f x).
Proof. exact (@lem6953362 (_127305 -> Prop) (type705 _127305) f x). Qed.
Lemma lem6953364 {_127305 : Type'} (s : _127305 -> Prop) : (@nsum _127305 s) = (@I ((_127305 -> Prop) -> (_127305 -> nat) -> nat) (@nsum _127305) s).
Proof. exact (@lem6953363 _127305 (@nsum _127305) s). Qed.
Lemma lem6953365 {_127305 : Type'} (f : _127305 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6953366 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (@nsum _127305 s f) = (@I ((_127305 -> Prop) -> (_127305 -> nat) -> nat) (@nsum _127305) s f).
Proof. exact (MK_COMB (@lem6953364 _127305 s) (@lem6953365 _127305 f)). Qed.
Lemma lem6953368 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6953369 {_127305 : Type'} (f : type705 _127305) (x : _127305 -> nat) : (f x) = (@I ((_127305 -> nat) -> nat) f x).
Proof. exact (@lem6953368 (_127305 -> nat) nat f x). Qed.
Lemma lem6953370 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (@I ((_127305 -> Prop) -> (_127305 -> nat) -> nat) (@nsum _127305) s f) = (term503 _127305 s f).
Proof. exact (@lem6953369 _127305 (@I ((_127305 -> Prop) -> (_127305 -> nat) -> nat) (@nsum _127305) s) f). Qed.
Lemma lem6953372 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (@nsum _127305 s f) = (term503 _127305 s f).
Proof. exact (TRANS (@lem6953366 _127305 s f) (@lem6953370 _127305 s f)). Qed.
Lemma lem6953377 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6953378 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem6953377 nat nat f x). Qed.
Lemma lem6953380 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem6953378 NUMERAL 0). Qed.
Lemma lem6953381 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term369 _127305 s f) = (term548 _127305 s f).
Proof. exact (MK_COMB (@lem6953355) (@lem6953372 _127305 s f)). Qed.
Lemma lem6953382 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : ((@nsum _127305 s f) = (NUMERAL 0)) = ((term503 _127305 s f) = (@I (nat -> nat) NUMERAL 0)).
Proof. exact (MK_COMB (@lem6953381 _127305 s f) (@lem6953380)). Qed.
Lemma lem6953383 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6953384 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term424 _127305 s f) = (term549 _127305 s f).
Proof. exact (MK_COMB (@lem6953383) (@lem6953382 _127305 s f)). Qed.
Lemma lem6953385 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) : (term437 _127305 s f x) = (term550 _127305 s f x).
Proof. exact (MK_COMB (@lem6953384 _127305 s f) (@lem6953354 _127305 s f x)). Qed.
Lemma lem6953386 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (h1 : term437 _127305 s f x) : term550 _127305 s f x.
Proof. exact (EQ_MP (@lem6953385 _127305 s f x) (@lem6952995 _127305 s f x h1)). Qed.
Lemma lem6953387 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (h1 : term437 _127305 s f x) : term547 _127305 s f x.
Proof. exact (proj2 (@lem6953386 _127305 s f x h1)). Qed.
Lemma lem6953391 (h1 : term335) : term533.
Proof. exact (proj2 (@lem6953314 h1)). Qed.
Lemma lem6953392 (h1 : term335) : term539.
Proof. exact (proj1 (@lem6953314 h1)). Qed.
Lemma lem6953398 {A : Type'} (P : Prop) (Q : A -> Prop) : (term551 A P Q) = (term552 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem6953399 {_127305 : Type'} (P : Prop) (Q : _127305 -> Prop) : (term551 _127305 P Q) = (term552 _127305 P Q).
Proof. exact (@lem6953398 _127305 P Q). Qed.
Lemma lem6953400 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term553 _127305 s f b) = (term554 _127305 s f b).
Proof. exact (@lem6953399 _127305 (term516 _127305 s f b) (term501 _127305 s f b)). Qed.
Lemma lem6953401 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (b : nat) : (term555 _127305 s f b x) = (term500 _127305 s f x b).
Proof. exact (eq_refl (term555 _127305 s f b x)). Qed.
Lemma lem6953402 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term556 _127305 s f b) = (term501 _127305 s f b).
Proof. exact (fun_ext (fun x : _127305 => @lem6953401 _127305 s f x b)). Qed.
Lemma lem6953403 {_127305 : Type'} : (@all _127305) = (@all _127305).
Proof. exact (eq_refl (@all _127305)). Qed.
Lemma lem6953404 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term557 _127305 s f b) = (term502 _127305 s f b).
Proof. exact (MK_COMB (@lem6953403 _127305) (@lem6953402 _127305 s f b)). Qed.
Lemma lem6953405 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term517 _127305 s f b) = (term517 _127305 s f b).
Proof. exact (eq_refl (term517 _127305 s f b)). Qed.
Lemma lem6953406 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term553 _127305 s f b) = (term518 _127305 s f b).
Proof. exact (MK_COMB (@lem6953405 _127305 s f b) (@lem6953404 _127305 s f b)). Qed.
Lemma lem6953407 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6953408 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term558 _127305 s f b) = (term559 _127305 s f b).
Proof. exact (MK_COMB (@lem6953407) (@lem6953406 _127305 s f b)). Qed.
Lemma lem6953409 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (b : nat) : (term555 _127305 s f b x) = (term500 _127305 s f x b).
Proof. exact (eq_refl (term555 _127305 s f b x)). Qed.
Lemma lem6953410 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term517 _127305 s f b) = (term517 _127305 s f b).
Proof. exact (eq_refl (term517 _127305 s f b)). Qed.
Lemma lem6953411 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (b : nat) : (term560 _127305 s f b x) = (term561 _127305 s f x b).
Proof. exact (MK_COMB (@lem6953410 _127305 s f b) (@lem6953409 _127305 s f x b)). Qed.
Lemma lem6953412 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term562 _127305 s f b) = (term563 _127305 s f b).
Proof. exact (fun_ext (fun x : _127305 => @lem6953411 _127305 s f x b)). Qed.
Lemma lem6953413 {_127305 : Type'} : (@all _127305) = (@all _127305).
Proof. exact (eq_refl (@all _127305)). Qed.
Lemma lem6953414 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term554 _127305 s f b) = (term564 _127305 s f b).
Proof. exact (MK_COMB (@lem6953413 _127305) (@lem6953412 _127305 s f b)). Qed.
Lemma lem6953415 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : ((term553 _127305 s f b) = (term554 _127305 s f b)) = ((term518 _127305 s f b) = (term564 _127305 s f b)).
Proof. exact (MK_COMB (@lem6953408 _127305 s f b) (@lem6953414 _127305 s f b)). Qed.
Lemma lem6953416 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term518 _127305 s f b) = (term564 _127305 s f b).
Proof. exact (EQ_MP (@lem6953415 _127305 s f b) (@lem6953400 _127305 s f b)). Qed.
Lemma lem6953417 {_127305 : Type'} (f : _127305 -> nat) (b : nat) : (term519 _127305 f b) = (term565 _127305 f b).
Proof. exact (fun_ext (fun s : _127305 -> Prop => @lem6953416 _127305 s f b)). Qed.
Lemma lem6953418 {_127305 : Type'} : (@all (_127305 -> Prop)) = (@all (_127305 -> Prop)).
Proof. exact (eq_refl (@all (_127305 -> Prop))). Qed.
Lemma lem6953419 {_127305 : Type'} (f : _127305 -> nat) (b : nat) : (term520 _127305 f b) = (term566 _127305 f b).
Proof. exact (MK_COMB (@lem6953418 _127305) (@lem6953417 _127305 f b)). Qed.
Lemma lem6953420 {_127305 : Type'} (f : _127305 -> nat) : (term521 _127305 f) = (term567 _127305 f).
Proof. exact (fun_ext (fun b : nat => @lem6953419 _127305 f b)). Qed.
Lemma lem6953421 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6953422 {_127305 : Type'} (f : _127305 -> nat) : (term522 _127305 f) = (term568 _127305 f).
Proof. exact (MK_COMB (@lem6953421) (@lem6953420 _127305 f)). Qed.
Lemma lem6953423 {_127305 : Type'} : (term523 _127305) = (term569 _127305).
Proof. exact (fun_ext (fun f : _127305 -> nat => @lem6953422 _127305 f)). Qed.
Lemma lem6953424 {_127305 : Type'} : (@all (_127305 -> nat)) = (@all (_127305 -> nat)).
Proof. exact (eq_refl (@all (_127305 -> nat))). Qed.
Lemma lem6953425 {_127305 : Type'} : (term524 _127305) = (term570 _127305).
Proof. exact (MK_COMB (@lem6953424 _127305) (@lem6953423 _127305)). Qed.
Lemma lem6953444 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (b : nat) : (term561 _127305 s f x b) = (term561 _127305 s f x b).
Proof. exact (eq_refl (term561 _127305 s f x b)). Qed.
Lemma lem6953445 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term563 _127305 s f b) = (term563 _127305 s f b).
Proof. exact (fun_ext (fun x : _127305 => @lem6953444 _127305 s f x b)). Qed.
Lemma lem6953446 {_127305 : Type'} : (@all _127305) = (@all _127305).
Proof. exact (eq_refl (@all _127305)). Qed.
Lemma lem6953447 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (b : nat) : (term564 _127305 s f b) = (term564 _127305 s f b).
Proof. exact (MK_COMB (@lem6953446 _127305) (@lem6953445 _127305 s f b)). Qed.
Lemma lem6953448 {_127305 : Type'} (f : _127305 -> nat) (b : nat) : (term565 _127305 f b) = (term565 _127305 f b).
Proof. exact (fun_ext (fun s : _127305 -> Prop => @lem6953447 _127305 s f b)). Qed.
Lemma lem6953449 {_127305 : Type'} : (@all (_127305 -> Prop)) = (@all (_127305 -> Prop)).
Proof. exact (eq_refl (@all (_127305 -> Prop))). Qed.
Lemma lem6953450 {_127305 : Type'} (f : _127305 -> nat) (b : nat) : (term566 _127305 f b) = (term566 _127305 f b).
Proof. exact (MK_COMB (@lem6953449 _127305) (@lem6953448 _127305 f b)). Qed.
Lemma lem6953451 {_127305 : Type'} (f : _127305 -> nat) : (term567 _127305 f) = (term567 _127305 f).
Proof. exact (fun_ext (fun b : nat => @lem6953450 _127305 f b)). Qed.
Lemma lem6953452 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6953453 {_127305 : Type'} (f : _127305 -> nat) : (term568 _127305 f) = (term568 _127305 f).
Proof. exact (MK_COMB (@lem6953452) (@lem6953451 _127305 f)). Qed.
Lemma lem6953454 {_127305 : Type'} : (term569 _127305) = (term569 _127305).
Proof. exact (fun_ext (fun f : _127305 -> nat => @lem6953453 _127305 f)). Qed.
Lemma lem6953455 {_127305 : Type'} : (@all (_127305 -> nat)) = (@all (_127305 -> nat)).
Proof. exact (eq_refl (@all (_127305 -> nat))). Qed.
Lemma lem6953456 {_127305 : Type'} : (term570 _127305) = (term570 _127305).
Proof. exact (MK_COMB (@lem6953455 _127305) (@lem6953454 _127305)). Qed.
Lemma lem6953457 {_127305 : Type'} : (term524 _127305) = (term570 _127305).
Proof. exact (TRANS (@lem6953425 _127305) (@lem6953456 _127305)). Qed.
Lemma lem6953458 {_127305 : Type'} (h1 : term377 _127305) : term570 _127305.
Proof. exact (EQ_MP (@lem6953457 _127305) (@lem6953113 _127305 h1)). Qed.
Lemma lem6953540 (n : nat) : (term537 n) = (term537 n).
Proof. exact (eq_refl (term537 n)). Qed.
Lemma lem6953541 : term538 = term538.
Proof. exact (fun_ext (fun n : nat => @lem6953540 n)). Qed.
Lemma lem6953542 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6953544 : term539 = term539.
Proof. exact (MK_COMB (@lem6953542) (@lem6953541)). Qed.
Lemma lem6953545 (h1 : term335) : term539.
Proof. exact (EQ_MP (@lem6953544) (@lem6953392 h1)). Qed.
Lemma lem6953553 (n : nat) : (term531 n) = (term531 n).
Proof. exact (eq_refl (term531 n)). Qed.
Lemma lem6953554 : term532 = term532.
Proof. exact (fun_ext (fun n : nat => @lem6953553 n)). Qed.
Lemma lem6953555 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6953557 : term533 = term533.
Proof. exact (MK_COMB (@lem6953555) (@lem6953554)). Qed.
Lemma lem6953558 (h1 : term335) : term533.
Proof. exact (EQ_MP (@lem6953557) (@lem6953391 h1)). Qed.
Lemma lem6953559 {_127305 : Type'} (_92593 : _127305 -> nat) (h1 : term377 _127305) : term571 _127305 _92593.
Proof. exact (@lem6953458 _127305 h1 _92593). Qed.
Lemma lem6953560 {_127305 : Type'} (_92593 : _127305 -> nat) : (term571 _127305 _92593) = (term568 _127305 _92593).
Proof. exact (eq_refl (term571 _127305 _92593)). Qed.
Lemma lem6953561 {_127305 : Type'} (_92593 : _127305 -> nat) (h1 : term377 _127305) : term568 _127305 _92593.
Proof. exact (EQ_MP (@lem6953560 _127305 _92593) (@lem6953559 _127305 _92593 h1)). Qed.
Lemma lem6953562 {_127305 : Type'} (_92593 : _127305 -> nat) (_92594 : nat) (h1 : term377 _127305) : term572 _127305 _92593 _92594.
Proof. exact (@lem6953561 _127305 _92593 h1 _92594). Qed.
Lemma lem6953563 {_127305 : Type'} (_92593 : _127305 -> nat) (_92594 : nat) : (term572 _127305 _92593 _92594) = (term566 _127305 _92593 _92594).
Proof. exact (eq_refl (term572 _127305 _92593 _92594)). Qed.
Lemma lem6953564 {_127305 : Type'} (_92593 : _127305 -> nat) (_92594 : nat) (h1 : term377 _127305) : term566 _127305 _92593 _92594.
Proof. exact (EQ_MP (@lem6953563 _127305 _92593 _92594) (@lem6953562 _127305 _92593 _92594 h1)). Qed.
Lemma lem6953565 {_127305 : Type'} (_92593 : _127305 -> nat) (_92594 : nat) (_92595 : _127305 -> Prop) (h1 : term377 _127305) : term573 _127305 _92593 _92594 _92595.
Proof. exact (@lem6953564 _127305 _92593 _92594 h1 _92595). Qed.
Lemma lem6953566 {_127305 : Type'} (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92594 : nat) : (term573 _127305 _92593 _92594 _92595) = (term564 _127305 _92595 _92593 _92594).
Proof. exact (eq_refl (term573 _127305 _92593 _92594 _92595)). Qed.
Lemma lem6953567 {_127305 : Type'} (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92594 : nat) (h1 : term377 _127305) : term564 _127305 _92595 _92593 _92594.
Proof. exact (EQ_MP (@lem6953566 _127305 _92595 _92593 _92594) (@lem6953565 _127305 _92593 _92594 _92595 h1)). Qed.
Lemma lem6953568 {_127305 : Type'} (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92594 : nat) (_92596 : _127305) (h1 : term377 _127305) : term574 _127305 _92595 _92593 _92594 _92596.
Proof. exact (@lem6953567 _127305 _92595 _92593 _92594 h1 _92596). Qed.
Lemma lem6953569 {_127305 : Type'} (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92596 : _127305) (_92594 : nat) : (term574 _127305 _92595 _92593 _92594 _92596) = (term561 _127305 _92595 _92593 _92596 _92594).
Proof. exact (eq_refl (term574 _127305 _92595 _92593 _92594 _92596)). Qed.
Lemma lem6953570 {_127305 : Type'} (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92596 : _127305) (_92594 : nat) (h1 : term377 _127305) : term561 _127305 _92595 _92593 _92596 _92594.
Proof. exact (EQ_MP (@lem6953569 _127305 _92595 _92593 _92596 _92594) (@lem6953568 _127305 _92595 _92593 _92594 _92596 h1)). Qed.
Lemma lem6953583 (_92601 : nat) (h1 : term335) : term575 _92601.
Proof. exact (@lem6953545 h1 _92601). Qed.
Lemma lem6953584 (_92601 : nat) : (term575 _92601) = (term537 _92601).
Proof. exact (eq_refl (term575 _92601)). Qed.
Lemma lem6953586 (_92602 : nat) (h1 : term335) : term576 _92602.
Proof. exact (@lem6953558 h1 _92602). Qed.
Lemma lem6953587 (_92602 : nat) : (term576 _92602) = (term531 _92602).
Proof. exact (eq_refl (term576 _92602)). Qed.
Lemma lem6953605 {_127305 : Type'} (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92596 : _127305) (_92594 : nat) : (term561 _127305 _92595 _92593 _92596 _92594) = (term577 _127305 _92595 _92593 _92596 _92594).
Proof. exact (@lem6951801 (term513 _127305 _92595) (term511 _127305 _92595 _92593 _92594) (term500 _127305 _92595 _92593 _92596 _92594)). Qed.
Lemma lem6953606 {_127305 : Type'} (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92596 : _127305) (_92594 : nat) (h1 : term377 _127305) : term577 _127305 _92595 _92593 _92596 _92594.
Proof. exact (EQ_MP (@lem6953605 _127305 _92595 _92593 _92596 _92594) (@lem6953570 _127305 _92595 _92593 _92596 _92594 h1)). Qed.
Lemma lem6953628 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (h1 : term437 _127305 s f x) : term544 _127305 f x.
Proof. exact (proj2 (@lem6953387 _127305 s f x h1)). Qed.
Lemma lem6953634 (_92601 : nat) (h1 : term335) : term537 _92601.
Proof. exact (EQ_MP (@lem6953584 _92601) (@lem6953583 _92601 h1)). Qed.
Lemma lem6953640 (_92602 : nat) (h1 : term335) : term531 _92602.
Proof. exact (EQ_MP (@lem6953587 _92602) (@lem6953586 _92602 h1)). Qed.
Lemma lem6953885 {_127305 : Type'} (s : _127305 -> Prop) (h1 : @FINITE _127305 s) : @I ((_127305 -> Prop) -> Prop) (@FINITE _127305) s.
Proof. exact (EQ_MP (@lem6953003 _127305 s) (@lem6952474 _127305 s h1)). Qed.
Lemma lem6953886 {_127305 : Type'} (s : _127305 -> Prop) (h1 : @FINITE _127305 s) : term578 _127305 s.
Proof. exact (fun h0 : term513 _127305 s => @lem6953885 _127305 s h1). Qed.
Lemma lem6953888 (p : Prop) : (term579 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6953889 {_127305 : Type'} (s : _127305 -> Prop) : (term578 _127305 s) = (@I ((_127305 -> Prop) -> Prop) (@FINITE _127305) s).
Proof. exact (@lem6953888 (@I ((_127305 -> Prop) -> Prop) (@FINITE _127305) s)). Qed.
Lemma lem6953890 {_127305 : Type'} (s : _127305 -> Prop) (h1 : @FINITE _127305 s) : @I ((_127305 -> Prop) -> Prop) (@FINITE _127305) s.
Proof. exact (EQ_MP (@lem6953889 _127305 s) (@lem6953886 _127305 s h1)). Qed.
Lemma lem6953892 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (h1 : term437 _127305 s f x) : (term503 _127305 s f) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (proj1 (@lem6953386 _127305 s f x h1)). Qed.
Lemma lem6953893 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (h1 : term437 _127305 s f x) : term580 _127305 s f.
Proof. exact (fun h0 : term581 _127305 s f => @lem6953892 _127305 s f x h1). Qed.
Lemma lem6953895 (p : Prop) : (term579 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6953896 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term580 _127305 s f) = ((term503 _127305 s f) = (@I (nat -> nat) NUMERAL 0)).
Proof. exact (@lem6953895 ((term503 _127305 s f) = (@I (nat -> nat) NUMERAL 0))). Qed.
Lemma lem6953897 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (h1 : term437 _127305 s f x) : (term503 _127305 s f) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (EQ_MP (@lem6953896 _127305 s f) (@lem6953893 _127305 s f x h1)). Qed.
Lemma lem6953903 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6953904 (_92602 : nat) : (term531 _92602) = (term582 _92602).
Proof. exact (@lem6953903 (term527 _92602) (term528 _92602)). Qed.
Lemma lem6953912 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6953913 (_92602 : nat) : (term583 _92602) = (term584 _92602).
Proof. exact (MK_COMB (@lem6953912) (@lem6953904 _92602)). Qed.
Lemma lem6953921 (_92602 : nat) : (term582 _92602) = (term582 _92602).
Proof. exact (eq_refl (term582 _92602)). Qed.
Lemma lem6953922 (_92602 : nat) : ((term531 _92602) = (term582 _92602)) = ((term582 _92602) = (term582 _92602)).
Proof. exact (MK_COMB (@lem6953913 _92602) (@lem6953921 _92602)). Qed.
Lemma lem6953924 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6953925 (x : Prop) : (x = x) = True.
Proof. exact (@lem6953924 Prop x). Qed.
Lemma lem6953926 (_92602 : nat) : ((term582 _92602) = (term582 _92602)) = True.
Proof. exact (@lem6953925 (term582 _92602)). Qed.
Lemma lem6953927 (_92602 : nat) : ((term531 _92602) = (term582 _92602)) = True.
Proof. exact (TRANS (@lem6953922 _92602) (@lem6953926 _92602)). Qed.
Lemma lem6953928 (_92602 : nat) : True = ((term531 _92602) = (term582 _92602)).
Proof. exact (SYM (@lem6953927 _92602)). Qed.
Lemma lem6953929 (_92602 : nat) : (term531 _92602) = (term582 _92602).
Proof. exact (EQ_MP (@lem6953928 _92602) (@lem0)). Qed.
Lemma lem6953930 (_92602 : nat) (h1 : term335) : term582 _92602.
Proof. exact (EQ_MP (@lem6953929 _92602) (@lem6953640 _92602 h1)). Qed.
Lemma lem6953932 (b : Prop) (a : Prop) : (a \/ b) = (term585 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6953933 (_92602 : nat) : (term582 _92602) = (term586 _92602).
Proof. exact (@lem6953932 (term528 _92602) (term527 _92602)). Qed.
Lemma lem6953935 (a : Prop) : (term105 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6953936 (_92602 : nat) : (term587 _92602) = (_92602 = (@I (nat -> nat) NUMERAL 0)).
Proof. exact (@lem6953935 (_92602 = (@I (nat -> nat) NUMERAL 0))). Qed.
Lemma lem6953937 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6953938 (_92602 : nat) : (term588 _92602) = (term589 _92602).
Proof. exact (MK_COMB (@lem6953937) (@lem6953936 _92602)). Qed.
Lemma lem6953939 (_92602 : nat) : (term527 _92602) = (term527 _92602).
Proof. exact (eq_refl (term527 _92602)). Qed.
Lemma lem6953940 (_92602 : nat) : (term586 _92602) = (term590 _92602).
Proof. exact (MK_COMB (@lem6953938 _92602) (@lem6953939 _92602)). Qed.
Lemma lem6953941 (_92602 : nat) : (term582 _92602) = (term590 _92602).
Proof. exact (TRANS (@lem6953933 _92602) (@lem6953940 _92602)). Qed.
Lemma lem6953944 (_92602 : nat) (h1 : term335) : term590 _92602.
Proof. exact (EQ_MP (@lem6953941 _92602) (@lem6953930 _92602 h1)). Qed.
Lemma lem6953945 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term335) : term591 _127305 s f.
Proof. exact (@lem6953944 (term503 _127305 s f) h1). Qed.
Lemma lem6953948 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (h1 : term335) (h2 : term437 _127305 s f x) : term592 _127305 s f.
Proof. exact (@lem6953945 _127305 s f h1 (@lem6953897 _127305 s f x h2)). Qed.
Lemma lem6953949 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (h1 : term335) (h2 : term437 _127305 s f x) : term593 _127305 s f.
Proof. exact (fun h0 : term594 _127305 s f => @lem6953948 _127305 s f x h1 h2). Qed.
Lemma lem6953951 (p : Prop) : (term579 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6953952 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term593 _127305 s f) = (term592 _127305 s f).
Proof. exact (@lem6953951 (term592 _127305 s f)). Qed.
Lemma lem6953953 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (h1 : term335) (h2 : term437 _127305 s f x) : term592 _127305 s f.
Proof. exact (EQ_MP (@lem6953952 _127305 s f) (@lem6953949 _127305 s f x h1 h2)). Qed.
Lemma lem6953955 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (h1 : term437 _127305 s f x) : term495 _127305 x s.
Proof. exact (proj1 (@lem6953387 _127305 s f x h1)). Qed.
Lemma lem6953956 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (h1 : term437 _127305 s f x) : term595 _127305 x s.
Proof. exact (fun h0 : term497 _127305 x s => @lem6953955 _127305 s f x h1). Qed.
Lemma lem6953958 (p : Prop) : (term579 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6953959 {_127305 : Type'} (x : _127305) (s : _127305 -> Prop) : (term595 _127305 x s) = (term495 _127305 x s).
Proof. exact (@lem6953958 (term495 _127305 x s)). Qed.
Lemma lem6953960 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (h1 : term437 _127305 s f x) : term495 _127305 x s.
Proof. exact (EQ_MP (@lem6953959 _127305 x s) (@lem6953956 _127305 s f x h1)). Qed.
Lemma lem6953976 (q : Prop) (p : Prop) (r : Prop) : (term333 p q r) = (term333 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6953977 {_127305 : Type'} (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92596 : _127305) (_92594 : nat) : (term596 _127305 _92595 _92593 _92596 _92594) = (term597 _127305 _92595 _92593 _92596 _92594).
Proof. exact (@lem6953976 (term497 _127305 _92596 _92595) (term511 _127305 _92595 _92593 _92594) (term494 _127305 _92593 _92596 _92594)). Qed.
Lemma lem6953991 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6953992 {_127305 : Type'} (_92596 : _127305) (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92594 : nat) : (term598 _127305 _92595 _92593 _92596 _92594) = (term599 _127305 _92596 _92595 _92593 _92594).
Proof. exact (@lem6953991 (term494 _127305 _92593 _92596 _92594) (term511 _127305 _92595 _92593 _92594)). Qed.
Lemma lem6953998 {_127305 : Type'} (_92596 : _127305) (_92595 : _127305 -> Prop) : (term499 _127305 _92596 _92595) = (term499 _127305 _92596 _92595).
Proof. exact (eq_refl (term499 _127305 _92596 _92595)). Qed.
Lemma lem6953999 {_127305 : Type'} (_92596 : _127305) (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92594 : nat) : (term597 _127305 _92595 _92593 _92596 _92594) = (term600 _127305 _92596 _92595 _92593 _92594).
Proof. exact (MK_COMB (@lem6953998 _127305 _92596 _92595) (@lem6953992 _127305 _92596 _92595 _92593 _92594)). Qed.
Lemma lem6954003 (q : Prop) (p : Prop) (r : Prop) : (term333 p q r) = (term333 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6954004 {_127305 : Type'} (_92596 : _127305) (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92594 : nat) : (term600 _127305 _92596 _92595 _92593 _92594) = (term601 _127305 _92596 _92595 _92593 _92594).
Proof. exact (@lem6954003 (term494 _127305 _92593 _92596 _92594) (term497 _127305 _92596 _92595) (term511 _127305 _92595 _92593 _92594)). Qed.
Lemma lem6954020 {_127305 : Type'} (_92596 : _127305) (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92594 : nat) : (term597 _127305 _92595 _92593 _92596 _92594) = (term601 _127305 _92596 _92595 _92593 _92594).
Proof. exact (TRANS (@lem6953999 _127305 _92596 _92595 _92593 _92594) (@lem6954004 _127305 _92596 _92595 _92593 _92594)). Qed.
Lemma lem6954021 {_127305 : Type'} (_92596 : _127305) (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92594 : nat) : (term596 _127305 _92595 _92593 _92596 _92594) = (term601 _127305 _92596 _92595 _92593 _92594).
Proof. exact (TRANS (@lem6953977 _127305 _92595 _92593 _92596 _92594) (@lem6954020 _127305 _92596 _92595 _92593 _92594)). Qed.
Lemma lem6954022 {_127305 : Type'} (_92595 : _127305 -> Prop) : (term515 _127305 _92595) = (term515 _127305 _92595).
Proof. exact (eq_refl (term515 _127305 _92595)). Qed.
Lemma lem6954023 {_127305 : Type'} (_92596 : _127305) (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92594 : nat) : (term577 _127305 _92595 _92593 _92596 _92594) = (term602 _127305 _92596 _92595 _92593 _92594).
Proof. exact (MK_COMB (@lem6954022 _127305 _92595) (@lem6954021 _127305 _92596 _92595 _92593 _92594)). Qed.
Lemma lem6954027 (q : Prop) (p : Prop) (r : Prop) : (term333 p q r) = (term333 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6954028 {_127305 : Type'} (_92596 : _127305) (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92594 : nat) : (term602 _127305 _92596 _92595 _92593 _92594) = (term603 _127305 _92596 _92595 _92593 _92594).
Proof. exact (@lem6954027 (term494 _127305 _92593 _92596 _92594) (term513 _127305 _92595) (term604 _127305 _92596 _92595 _92593 _92594)). Qed.
Lemma lem6954054 {_127305 : Type'} (_92596 : _127305) (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92594 : nat) : (term577 _127305 _92595 _92593 _92596 _92594) = (term603 _127305 _92596 _92595 _92593 _92594).
Proof. exact (TRANS (@lem6954023 _127305 _92596 _92595 _92593 _92594) (@lem6954028 _127305 _92596 _92595 _92593 _92594)). Qed.
Lemma lem6954055 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6954056 {_127305 : Type'} (_92596 : _127305) (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92594 : nat) : (term605 _127305 _92595 _92593 _92596 _92594) = (term606 _127305 _92596 _92595 _92593 _92594).
Proof. exact (MK_COMB (@lem6954055) (@lem6954054 _127305 _92596 _92595 _92593 _92594)). Qed.
Lemma lem6954080 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6954081 {_127305 : Type'} (_92596 : _127305) (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92594 : nat) : (term607 _127305 _92593 _92594 _92596 _92595) = (term604 _127305 _92596 _92595 _92593 _92594).
Proof. exact (@lem6954080 (term497 _127305 _92596 _92595) (term511 _127305 _92595 _92593 _92594)). Qed.
Lemma lem6954087 {_127305 : Type'} (_92595 : _127305 -> Prop) : (term515 _127305 _92595) = (term515 _127305 _92595).
Proof. exact (eq_refl (term515 _127305 _92595)). Qed.
Lemma lem6954088 {_127305 : Type'} (_92596 : _127305) (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92594 : nat) : (term608 _127305 _92593 _92594 _92596 _92595) = (term609 _127305 _92596 _92595 _92593 _92594).
Proof. exact (MK_COMB (@lem6954087 _127305 _92595) (@lem6954081 _127305 _92596 _92595 _92593 _92594)). Qed.
Lemma lem6954099 {_127305 : Type'} (_92593 : _127305 -> nat) (_92596 : _127305) (_92594 : nat) : (term610 _127305 _92593 _92596 _92594) = (term610 _127305 _92593 _92596 _92594).
Proof. exact (eq_refl (term610 _127305 _92593 _92596 _92594)). Qed.
Lemma lem6954100 {_127305 : Type'} (_92596 : _127305) (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92594 : nat) : (term611 _127305 _92593 _92594 _92596 _92595) = (term603 _127305 _92596 _92595 _92593 _92594).
Proof. exact (MK_COMB (@lem6954099 _127305 _92593 _92596 _92594) (@lem6954088 _127305 _92596 _92595 _92593 _92594)). Qed.
Lemma lem6954111 {_127305 : Type'} (_92596 : _127305) (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92594 : nat) : ((term577 _127305 _92595 _92593 _92596 _92594) = (term611 _127305 _92593 _92594 _92596 _92595)) = ((term603 _127305 _92596 _92595 _92593 _92594) = (term603 _127305 _92596 _92595 _92593 _92594)).
Proof. exact (MK_COMB (@lem6954056 _127305 _92596 _92595 _92593 _92594) (@lem6954100 _127305 _92596 _92595 _92593 _92594)). Qed.
Lemma lem6954113 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6954114 (x : Prop) : (x = x) = True.
Proof. exact (@lem6954113 Prop x). Qed.
Lemma lem6954115 {_127305 : Type'} (_92596 : _127305) (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92594 : nat) : ((term603 _127305 _92596 _92595 _92593 _92594) = (term603 _127305 _92596 _92595 _92593 _92594)) = True.
Proof. exact (@lem6954114 (term603 _127305 _92596 _92595 _92593 _92594)). Qed.
Lemma lem6954116 {_127305 : Type'} (_92593 : _127305 -> nat) (_92594 : nat) (_92596 : _127305) (_92595 : _127305 -> Prop) : ((term577 _127305 _92595 _92593 _92596 _92594) = (term611 _127305 _92593 _92594 _92596 _92595)) = True.
Proof. exact (TRANS (@lem6954111 _127305 _92596 _92595 _92593 _92594) (@lem6954115 _127305 _92596 _92595 _92593 _92594)). Qed.
Lemma lem6954117 {_127305 : Type'} (_92593 : _127305 -> nat) (_92594 : nat) (_92596 : _127305) (_92595 : _127305 -> Prop) : True = ((term577 _127305 _92595 _92593 _92596 _92594) = (term611 _127305 _92593 _92594 _92596 _92595)).
Proof. exact (SYM (@lem6954116 _127305 _92593 _92594 _92596 _92595)). Qed.
Lemma lem6954118 {_127305 : Type'} (_92593 : _127305 -> nat) (_92594 : nat) (_92596 : _127305) (_92595 : _127305 -> Prop) : (term577 _127305 _92595 _92593 _92596 _92594) = (term611 _127305 _92593 _92594 _92596 _92595).
Proof. exact (EQ_MP (@lem6954117 _127305 _92593 _92594 _92596 _92595) (@lem0)). Qed.
Lemma lem6954119 {_127305 : Type'} (_92593 : _127305 -> nat) (_92594 : nat) (_92596 : _127305) (_92595 : _127305 -> Prop) (h1 : term377 _127305) : term611 _127305 _92593 _92594 _92596 _92595.
Proof. exact (EQ_MP (@lem6954118 _127305 _92593 _92594 _92596 _92595) (@lem6953606 _127305 _92595 _92593 _92596 _92594 h1)). Qed.
Lemma lem6954121 (b : Prop) (a : Prop) : (a \/ b) = (term585 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6954122 {_127305 : Type'} (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92596 : _127305) (_92594 : nat) : (term611 _127305 _92593 _92594 _92596 _92595) = (term612 _127305 _92595 _92593 _92596 _92594).
Proof. exact (@lem6954121 (term608 _127305 _92593 _92594 _92596 _92595) (term494 _127305 _92593 _92596 _92594)). Qed.
Lemma lem6954124 (a : Prop) (b : Prop) : (term613 a b) = (term614 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6954125 {_127305 : Type'} (_92593 : _127305 -> nat) (_92594 : nat) (_92596 : _127305) (_92595 : _127305 -> Prop) : (term615 _127305 _92593 _92594 _92596 _92595) = (term616 _127305 _92593 _92594 _92596 _92595).
Proof. exact (@lem6954124 (term513 _127305 _92595) (term607 _127305 _92593 _92594 _92596 _92595)). Qed.
Lemma lem6954127 (a : Prop) : (term105 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6954128 {_127305 : Type'} (_92595 : _127305 -> Prop) : (term617 _127305 _92595) = (@I ((_127305 -> Prop) -> Prop) (@FINITE _127305) _92595).
Proof. exact (@lem6954127 (@I ((_127305 -> Prop) -> Prop) (@FINITE _127305) _92595)). Qed.
Lemma lem6954129 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6954130 {_127305 : Type'} (_92595 : _127305 -> Prop) : (term618 _127305 _92595) = (term619 _127305 _92595).
Proof. exact (MK_COMB (@lem6954129) (@lem6954128 _127305 _92595)). Qed.
Lemma lem6954132 (a : Prop) (b : Prop) : (term613 a b) = (term614 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6954133 {_127305 : Type'} (_92593 : _127305 -> nat) (_92594 : nat) (_92596 : _127305) (_92595 : _127305 -> Prop) : (term620 _127305 _92593 _92594 _92596 _92595) = (term621 _127305 _92593 _92594 _92596 _92595).
Proof. exact (@lem6954132 (term511 _127305 _92595 _92593 _92594) (term497 _127305 _92596 _92595)). Qed.
Lemma lem6954135 (a : Prop) : (term105 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6954136 {_127305 : Type'} (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92594 : nat) : (term622 _127305 _92595 _92593 _92594) = (term509 _127305 _92595 _92593 _92594).
Proof. exact (@lem6954135 (term509 _127305 _92595 _92593 _92594)). Qed.
Lemma lem6954137 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6954138 {_127305 : Type'} (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92594 : nat) : (term623 _127305 _92595 _92593 _92594) = (term624 _127305 _92595 _92593 _92594).
Proof. exact (MK_COMB (@lem6954137) (@lem6954136 _127305 _92595 _92593 _92594)). Qed.
Lemma lem6954140 (a : Prop) : (term105 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6954141 {_127305 : Type'} (_92596 : _127305) (_92595 : _127305 -> Prop) : (term625 _127305 _92596 _92595) = (term495 _127305 _92596 _92595).
Proof. exact (@lem6954140 (term495 _127305 _92596 _92595)). Qed.
Lemma lem6954142 {_127305 : Type'} (_92593 : _127305 -> nat) (_92594 : nat) (_92596 : _127305) (_92595 : _127305 -> Prop) : (term621 _127305 _92593 _92594 _92596 _92595) = (term626 _127305 _92593 _92594 _92596 _92595).
Proof. exact (MK_COMB (@lem6954138 _127305 _92595 _92593 _92594) (@lem6954141 _127305 _92596 _92595)). Qed.
Lemma lem6954143 {_127305 : Type'} (_92593 : _127305 -> nat) (_92594 : nat) (_92596 : _127305) (_92595 : _127305 -> Prop) : (term620 _127305 _92593 _92594 _92596 _92595) = (term626 _127305 _92593 _92594 _92596 _92595).
Proof. exact (TRANS (@lem6954133 _127305 _92593 _92594 _92596 _92595) (@lem6954142 _127305 _92593 _92594 _92596 _92595)). Qed.
Lemma lem6954144 {_127305 : Type'} (_92593 : _127305 -> nat) (_92594 : nat) (_92596 : _127305) (_92595 : _127305 -> Prop) : (term616 _127305 _92593 _92594 _92596 _92595) = (term627 _127305 _92593 _92594 _92596 _92595).
Proof. exact (MK_COMB (@lem6954130 _127305 _92595) (@lem6954143 _127305 _92593 _92594 _92596 _92595)). Qed.
Lemma lem6954145 {_127305 : Type'} (_92593 : _127305 -> nat) (_92594 : nat) (_92596 : _127305) (_92595 : _127305 -> Prop) : (term615 _127305 _92593 _92594 _92596 _92595) = (term627 _127305 _92593 _92594 _92596 _92595).
Proof. exact (TRANS (@lem6954125 _127305 _92593 _92594 _92596 _92595) (@lem6954144 _127305 _92593 _92594 _92596 _92595)). Qed.
Lemma lem6954146 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6954147 {_127305 : Type'} (_92593 : _127305 -> nat) (_92594 : nat) (_92596 : _127305) (_92595 : _127305 -> Prop) : (term628 _127305 _92593 _92594 _92596 _92595) = (term629 _127305 _92593 _92594 _92596 _92595).
Proof. exact (MK_COMB (@lem6954146) (@lem6954145 _127305 _92593 _92594 _92596 _92595)). Qed.
Lemma lem6954148 {_127305 : Type'} (_92593 : _127305 -> nat) (_92596 : _127305) (_92594 : nat) : (term494 _127305 _92593 _92596 _92594) = (term494 _127305 _92593 _92596 _92594).
Proof. exact (eq_refl (term494 _127305 _92593 _92596 _92594)). Qed.
Lemma lem6954149 {_127305 : Type'} (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92596 : _127305) (_92594 : nat) : (term612 _127305 _92595 _92593 _92596 _92594) = (term630 _127305 _92595 _92593 _92596 _92594).
Proof. exact (MK_COMB (@lem6954147 _127305 _92593 _92594 _92596 _92595) (@lem6954148 _127305 _92593 _92596 _92594)). Qed.
Lemma lem6954150 {_127305 : Type'} (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92596 : _127305) (_92594 : nat) : (term611 _127305 _92593 _92594 _92596 _92595) = (term630 _127305 _92595 _92593 _92596 _92594).
Proof. exact (TRANS (@lem6954122 _127305 _92595 _92593 _92596 _92594) (@lem6954149 _127305 _92595 _92593 _92596 _92594)). Qed.
Lemma lem6954152 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (h1 : term335) (h2 : term437 _127305 s f x) : term631 _127305 f x s.
Proof. exact (conj (@lem6953953 _127305 s f x h1 h2) (@lem6953960 _127305 s f x h2)). Qed.
Lemma lem6954153 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (h1 : term335) (h2 : @FINITE _127305 s) (h3 : term437 _127305 s f x) : term632 _127305 f x s.
Proof. exact (conj (@lem6953890 _127305 s h2) (@lem6954152 _127305 s f x h1 h3)). Qed.
Lemma lem6954155 {_127305 : Type'} (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92596 : _127305) (_92594 : nat) (h1 : term377 _127305) : term630 _127305 _92595 _92593 _92596 _92594.
Proof. exact (EQ_MP (@lem6954150 _127305 _92595 _92593 _92596 _92594) (@lem6954119 _127305 _92593 _92594 _92596 _92595 h1)). Qed.
Lemma lem6954156 {_127305 : Type'} (_92595 : _127305 -> Prop) (_92593 : _127305 -> nat) (_92596 : _127305) (_92594 : nat) (h1 : term377 _127305) : term630 _127305 _92595 _92593 _92596 _92594.
Proof. exact (@lem6954155 _127305 _92595 _92593 _92596 _92594 h1). Qed.
Lemma lem6954157 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (h1 : term377 _127305) : term633 _127305 s f x.
Proof. exact (@lem6954156 _127305 s f x (@I (nat -> nat) NUMERAL 0) h1). Qed.
Lemma lem6954160 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (h1 : term377 _127305) (h2 : term335) (h3 : @FINITE _127305 s) (h4 : term437 _127305 s f x) : term634 _127305 f x.
Proof. exact (@lem6954157 _127305 s f x h1 (@lem6954153 _127305 s f x h2 h3 h4)). Qed.
Lemma lem6954161 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (h1 : term377 _127305) (h2 : term335) (h3 : @FINITE _127305 s) (h4 : term437 _127305 s f x) : term635 _127305 f x.
Proof. exact (fun h0 : term636 _127305 f x => @lem6954160 _127305 s f x h1 h2 h3 h4). Qed.
Lemma lem6954163 (p : Prop) : (term579 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6954164 {_127305 : Type'} (f : _127305 -> nat) (x : _127305) : (term635 _127305 f x) = (term634 _127305 f x).
Proof. exact (@lem6954163 (term634 _127305 f x)). Qed.
Lemma lem6954165 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (h1 : term377 _127305) (h2 : term335) (h3 : @FINITE _127305 s) (h4 : term437 _127305 s f x) : term634 _127305 f x.
Proof. exact (EQ_MP (@lem6954164 _127305 f x) (@lem6954161 _127305 s f x h1 h2 h3 h4)). Qed.
Lemma lem6954167 (b : Prop) (a : Prop) : (a \/ b) = (term585 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6954168 (_92601 : nat) : (term537 _92601) = (term637 _92601).
Proof. exact (@lem6954167 (term534 _92601) (_92601 = (@I (nat -> nat) NUMERAL 0))). Qed.
Lemma lem6954170 (a : Prop) : (term105 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6954171 (_92601 : nat) : (term638 _92601) = (term527 _92601).
Proof. exact (@lem6954170 (term527 _92601)). Qed.
Lemma lem6954172 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6954173 (_92601 : nat) : (term639 _92601) = (term640 _92601).
Proof. exact (MK_COMB (@lem6954172) (@lem6954171 _92601)). Qed.
Lemma lem6954174 (_92601 : nat) : (_92601 = (@I (nat -> nat) NUMERAL 0)) = (_92601 = (@I (nat -> nat) NUMERAL 0)).
Proof. exact (eq_refl (_92601 = (@I (nat -> nat) NUMERAL 0))). Qed.
Lemma lem6954175 (_92601 : nat) : (term637 _92601) = (term641 _92601).
Proof. exact (MK_COMB (@lem6954173 _92601) (@lem6954174 _92601)). Qed.
Lemma lem6954176 (_92601 : nat) : (term537 _92601) = (term641 _92601).
Proof. exact (TRANS (@lem6954168 _92601) (@lem6954175 _92601)). Qed.
Lemma lem6954179 (_92601 : nat) (h1 : term335) : term641 _92601.
Proof. exact (EQ_MP (@lem6954176 _92601) (@lem6953634 _92601 h1)). Qed.
Lemma lem6954180 {_127305 : Type'} (f : _127305 -> nat) (x : _127305) (h1 : term335) : term642 _127305 f x.
Proof. exact (@lem6954179 (@I (_127305 -> nat) f x) h1). Qed.
Lemma lem6954183 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (h1 : term377 _127305) (h2 : term335) (h3 : @FINITE _127305 s) (h4 : term437 _127305 s f x) : (@I (_127305 -> nat) f x) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem6954180 _127305 f x h2 (@lem6954165 _127305 s f x h1 h2 h3 h4)). Qed.
Lemma lem6954184 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (h1 : term377 _127305) (h2 : term335) (h3 : @FINITE _127305 s) (h4 : term437 _127305 s f x) : term643 _127305 f x.
Proof. exact (fun h0 : term544 _127305 f x => @lem6954183 _127305 s f x h1 h2 h3 h4). Qed.
Lemma lem6954186 (p : Prop) : (term579 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6954187 {_127305 : Type'} (f : _127305 -> nat) (x : _127305) : (term643 _127305 f x) = ((@I (_127305 -> nat) f x) = (@I (nat -> nat) NUMERAL 0)).
Proof. exact (@lem6954186 ((@I (_127305 -> nat) f x) = (@I (nat -> nat) NUMERAL 0))). Qed.
Lemma lem6954188 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (h1 : term377 _127305) (h2 : term335) (h3 : @FINITE _127305 s) (h4 : term437 _127305 s f x) : (@I (_127305 -> nat) f x) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (EQ_MP (@lem6954187 _127305 f x) (@lem6954184 _127305 s f x h1 h2 h3 h4)). Qed.
Lemma lem6954191 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6954193 {_127305 : Type'} (f : _127305 -> nat) (x : _127305) : (term544 _127305 f x) = (term644 _127305 f x).
Proof. exact (@lem6954191 ((@I (_127305 -> nat) f x) = (@I (nat -> nat) NUMERAL 0))). Qed.
Lemma lem6954196 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (h1 : term437 _127305 s f x) : term644 _127305 f x.
Proof. exact (EQ_MP (@lem6954193 _127305 f x) (@lem6953628 _127305 s f x h1)). Qed.
Lemma lem6954199 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (h1 : term377 _127305) (h2 : term335) (h3 : @FINITE _127305 s) (h4 : term437 _127305 s f x) : False.
Proof. exact (@lem6954196 _127305 s f x h4 (@lem6954188 _127305 s f x h1 h2 h3 h4)). Qed.
Lemma lem6954200 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (h1 : term377 _127305) (h2 : term335) (h3 : @FINITE _127305 s) (h4 : term437 _127305 s f x) : term645.
Proof. exact (fun h0 : ~ False => @lem6954199 _127305 s f x h1 h2 h3 h4). Qed.
Lemma lem6954202 (p : Prop) : (term579 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6954203 : term645 = False.
Proof. exact (@lem6954202 False). Qed.
Lemma lem6954204 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (x : _127305) (h1 : term377 _127305) (h2 : term335) (h3 : @FINITE _127305 s) (h4 : term437 _127305 s f x) : False.
Proof. exact (EQ_MP (@lem6954203) (@lem6954200 _127305 s f x h1 h2 h3 h4)). Qed.
Lemma lem6954205 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term377 _127305) (h2 : term335) (h3 : @FINITE _127305 s) (h4 : term376 _127305 s f) : False.
Proof. exact (ex_elim (@lem6952569 _127305 s f h4) (fun x : _127305 => fun h0 : term439 _127305 s f x => @lem6954204 _127305 s f x h1 h2 h3 h0)). Qed.
Lemma lem6954206 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term377 _127305) (h2 : term335) (h3 : @FINITE _127305 s) (h4 : term376 _127305 s f) : (@FINITE _127305 s) = False.
Proof. exact (prop_ext (fun h5 : @FINITE _127305 s => @lem6954205 _127305 s f h1 h2 h3 h4) (fun h5 : False => @lem6952474 _127305 s h3)). Qed.
Lemma lem6954207 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term377 _127305) (h2 : term335) (h3 : @FINITE _127305 s) (h4 : term376 _127305 s f) : False.
Proof. exact (EQ_MP (@lem6954206 _127305 s f h1 h2 h3 h4) (@lem6952474 _127305 s h3)). Qed.
Lemma lem6954208 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term377 _127305) (h2 : @FINITE _127305 s) (h3 : term376 _127305 s f) : term382.
Proof. exact (fun h0 : term335 => @lem6954207 _127305 s f h1 h0 h2 h3). Qed.
Lemma lem6954209 : term382 = term383.
Proof. exact (@lem69 term335). Qed.
Lemma lem6954210 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term377 _127305) (h2 : @FINITE _127305 s) (h3 : term376 _127305 s f) : term383.
Proof. exact (EQ_MP (@lem6954209) (@lem6954208 _127305 s f h1 h2 h3)). Qed.
Lemma lem6954211 {_127305 A : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : term377 _127305) (h2 : @FINITE _127305 s) (h3 : term376 _127305 s f) : term386 A.
Proof. exact (fun h0 : term377 A => @lem6954210 _127305 s f h1 h2 h3). Qed.
Lemma lem6954212 {_127305 A : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : @FINITE _127305 s) (h2 : term376 _127305 s f) : term388 _127305 A.
Proof. exact (fun h0 : term377 _127305 => @lem6954211 _127305 A s f h0 h1 h2). Qed.
Lemma lem6954213 {_127305 A : Type'} (f : _127305 -> nat) (s : _127305 -> Prop) (h1 : @FINITE _127305 s) : term391 _127305 A s f.
Proof. exact (fun h0 : term376 _127305 s f => @lem6954212 _127305 A s f h1 h0). Qed.
Lemma lem6954214 {_127305 A : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : term393 _127305 A s f.
Proof. exact (fun h0 : @FINITE _127305 s => @lem6954213 _127305 A f s h0). Qed.
Lemma lem6954219 {_127305 A : Type'} (f : _127305 -> nat) : term397 _127305 A f.
Proof. exact (fun s : _127305 -> Prop => @lem6954214 _127305 A s f). Qed.
Lemma lem6954224 {_127305 A : Type'} : term401 _127305 A.
Proof. exact (fun f : _127305 -> nat => @lem6954219 _127305 A f). Qed.
Lemma lem6954225 {_127305 A : Type'} : term400 _127305 A.
Proof. exact (EQ_MP (@lem6952463 _127305 A) (@lem6954224 _127305 A)). Qed.
Lemma lem6954226 {_127305 A : Type'} (f : _127305 -> nat) : term646 _127305 A f.
Proof. exact (@lem6954225 _127305 A f). Qed.
Lemma lem6954227 {_127305 A : Type'} (f : _127305 -> nat) : (term646 _127305 A f) = (term396 _127305 A f).
Proof. exact (eq_refl (term646 _127305 A f)). Qed.
Lemma lem6954228 {_127305 A : Type'} (f : _127305 -> nat) : term396 _127305 A f.
Proof. exact (EQ_MP (@lem6954227 _127305 A f) (@lem6954226 _127305 A f)). Qed.
Lemma lem6954229 {_127305 A : Type'} (f : _127305 -> nat) (s : _127305 -> Prop) : term647 _127305 A f s.
Proof. exact (@lem6954228 _127305 A f s). Qed.
Lemma lem6954230 {_127305 A : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term647 _127305 A f s) = (term378 _127305 A s f).
Proof. exact (eq_refl (term647 _127305 A f s)). Qed.
Lemma lem6954231 {_127305 A : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : term378 _127305 A s f.
Proof. exact (EQ_MP (@lem6954230 _127305 A s f) (@lem6954229 _127305 A f s)). Qed.
Lemma lem6954233 {_127305 A : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : term378 _127305 A s f.
Proof. exact (@lem6952161 _127305 A s f (@lem6954231 _127305 A s f)). Qed.
Lemma lem6954234 {_127305 A : Type'} (f : _127305 -> nat) (s : _127305 -> Prop) (h1 : @FINITE _127305 s) : term390 _127305 A s f.
Proof. exact (@lem6954233 _127305 A s f (@lem6951803 _127305 s h1)). Qed.
Lemma lem6954235 {_127305 A : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : @FINITE _127305 s) (h2 : term376 _127305 s f) : term387 _127305 A.
Proof. exact (@lem6954234 _127305 A f s h1 (@lem6952142 _127305 s f h2)). Qed.
Lemma lem6954236 {_127305 A : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : @FINITE _127305 s) (h2 : term376 _127305 s f) : term385 A.
Proof. exact (@lem6954235 _127305 A s f h1 h2 (@lem6952143 _127305)). Qed.
Lemma lem6954237 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : @FINITE _127305 s) (h2 : term376 _127305 s f) : term382.
Proof. exact (@lem6954236 _127305 Prop s f h1 h2 (@lem6949047 Prop)). Qed.
Lemma lem6954238 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : @FINITE _127305 s) (h2 : term376 _127305 s f) : False.
Proof. exact (@lem6954237 _127305 s f h1 h2 (@lem6951802)). Qed.
Lemma lem6954239 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : @FINITE _127305 s) (h2 : term376 _127305 s f) : (term376 _127305 s f) = False.
Proof. exact (prop_ext (fun h3 : term376 _127305 s f => @lem6954238 _127305 s f h1 h2) (fun h3 : False => @lem6952142 _127305 s f h2)). Qed.
Lemma lem6954240 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) (h1 : @FINITE _127305 s) (h2 : term376 _127305 s f) : False.
Proof. exact (EQ_MP (@lem6954239 _127305 s f h1 h2) (@lem6952142 _127305 s f h2)). Qed.
Lemma lem6954241 {_127305 : Type'} (f : _127305 -> nat) (s : _127305 -> Prop) (h1 : @FINITE _127305 s) : term375 _127305 s f.
Proof. exact (fun h0 : term376 _127305 s f => @lem6954240 _127305 s f h1 h0). Qed.
Lemma lem6954243 {_127305 : Type'} (f : _127305 -> nat) (s : _127305 -> Prop) (h1 : @FINITE _127305 s) : term374 _127305 s f.
Proof. exact (EQ_MP (@lem6952141 _127305 s f) (@lem6954241 _127305 f s h1)). Qed.
Lemma lem6954244 {_127305 : Type'} (f : _127305 -> nat) (s : _127305 -> Prop) (h1 : @FINITE _127305 s) : term648 _127305 s f.
Proof. exact (conj (@lem6954243 _127305 f s h1) (@lem6952137 _127305 s f)). Qed.
Lemma lem6954245 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term648 _127305 s f) = (((@nsum _127305 s f) = (NUMERAL 0)) = (term340 _127305 s f)).
Proof. exact (@lem32 ((@nsum _127305 s f) = (NUMERAL 0)) (term340 _127305 s f)). Qed.
Lemma lem6954246 {_127305 : Type'} (f : _127305 -> nat) (s : _127305 -> Prop) (h1 : @FINITE _127305 s) : ((@nsum _127305 s f) = (NUMERAL 0)) = (term340 _127305 s f).
Proof. exact (EQ_MP (@lem6954245 _127305 s f) (@lem6954244 _127305 f s h1)). Qed.
Lemma lem6954247 {_127305 : Type'} (f : _127305 -> nat) (s : _127305 -> Prop) (h1 : @FINITE _127305 s) : (@FINITE _127305 s) = (((@nsum _127305 s f) = (NUMERAL 0)) = (term340 _127305 s f)).
Proof. exact (prop_ext (fun h2 : @FINITE _127305 s => @lem6954246 _127305 f s h1) (fun h2 : ((@nsum _127305 s f) = (NUMERAL 0)) = (term340 _127305 s f) => @lem6951803 _127305 s h1)). Qed.
Lemma lem6954248 {_127305 : Type'} (f : _127305 -> nat) (s : _127305 -> Prop) (h1 : @FINITE _127305 s) : ((@nsum _127305 s f) = (NUMERAL 0)) = (term340 _127305 s f).
Proof. exact (EQ_MP (@lem6954247 _127305 f s h1) (@lem6951803 _127305 s h1)). Qed.
Lemma lem6954249 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : term649 _127305 s f.
Proof. exact (fun h0 : @FINITE _127305 s => @lem6954248 _127305 f s h0). Qed.
Lemma lem6954254 {_127305 : Type'} (f : _127305 -> nat) : term650 _127305 f.
Proof. exact (fun s : _127305 -> Prop => @lem6954249 _127305 s f). Qed.
