Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5405853_term_abbrevs.
Require Import INT_POS_spec.
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
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
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
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm2318497_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm2841413_spec.
Require Import thm2841414_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem5404145 (m : nat) (x : nat) : (term0 m x) = (term0 m x).
Proof. exact (eq_refl (term0 m x)). Qed.
Lemma lem5404146 (m : nat) : (term1 m) = (term1 m).
Proof. exact (fun_ext (fun x : nat => @lem5404145 m x)). Qed.
Lemma lem5404147 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5404148 (m : nat) : (term2 m) = (term2 m).
Proof. exact (MK_COMB (@lem5404147) (@lem5404146 m)). Qed.
Lemma lem5404153 (m : nat) : (term3 m) = (term3 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem5404155 (m : nat) : (term4 m) = (term4 m).
Proof. exact (MK_COMB (@lem5404153 m) (@lem5404148 m)). Qed.
Lemma lem5404158 (m : nat) : (term5 m) = (m = (NUMERAL 0)).
Proof. exact (@lem16933 (m = (NUMERAL 0))). Qed.
Lemma lem5404165 (m : nat) (x : nat) : (term0 m x) = (term6 m x).
Proof. exact (@lem17045 (Peano.le m x) (term7 x)). Qed.
Lemma lem5404166 (m : nat) : (term1 m) = (term8 m).
Proof. exact (fun_ext (fun x : nat => @lem5404165 m x)). Qed.
Lemma lem5404167 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5404168 (m : nat) : (term2 m) = (term9 m).
Proof. exact (MK_COMB (@lem5404167) (@lem5404166 m)). Qed.
Lemma lem5404169 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5404170 (m : nat) : (term10 m) = (term11 m).
Proof. exact (MK_COMB (@lem5404169) (@lem5404158 m)). Qed.
Lemma lem5404171 (m : nat) : (term12 m) = (term13 m).
Proof. exact (MK_COMB (@lem5404170 m) (@lem5404168 m)). Qed.
Lemma lem5404172 (m : nat) : (term4 m) = (term12 m).
Proof. exact (@lem17265 (term14 m) (term2 m)). Qed.
Lemma lem5404173 (m : nat) : (term4 m) = (term13 m).
Proof. exact (TRANS (@lem5404172 m) (@lem5404171 m)). Qed.
Lemma lem5404174 (m : nat) : (term4 m) = (term13 m).
Proof. exact (TRANS (@lem5404155 m) (@lem5404173 m)). Qed.
Lemma lem5404175 (m : nat) (x : nat) : (term6 m x) = (term6 m x).
Proof. exact (eq_refl (term6 m x)). Qed.
Lemma lem5404176 (m : nat) : (term8 m) = (term8 m).
Proof. exact (fun_ext (fun x : nat => @lem5404175 m x)). Qed.
Lemma lem5404177 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5404178 (m : nat) : (term9 m) = (term9 m).
Proof. exact (MK_COMB (@lem5404177) (@lem5404176 m)). Qed.
Lemma lem5404181 (m : nat) : (term11 m) = (term11 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem5404182 (m : nat) : (term13 m) = (term13 m).
Proof. exact (MK_COMB (@lem5404181 m) (@lem5404178 m)). Qed.
Lemma lem5404199 (m : nat) : (term4 m) = (term13 m).
Proof. exact (TRANS (@lem5404174 m) (@lem5404182 m)). Qed.
Lemma lem5404216 (m : nat) (x : nat) : (term6 m x) = (term6 m x).
Proof. exact (eq_refl (term6 m x)). Qed.
Lemma lem5404217 (m : nat) : (term8 m) = (term8 m).
Proof. exact (fun_ext (fun x : nat => @lem5404216 m x)). Qed.
Lemma lem5404218 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5404219 (m : nat) : (term9 m) = (term9 m).
Proof. exact (MK_COMB (@lem5404218) (@lem5404217 m)). Qed.
Lemma lem5404226 (m : nat) : (term11 m) = (term11 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem5404227 (m : nat) : (term13 m) = (term13 m).
Proof. exact (MK_COMB (@lem5404226 m) (@lem5404219 m)). Qed.
Lemma lem5404228 (m : nat) : (term4 m) = (term13 m).
Proof. exact (TRANS (@lem5404199 m) (@lem5404227 m)). Qed.
Lemma lem5404230 {A : Type'} (P : Prop) (Q : A -> Prop) : (term15 A P Q) = (term16 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5404231 (P : Prop) (Q : nat -> Prop) : (term17 P Q) = (term18 P Q).
Proof. exact (@lem5404230 nat P Q). Qed.
Lemma lem5404232 (m : nat) : (term19 m) = (term20 m).
Proof. exact (@lem5404231 (m = (NUMERAL 0)) (term8 m)). Qed.
Lemma lem5404233 (m : nat) (x : nat) : (term21 m x) = (term6 m x).
Proof. exact (eq_refl (term21 m x)). Qed.
Lemma lem5404234 (m : nat) : (term22 m) = (term8 m).
Proof. exact (fun_ext (fun x : nat => @lem5404233 m x)). Qed.
Lemma lem5404235 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5404236 (m : nat) : (term23 m) = (term9 m).
Proof. exact (MK_COMB (@lem5404235) (@lem5404234 m)). Qed.
Lemma lem5404237 (m : nat) : (term11 m) = (term11 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem5404238 (m : nat) : (term19 m) = (term13 m).
Proof. exact (MK_COMB (@lem5404237 m) (@lem5404236 m)). Qed.
Lemma lem5404239 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5404240 (m : nat) : (term24 m) = (term25 m).
Proof. exact (MK_COMB (@lem5404239) (@lem5404238 m)). Qed.
Lemma lem5404241 (m : nat) (x : nat) : (term21 m x) = (term6 m x).
Proof. exact (eq_refl (term21 m x)). Qed.
Lemma lem5404242 (m : nat) : (term11 m) = (term11 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem5404243 (m : nat) (x : nat) : (term26 m x) = (term27 m x).
Proof. exact (MK_COMB (@lem5404242 m) (@lem5404241 m x)). Qed.
Lemma lem5404244 (m : nat) : (term28 m) = (term29 m).
Proof. exact (fun_ext (fun x : nat => @lem5404243 m x)). Qed.
Lemma lem5404245 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5404246 (m : nat) : (term20 m) = (term30 m).
Proof. exact (MK_COMB (@lem5404245) (@lem5404244 m)). Qed.
Lemma lem5404247 (m : nat) : ((term19 m) = (term20 m)) = ((term13 m) = (term30 m)).
Proof. exact (MK_COMB (@lem5404240 m) (@lem5404246 m)). Qed.
Lemma lem5404248 (m : nat) : (term13 m) = (term30 m).
Proof. exact (EQ_MP (@lem5404247 m) (@lem5404232 m)). Qed.
Lemma lem5404249 (m : nat) : (term4 m) = (term30 m).
Proof. exact (TRANS (@lem5404228 m) (@lem5404248 m)). Qed.
Lemma lem5404251 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem5404252 (m : nat) : (m = (NUMERAL 0)) = ((int_of_num m) = term31).
Proof. exact (@lem5404251 m (NUMERAL 0)). Qed.
Lemma lem5404255 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5404256 (m : nat) : (term11 m) = (term32 m).
Proof. exact (MK_COMB (@lem5404255) (@lem5404252 m)). Qed.
Lemma lem5404258 (m : nat) (n : nat) : (Peano.le m n) = (term33 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5404259 (m : nat) (x : nat) : (Peano.le m x) = (term33 m x).
Proof. exact (@lem5404258 m x). Qed.
Lemma lem5404260 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5404261 (m : nat) (x : nat) : (term34 m x) = (term35 m x).
Proof. exact (MK_COMB (@lem5404260) (@lem5404259 m x)). Qed.
Lemma lem5404262 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5404263 (m : nat) (x : nat) : (term36 m x) = (term37 m x).
Proof. exact (MK_COMB (@lem5404262) (@lem5404261 m x)). Qed.
Lemma lem5404265 (m : nat) (n : nat) : (Peano.le m n) = (term33 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5404266 (x : nat) : (term7 x) = (term38 x).
Proof. exact (@lem5404265 x (NUMERAL 0)). Qed.
Lemma lem5404267 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5404268 (x : nat) : (term39 x) = (term40 x).
Proof. exact (MK_COMB (@lem5404267) (@lem5404266 x)). Qed.
Lemma lem5404269 (m : nat) (x : nat) : (term6 m x) = (term41 m x).
Proof. exact (MK_COMB (@lem5404263 m x) (@lem5404268 x)). Qed.
Lemma lem5404270 (m : nat) (x : nat) : (term27 m x) = (term42 m x).
Proof. exact (MK_COMB (@lem5404256 m) (@lem5404269 m x)). Qed.
Lemma lem5404271 (m : nat) : (term29 m) = (term43 m).
Proof. exact (fun_ext (fun x : nat => @lem5404270 m x)). Qed.
Lemma lem5404272 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5404273 (m : nat) : (term30 m) = (term44 m).
Proof. exact (MK_COMB (@lem5404272) (@lem5404271 m)). Qed.
Lemma lem5404274 (m : nat) : (term4 m) = (term44 m).
Proof. exact (TRANS (@lem5404249 m) (@lem5404273 m)). Qed.
Lemma lem5404275 (m : nat) : term45 m.
Proof. exact (@lem2307535 m). Qed.
Lemma lem5404276 (m : nat) : (term45 m) = (term46 m).
Proof. exact (eq_refl (term45 m)). Qed.
Lemma lem5404277 (m : nat) : term46 m.
Proof. exact (EQ_MP (@lem5404276 m) (@lem5404275 m)). Qed.
Lemma lem5404278 (x : nat) : term45 x.
Proof. exact (@lem2307535 x). Qed.
Lemma lem5404279 (x : nat) : (term45 x) = (term46 x).
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem5404280 (x : nat) : term46 x.
Proof. exact (EQ_MP (@lem5404279 x) (@lem5404278 x)). Qed.
Lemma lem5404281 (_69899 : int) (_69900 : int) : (term47 _69899 _69900) = (term48 _69899 _69900).
Proof. exact (@lem2318604 (term48 _69899 _69900)). Qed.
Lemma lem5404300 (_69899 : int) (_69900 : int) : (term49 _69899 _69900) = (int_le _69899 _69900).
Proof. exact (@lem16933 (int_le _69899 _69900)). Qed.
Lemma lem5404303 (_69900 : int) : (term50 _69900) = (term51 _69900).
Proof. exact (@lem16933 (term51 _69900)). Qed.
Lemma lem5404304 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5404305 (_69899 : int) (_69900 : int) : (term52 _69899 _69900) = (term53 _69899 _69900).
Proof. exact (MK_COMB (@lem5404304) (@lem5404300 _69899 _69900)). Qed.
Lemma lem5404306 (_69899 : int) (_69900 : int) : (term54 _69899 _69900) = (term55 _69899 _69900).
Proof. exact (MK_COMB (@lem5404305 _69899 _69900) (@lem5404303 _69900)). Qed.
Lemma lem5404307 (_69899 : int) (_69900 : int) : (term56 _69899 _69900) = (term54 _69899 _69900).
Proof. exact (@lem17160 (term57 _69899 _69900) (term58 _69900)). Qed.
Lemma lem5404308 (_69899 : int) (_69900 : int) : (term56 _69899 _69900) = (term55 _69899 _69900).
Proof. exact (TRANS (@lem5404307 _69899 _69900) (@lem5404306 _69899 _69900)). Qed.
Lemma lem5404310 (_69899 : int) : (term59 _69899) = (term59 _69899).
Proof. exact (eq_refl (term59 _69899)). Qed.
Lemma lem5404311 (_69899 : int) (_69900 : int) : (term60 _69899 _69900) = (term61 _69899 _69900).
Proof. exact (MK_COMB (@lem5404310 _69899) (@lem5404308 _69899 _69900)). Qed.
Lemma lem5404312 (_69899 : int) (_69900 : int) : (term62 _69899 _69900) = (term60 _69899 _69900).
Proof. exact (@lem17160 (_69899 = term31) (term63 _69899 _69900)). Qed.
Lemma lem5404313 (_69899 : int) (_69900 : int) : (term62 _69899 _69900) = (term61 _69899 _69900).
Proof. exact (TRANS (@lem5404312 _69899 _69900) (@lem5404311 _69899 _69900)). Qed.
Lemma lem5404315 (_69900 : int) : (term64 _69900) = (term64 _69900).
Proof. exact (eq_refl (term64 _69900)). Qed.
Lemma lem5404316 (_69899 : int) (_69900 : int) : (term65 _69899 _69900) = (term66 _69899 _69900).
Proof. exact (MK_COMB (@lem5404315 _69900) (@lem5404313 _69899 _69900)). Qed.
Lemma lem5404317 (_69899 : int) (_69900 : int) : (term67 _69899 _69900) = (term65 _69899 _69900).
Proof. exact (@lem17362 (term68 _69900) (term69 _69899 _69900)). Qed.
Lemma lem5404318 (_69899 : int) (_69900 : int) : (term67 _69899 _69900) = (term66 _69899 _69900).
Proof. exact (TRANS (@lem5404317 _69899 _69900) (@lem5404316 _69899 _69900)). Qed.
Lemma lem5404320 (_69899 : int) : (term64 _69899) = (term64 _69899).
Proof. exact (eq_refl (term64 _69899)). Qed.
Lemma lem5404321 (_69899 : int) (_69900 : int) : (term70 _69899 _69900) = (term71 _69899 _69900).
Proof. exact (MK_COMB (@lem5404320 _69899) (@lem5404318 _69899 _69900)). Qed.
Lemma lem5404322 (_69899 : int) (_69900 : int) : (term72 _69899 _69900) = (term70 _69899 _69900).
Proof. exact (@lem17362 (term68 _69899) (term73 _69899 _69900)). Qed.
Lemma lem5404344 (_69899 : int) (_69900 : int) : (term72 _69899 _69900) = (term71 _69899 _69900).
Proof. exact (TRANS (@lem5404322 _69899 _69900) (@lem5404321 _69899 _69900)). Qed.
Lemma lem5404347 (x : int) (y : int) : (int_le x y) = (term74 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5404348 (_69899 : int) : (term68 _69899) = (term75 _69899).
Proof. exact (@lem5404347 term31 _69899). Qed.
Lemma lem5404350 (n : nat) : (term76 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5404351 : term77 = term78.
Proof. exact (@lem5404350 (NUMERAL 0)). Qed.
Lemma lem5404352 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5404353 : term79 = term80.
Proof. exact (MK_COMB (@lem5404352) (@lem5404351)). Qed.
Lemma lem5404354 (_69899 : int) : (real_of_int _69899) = (real_of_int _69899).
Proof. exact (eq_refl (real_of_int _69899)). Qed.
Lemma lem5404355 (_69899 : int) : (term75 _69899) = (term81 _69899).
Proof. exact (MK_COMB (@lem5404353) (@lem5404354 _69899)). Qed.
Lemma lem5404357 (_69899 : int) : (term68 _69899) = (term81 _69899).
Proof. exact (TRANS (@lem5404348 _69899) (@lem5404355 _69899)). Qed.
Lemma lem5404360 (x : int) (y : int) : (int_le x y) = (term74 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5404361 (_69900 : int) : (term68 _69900) = (term75 _69900).
Proof. exact (@lem5404360 term31 _69900). Qed.
Lemma lem5404363 (n : nat) : (term76 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5404364 : term77 = term78.
Proof. exact (@lem5404363 (NUMERAL 0)). Qed.
Lemma lem5404365 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5404366 : term79 = term80.
Proof. exact (MK_COMB (@lem5404365) (@lem5404364)). Qed.
Lemma lem5404367 (_69900 : int) : (real_of_int _69900) = (real_of_int _69900).
Proof. exact (eq_refl (real_of_int _69900)). Qed.
Lemma lem5404368 (_69900 : int) : (term75 _69900) = (term81 _69900).
Proof. exact (MK_COMB (@lem5404366) (@lem5404367 _69900)). Qed.
Lemma lem5404370 (_69900 : int) : (term68 _69900) = (term81 _69900).
Proof. exact (TRANS (@lem5404361 _69900) (@lem5404368 _69900)). Qed.
Lemma lem5404372 (y : int) (x : int) : (term82 x y) = (term83 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem5404373 (_69899 : int) : (term84 _69899) = (term85 _69899).
Proof. exact (@lem5404372 term31 _69899). Qed.
Lemma lem5404375 (x : int) (y : int) : (int_le x y) = (term74 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5404376 (_69899 : int) : (term86 _69899) = (term87 _69899).
Proof. exact (@lem5404375 (term88 _69899) term31). Qed.
Lemma lem5404378 (x : int) (y : int) : (term89 x y) = (term90 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5404379 (_69899 : int) : (term91 _69899) = (term92 _69899).
Proof. exact (@lem5404378 _69899 term93). Qed.
Lemma lem5404381 (n : nat) : (term76 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5404382 : term94 = term95.
Proof. exact (@lem5404381 term96). Qed.
Lemma lem5404383 (_69899 : int) : (term97 _69899) = (term97 _69899).
Proof. exact (eq_refl (term97 _69899)). Qed.
Lemma lem5404384 (_69899 : int) : (term92 _69899) = (term98 _69899).
Proof. exact (MK_COMB (@lem5404383 _69899) (@lem5404382)). Qed.
Lemma lem5404385 (_69899 : int) : (term91 _69899) = (term98 _69899).
Proof. exact (TRANS (@lem5404379 _69899) (@lem5404384 _69899)). Qed.
Lemma lem5404386 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5404387 (_69899 : int) : (term99 _69899) = (term100 _69899).
Proof. exact (MK_COMB (@lem5404386) (@lem5404385 _69899)). Qed.
Lemma lem5404389 (n : nat) : (term76 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5404390 : term77 = term78.
Proof. exact (@lem5404389 (NUMERAL 0)). Qed.
Lemma lem5404391 (_69899 : int) : (term87 _69899) = (term101 _69899).
Proof. exact (MK_COMB (@lem5404387 _69899) (@lem5404390)). Qed.
Lemma lem5404392 (_69899 : int) : (term86 _69899) = (term101 _69899).
Proof. exact (TRANS (@lem5404376 _69899) (@lem5404391 _69899)). Qed.
Lemma lem5404393 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5404394 (_69899 : int) : (term102 _69899) = (term103 _69899).
Proof. exact (MK_COMB (@lem5404393) (@lem5404392 _69899)). Qed.
Lemma lem5404396 (x : int) (y : int) : (int_le x y) = (term74 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5404397 (_69899 : int) : (term104 _69899) = (term105 _69899).
Proof. exact (@lem5404396 term106 _69899). Qed.
Lemma lem5404399 (x : int) (y : int) : (term89 x y) = (term90 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5404400 : term107 = term108.
Proof. exact (@lem5404399 term31 term93). Qed.
Lemma lem5404402 (n : nat) : (term76 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5404403 : term77 = term78.
Proof. exact (@lem5404402 (NUMERAL 0)). Qed.
Lemma lem5404404 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5404405 : term109 = term110.
Proof. exact (MK_COMB (@lem5404404) (@lem5404403)). Qed.
Lemma lem5404407 (n : nat) : (term76 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5404408 : term94 = term95.
Proof. exact (@lem5404407 term96). Qed.
Lemma lem5404409 : term108 = term111.
Proof. exact (MK_COMB (@lem5404405) (@lem5404408)). Qed.
Lemma lem5404410 : term107 = term111.
Proof. exact (TRANS (@lem5404400) (@lem5404409)). Qed.
Lemma lem5404411 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5404412 : term112 = term113.
Proof. exact (MK_COMB (@lem5404411) (@lem5404410)). Qed.
Lemma lem5404413 (_69899 : int) : (real_of_int _69899) = (real_of_int _69899).
Proof. exact (eq_refl (real_of_int _69899)). Qed.
Lemma lem5404414 (_69899 : int) : (term105 _69899) = (term114 _69899).
Proof. exact (MK_COMB (@lem5404412) (@lem5404413 _69899)). Qed.
Lemma lem5404415 (_69899 : int) : (term104 _69899) = (term114 _69899).
Proof. exact (TRANS (@lem5404397 _69899) (@lem5404414 _69899)). Qed.
Lemma lem5404416 (_69899 : int) : (term85 _69899) = (term115 _69899).
Proof. exact (MK_COMB (@lem5404394 _69899) (@lem5404415 _69899)). Qed.
Lemma lem5404417 (_69899 : int) : (term84 _69899) = (term115 _69899).
Proof. exact (TRANS (@lem5404373 _69899) (@lem5404416 _69899)). Qed.
Lemma lem5404420 (x : int) (y : int) : (int_le x y) = (term74 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5404422 (_69899 : int) (_69900 : int) : (int_le _69899 _69900) = (term74 _69899 _69900).
Proof. exact (@lem5404420 _69899 _69900). Qed.
Lemma lem5404425 (x : int) (y : int) : (int_le x y) = (term74 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5404426 (_69900 : int) : (term51 _69900) = (term116 _69900).
Proof. exact (@lem5404425 _69900 term31). Qed.
Lemma lem5404428 (n : nat) : (term76 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5404429 : term77 = term78.
Proof. exact (@lem5404428 (NUMERAL 0)). Qed.
Lemma lem5404430 (_69900 : int) : (term117 _69900) = (term117 _69900).
Proof. exact (eq_refl (term117 _69900)). Qed.
Lemma lem5404431 (_69900 : int) : (term116 _69900) = (term118 _69900).
Proof. exact (MK_COMB (@lem5404430 _69900) (@lem5404429)). Qed.
Lemma lem5404433 (_69900 : int) : (term51 _69900) = (term118 _69900).
Proof. exact (TRANS (@lem5404426 _69900) (@lem5404431 _69900)). Qed.
Lemma lem5404434 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5404435 (_69899 : int) (_69900 : int) : (term53 _69899 _69900) = (term119 _69899 _69900).
Proof. exact (MK_COMB (@lem5404434) (@lem5404422 _69899 _69900)). Qed.
Lemma lem5404436 (_69899 : int) (_69900 : int) : (term55 _69899 _69900) = (term120 _69899 _69900).
Proof. exact (MK_COMB (@lem5404435 _69899 _69900) (@lem5404433 _69900)). Qed.
Lemma lem5404437 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5404438 (_69899 : int) : (term59 _69899) = (term121 _69899).
Proof. exact (MK_COMB (@lem5404437) (@lem5404417 _69899)). Qed.
Lemma lem5404439 (_69899 : int) (_69900 : int) : (term61 _69899 _69900) = (term122 _69899 _69900).
Proof. exact (MK_COMB (@lem5404438 _69899) (@lem5404436 _69899 _69900)). Qed.
Lemma lem5404440 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5404441 (_69900 : int) : (term64 _69900) = (term123 _69900).
Proof. exact (MK_COMB (@lem5404440) (@lem5404370 _69900)). Qed.
Lemma lem5404442 (_69899 : int) (_69900 : int) : (term66 _69899 _69900) = (term124 _69899 _69900).
Proof. exact (MK_COMB (@lem5404441 _69900) (@lem5404439 _69899 _69900)). Qed.
Lemma lem5404443 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5404444 (_69899 : int) : (term64 _69899) = (term123 _69899).
Proof. exact (MK_COMB (@lem5404443) (@lem5404357 _69899)). Qed.
Lemma lem5404445 (_69899 : int) (_69900 : int) : (term71 _69899 _69900) = (term125 _69899 _69900).
Proof. exact (MK_COMB (@lem5404444 _69899) (@lem5404442 _69899 _69900)). Qed.
Lemma lem5404446 (_69899 : int) (_69900 : int) : (term72 _69899 _69900) = (term125 _69899 _69900).
Proof. exact (TRANS (@lem5404344 _69899 _69900) (@lem5404445 _69899 _69900)). Qed.
Lemma lem5404450 (t : Prop) : (term126 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5404506 (_69899 : int) (_69900 : int) : (term127 _69899 _69900) = (term125 _69899 _69900).
Proof. exact (@lem5404450 (term125 _69899 _69900)). Qed.
Lemma lem5404507 (_69899 : int) : (term81 _69899) = (term128 _69899).
Proof. exact (@lem1988287 (real_of_int _69899) term78). Qed.
Lemma lem5404513 (_69899 : int) : (term129 _69899) = (term130 _69899).
Proof. exact (@lem1982792 (real_of_int _69899) term78). Qed.
Lemma lem5404515 (x : nat) : (real_of_num x) = (term131 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5404516 : term78 = term132.
Proof. exact (@lem5404515 (NUMERAL 0)). Qed.
Lemma lem5404518 (x : nat) : (term133 x) = (term134 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5404519 : term135 = term136.
Proof. exact (@lem5404518 term96). Qed.
Lemma lem5404520 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5404521 : term137 = term138.
Proof. exact (MK_COMB (@lem5404520) (@lem5404519)). Qed.
Lemma lem5404522 : term139 = term140.
Proof. exact (MK_COMB (@lem5404521) (@lem5404516)). Qed.
Lemma lem5404523 : term140 = term141.
Proof. exact (@lem1981613 term135 term78 term95 term95). Qed.
Lemma lem5404525 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5404526 : term144 = term145.
Proof. exact (@lem5404525 term96 term96). Qed.
Lemma lem5404527 : (term146 = (BIT1 0)) = (term147 = term96).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5404528 : term147 = term96.
Proof. exact (EQ_MP (@lem5404527) (@lem940073)). Qed.
Lemma lem5404529 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5404530 : term145 = term95.
Proof. exact (MK_COMB (@lem5404529) (@lem5404528)). Qed.
Lemma lem5404531 : term144 = term95.
Proof. exact (TRANS (@lem5404526) (@lem5404530)). Qed.
Lemma lem5404533 (x : nat) : (term148 x) = term78.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5404534 : term139 = term78.
Proof. exact (@lem5404533 term96). Qed.
Lemma lem5404535 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5404536 : term149 = term150.
Proof. exact (MK_COMB (@lem5404535) (@lem5404534)). Qed.
Lemma lem5404537 : term141 = term132.
Proof. exact (MK_COMB (@lem5404536) (@lem5404531)). Qed.
Lemma lem5404538 : term140 = term132.
Proof. exact (TRANS (@lem5404523) (@lem5404537)). Qed.
Lemma lem5404539 : term139 = term132.
Proof. exact (TRANS (@lem5404522) (@lem5404538)). Qed.
Lemma lem5404541 (x : real) : (term151 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5404542 : term132 = term78.
Proof. exact (@lem5404541 term78). Qed.
Lemma lem5404543 : term139 = term78.
Proof. exact (TRANS (@lem5404539) (@lem5404542)). Qed.
Lemma lem5404544 (_69899 : int) : (term97 _69899) = (term97 _69899).
Proof. exact (eq_refl (term97 _69899)). Qed.
Lemma lem5404545 (_69899 : int) : (term130 _69899) = (term152 _69899).
Proof. exact (MK_COMB (@lem5404544 _69899) (@lem5404543)). Qed.
Lemma lem5404546 (_69899 : int) : (term152 _69899) = (real_of_int _69899).
Proof. exact (@lem1982723 (real_of_int _69899)). Qed.
Lemma lem5404547 (_69899 : int) : (term130 _69899) = (real_of_int _69899).
Proof. exact (TRANS (@lem5404545 _69899) (@lem5404546 _69899)). Qed.
Lemma lem5404549 (_69899 : int) : (term129 _69899) = (real_of_int _69899).
Proof. exact (TRANS (@lem5404513 _69899) (@lem5404547 _69899)). Qed.
Lemma lem5404550 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5404551 (_69899 : int) : (term153 _69899) = (term154 _69899).
Proof. exact (MK_COMB (@lem5404550) (@lem5404549 _69899)). Qed.
Lemma lem5404552 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem5404553 (_69899 : int) : (term128 _69899) = (term155 _69899).
Proof. exact (MK_COMB (@lem5404551 _69899) (@lem5404552)). Qed.
Lemma lem5404554 (_69899 : int) : (term81 _69899) = (term155 _69899).
Proof. exact (TRANS (@lem5404507 _69899) (@lem5404553 _69899)). Qed.
Lemma lem5404555 (_69900 : int) : (term81 _69900) = (term128 _69900).
Proof. exact (@lem1988287 (real_of_int _69900) term78). Qed.
Lemma lem5404561 (_69900 : int) : (term129 _69900) = (term130 _69900).
Proof. exact (@lem1982792 (real_of_int _69900) term78). Qed.
Lemma lem5404563 (x : nat) : (real_of_num x) = (term131 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5404564 : term78 = term132.
Proof. exact (@lem5404563 (NUMERAL 0)). Qed.
Lemma lem5404566 (x : nat) : (term133 x) = (term134 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5404567 : term135 = term136.
Proof. exact (@lem5404566 term96). Qed.
Lemma lem5404568 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5404569 : term137 = term138.
Proof. exact (MK_COMB (@lem5404568) (@lem5404567)). Qed.
Lemma lem5404570 : term139 = term140.
Proof. exact (MK_COMB (@lem5404569) (@lem5404564)). Qed.
Lemma lem5404571 : term140 = term141.
Proof. exact (@lem1981613 term135 term78 term95 term95). Qed.
Lemma lem5404573 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5404574 : term144 = term145.
Proof. exact (@lem5404573 term96 term96). Qed.
Lemma lem5404575 : (term146 = (BIT1 0)) = (term147 = term96).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5404576 : term147 = term96.
Proof. exact (EQ_MP (@lem5404575) (@lem940073)). Qed.
Lemma lem5404577 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5404578 : term145 = term95.
Proof. exact (MK_COMB (@lem5404577) (@lem5404576)). Qed.
Lemma lem5404579 : term144 = term95.
Proof. exact (TRANS (@lem5404574) (@lem5404578)). Qed.
Lemma lem5404581 (x : nat) : (term148 x) = term78.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5404582 : term139 = term78.
Proof. exact (@lem5404581 term96). Qed.
Lemma lem5404583 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5404584 : term149 = term150.
Proof. exact (MK_COMB (@lem5404583) (@lem5404582)). Qed.
Lemma lem5404585 : term141 = term132.
Proof. exact (MK_COMB (@lem5404584) (@lem5404579)). Qed.
Lemma lem5404586 : term140 = term132.
Proof. exact (TRANS (@lem5404571) (@lem5404585)). Qed.
Lemma lem5404587 : term139 = term132.
Proof. exact (TRANS (@lem5404570) (@lem5404586)). Qed.
Lemma lem5404589 (x : real) : (term151 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5404590 : term132 = term78.
Proof. exact (@lem5404589 term78). Qed.
Lemma lem5404591 : term139 = term78.
Proof. exact (TRANS (@lem5404587) (@lem5404590)). Qed.
Lemma lem5404592 (_69900 : int) : (term97 _69900) = (term97 _69900).
Proof. exact (eq_refl (term97 _69900)). Qed.
Lemma lem5404593 (_69900 : int) : (term130 _69900) = (term152 _69900).
Proof. exact (MK_COMB (@lem5404592 _69900) (@lem5404591)). Qed.
Lemma lem5404594 (_69900 : int) : (term152 _69900) = (real_of_int _69900).
Proof. exact (@lem1982723 (real_of_int _69900)). Qed.
Lemma lem5404595 (_69900 : int) : (term130 _69900) = (real_of_int _69900).
Proof. exact (TRANS (@lem5404593 _69900) (@lem5404594 _69900)). Qed.
Lemma lem5404597 (_69900 : int) : (term129 _69900) = (real_of_int _69900).
Proof. exact (TRANS (@lem5404561 _69900) (@lem5404595 _69900)). Qed.
Lemma lem5404598 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5404599 (_69900 : int) : (term153 _69900) = (term154 _69900).
Proof. exact (MK_COMB (@lem5404598) (@lem5404597 _69900)). Qed.
Lemma lem5404600 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem5404601 (_69900 : int) : (term128 _69900) = (term155 _69900).
Proof. exact (MK_COMB (@lem5404599 _69900) (@lem5404600)). Qed.
Lemma lem5404602 (_69900 : int) : (term81 _69900) = (term155 _69900).
Proof. exact (TRANS (@lem5404555 _69900) (@lem5404601 _69900)). Qed.
Lemma lem5404603 (_69899 : int) : (term101 _69899) = (term156 _69899).
Proof. exact (@lem1988287 term78 (term98 _69899)). Qed.
Lemma lem5404615 (_69899 : int) : (term157 _69899) = (term158 _69899).
Proof. exact (@lem1982792 term78 (term98 _69899)). Qed.
Lemma lem5404616 (_69899 : int) : (term159 _69899) = (term160 _69899).
Proof. exact (@lem1982781 (real_of_int _69899) term135 term95). Qed.
Lemma lem5404618 (x : nat) : (real_of_num x) = (term131 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5404619 : term95 = term161.
Proof. exact (@lem5404618 term96). Qed.
Lemma lem5404621 (x : nat) : (term133 x) = (term134 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5404622 : term135 = term136.
Proof. exact (@lem5404621 term96). Qed.
Lemma lem5404623 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5404624 : term137 = term138.
Proof. exact (MK_COMB (@lem5404623) (@lem5404622)). Qed.
Lemma lem5404625 : term162 = term163.
Proof. exact (MK_COMB (@lem5404624) (@lem5404619)). Qed.
Lemma lem5404626 : term163 = term164.
Proof. exact (@lem1981613 term135 term95 term95 term95). Qed.
Lemma lem5404628 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5404629 : term144 = term145.
Proof. exact (@lem5404628 term96 term96). Qed.
Lemma lem5404630 : (term146 = (BIT1 0)) = (term147 = term96).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5404631 : term147 = term96.
Proof. exact (EQ_MP (@lem5404630) (@lem940073)). Qed.
Lemma lem5404632 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5404633 : term145 = term95.
Proof. exact (MK_COMB (@lem5404632) (@lem5404631)). Qed.
Lemma lem5404634 : term144 = term95.
Proof. exact (TRANS (@lem5404629) (@lem5404633)). Qed.
Lemma lem5404636 (m : nat) (n : nat) : (term165 m n) = (term166 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5404637 : term162 = term167.
Proof. exact (@lem5404636 term96 term96). Qed.
Lemma lem5404638 : (term146 = (BIT1 0)) = (term147 = term96).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5404639 : term147 = term96.
Proof. exact (EQ_MP (@lem5404638) (@lem940073)). Qed.
Lemma lem5404640 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5404641 : term145 = term95.
Proof. exact (MK_COMB (@lem5404640) (@lem5404639)). Qed.
Lemma lem5404642 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5404643 : term167 = term135.
Proof. exact (MK_COMB (@lem5404642) (@lem5404641)). Qed.
Lemma lem5404644 : term162 = term135.
Proof. exact (TRANS (@lem5404637) (@lem5404643)). Qed.
Lemma lem5404645 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5404646 : term168 = term169.
Proof. exact (MK_COMB (@lem5404645) (@lem5404644)). Qed.
Lemma lem5404647 : term164 = term136.
Proof. exact (MK_COMB (@lem5404646) (@lem5404634)). Qed.
Lemma lem5404648 : term163 = term136.
Proof. exact (TRANS (@lem5404626) (@lem5404647)). Qed.
Lemma lem5404649 : term162 = term136.
Proof. exact (TRANS (@lem5404625) (@lem5404648)). Qed.
Lemma lem5404651 (x : real) : (term151 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5404652 : term136 = term135.
Proof. exact (@lem5404651 term135). Qed.
Lemma lem5404653 : term162 = term135.
Proof. exact (TRANS (@lem5404649) (@lem5404652)). Qed.
Lemma lem5404656 (_69899 : int) : (term170 _69899) = (term170 _69899).
Proof. exact (eq_refl (term170 _69899)). Qed.
Lemma lem5404657 (_69899 : int) : (term160 _69899) = (term171 _69899).
Proof. exact (MK_COMB (@lem5404656 _69899) (@lem5404653)). Qed.
Lemma lem5404658 (_69899 : int) : (term159 _69899) = (term171 _69899).
Proof. exact (TRANS (@lem5404616 _69899) (@lem5404657 _69899)). Qed.
Lemma lem5404659 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem5404660 (_69899 : int) : (term158 _69899) = (term172 _69899).
Proof. exact (MK_COMB (@lem5404659) (@lem5404658 _69899)). Qed.
Lemma lem5404661 (_69899 : int) : (term172 _69899) = (term171 _69899).
Proof. exact (@lem1982721 (term171 _69899)). Qed.
Lemma lem5404662 (_69899 : int) : (term158 _69899) = (term171 _69899).
Proof. exact (TRANS (@lem5404660 _69899) (@lem5404661 _69899)). Qed.
Lemma lem5404664 (_69899 : int) : (term157 _69899) = (term171 _69899).
Proof. exact (TRANS (@lem5404615 _69899) (@lem5404662 _69899)). Qed.
Lemma lem5404665 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5404666 (_69899 : int) : (term173 _69899) = (term174 _69899).
Proof. exact (MK_COMB (@lem5404665) (@lem5404664 _69899)). Qed.
Lemma lem5404667 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem5404668 (_69899 : int) : (term156 _69899) = (term175 _69899).
Proof. exact (MK_COMB (@lem5404666 _69899) (@lem5404667)). Qed.
Lemma lem5404669 (_69899 : int) : (term101 _69899) = (term175 _69899).
Proof. exact (TRANS (@lem5404603 _69899) (@lem5404668 _69899)). Qed.
Lemma lem5404670 (_69899 : int) : (term114 _69899) = (term176 _69899).
Proof. exact (@lem1988287 (real_of_int _69899) term111). Qed.
Lemma lem5404677 : term111 = term95.
Proof. exact (@lem1982721 term95). Qed.
Lemma lem5404680 (_69899 : int) : (term177 _69899) = (term177 _69899).
Proof. exact (eq_refl (term177 _69899)). Qed.
Lemma lem5404681 (_69899 : int) : (term178 _69899) = (term179 _69899).
Proof. exact (MK_COMB (@lem5404680 _69899) (@lem5404677)). Qed.
Lemma lem5404682 (_69899 : int) : (term179 _69899) = (term180 _69899).
Proof. exact (@lem1982792 (real_of_int _69899) term95). Qed.
Lemma lem5404684 (x : nat) : (real_of_num x) = (term131 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5404685 : term95 = term161.
Proof. exact (@lem5404684 term96). Qed.
Lemma lem5404687 (x : nat) : (term133 x) = (term134 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5404688 : term135 = term136.
Proof. exact (@lem5404687 term96). Qed.
Lemma lem5404689 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5404690 : term137 = term138.
Proof. exact (MK_COMB (@lem5404689) (@lem5404688)). Qed.
Lemma lem5404691 : term162 = term163.
Proof. exact (MK_COMB (@lem5404690) (@lem5404685)). Qed.
Lemma lem5404692 : term163 = term164.
Proof. exact (@lem1981613 term135 term95 term95 term95). Qed.
Lemma lem5404694 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5404695 : term144 = term145.
Proof. exact (@lem5404694 term96 term96). Qed.
Lemma lem5404696 : (term146 = (BIT1 0)) = (term147 = term96).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5404697 : term147 = term96.
Proof. exact (EQ_MP (@lem5404696) (@lem940073)). Qed.
Lemma lem5404698 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5404699 : term145 = term95.
Proof. exact (MK_COMB (@lem5404698) (@lem5404697)). Qed.
Lemma lem5404700 : term144 = term95.
Proof. exact (TRANS (@lem5404695) (@lem5404699)). Qed.
Lemma lem5404702 (m : nat) (n : nat) : (term165 m n) = (term166 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5404703 : term162 = term167.
Proof. exact (@lem5404702 term96 term96). Qed.
Lemma lem5404704 : (term146 = (BIT1 0)) = (term147 = term96).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5404705 : term147 = term96.
Proof. exact (EQ_MP (@lem5404704) (@lem940073)). Qed.
Lemma lem5404706 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5404707 : term145 = term95.
Proof. exact (MK_COMB (@lem5404706) (@lem5404705)). Qed.
Lemma lem5404708 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5404709 : term167 = term135.
Proof. exact (MK_COMB (@lem5404708) (@lem5404707)). Qed.
Lemma lem5404710 : term162 = term135.
Proof. exact (TRANS (@lem5404703) (@lem5404709)). Qed.
Lemma lem5404711 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5404712 : term168 = term169.
Proof. exact (MK_COMB (@lem5404711) (@lem5404710)). Qed.
Lemma lem5404713 : term164 = term136.
Proof. exact (MK_COMB (@lem5404712) (@lem5404700)). Qed.
Lemma lem5404714 : term163 = term136.
Proof. exact (TRANS (@lem5404692) (@lem5404713)). Qed.
Lemma lem5404715 : term162 = term136.
Proof. exact (TRANS (@lem5404691) (@lem5404714)). Qed.
Lemma lem5404717 (x : real) : (term151 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5404718 : term136 = term135.
Proof. exact (@lem5404717 term135). Qed.
Lemma lem5404719 : term162 = term135.
Proof. exact (TRANS (@lem5404715) (@lem5404718)). Qed.
Lemma lem5404720 (_69899 : int) : (term97 _69899) = (term97 _69899).
Proof. exact (eq_refl (term97 _69899)). Qed.
Lemma lem5404723 (_69899 : int) : (term180 _69899) = (term181 _69899).
Proof. exact (MK_COMB (@lem5404720 _69899) (@lem5404719)). Qed.
Lemma lem5404724 (_69899 : int) : (term179 _69899) = (term181 _69899).
Proof. exact (TRANS (@lem5404682 _69899) (@lem5404723 _69899)). Qed.
Lemma lem5404725 (_69899 : int) : (term178 _69899) = (term181 _69899).
Proof. exact (TRANS (@lem5404681 _69899) (@lem5404724 _69899)). Qed.
Lemma lem5404726 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5404727 (_69899 : int) : (term182 _69899) = (term183 _69899).
Proof. exact (MK_COMB (@lem5404726) (@lem5404725 _69899)). Qed.
Lemma lem5404728 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem5404729 (_69899 : int) : (term176 _69899) = (term184 _69899).
Proof. exact (MK_COMB (@lem5404727 _69899) (@lem5404728)). Qed.
Lemma lem5404730 (_69899 : int) : (term114 _69899) = (term184 _69899).
Proof. exact (TRANS (@lem5404670 _69899) (@lem5404729 _69899)). Qed.
Lemma lem5404731 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5404732 (_69899 : int) : (term103 _69899) = (term185 _69899).
Proof. exact (MK_COMB (@lem5404731) (@lem5404669 _69899)). Qed.
Lemma lem5404733 (_69899 : int) : (term115 _69899) = (term186 _69899).
Proof. exact (MK_COMB (@lem5404732 _69899) (@lem5404730 _69899)). Qed.
Lemma lem5404734 (_69900 : int) (_69899 : int) : (term74 _69899 _69900) = (term187 _69900 _69899).
Proof. exact (@lem1988287 (real_of_int _69900) (real_of_int _69899)). Qed.
Lemma lem5404740 (_69900 : int) (_69899 : int) : (term188 _69900 _69899) = (term189 _69900 _69899).
Proof. exact (@lem1982792 (real_of_int _69900) (real_of_int _69899)). Qed.
Lemma lem5404745 (_69899 : int) (_69900 : int) : (term189 _69900 _69899) = (term190 _69899 _69900).
Proof. exact (@lem1982761 (term191 _69899) (real_of_int _69900)). Qed.
Lemma lem5404747 (_69899 : int) (_69900 : int) : (term188 _69900 _69899) = (term190 _69899 _69900).
Proof. exact (TRANS (@lem5404740 _69900 _69899) (@lem5404745 _69899 _69900)). Qed.
Lemma lem5404748 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5404749 (_69899 : int) (_69900 : int) : (term192 _69900 _69899) = (term193 _69899 _69900).
Proof. exact (MK_COMB (@lem5404748) (@lem5404747 _69899 _69900)). Qed.
Lemma lem5404750 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem5404751 (_69899 : int) (_69900 : int) : (term187 _69900 _69899) = (term194 _69899 _69900).
Proof. exact (MK_COMB (@lem5404749 _69899 _69900) (@lem5404750)). Qed.
Lemma lem5404752 (_69899 : int) (_69900 : int) : (term74 _69899 _69900) = (term194 _69899 _69900).
Proof. exact (TRANS (@lem5404734 _69900 _69899) (@lem5404751 _69899 _69900)). Qed.
Lemma lem5404753 (_69900 : int) : (term118 _69900) = (term195 _69900).
Proof. exact (@lem1988287 term78 (real_of_int _69900)). Qed.
Lemma lem5404759 (_69900 : int) : (term196 _69900) = (term197 _69900).
Proof. exact (@lem1982792 term78 (real_of_int _69900)). Qed.
Lemma lem5404764 (_69900 : int) : (term197 _69900) = (term191 _69900).
Proof. exact (@lem1982721 (term191 _69900)). Qed.
Lemma lem5404766 (_69900 : int) : (term196 _69900) = (term191 _69900).
Proof. exact (TRANS (@lem5404759 _69900) (@lem5404764 _69900)). Qed.
Lemma lem5404767 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5404768 (_69900 : int) : (term198 _69900) = (term199 _69900).
Proof. exact (MK_COMB (@lem5404767) (@lem5404766 _69900)). Qed.
Lemma lem5404769 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem5404770 (_69900 : int) : (term195 _69900) = (term200 _69900).
Proof. exact (MK_COMB (@lem5404768 _69900) (@lem5404769)). Qed.
Lemma lem5404771 (_69900 : int) : (term118 _69900) = (term200 _69900).
Proof. exact (TRANS (@lem5404753 _69900) (@lem5404770 _69900)). Qed.
Lemma lem5404772 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5404773 (_69899 : int) (_69900 : int) : (term119 _69899 _69900) = (term201 _69899 _69900).
Proof. exact (MK_COMB (@lem5404772) (@lem5404752 _69899 _69900)). Qed.
Lemma lem5404774 (_69899 : int) (_69900 : int) : (term120 _69899 _69900) = (term202 _69899 _69900).
Proof. exact (MK_COMB (@lem5404773 _69899 _69900) (@lem5404771 _69900)). Qed.
Lemma lem5404775 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5404776 (_69899 : int) : (term121 _69899) = (term203 _69899).
Proof. exact (MK_COMB (@lem5404775) (@lem5404733 _69899)). Qed.
Lemma lem5404777 (_69899 : int) (_69900 : int) : (term122 _69899 _69900) = (term204 _69899 _69900).
Proof. exact (MK_COMB (@lem5404776 _69899) (@lem5404774 _69899 _69900)). Qed.
Lemma lem5404778 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5404779 (_69900 : int) : (term123 _69900) = (term205 _69900).
Proof. exact (MK_COMB (@lem5404778) (@lem5404602 _69900)). Qed.
Lemma lem5404780 (_69899 : int) (_69900 : int) : (term124 _69899 _69900) = (term206 _69899 _69900).
Proof. exact (MK_COMB (@lem5404779 _69900) (@lem5404777 _69899 _69900)). Qed.
Lemma lem5404781 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5404782 (_69899 : int) : (term123 _69899) = (term205 _69899).
Proof. exact (MK_COMB (@lem5404781) (@lem5404554 _69899)). Qed.
Lemma lem5404783 (_69899 : int) (_69900 : int) : (term125 _69899 _69900) = (term207 _69899 _69900).
Proof. exact (MK_COMB (@lem5404782 _69899) (@lem5404780 _69899 _69900)). Qed.
Lemma lem5404790 (_69899 : int) (_69900 : int) : (term127 _69899 _69900) = (term207 _69899 _69900).
Proof. exact (TRANS (@lem5404506 _69899 _69900) (@lem5404783 _69899 _69900)). Qed.
Lemma lem5404813 (_69899 : int) (_69900 : int) : (term204 _69899 _69900) = (term208 _69899 _69900).
Proof. exact (@lem19367 (term175 _69899) (term184 _69899) (term202 _69899 _69900)). Qed.
Lemma lem5404816 (_69900 : int) : (term205 _69900) = (term205 _69900).
Proof. exact (eq_refl (term205 _69900)). Qed.
Lemma lem5404817 (_69899 : int) (_69900 : int) : (term206 _69899 _69900) = (term209 _69899 _69900).
Proof. exact (MK_COMB (@lem5404816 _69900) (@lem5404813 _69899 _69900)). Qed.
Lemma lem5404824 (_69899 : int) (_69900 : int) : (term209 _69899 _69900) = (term210 _69899 _69900).
Proof. exact (@lem19158 (term211 _69899 _69900) (term155 _69900) (term212 _69899 _69900)). Qed.
Lemma lem5404825 (_69899 : int) (_69900 : int) : (term206 _69899 _69900) = (term210 _69899 _69900).
Proof. exact (TRANS (@lem5404817 _69899 _69900) (@lem5404824 _69899 _69900)). Qed.
Lemma lem5404828 (_69899 : int) : (term205 _69899) = (term205 _69899).
Proof. exact (eq_refl (term205 _69899)). Qed.
Lemma lem5404829 (_69899 : int) (_69900 : int) : (term207 _69899 _69900) = (term213 _69899 _69900).
Proof. exact (MK_COMB (@lem5404828 _69899) (@lem5404825 _69899 _69900)). Qed.
Lemma lem5404836 (_69899 : int) (_69900 : int) : (term213 _69899 _69900) = (term214 _69899 _69900).
Proof. exact (@lem19158 (term215 _69899 _69900) (term155 _69899) (term216 _69899 _69900)). Qed.
Lemma lem5404837 (_69899 : int) (_69900 : int) : (term207 _69899 _69900) = (term214 _69899 _69900).
Proof. exact (TRANS (@lem5404829 _69899 _69900) (@lem5404836 _69899 _69900)). Qed.
Lemma lem5404838 (_69899 : int) (_69900 : int) : (term127 _69899 _69900) = (term214 _69899 _69900).
Proof. exact (TRANS (@lem5404790 _69899 _69900) (@lem5404837 _69899 _69900)). Qed.
Lemma lem5404848 (_69899 : int) (_69900 : int) (h1 : term214 _69899 _69900) : term214 _69899 _69900.
Proof. exact (h1). Qed.
Lemma lem5404849 (_69899 : int) (_69900 : int) (h1 : term217 _69899 _69900) : term217 _69899 _69900.
Proof. exact (h1). Qed.
Lemma lem5404850 (_69899 : int) (_69900 : int) (h1 : term217 _69899 _69900) : term215 _69899 _69900.
Proof. exact (proj2 (@lem5404849 _69899 _69900 h1)). Qed.
Lemma lem5404851 (_69899 : int) (_69900 : int) (h1 : term217 _69899 _69900) : term155 _69899.
Proof. exact (proj1 (@lem5404849 _69899 _69900 h1)). Qed.
Lemma lem5404852 (_69899 : int) (_69900 : int) (h1 : term217 _69899 _69900) : term211 _69899 _69900.
Proof. exact (proj2 (@lem5404850 _69899 _69900 h1)). Qed.
Lemma lem5404855 (_69899 : int) (_69900 : int) (h1 : term217 _69899 _69900) : term175 _69899.
Proof. exact (proj1 (@lem5404852 _69899 _69900 h1)). Qed.
Lemma lem5404859 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5404860 : term218 = term219.
Proof. exact (@lem5404859 term78 term95). Qed.
Lemma lem5404862 (x : nat) : (real_of_num x) = (term131 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5404863 : term95 = term161.
Proof. exact (@lem5404862 term96). Qed.
Lemma lem5404865 (x : nat) : (real_of_num x) = (term131 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5404866 : term78 = term132.
Proof. exact (@lem5404865 (NUMERAL 0)). Qed.
Lemma lem5404867 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5404868 : term220 = term221.
Proof. exact (MK_COMB (@lem5404867) (@lem5404866)). Qed.
Lemma lem5404869 : term219 = term222.
Proof. exact (MK_COMB (@lem5404868) (@lem5404863)). Qed.
Lemma lem5404870 : term223.
Proof. exact (@lem1980255 term78 term95 term95 term95). Qed.
Lemma lem5404872 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5404873 : term219 = term225.
Proof. exact (@lem5404872 (NUMERAL 0) term96). Qed.
Lemma lem5404874 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5404875 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5404876 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5404875 h1) (fun h1 : term225 = True => @lem5404874)). Qed.
Lemma lem5404877 : term225 = True.
Proof. exact (EQ_MP (@lem5404876) (@lem5404874)). Qed.
Lemma lem5404878 : term219 = True.
Proof. exact (TRANS (@lem5404873) (@lem5404877)). Qed.
Lemma lem5404879 : True = term219.
Proof. exact (SYM (@lem5404878)). Qed.
Lemma lem5404880 : term219.
Proof. exact (EQ_MP (@lem5404879) (@lem0)). Qed.
Lemma lem5404881 : term227.
Proof. exact (@lem5404870 (@lem5404880)). Qed.
Lemma lem5404883 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5404884 : term219 = term225.
Proof. exact (@lem5404883 (NUMERAL 0) term96). Qed.
Lemma lem5404885 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5404886 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5404887 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5404886 h1) (fun h1 : term225 = True => @lem5404885)). Qed.
Lemma lem5404888 : term225 = True.
Proof. exact (EQ_MP (@lem5404887) (@lem5404885)). Qed.
Lemma lem5404889 : term219 = True.
Proof. exact (TRANS (@lem5404884) (@lem5404888)). Qed.
Lemma lem5404890 : True = term219.
Proof. exact (SYM (@lem5404889)). Qed.
Lemma lem5404891 : term219.
Proof. exact (EQ_MP (@lem5404890) (@lem0)). Qed.
Lemma lem5404892 : term222 = term228.
Proof. exact (@lem5404881 (@lem5404891)). Qed.
Lemma lem5404894 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5404895 : term144 = term145.
Proof. exact (@lem5404894 term96 term96). Qed.
Lemma lem5404896 : (term146 = (BIT1 0)) = (term147 = term96).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5404897 : term147 = term96.
Proof. exact (EQ_MP (@lem5404896) (@lem940073)). Qed.
Lemma lem5404898 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5404899 : term145 = term95.
Proof. exact (MK_COMB (@lem5404898) (@lem5404897)). Qed.
Lemma lem5404900 : term144 = term95.
Proof. exact (TRANS (@lem5404895) (@lem5404899)). Qed.
Lemma lem5404902 (x : nat) : (term229 x) = term78.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5404903 : term230 = term78.
Proof. exact (@lem5404902 term96). Qed.
Lemma lem5404904 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5404905 : term231 = term220.
Proof. exact (MK_COMB (@lem5404904) (@lem5404903)). Qed.
Lemma lem5404906 : term228 = term219.
Proof. exact (MK_COMB (@lem5404905) (@lem5404900)). Qed.
Lemma lem5404908 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5404909 : term219 = term225.
Proof. exact (@lem5404908 (NUMERAL 0) term96). Qed.
Lemma lem5404910 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5404911 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5404912 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5404911 h1) (fun h1 : term225 = True => @lem5404910)). Qed.
Lemma lem5404913 : term225 = True.
Proof. exact (EQ_MP (@lem5404912) (@lem5404910)). Qed.
Lemma lem5404914 : term219 = True.
Proof. exact (TRANS (@lem5404909) (@lem5404913)). Qed.
Lemma lem5404915 : term228 = True.
Proof. exact (TRANS (@lem5404906) (@lem5404914)). Qed.
Lemma lem5404916 : term222 = True.
Proof. exact (TRANS (@lem5404892) (@lem5404915)). Qed.
Lemma lem5404917 : term219 = True.
Proof. exact (TRANS (@lem5404869) (@lem5404916)). Qed.
Lemma lem5404918 : term218 = True.
Proof. exact (TRANS (@lem5404860) (@lem5404917)). Qed.
Lemma lem5404919 : True = term218.
Proof. exact (SYM (@lem5404918)). Qed.
Lemma lem5404920 : term218.
Proof. exact (EQ_MP (@lem5404919) (@lem0)). Qed.
Lemma lem5404921 (_69899 : int) (_69900 : int) (h1 : term217 _69899 _69900) : term232 _69899.
Proof. exact (conj (@lem5404920) (@lem5404851 _69899 _69900 h1)). Qed.
Lemma lem5404923 (x : real) (y : real) : term233 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5404924 (_69899 : int) : term234 _69899.
Proof. exact (@lem5404923 term95 (real_of_int _69899)). Qed.
Lemma lem5404925 (_69899 : int) (_69900 : int) (h1 : term217 _69899 _69900) : term235 _69899.
Proof. exact (@lem5404924 _69899 (@lem5404921 _69899 _69900 h1)). Qed.
Lemma lem5404926 (_69899 : int) : (term236 _69899) = (real_of_int _69899).
Proof. exact (@lem1982733 (real_of_int _69899)). Qed.
Lemma lem5404927 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5404928 (_69899 : int) : (term237 _69899) = (term154 _69899).
Proof. exact (MK_COMB (@lem5404927) (@lem5404926 _69899)). Qed.
Lemma lem5404929 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem5404930 (_69899 : int) : (term235 _69899) = (term155 _69899).
Proof. exact (MK_COMB (@lem5404928 _69899) (@lem5404929)). Qed.
Lemma lem5404931 (_69899 : int) (_69900 : int) (h1 : term217 _69899 _69900) : term155 _69899.
Proof. exact (EQ_MP (@lem5404930 _69899) (@lem5404925 _69899 _69900 h1)). Qed.
Lemma lem5404933 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5404934 : term218 = term219.
Proof. exact (@lem5404933 term78 term95). Qed.
Lemma lem5404936 (x : nat) : (real_of_num x) = (term131 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5404937 : term95 = term161.
Proof. exact (@lem5404936 term96). Qed.
Lemma lem5404939 (x : nat) : (real_of_num x) = (term131 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5404940 : term78 = term132.
Proof. exact (@lem5404939 (NUMERAL 0)). Qed.
Lemma lem5404941 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5404942 : term220 = term221.
Proof. exact (MK_COMB (@lem5404941) (@lem5404940)). Qed.
Lemma lem5404943 : term219 = term222.
Proof. exact (MK_COMB (@lem5404942) (@lem5404937)). Qed.
Lemma lem5404944 : term223.
Proof. exact (@lem1980255 term78 term95 term95 term95). Qed.
Lemma lem5404946 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5404947 : term219 = term225.
Proof. exact (@lem5404946 (NUMERAL 0) term96). Qed.
Lemma lem5404948 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5404949 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5404950 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5404949 h1) (fun h1 : term225 = True => @lem5404948)). Qed.
Lemma lem5404951 : term225 = True.
Proof. exact (EQ_MP (@lem5404950) (@lem5404948)). Qed.
Lemma lem5404952 : term219 = True.
Proof. exact (TRANS (@lem5404947) (@lem5404951)). Qed.
Lemma lem5404953 : True = term219.
Proof. exact (SYM (@lem5404952)). Qed.
Lemma lem5404954 : term219.
Proof. exact (EQ_MP (@lem5404953) (@lem0)). Qed.
Lemma lem5404955 : term227.
Proof. exact (@lem5404944 (@lem5404954)). Qed.
Lemma lem5404957 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5404958 : term219 = term225.
Proof. exact (@lem5404957 (NUMERAL 0) term96). Qed.
Lemma lem5404959 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5404960 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5404961 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5404960 h1) (fun h1 : term225 = True => @lem5404959)). Qed.
Lemma lem5404962 : term225 = True.
Proof. exact (EQ_MP (@lem5404961) (@lem5404959)). Qed.
Lemma lem5404963 : term219 = True.
Proof. exact (TRANS (@lem5404958) (@lem5404962)). Qed.
Lemma lem5404964 : True = term219.
Proof. exact (SYM (@lem5404963)). Qed.
Lemma lem5404965 : term219.
Proof. exact (EQ_MP (@lem5404964) (@lem0)). Qed.
Lemma lem5404966 : term222 = term228.
Proof. exact (@lem5404955 (@lem5404965)). Qed.
Lemma lem5404968 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5404969 : term144 = term145.
Proof. exact (@lem5404968 term96 term96). Qed.
Lemma lem5404970 : (term146 = (BIT1 0)) = (term147 = term96).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5404971 : term147 = term96.
Proof. exact (EQ_MP (@lem5404970) (@lem940073)). Qed.
Lemma lem5404972 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5404973 : term145 = term95.
Proof. exact (MK_COMB (@lem5404972) (@lem5404971)). Qed.
Lemma lem5404974 : term144 = term95.
Proof. exact (TRANS (@lem5404969) (@lem5404973)). Qed.
Lemma lem5404976 (x : nat) : (term229 x) = term78.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5404977 : term230 = term78.
Proof. exact (@lem5404976 term96). Qed.
Lemma lem5404978 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5404979 : term231 = term220.
Proof. exact (MK_COMB (@lem5404978) (@lem5404977)). Qed.
Lemma lem5404980 : term228 = term219.
Proof. exact (MK_COMB (@lem5404979) (@lem5404974)). Qed.
Lemma lem5404982 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5404983 : term219 = term225.
Proof. exact (@lem5404982 (NUMERAL 0) term96). Qed.
Lemma lem5404984 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5404985 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5404986 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5404985 h1) (fun h1 : term225 = True => @lem5404984)). Qed.
Lemma lem5404987 : term225 = True.
Proof. exact (EQ_MP (@lem5404986) (@lem5404984)). Qed.
Lemma lem5404988 : term219 = True.
Proof. exact (TRANS (@lem5404983) (@lem5404987)). Qed.
Lemma lem5404989 : term228 = True.
Proof. exact (TRANS (@lem5404980) (@lem5404988)). Qed.
Lemma lem5404990 : term222 = True.
Proof. exact (TRANS (@lem5404966) (@lem5404989)). Qed.
Lemma lem5404991 : term219 = True.
Proof. exact (TRANS (@lem5404943) (@lem5404990)). Qed.
Lemma lem5404992 : term218 = True.
Proof. exact (TRANS (@lem5404934) (@lem5404991)). Qed.
Lemma lem5404993 : True = term218.
Proof. exact (SYM (@lem5404992)). Qed.
Lemma lem5404994 : term218.
Proof. exact (EQ_MP (@lem5404993) (@lem0)). Qed.
Lemma lem5404995 (_69899 : int) (_69900 : int) (h1 : term217 _69899 _69900) : term238 _69899.
Proof. exact (conj (@lem5404994) (@lem5404855 _69899 _69900 h1)). Qed.
Lemma lem5404997 (x : real) (y : real) : term233 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5404998 (_69899 : int) : term239 _69899.
Proof. exact (@lem5404997 term95 (term171 _69899)). Qed.
Lemma lem5404999 (_69899 : int) (_69900 : int) (h1 : term217 _69899 _69900) : term240 _69899.
Proof. exact (@lem5404998 _69899 (@lem5404995 _69899 _69900 h1)). Qed.
Lemma lem5405000 (_69899 : int) : (term241 _69899) = (term171 _69899).
Proof. exact (@lem1982733 (term171 _69899)). Qed.
Lemma lem5405001 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5405002 (_69899 : int) : (term242 _69899) = (term174 _69899).
Proof. exact (MK_COMB (@lem5405001) (@lem5405000 _69899)). Qed.
Lemma lem5405003 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem5405004 (_69899 : int) : (term240 _69899) = (term175 _69899).
Proof. exact (MK_COMB (@lem5405002 _69899) (@lem5405003)). Qed.
Lemma lem5405005 (_69899 : int) (_69900 : int) (h1 : term217 _69899 _69900) : term175 _69899.
Proof. exact (EQ_MP (@lem5405004 _69899) (@lem5404999 _69899 _69900 h1)). Qed.
Lemma lem5405006 (_69899 : int) (_69900 : int) (h1 : term217 _69899 _69900) : term243 _69899.
Proof. exact (conj (@lem5405005 _69899 _69900 h1) (@lem5404931 _69899 _69900 h1)). Qed.
Lemma lem5405008 (x : real) (y : real) : term244 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5405009 (_69899 : int) : term245 _69899.
Proof. exact (@lem5405008 (term171 _69899) (real_of_int _69899)). Qed.
Lemma lem5405010 (_69899 : int) (_69900 : int) (h1 : term217 _69899 _69900) : term246 _69899.
Proof. exact (@lem5405009 _69899 (@lem5405006 _69899 _69900 h1)). Qed.
Lemma lem5405011 (_69899 : int) : (term247 _69899) = (term248 _69899).
Proof. exact (@lem1982759 (term191 _69899) (real_of_int _69899) term135). Qed.
Lemma lem5405012 (_69899 : int) : (term249 _69899) = (term250 _69899).
Proof. exact (@lem1982713 term135 (real_of_int _69899)). Qed.
Lemma lem5405014 (x : nat) : (real_of_num x) = (term131 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5405015 : term95 = term161.
Proof. exact (@lem5405014 term96). Qed.
Lemma lem5405017 (x : nat) : (term133 x) = (term134 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5405018 : term135 = term136.
Proof. exact (@lem5405017 term96). Qed.
Lemma lem5405019 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5405020 : term251 = term252.
Proof. exact (MK_COMB (@lem5405019) (@lem5405018)). Qed.
Lemma lem5405021 : term253 = term254.
Proof. exact (MK_COMB (@lem5405020) (@lem5405015)). Qed.
Lemma lem5405022 : term255.
Proof. exact (@lem1981473 term135 term95 term95 term95 term78 term95). Qed.
Lemma lem5405024 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5405025 : term219 = term225.
Proof. exact (@lem5405024 (NUMERAL 0) term96). Qed.
Lemma lem5405026 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5405027 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5405028 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5405027 h1) (fun h1 : term225 = True => @lem5405026)). Qed.
Lemma lem5405029 : term225 = True.
Proof. exact (EQ_MP (@lem5405028) (@lem5405026)). Qed.
Lemma lem5405030 : term219 = True.
Proof. exact (TRANS (@lem5405025) (@lem5405029)). Qed.
Lemma lem5405031 : True = term219.
Proof. exact (SYM (@lem5405030)). Qed.
Lemma lem5405032 : term219.
Proof. exact (EQ_MP (@lem5405031) (@lem0)). Qed.
Lemma lem5405033 : term256.
Proof. exact (@lem5405022 (@lem5405032)). Qed.
Lemma lem5405035 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5405036 : term219 = term225.
Proof. exact (@lem5405035 (NUMERAL 0) term96). Qed.
Lemma lem5405037 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5405038 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5405039 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5405038 h1) (fun h1 : term225 = True => @lem5405037)). Qed.
Lemma lem5405040 : term225 = True.
Proof. exact (EQ_MP (@lem5405039) (@lem5405037)). Qed.
Lemma lem5405041 : term219 = True.
Proof. exact (TRANS (@lem5405036) (@lem5405040)). Qed.
Lemma lem5405042 : True = term219.
Proof. exact (SYM (@lem5405041)). Qed.
Lemma lem5405043 : term219.
Proof. exact (EQ_MP (@lem5405042) (@lem0)). Qed.
Lemma lem5405044 : term257.
Proof. exact (@lem5405033 (@lem5405043)). Qed.
Lemma lem5405046 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5405047 : term219 = term225.
Proof. exact (@lem5405046 (NUMERAL 0) term96). Qed.
Lemma lem5405048 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5405049 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5405050 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5405049 h1) (fun h1 : term225 = True => @lem5405048)). Qed.
Lemma lem5405051 : term225 = True.
Proof. exact (EQ_MP (@lem5405050) (@lem5405048)). Qed.
Lemma lem5405052 : term219 = True.
Proof. exact (TRANS (@lem5405047) (@lem5405051)). Qed.
Lemma lem5405053 : True = term219.
Proof. exact (SYM (@lem5405052)). Qed.
Lemma lem5405054 : term219.
Proof. exact (EQ_MP (@lem5405053) (@lem0)). Qed.
Lemma lem5405055 : term258.
Proof. exact (@lem5405044 (@lem5405054)). Qed.
Lemma lem5405057 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5405058 : term144 = term145.
Proof. exact (@lem5405057 term96 term96). Qed.
Lemma lem5405059 : (term146 = (BIT1 0)) = (term147 = term96).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5405060 : term147 = term96.
Proof. exact (EQ_MP (@lem5405059) (@lem940073)). Qed.
Lemma lem5405061 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5405062 : term145 = term95.
Proof. exact (MK_COMB (@lem5405061) (@lem5405060)). Qed.
Lemma lem5405063 : term144 = term95.
Proof. exact (TRANS (@lem5405058) (@lem5405062)). Qed.
Lemma lem5405065 (m : nat) (n : nat) : (term165 m n) = (term166 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5405066 : term162 = term167.
Proof. exact (@lem5405065 term96 term96). Qed.
Lemma lem5405067 : (term146 = (BIT1 0)) = (term147 = term96).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5405068 : term147 = term96.
Proof. exact (EQ_MP (@lem5405067) (@lem940073)). Qed.
Lemma lem5405069 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5405070 : term145 = term95.
Proof. exact (MK_COMB (@lem5405069) (@lem5405068)). Qed.
Lemma lem5405071 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5405072 : term167 = term135.
Proof. exact (MK_COMB (@lem5405071) (@lem5405070)). Qed.
Lemma lem5405073 : term162 = term135.
Proof. exact (TRANS (@lem5405066) (@lem5405072)). Qed.
Lemma lem5405074 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5405075 : term259 = term251.
Proof. exact (MK_COMB (@lem5405074) (@lem5405073)). Qed.
Lemma lem5405076 : term260 = term253.
Proof. exact (MK_COMB (@lem5405075) (@lem5405063)). Qed.
Lemma lem5405078 (m : nat) : (term261 m) = term78.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5405079 : term253 = term78.
Proof. exact (@lem5405078 term96). Qed.
Lemma lem5405080 : term260 = term78.
Proof. exact (TRANS (@lem5405076) (@lem5405079)). Qed.
Lemma lem5405081 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5405082 : term262 = term263.
Proof. exact (MK_COMB (@lem5405081) (@lem5405080)). Qed.
Lemma lem5405083 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem5405084 : term264 = term230.
Proof. exact (MK_COMB (@lem5405082) (@lem5405083)). Qed.
Lemma lem5405086 (x : nat) : (term229 x) = term78.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5405087 : term230 = term78.
Proof. exact (@lem5405086 term96). Qed.
Lemma lem5405088 : term264 = term78.
Proof. exact (TRANS (@lem5405084) (@lem5405087)). Qed.
Lemma lem5405090 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5405091 : term144 = term145.
Proof. exact (@lem5405090 term96 term96). Qed.
Lemma lem5405092 : (term146 = (BIT1 0)) = (term147 = term96).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5405093 : term147 = term96.
Proof. exact (EQ_MP (@lem5405092) (@lem940073)). Qed.
Lemma lem5405094 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5405095 : term145 = term95.
Proof. exact (MK_COMB (@lem5405094) (@lem5405093)). Qed.
Lemma lem5405096 : term144 = term95.
Proof. exact (TRANS (@lem5405091) (@lem5405095)). Qed.
Lemma lem5405097 : term263 = term263.
Proof. exact (eq_refl term263). Qed.
Lemma lem5405098 : term265 = term230.
Proof. exact (MK_COMB (@lem5405097) (@lem5405096)). Qed.
Lemma lem5405100 (x : nat) : (term229 x) = term78.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5405101 : term230 = term78.
Proof. exact (@lem5405100 term96). Qed.
Lemma lem5405102 : term265 = term78.
Proof. exact (TRANS (@lem5405098) (@lem5405101)). Qed.
Lemma lem5405103 : term78 = term265.
Proof. exact (SYM (@lem5405102)). Qed.
Lemma lem5405104 : term264 = term265.
Proof. exact (TRANS (@lem5405088) (@lem5405103)). Qed.
Lemma lem5405105 : term254 = term132.
Proof. exact (@lem5405055 (@lem5405104)). Qed.
Lemma lem5405106 : term253 = term132.
Proof. exact (TRANS (@lem5405021) (@lem5405105)). Qed.
Lemma lem5405108 (x : real) : (term151 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5405109 : term132 = term78.
Proof. exact (@lem5405108 term78). Qed.
Lemma lem5405110 : term253 = term78.
Proof. exact (TRANS (@lem5405106) (@lem5405109)). Qed.
Lemma lem5405111 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5405112 : term266 = term263.
Proof. exact (MK_COMB (@lem5405111) (@lem5405110)). Qed.
Lemma lem5405113 (_69899 : int) : (real_of_int _69899) = (real_of_int _69899).
Proof. exact (eq_refl (real_of_int _69899)). Qed.
Lemma lem5405114 (_69899 : int) : (term250 _69899) = (term267 _69899).
Proof. exact (MK_COMB (@lem5405112) (@lem5405113 _69899)). Qed.
Lemma lem5405115 (_69899 : int) : (term249 _69899) = (term267 _69899).
Proof. exact (TRANS (@lem5405012 _69899) (@lem5405114 _69899)). Qed.
Lemma lem5405116 (_69899 : int) : (term267 _69899) = term78.
Proof. exact (@lem1982719 (real_of_int _69899)). Qed.
Lemma lem5405117 (_69899 : int) : (term249 _69899) = term78.
Proof. exact (TRANS (@lem5405115 _69899) (@lem5405116 _69899)). Qed.
Lemma lem5405118 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5405119 (_69899 : int) : (term268 _69899) = term110.
Proof. exact (MK_COMB (@lem5405118) (@lem5405117 _69899)). Qed.
Lemma lem5405120 : term135 = term135.
Proof. exact (eq_refl term135). Qed.
Lemma lem5405121 (_69899 : int) : (term248 _69899) = term269.
Proof. exact (MK_COMB (@lem5405119 _69899) (@lem5405120)). Qed.
Lemma lem5405122 (_69899 : int) : (term247 _69899) = term269.
Proof. exact (TRANS (@lem5405011 _69899) (@lem5405121 _69899)). Qed.
Lemma lem5405123 : term269 = term135.
Proof. exact (@lem1982721 term135). Qed.
Lemma lem5405124 (_69899 : int) : (term247 _69899) = term135.
Proof. exact (TRANS (@lem5405122 _69899) (@lem5405123)). Qed.
Lemma lem5405125 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5405126 (_69899 : int) : (term270 _69899) = term271.
Proof. exact (MK_COMB (@lem5405125) (@lem5405124 _69899)). Qed.
Lemma lem5405127 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem5405128 (_69899 : int) : (term246 _69899) = term272.
Proof. exact (MK_COMB (@lem5405126 _69899) (@lem5405127)). Qed.
Lemma lem5405129 (_69899 : int) (_69900 : int) (h1 : term217 _69899 _69900) : term272.
Proof. exact (EQ_MP (@lem5405128 _69899) (@lem5405010 _69899 _69900 h1)). Qed.
Lemma lem5405131 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5405132 : term272 = term273.
Proof. exact (@lem5405131 term78 term135). Qed.
Lemma lem5405134 (x : nat) : (term133 x) = (term134 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5405135 : term135 = term136.
Proof. exact (@lem5405134 term96). Qed.
Lemma lem5405137 (x : nat) : (real_of_num x) = (term131 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5405138 : term78 = term132.
Proof. exact (@lem5405137 (NUMERAL 0)). Qed.
Lemma lem5405139 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5405140 : term80 = term274.
Proof. exact (MK_COMB (@lem5405139) (@lem5405138)). Qed.
Lemma lem5405141 : term273 = term275.
Proof. exact (MK_COMB (@lem5405140) (@lem5405135)). Qed.
Lemma lem5405142 : term276.
Proof. exact (@lem1980026 term78 term95 term135 term95). Qed.
Lemma lem5405144 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5405145 : term219 = term225.
Proof. exact (@lem5405144 (NUMERAL 0) term96). Qed.
Lemma lem5405146 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5405147 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5405148 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5405147 h1) (fun h1 : term225 = True => @lem5405146)). Qed.
Lemma lem5405149 : term225 = True.
Proof. exact (EQ_MP (@lem5405148) (@lem5405146)). Qed.
Lemma lem5405150 : term219 = True.
Proof. exact (TRANS (@lem5405145) (@lem5405149)). Qed.
Lemma lem5405151 : True = term219.
Proof. exact (SYM (@lem5405150)). Qed.
Lemma lem5405152 : term219.
Proof. exact (EQ_MP (@lem5405151) (@lem0)). Qed.
Lemma lem5405153 : term277.
Proof. exact (@lem5405142 (@lem5405152)). Qed.
Lemma lem5405155 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5405156 : term219 = term225.
Proof. exact (@lem5405155 (NUMERAL 0) term96). Qed.
Lemma lem5405157 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5405158 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5405159 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5405158 h1) (fun h1 : term225 = True => @lem5405157)). Qed.
Lemma lem5405160 : term225 = True.
Proof. exact (EQ_MP (@lem5405159) (@lem5405157)). Qed.
Lemma lem5405161 : term219 = True.
Proof. exact (TRANS (@lem5405156) (@lem5405160)). Qed.
Lemma lem5405162 : True = term219.
Proof. exact (SYM (@lem5405161)). Qed.
Lemma lem5405163 : term219.
Proof. exact (EQ_MP (@lem5405162) (@lem0)). Qed.
Lemma lem5405164 : term275 = term278.
Proof. exact (@lem5405153 (@lem5405163)). Qed.
Lemma lem5405166 (m : nat) (n : nat) : (term165 m n) = (term166 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5405167 : term162 = term167.
Proof. exact (@lem5405166 term96 term96). Qed.
Lemma lem5405168 : (term146 = (BIT1 0)) = (term147 = term96).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5405169 : term147 = term96.
Proof. exact (EQ_MP (@lem5405168) (@lem940073)). Qed.
Lemma lem5405170 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5405171 : term145 = term95.
Proof. exact (MK_COMB (@lem5405170) (@lem5405169)). Qed.
Lemma lem5405172 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5405173 : term167 = term135.
Proof. exact (MK_COMB (@lem5405172) (@lem5405171)). Qed.
Lemma lem5405174 : term162 = term135.
Proof. exact (TRANS (@lem5405167) (@lem5405173)). Qed.
Lemma lem5405176 (x : nat) : (term229 x) = term78.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5405177 : term230 = term78.
Proof. exact (@lem5405176 term96). Qed.
Lemma lem5405178 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5405179 : term279 = term80.
Proof. exact (MK_COMB (@lem5405178) (@lem5405177)). Qed.
Lemma lem5405180 : term278 = term273.
Proof. exact (MK_COMB (@lem5405179) (@lem5405174)). Qed.
Lemma lem5405182 (m : nat) (n : nat) : (term280 m n) = (term281 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5405183 : term273 = term282.
Proof. exact (@lem5405182 (NUMERAL 0) term96). Qed.
Lemma lem5405184 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5405185 (h1 : term226 = (BIT1 0)) : (term96 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5405186 : (term226 = (BIT1 0)) = ((term96 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5405185 h1) (fun h1 : (term96 = (NUMERAL 0)) = False => @lem5405184)). Qed.
Lemma lem5405187 : (term96 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5405186) (@lem5405184)). Qed.
Lemma lem5405188 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5405189 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5405190 : term283 = (and True).
Proof. exact (MK_COMB (@lem5405189) (@lem5405188)). Qed.
Lemma lem5405191 : term282 = (True /\ False).
Proof. exact (MK_COMB (@lem5405190) (@lem5405187)). Qed.
Lemma lem5405193 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5405194 : term282 = False.
Proof. exact (TRANS (@lem5405191) (@lem5405193)). Qed.
Lemma lem5405195 : term273 = False.
Proof. exact (TRANS (@lem5405183) (@lem5405194)). Qed.
Lemma lem5405196 : term278 = False.
Proof. exact (TRANS (@lem5405180) (@lem5405195)). Qed.
Lemma lem5405197 : term275 = False.
Proof. exact (TRANS (@lem5405164) (@lem5405196)). Qed.
Lemma lem5405198 : term273 = False.
Proof. exact (TRANS (@lem5405141) (@lem5405197)). Qed.
Lemma lem5405199 : term272 = False.
Proof. exact (TRANS (@lem5405132) (@lem5405198)). Qed.
Lemma lem5405200 (_69899 : int) (_69900 : int) (h1 : term217 _69899 _69900) : False.
Proof. exact (EQ_MP (@lem5405199) (@lem5405129 _69899 _69900 h1)). Qed.
Lemma lem5405201 (_69899 : int) (_69900 : int) (h1 : term284 _69899 _69900) : term284 _69899 _69900.
Proof. exact (h1). Qed.
Lemma lem5405202 (_69899 : int) (_69900 : int) (h1 : term284 _69899 _69900) : term216 _69899 _69900.
Proof. exact (proj2 (@lem5405201 _69899 _69900 h1)). Qed.
Lemma lem5405204 (_69899 : int) (_69900 : int) (h1 : term284 _69899 _69900) : term212 _69899 _69900.
Proof. exact (proj2 (@lem5405202 _69899 _69900 h1)). Qed.
Lemma lem5405206 (_69899 : int) (_69900 : int) (h1 : term284 _69899 _69900) : term202 _69899 _69900.
Proof. exact (proj2 (@lem5405204 _69899 _69900 h1)). Qed.
Lemma lem5405207 (_69899 : int) (_69900 : int) (h1 : term284 _69899 _69900) : term184 _69899.
Proof. exact (proj1 (@lem5405204 _69899 _69900 h1)). Qed.
Lemma lem5405208 (_69899 : int) (_69900 : int) (h1 : term284 _69899 _69900) : term200 _69900.
Proof. exact (proj2 (@lem5405206 _69899 _69900 h1)). Qed.
Lemma lem5405209 (_69899 : int) (_69900 : int) (h1 : term284 _69899 _69900) : term194 _69899 _69900.
Proof. exact (proj1 (@lem5405206 _69899 _69900 h1)). Qed.
Lemma lem5405211 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5405212 : term218 = term219.
Proof. exact (@lem5405211 term78 term95). Qed.
Lemma lem5405214 (x : nat) : (real_of_num x) = (term131 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5405215 : term95 = term161.
Proof. exact (@lem5405214 term96). Qed.
Lemma lem5405217 (x : nat) : (real_of_num x) = (term131 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5405218 : term78 = term132.
Proof. exact (@lem5405217 (NUMERAL 0)). Qed.
Lemma lem5405219 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5405220 : term220 = term221.
Proof. exact (MK_COMB (@lem5405219) (@lem5405218)). Qed.
Lemma lem5405221 : term219 = term222.
Proof. exact (MK_COMB (@lem5405220) (@lem5405215)). Qed.
Lemma lem5405222 : term223.
Proof. exact (@lem1980255 term78 term95 term95 term95). Qed.
Lemma lem5405224 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5405225 : term219 = term225.
Proof. exact (@lem5405224 (NUMERAL 0) term96). Qed.
Lemma lem5405226 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5405227 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5405228 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5405227 h1) (fun h1 : term225 = True => @lem5405226)). Qed.
Lemma lem5405229 : term225 = True.
Proof. exact (EQ_MP (@lem5405228) (@lem5405226)). Qed.
Lemma lem5405230 : term219 = True.
Proof. exact (TRANS (@lem5405225) (@lem5405229)). Qed.
Lemma lem5405231 : True = term219.
Proof. exact (SYM (@lem5405230)). Qed.
Lemma lem5405232 : term219.
Proof. exact (EQ_MP (@lem5405231) (@lem0)). Qed.
Lemma lem5405233 : term227.
Proof. exact (@lem5405222 (@lem5405232)). Qed.
Lemma lem5405235 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5405236 : term219 = term225.
Proof. exact (@lem5405235 (NUMERAL 0) term96). Qed.
Lemma lem5405237 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5405238 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5405239 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5405238 h1) (fun h1 : term225 = True => @lem5405237)). Qed.
Lemma lem5405240 : term225 = True.
Proof. exact (EQ_MP (@lem5405239) (@lem5405237)). Qed.
Lemma lem5405241 : term219 = True.
Proof. exact (TRANS (@lem5405236) (@lem5405240)). Qed.
Lemma lem5405242 : True = term219.
Proof. exact (SYM (@lem5405241)). Qed.
Lemma lem5405243 : term219.
Proof. exact (EQ_MP (@lem5405242) (@lem0)). Qed.
Lemma lem5405244 : term222 = term228.
Proof. exact (@lem5405233 (@lem5405243)). Qed.
Lemma lem5405246 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5405247 : term144 = term145.
Proof. exact (@lem5405246 term96 term96). Qed.
Lemma lem5405248 : (term146 = (BIT1 0)) = (term147 = term96).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5405249 : term147 = term96.
Proof. exact (EQ_MP (@lem5405248) (@lem940073)). Qed.
Lemma lem5405250 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5405251 : term145 = term95.
Proof. exact (MK_COMB (@lem5405250) (@lem5405249)). Qed.
Lemma lem5405252 : term144 = term95.
Proof. exact (TRANS (@lem5405247) (@lem5405251)). Qed.
Lemma lem5405254 (x : nat) : (term229 x) = term78.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5405255 : term230 = term78.
Proof. exact (@lem5405254 term96). Qed.
Lemma lem5405256 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5405257 : term231 = term220.
Proof. exact (MK_COMB (@lem5405256) (@lem5405255)). Qed.
Lemma lem5405258 : term228 = term219.
Proof. exact (MK_COMB (@lem5405257) (@lem5405252)). Qed.
Lemma lem5405260 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5405261 : term219 = term225.
Proof. exact (@lem5405260 (NUMERAL 0) term96). Qed.
Lemma lem5405262 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5405263 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5405264 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5405263 h1) (fun h1 : term225 = True => @lem5405262)). Qed.
Lemma lem5405265 : term225 = True.
Proof. exact (EQ_MP (@lem5405264) (@lem5405262)). Qed.
Lemma lem5405266 : term219 = True.
Proof. exact (TRANS (@lem5405261) (@lem5405265)). Qed.
Lemma lem5405267 : term228 = True.
Proof. exact (TRANS (@lem5405258) (@lem5405266)). Qed.
Lemma lem5405268 : term222 = True.
Proof. exact (TRANS (@lem5405244) (@lem5405267)). Qed.
Lemma lem5405269 : term219 = True.
Proof. exact (TRANS (@lem5405221) (@lem5405268)). Qed.
Lemma lem5405270 : term218 = True.
Proof. exact (TRANS (@lem5405212) (@lem5405269)). Qed.
Lemma lem5405271 : True = term218.
Proof. exact (SYM (@lem5405270)). Qed.
Lemma lem5405272 : term218.
Proof. exact (EQ_MP (@lem5405271) (@lem0)). Qed.
Lemma lem5405273 (_69899 : int) (_69900 : int) (h1 : term284 _69899 _69900) : term285 _69899.
Proof. exact (conj (@lem5405272) (@lem5405207 _69899 _69900 h1)). Qed.
Lemma lem5405275 (x : real) (y : real) : term233 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5405276 (_69899 : int) : term286 _69899.
Proof. exact (@lem5405275 term95 (term181 _69899)). Qed.
Lemma lem5405277 (_69899 : int) (_69900 : int) (h1 : term284 _69899 _69900) : term287 _69899.
Proof. exact (@lem5405276 _69899 (@lem5405273 _69899 _69900 h1)). Qed.
Lemma lem5405278 (_69899 : int) : (term288 _69899) = (term181 _69899).
Proof. exact (@lem1982733 (term181 _69899)). Qed.
Lemma lem5405279 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5405280 (_69899 : int) : (term289 _69899) = (term183 _69899).
Proof. exact (MK_COMB (@lem5405279) (@lem5405278 _69899)). Qed.
Lemma lem5405281 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem5405282 (_69899 : int) : (term287 _69899) = (term184 _69899).
Proof. exact (MK_COMB (@lem5405280 _69899) (@lem5405281)). Qed.
Lemma lem5405283 (_69899 : int) (_69900 : int) (h1 : term284 _69899 _69900) : term184 _69899.
Proof. exact (EQ_MP (@lem5405282 _69899) (@lem5405277 _69899 _69900 h1)). Qed.
Lemma lem5405285 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5405286 : term218 = term219.
Proof. exact (@lem5405285 term78 term95). Qed.
Lemma lem5405288 (x : nat) : (real_of_num x) = (term131 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5405289 : term95 = term161.
Proof. exact (@lem5405288 term96). Qed.
Lemma lem5405291 (x : nat) : (real_of_num x) = (term131 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5405292 : term78 = term132.
Proof. exact (@lem5405291 (NUMERAL 0)). Qed.
Lemma lem5405293 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5405294 : term220 = term221.
Proof. exact (MK_COMB (@lem5405293) (@lem5405292)). Qed.
Lemma lem5405295 : term219 = term222.
Proof. exact (MK_COMB (@lem5405294) (@lem5405289)). Qed.
Lemma lem5405296 : term223.
Proof. exact (@lem1980255 term78 term95 term95 term95). Qed.
Lemma lem5405298 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5405299 : term219 = term225.
Proof. exact (@lem5405298 (NUMERAL 0) term96). Qed.
Lemma lem5405300 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5405301 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5405302 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5405301 h1) (fun h1 : term225 = True => @lem5405300)). Qed.
Lemma lem5405303 : term225 = True.
Proof. exact (EQ_MP (@lem5405302) (@lem5405300)). Qed.
Lemma lem5405304 : term219 = True.
Proof. exact (TRANS (@lem5405299) (@lem5405303)). Qed.
Lemma lem5405305 : True = term219.
Proof. exact (SYM (@lem5405304)). Qed.
Lemma lem5405306 : term219.
Proof. exact (EQ_MP (@lem5405305) (@lem0)). Qed.
Lemma lem5405307 : term227.
Proof. exact (@lem5405296 (@lem5405306)). Qed.
Lemma lem5405309 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5405310 : term219 = term225.
Proof. exact (@lem5405309 (NUMERAL 0) term96). Qed.
Lemma lem5405311 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5405312 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5405313 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5405312 h1) (fun h1 : term225 = True => @lem5405311)). Qed.
Lemma lem5405314 : term225 = True.
Proof. exact (EQ_MP (@lem5405313) (@lem5405311)). Qed.
Lemma lem5405315 : term219 = True.
Proof. exact (TRANS (@lem5405310) (@lem5405314)). Qed.
Lemma lem5405316 : True = term219.
Proof. exact (SYM (@lem5405315)). Qed.
Lemma lem5405317 : term219.
Proof. exact (EQ_MP (@lem5405316) (@lem0)). Qed.
Lemma lem5405318 : term222 = term228.
Proof. exact (@lem5405307 (@lem5405317)). Qed.
Lemma lem5405320 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5405321 : term144 = term145.
Proof. exact (@lem5405320 term96 term96). Qed.
Lemma lem5405322 : (term146 = (BIT1 0)) = (term147 = term96).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5405323 : term147 = term96.
Proof. exact (EQ_MP (@lem5405322) (@lem940073)). Qed.
Lemma lem5405324 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5405325 : term145 = term95.
Proof. exact (MK_COMB (@lem5405324) (@lem5405323)). Qed.
Lemma lem5405326 : term144 = term95.
Proof. exact (TRANS (@lem5405321) (@lem5405325)). Qed.
Lemma lem5405328 (x : nat) : (term229 x) = term78.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5405329 : term230 = term78.
Proof. exact (@lem5405328 term96). Qed.
Lemma lem5405330 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5405331 : term231 = term220.
Proof. exact (MK_COMB (@lem5405330) (@lem5405329)). Qed.
Lemma lem5405332 : term228 = term219.
Proof. exact (MK_COMB (@lem5405331) (@lem5405326)). Qed.
Lemma lem5405334 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5405335 : term219 = term225.
Proof. exact (@lem5405334 (NUMERAL 0) term96). Qed.
Lemma lem5405336 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5405337 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5405338 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5405337 h1) (fun h1 : term225 = True => @lem5405336)). Qed.
Lemma lem5405339 : term225 = True.
Proof. exact (EQ_MP (@lem5405338) (@lem5405336)). Qed.
Lemma lem5405340 : term219 = True.
Proof. exact (TRANS (@lem5405335) (@lem5405339)). Qed.
Lemma lem5405341 : term228 = True.
Proof. exact (TRANS (@lem5405332) (@lem5405340)). Qed.
Lemma lem5405342 : term222 = True.
Proof. exact (TRANS (@lem5405318) (@lem5405341)). Qed.
Lemma lem5405343 : term219 = True.
Proof. exact (TRANS (@lem5405295) (@lem5405342)). Qed.
Lemma lem5405344 : term218 = True.
Proof. exact (TRANS (@lem5405286) (@lem5405343)). Qed.
Lemma lem5405345 : True = term218.
Proof. exact (SYM (@lem5405344)). Qed.
Lemma lem5405346 : term218.
Proof. exact (EQ_MP (@lem5405345) (@lem0)). Qed.
Lemma lem5405347 (_69899 : int) (_69900 : int) (h1 : term284 _69899 _69900) : term290 _69899 _69900.
Proof. exact (conj (@lem5405346) (@lem5405209 _69899 _69900 h1)). Qed.
Lemma lem5405349 (x : real) (y : real) : term233 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5405350 (_69899 : int) (_69900 : int) : term291 _69899 _69900.
Proof. exact (@lem5405349 term95 (term190 _69899 _69900)). Qed.
Lemma lem5405351 (_69899 : int) (_69900 : int) (h1 : term284 _69899 _69900) : term292 _69899 _69900.
Proof. exact (@lem5405350 _69899 _69900 (@lem5405347 _69899 _69900 h1)). Qed.
Lemma lem5405352 (_69899 : int) (_69900 : int) : (term293 _69899 _69900) = (term190 _69899 _69900).
Proof. exact (@lem1982733 (term190 _69899 _69900)). Qed.
Lemma lem5405353 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5405354 (_69899 : int) (_69900 : int) : (term294 _69899 _69900) = (term193 _69899 _69900).
Proof. exact (MK_COMB (@lem5405353) (@lem5405352 _69899 _69900)). Qed.
Lemma lem5405355 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem5405356 (_69899 : int) (_69900 : int) : (term292 _69899 _69900) = (term194 _69899 _69900).
Proof. exact (MK_COMB (@lem5405354 _69899 _69900) (@lem5405355)). Qed.
Lemma lem5405357 (_69899 : int) (_69900 : int) (h1 : term284 _69899 _69900) : term194 _69899 _69900.
Proof. exact (EQ_MP (@lem5405356 _69899 _69900) (@lem5405351 _69899 _69900 h1)). Qed.
Lemma lem5405358 (_69899 : int) (_69900 : int) (h1 : term284 _69899 _69900) : term295 _69900 _69899.
Proof. exact (conj (@lem5405357 _69899 _69900 h1) (@lem5405283 _69899 _69900 h1)). Qed.
Lemma lem5405360 (x : real) (y : real) : term244 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5405361 (_69900 : int) (_69899 : int) : term296 _69900 _69899.
Proof. exact (@lem5405360 (term190 _69899 _69900) (term181 _69899)). Qed.
Lemma lem5405362 (_69899 : int) (_69900 : int) (h1 : term284 _69899 _69900) : term297 _69900 _69899.
Proof. exact (@lem5405361 _69900 _69899 (@lem5405358 _69899 _69900 h1)). Qed.
Lemma lem5405363 (_69899 : int) (_69900 : int) : (term298 _69900 _69899) = (term299 _69899 _69900).
Proof. exact (@lem1982753 (term191 _69899) (real_of_int _69899) (real_of_int _69900) term135). Qed.
Lemma lem5405364 (_69899 : int) : (term249 _69899) = (term250 _69899).
Proof. exact (@lem1982713 term135 (real_of_int _69899)). Qed.
Lemma lem5405366 (x : nat) : (real_of_num x) = (term131 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5405367 : term95 = term161.
Proof. exact (@lem5405366 term96). Qed.
Lemma lem5405369 (x : nat) : (term133 x) = (term134 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5405370 : term135 = term136.
Proof. exact (@lem5405369 term96). Qed.
Lemma lem5405371 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5405372 : term251 = term252.
Proof. exact (MK_COMB (@lem5405371) (@lem5405370)). Qed.
Lemma lem5405373 : term253 = term254.
Proof. exact (MK_COMB (@lem5405372) (@lem5405367)). Qed.
Lemma lem5405374 : term255.
Proof. exact (@lem1981473 term135 term95 term95 term95 term78 term95). Qed.
Lemma lem5405376 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5405377 : term219 = term225.
Proof. exact (@lem5405376 (NUMERAL 0) term96). Qed.
Lemma lem5405378 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5405379 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5405380 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5405379 h1) (fun h1 : term225 = True => @lem5405378)). Qed.
Lemma lem5405381 : term225 = True.
Proof. exact (EQ_MP (@lem5405380) (@lem5405378)). Qed.
Lemma lem5405382 : term219 = True.
Proof. exact (TRANS (@lem5405377) (@lem5405381)). Qed.
Lemma lem5405383 : True = term219.
Proof. exact (SYM (@lem5405382)). Qed.
Lemma lem5405384 : term219.
Proof. exact (EQ_MP (@lem5405383) (@lem0)). Qed.
Lemma lem5405385 : term256.
Proof. exact (@lem5405374 (@lem5405384)). Qed.
Lemma lem5405387 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5405388 : term219 = term225.
Proof. exact (@lem5405387 (NUMERAL 0) term96). Qed.
Lemma lem5405389 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5405390 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5405391 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5405390 h1) (fun h1 : term225 = True => @lem5405389)). Qed.
Lemma lem5405392 : term225 = True.
Proof. exact (EQ_MP (@lem5405391) (@lem5405389)). Qed.
Lemma lem5405393 : term219 = True.
Proof. exact (TRANS (@lem5405388) (@lem5405392)). Qed.
Lemma lem5405394 : True = term219.
Proof. exact (SYM (@lem5405393)). Qed.
Lemma lem5405395 : term219.
Proof. exact (EQ_MP (@lem5405394) (@lem0)). Qed.
Lemma lem5405396 : term257.
Proof. exact (@lem5405385 (@lem5405395)). Qed.
Lemma lem5405398 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5405399 : term219 = term225.
Proof. exact (@lem5405398 (NUMERAL 0) term96). Qed.
Lemma lem5405400 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5405401 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5405402 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5405401 h1) (fun h1 : term225 = True => @lem5405400)). Qed.
Lemma lem5405403 : term225 = True.
Proof. exact (EQ_MP (@lem5405402) (@lem5405400)). Qed.
Lemma lem5405404 : term219 = True.
Proof. exact (TRANS (@lem5405399) (@lem5405403)). Qed.
Lemma lem5405405 : True = term219.
Proof. exact (SYM (@lem5405404)). Qed.
Lemma lem5405406 : term219.
Proof. exact (EQ_MP (@lem5405405) (@lem0)). Qed.
Lemma lem5405407 : term258.
Proof. exact (@lem5405396 (@lem5405406)). Qed.
Lemma lem5405409 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5405410 : term144 = term145.
Proof. exact (@lem5405409 term96 term96). Qed.
Lemma lem5405411 : (term146 = (BIT1 0)) = (term147 = term96).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5405412 : term147 = term96.
Proof. exact (EQ_MP (@lem5405411) (@lem940073)). Qed.
Lemma lem5405413 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5405414 : term145 = term95.
Proof. exact (MK_COMB (@lem5405413) (@lem5405412)). Qed.
Lemma lem5405415 : term144 = term95.
Proof. exact (TRANS (@lem5405410) (@lem5405414)). Qed.
Lemma lem5405417 (m : nat) (n : nat) : (term165 m n) = (term166 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5405418 : term162 = term167.
Proof. exact (@lem5405417 term96 term96). Qed.
Lemma lem5405419 : (term146 = (BIT1 0)) = (term147 = term96).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5405420 : term147 = term96.
Proof. exact (EQ_MP (@lem5405419) (@lem940073)). Qed.
Lemma lem5405421 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5405422 : term145 = term95.
Proof. exact (MK_COMB (@lem5405421) (@lem5405420)). Qed.
Lemma lem5405423 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5405424 : term167 = term135.
Proof. exact (MK_COMB (@lem5405423) (@lem5405422)). Qed.
Lemma lem5405425 : term162 = term135.
Proof. exact (TRANS (@lem5405418) (@lem5405424)). Qed.
Lemma lem5405426 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5405427 : term259 = term251.
Proof. exact (MK_COMB (@lem5405426) (@lem5405425)). Qed.
Lemma lem5405428 : term260 = term253.
Proof. exact (MK_COMB (@lem5405427) (@lem5405415)). Qed.
Lemma lem5405430 (m : nat) : (term261 m) = term78.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5405431 : term253 = term78.
Proof. exact (@lem5405430 term96). Qed.
Lemma lem5405432 : term260 = term78.
Proof. exact (TRANS (@lem5405428) (@lem5405431)). Qed.
Lemma lem5405433 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5405434 : term262 = term263.
Proof. exact (MK_COMB (@lem5405433) (@lem5405432)). Qed.
Lemma lem5405435 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem5405436 : term264 = term230.
Proof. exact (MK_COMB (@lem5405434) (@lem5405435)). Qed.
Lemma lem5405438 (x : nat) : (term229 x) = term78.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5405439 : term230 = term78.
Proof. exact (@lem5405438 term96). Qed.
Lemma lem5405440 : term264 = term78.
Proof. exact (TRANS (@lem5405436) (@lem5405439)). Qed.
Lemma lem5405442 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5405443 : term144 = term145.
Proof. exact (@lem5405442 term96 term96). Qed.
Lemma lem5405444 : (term146 = (BIT1 0)) = (term147 = term96).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5405445 : term147 = term96.
Proof. exact (EQ_MP (@lem5405444) (@lem940073)). Qed.
Lemma lem5405446 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5405447 : term145 = term95.
Proof. exact (MK_COMB (@lem5405446) (@lem5405445)). Qed.
Lemma lem5405448 : term144 = term95.
Proof. exact (TRANS (@lem5405443) (@lem5405447)). Qed.
Lemma lem5405449 : term263 = term263.
Proof. exact (eq_refl term263). Qed.
Lemma lem5405450 : term265 = term230.
Proof. exact (MK_COMB (@lem5405449) (@lem5405448)). Qed.
Lemma lem5405452 (x : nat) : (term229 x) = term78.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5405453 : term230 = term78.
Proof. exact (@lem5405452 term96). Qed.
Lemma lem5405454 : term265 = term78.
Proof. exact (TRANS (@lem5405450) (@lem5405453)). Qed.
Lemma lem5405455 : term78 = term265.
Proof. exact (SYM (@lem5405454)). Qed.
Lemma lem5405456 : term264 = term265.
Proof. exact (TRANS (@lem5405440) (@lem5405455)). Qed.
Lemma lem5405457 : term254 = term132.
Proof. exact (@lem5405407 (@lem5405456)). Qed.
Lemma lem5405458 : term253 = term132.
Proof. exact (TRANS (@lem5405373) (@lem5405457)). Qed.
Lemma lem5405460 (x : real) : (term151 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5405461 : term132 = term78.
Proof. exact (@lem5405460 term78). Qed.
Lemma lem5405462 : term253 = term78.
Proof. exact (TRANS (@lem5405458) (@lem5405461)). Qed.
Lemma lem5405463 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5405464 : term266 = term263.
Proof. exact (MK_COMB (@lem5405463) (@lem5405462)). Qed.
Lemma lem5405465 (_69899 : int) : (real_of_int _69899) = (real_of_int _69899).
Proof. exact (eq_refl (real_of_int _69899)). Qed.
Lemma lem5405466 (_69899 : int) : (term250 _69899) = (term267 _69899).
Proof. exact (MK_COMB (@lem5405464) (@lem5405465 _69899)). Qed.
Lemma lem5405467 (_69899 : int) : (term249 _69899) = (term267 _69899).
Proof. exact (TRANS (@lem5405364 _69899) (@lem5405466 _69899)). Qed.
Lemma lem5405468 (_69899 : int) : (term267 _69899) = term78.
Proof. exact (@lem1982719 (real_of_int _69899)). Qed.
Lemma lem5405469 (_69899 : int) : (term249 _69899) = term78.
Proof. exact (TRANS (@lem5405467 _69899) (@lem5405468 _69899)). Qed.
Lemma lem5405470 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5405471 (_69899 : int) : (term268 _69899) = term110.
Proof. exact (MK_COMB (@lem5405470) (@lem5405469 _69899)). Qed.
Lemma lem5405472 (_69900 : int) : (term181 _69900) = (term181 _69900).
Proof. exact (eq_refl (term181 _69900)). Qed.
Lemma lem5405473 (_69899 : int) (_69900 : int) : (term299 _69899 _69900) = (term300 _69900).
Proof. exact (MK_COMB (@lem5405471 _69899) (@lem5405472 _69900)). Qed.
Lemma lem5405474 (_69899 : int) (_69900 : int) : (term298 _69900 _69899) = (term300 _69900).
Proof. exact (TRANS (@lem5405363 _69899 _69900) (@lem5405473 _69899 _69900)). Qed.
Lemma lem5405475 (_69900 : int) : (term300 _69900) = (term181 _69900).
Proof. exact (@lem1982721 (term181 _69900)). Qed.
Lemma lem5405476 (_69899 : int) (_69900 : int) : (term298 _69900 _69899) = (term181 _69900).
Proof. exact (TRANS (@lem5405474 _69899 _69900) (@lem5405475 _69900)). Qed.
Lemma lem5405477 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5405478 (_69899 : int) (_69900 : int) : (term301 _69900 _69899) = (term183 _69900).
Proof. exact (MK_COMB (@lem5405477) (@lem5405476 _69899 _69900)). Qed.
Lemma lem5405479 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem5405480 (_69899 : int) (_69900 : int) : (term297 _69900 _69899) = (term184 _69900).
Proof. exact (MK_COMB (@lem5405478 _69899 _69900) (@lem5405479)). Qed.
Lemma lem5405481 (_69899 : int) (_69900 : int) (h1 : term284 _69899 _69900) : term184 _69900.
Proof. exact (EQ_MP (@lem5405480 _69899 _69900) (@lem5405362 _69899 _69900 h1)). Qed.
Lemma lem5405483 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5405484 : term218 = term219.
Proof. exact (@lem5405483 term78 term95). Qed.
Lemma lem5405486 (x : nat) : (real_of_num x) = (term131 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5405487 : term95 = term161.
Proof. exact (@lem5405486 term96). Qed.
Lemma lem5405489 (x : nat) : (real_of_num x) = (term131 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5405490 : term78 = term132.
Proof. exact (@lem5405489 (NUMERAL 0)). Qed.
Lemma lem5405491 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5405492 : term220 = term221.
Proof. exact (MK_COMB (@lem5405491) (@lem5405490)). Qed.
Lemma lem5405493 : term219 = term222.
Proof. exact (MK_COMB (@lem5405492) (@lem5405487)). Qed.
Lemma lem5405494 : term223.
Proof. exact (@lem1980255 term78 term95 term95 term95). Qed.
Lemma lem5405496 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5405497 : term219 = term225.
Proof. exact (@lem5405496 (NUMERAL 0) term96). Qed.
Lemma lem5405498 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5405499 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5405500 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5405499 h1) (fun h1 : term225 = True => @lem5405498)). Qed.
Lemma lem5405501 : term225 = True.
Proof. exact (EQ_MP (@lem5405500) (@lem5405498)). Qed.
Lemma lem5405502 : term219 = True.
Proof. exact (TRANS (@lem5405497) (@lem5405501)). Qed.
Lemma lem5405503 : True = term219.
Proof. exact (SYM (@lem5405502)). Qed.
Lemma lem5405504 : term219.
Proof. exact (EQ_MP (@lem5405503) (@lem0)). Qed.
Lemma lem5405505 : term227.
Proof. exact (@lem5405494 (@lem5405504)). Qed.
Lemma lem5405507 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5405508 : term219 = term225.
Proof. exact (@lem5405507 (NUMERAL 0) term96). Qed.
Lemma lem5405509 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5405510 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5405511 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5405510 h1) (fun h1 : term225 = True => @lem5405509)). Qed.
Lemma lem5405512 : term225 = True.
Proof. exact (EQ_MP (@lem5405511) (@lem5405509)). Qed.
Lemma lem5405513 : term219 = True.
Proof. exact (TRANS (@lem5405508) (@lem5405512)). Qed.
Lemma lem5405514 : True = term219.
Proof. exact (SYM (@lem5405513)). Qed.
Lemma lem5405515 : term219.
Proof. exact (EQ_MP (@lem5405514) (@lem0)). Qed.
Lemma lem5405516 : term222 = term228.
Proof. exact (@lem5405505 (@lem5405515)). Qed.
Lemma lem5405518 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5405519 : term144 = term145.
Proof. exact (@lem5405518 term96 term96). Qed.
Lemma lem5405520 : (term146 = (BIT1 0)) = (term147 = term96).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5405521 : term147 = term96.
Proof. exact (EQ_MP (@lem5405520) (@lem940073)). Qed.
Lemma lem5405522 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5405523 : term145 = term95.
Proof. exact (MK_COMB (@lem5405522) (@lem5405521)). Qed.
Lemma lem5405524 : term144 = term95.
Proof. exact (TRANS (@lem5405519) (@lem5405523)). Qed.
Lemma lem5405526 (x : nat) : (term229 x) = term78.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5405527 : term230 = term78.
Proof. exact (@lem5405526 term96). Qed.
Lemma lem5405528 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5405529 : term231 = term220.
Proof. exact (MK_COMB (@lem5405528) (@lem5405527)). Qed.
Lemma lem5405530 : term228 = term219.
Proof. exact (MK_COMB (@lem5405529) (@lem5405524)). Qed.
Lemma lem5405532 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5405533 : term219 = term225.
Proof. exact (@lem5405532 (NUMERAL 0) term96). Qed.
Lemma lem5405534 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5405535 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5405536 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5405535 h1) (fun h1 : term225 = True => @lem5405534)). Qed.
Lemma lem5405537 : term225 = True.
Proof. exact (EQ_MP (@lem5405536) (@lem5405534)). Qed.
Lemma lem5405538 : term219 = True.
Proof. exact (TRANS (@lem5405533) (@lem5405537)). Qed.
Lemma lem5405539 : term228 = True.
Proof. exact (TRANS (@lem5405530) (@lem5405538)). Qed.
Lemma lem5405540 : term222 = True.
Proof. exact (TRANS (@lem5405516) (@lem5405539)). Qed.
Lemma lem5405541 : term219 = True.
Proof. exact (TRANS (@lem5405493) (@lem5405540)). Qed.
Lemma lem5405542 : term218 = True.
Proof. exact (TRANS (@lem5405484) (@lem5405541)). Qed.
Lemma lem5405543 : True = term218.
Proof. exact (SYM (@lem5405542)). Qed.
Lemma lem5405544 : term218.
Proof. exact (EQ_MP (@lem5405543) (@lem0)). Qed.
Lemma lem5405545 (_69899 : int) (_69900 : int) (h1 : term284 _69899 _69900) : term285 _69900.
Proof. exact (conj (@lem5405544) (@lem5405481 _69899 _69900 h1)). Qed.
Lemma lem5405547 (x : real) (y : real) : term233 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5405548 (_69900 : int) : term286 _69900.
Proof. exact (@lem5405547 term95 (term181 _69900)). Qed.
Lemma lem5405549 (_69899 : int) (_69900 : int) (h1 : term284 _69899 _69900) : term287 _69900.
Proof. exact (@lem5405548 _69900 (@lem5405545 _69899 _69900 h1)). Qed.
Lemma lem5405550 (_69900 : int) : (term288 _69900) = (term181 _69900).
Proof. exact (@lem1982733 (term181 _69900)). Qed.
Lemma lem5405551 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5405552 (_69900 : int) : (term289 _69900) = (term183 _69900).
Proof. exact (MK_COMB (@lem5405551) (@lem5405550 _69900)). Qed.
Lemma lem5405553 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem5405554 (_69900 : int) : (term287 _69900) = (term184 _69900).
Proof. exact (MK_COMB (@lem5405552 _69900) (@lem5405553)). Qed.
Lemma lem5405555 (_69899 : int) (_69900 : int) (h1 : term284 _69899 _69900) : term184 _69900.
Proof. exact (EQ_MP (@lem5405554 _69900) (@lem5405549 _69899 _69900 h1)). Qed.
Lemma lem5405557 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5405558 : term218 = term219.
Proof. exact (@lem5405557 term78 term95). Qed.
Lemma lem5405560 (x : nat) : (real_of_num x) = (term131 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5405561 : term95 = term161.
Proof. exact (@lem5405560 term96). Qed.
Lemma lem5405563 (x : nat) : (real_of_num x) = (term131 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5405564 : term78 = term132.
Proof. exact (@lem5405563 (NUMERAL 0)). Qed.
Lemma lem5405565 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5405566 : term220 = term221.
Proof. exact (MK_COMB (@lem5405565) (@lem5405564)). Qed.
Lemma lem5405567 : term219 = term222.
Proof. exact (MK_COMB (@lem5405566) (@lem5405561)). Qed.
Lemma lem5405568 : term223.
Proof. exact (@lem1980255 term78 term95 term95 term95). Qed.
Lemma lem5405570 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5405571 : term219 = term225.
Proof. exact (@lem5405570 (NUMERAL 0) term96). Qed.
Lemma lem5405572 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5405573 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5405574 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5405573 h1) (fun h1 : term225 = True => @lem5405572)). Qed.
Lemma lem5405575 : term225 = True.
Proof. exact (EQ_MP (@lem5405574) (@lem5405572)). Qed.
Lemma lem5405576 : term219 = True.
Proof. exact (TRANS (@lem5405571) (@lem5405575)). Qed.
Lemma lem5405577 : True = term219.
Proof. exact (SYM (@lem5405576)). Qed.
Lemma lem5405578 : term219.
Proof. exact (EQ_MP (@lem5405577) (@lem0)). Qed.
Lemma lem5405579 : term227.
Proof. exact (@lem5405568 (@lem5405578)). Qed.
Lemma lem5405581 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5405582 : term219 = term225.
Proof. exact (@lem5405581 (NUMERAL 0) term96). Qed.
Lemma lem5405583 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5405584 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5405585 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5405584 h1) (fun h1 : term225 = True => @lem5405583)). Qed.
Lemma lem5405586 : term225 = True.
Proof. exact (EQ_MP (@lem5405585) (@lem5405583)). Qed.
Lemma lem5405587 : term219 = True.
Proof. exact (TRANS (@lem5405582) (@lem5405586)). Qed.
Lemma lem5405588 : True = term219.
Proof. exact (SYM (@lem5405587)). Qed.
Lemma lem5405589 : term219.
Proof. exact (EQ_MP (@lem5405588) (@lem0)). Qed.
Lemma lem5405590 : term222 = term228.
Proof. exact (@lem5405579 (@lem5405589)). Qed.
Lemma lem5405592 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5405593 : term144 = term145.
Proof. exact (@lem5405592 term96 term96). Qed.
Lemma lem5405594 : (term146 = (BIT1 0)) = (term147 = term96).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5405595 : term147 = term96.
Proof. exact (EQ_MP (@lem5405594) (@lem940073)). Qed.
Lemma lem5405596 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5405597 : term145 = term95.
Proof. exact (MK_COMB (@lem5405596) (@lem5405595)). Qed.
Lemma lem5405598 : term144 = term95.
Proof. exact (TRANS (@lem5405593) (@lem5405597)). Qed.
Lemma lem5405600 (x : nat) : (term229 x) = term78.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5405601 : term230 = term78.
Proof. exact (@lem5405600 term96). Qed.
Lemma lem5405602 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5405603 : term231 = term220.
Proof. exact (MK_COMB (@lem5405602) (@lem5405601)). Qed.
Lemma lem5405604 : term228 = term219.
Proof. exact (MK_COMB (@lem5405603) (@lem5405598)). Qed.
Lemma lem5405606 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5405607 : term219 = term225.
Proof. exact (@lem5405606 (NUMERAL 0) term96). Qed.
Lemma lem5405608 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5405609 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5405610 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5405609 h1) (fun h1 : term225 = True => @lem5405608)). Qed.
Lemma lem5405611 : term225 = True.
Proof. exact (EQ_MP (@lem5405610) (@lem5405608)). Qed.
Lemma lem5405612 : term219 = True.
Proof. exact (TRANS (@lem5405607) (@lem5405611)). Qed.
Lemma lem5405613 : term228 = True.
Proof. exact (TRANS (@lem5405604) (@lem5405612)). Qed.
Lemma lem5405614 : term222 = True.
Proof. exact (TRANS (@lem5405590) (@lem5405613)). Qed.
Lemma lem5405615 : term219 = True.
Proof. exact (TRANS (@lem5405567) (@lem5405614)). Qed.
Lemma lem5405616 : term218 = True.
Proof. exact (TRANS (@lem5405558) (@lem5405615)). Qed.
Lemma lem5405617 : True = term218.
Proof. exact (SYM (@lem5405616)). Qed.
Lemma lem5405618 : term218.
Proof. exact (EQ_MP (@lem5405617) (@lem0)). Qed.
Lemma lem5405619 (_69899 : int) (_69900 : int) (h1 : term284 _69899 _69900) : term302 _69900.
Proof. exact (conj (@lem5405618) (@lem5405208 _69899 _69900 h1)). Qed.
Lemma lem5405621 (x : real) (y : real) : term233 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5405622 (_69900 : int) : term303 _69900.
Proof. exact (@lem5405621 term95 (term191 _69900)). Qed.
Lemma lem5405623 (_69899 : int) (_69900 : int) (h1 : term284 _69899 _69900) : term304 _69900.
Proof. exact (@lem5405622 _69900 (@lem5405619 _69899 _69900 h1)). Qed.
Lemma lem5405624 (_69900 : int) : (term305 _69900) = (term191 _69900).
Proof. exact (@lem1982733 (term191 _69900)). Qed.
Lemma lem5405625 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5405626 (_69900 : int) : (term306 _69900) = (term199 _69900).
Proof. exact (MK_COMB (@lem5405625) (@lem5405624 _69900)). Qed.
Lemma lem5405627 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem5405628 (_69900 : int) : (term304 _69900) = (term200 _69900).
Proof. exact (MK_COMB (@lem5405626 _69900) (@lem5405627)). Qed.
Lemma lem5405629 (_69899 : int) (_69900 : int) (h1 : term284 _69899 _69900) : term200 _69900.
Proof. exact (EQ_MP (@lem5405628 _69900) (@lem5405623 _69899 _69900 h1)). Qed.
Lemma lem5405630 (_69899 : int) (_69900 : int) (h1 : term284 _69899 _69900) : term307 _69900.
Proof. exact (conj (@lem5405629 _69899 _69900 h1) (@lem5405555 _69899 _69900 h1)). Qed.
Lemma lem5405632 (x : real) (y : real) : term244 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5405633 (_69900 : int) : term308 _69900.
Proof. exact (@lem5405632 (term191 _69900) (term181 _69900)). Qed.
Lemma lem5405634 (_69899 : int) (_69900 : int) (h1 : term284 _69899 _69900) : term309 _69900.
Proof. exact (@lem5405633 _69900 (@lem5405630 _69899 _69900 h1)). Qed.
Lemma lem5405635 (_69900 : int) : (term310 _69900) = (term248 _69900).
Proof. exact (@lem1982763 (term191 _69900) (real_of_int _69900) term135). Qed.
Lemma lem5405636 (_69900 : int) : (term249 _69900) = (term250 _69900).
Proof. exact (@lem1982713 term135 (real_of_int _69900)). Qed.
Lemma lem5405638 (x : nat) : (real_of_num x) = (term131 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5405639 : term95 = term161.
Proof. exact (@lem5405638 term96). Qed.
Lemma lem5405641 (x : nat) : (term133 x) = (term134 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5405642 : term135 = term136.
Proof. exact (@lem5405641 term96). Qed.
Lemma lem5405643 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5405644 : term251 = term252.
Proof. exact (MK_COMB (@lem5405643) (@lem5405642)). Qed.
Lemma lem5405645 : term253 = term254.
Proof. exact (MK_COMB (@lem5405644) (@lem5405639)). Qed.
Lemma lem5405646 : term255.
Proof. exact (@lem1981473 term135 term95 term95 term95 term78 term95). Qed.
Lemma lem5405648 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5405649 : term219 = term225.
Proof. exact (@lem5405648 (NUMERAL 0) term96). Qed.
Lemma lem5405650 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5405651 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5405652 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5405651 h1) (fun h1 : term225 = True => @lem5405650)). Qed.
Lemma lem5405653 : term225 = True.
Proof. exact (EQ_MP (@lem5405652) (@lem5405650)). Qed.
Lemma lem5405654 : term219 = True.
Proof. exact (TRANS (@lem5405649) (@lem5405653)). Qed.
Lemma lem5405655 : True = term219.
Proof. exact (SYM (@lem5405654)). Qed.
Lemma lem5405656 : term219.
Proof. exact (EQ_MP (@lem5405655) (@lem0)). Qed.
Lemma lem5405657 : term256.
Proof. exact (@lem5405646 (@lem5405656)). Qed.
Lemma lem5405659 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5405660 : term219 = term225.
Proof. exact (@lem5405659 (NUMERAL 0) term96). Qed.
Lemma lem5405661 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5405662 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5405663 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5405662 h1) (fun h1 : term225 = True => @lem5405661)). Qed.
Lemma lem5405664 : term225 = True.
Proof. exact (EQ_MP (@lem5405663) (@lem5405661)). Qed.
Lemma lem5405665 : term219 = True.
Proof. exact (TRANS (@lem5405660) (@lem5405664)). Qed.
Lemma lem5405666 : True = term219.
Proof. exact (SYM (@lem5405665)). Qed.
Lemma lem5405667 : term219.
Proof. exact (EQ_MP (@lem5405666) (@lem0)). Qed.
Lemma lem5405668 : term257.
Proof. exact (@lem5405657 (@lem5405667)). Qed.
Lemma lem5405670 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5405671 : term219 = term225.
Proof. exact (@lem5405670 (NUMERAL 0) term96). Qed.
Lemma lem5405672 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5405673 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5405674 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5405673 h1) (fun h1 : term225 = True => @lem5405672)). Qed.
Lemma lem5405675 : term225 = True.
Proof. exact (EQ_MP (@lem5405674) (@lem5405672)). Qed.
Lemma lem5405676 : term219 = True.
Proof. exact (TRANS (@lem5405671) (@lem5405675)). Qed.
Lemma lem5405677 : True = term219.
Proof. exact (SYM (@lem5405676)). Qed.
Lemma lem5405678 : term219.
Proof. exact (EQ_MP (@lem5405677) (@lem0)). Qed.
Lemma lem5405679 : term258.
Proof. exact (@lem5405668 (@lem5405678)). Qed.
Lemma lem5405681 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5405682 : term144 = term145.
Proof. exact (@lem5405681 term96 term96). Qed.
Lemma lem5405683 : (term146 = (BIT1 0)) = (term147 = term96).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5405684 : term147 = term96.
Proof. exact (EQ_MP (@lem5405683) (@lem940073)). Qed.
Lemma lem5405685 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5405686 : term145 = term95.
Proof. exact (MK_COMB (@lem5405685) (@lem5405684)). Qed.
Lemma lem5405687 : term144 = term95.
Proof. exact (TRANS (@lem5405682) (@lem5405686)). Qed.
Lemma lem5405689 (m : nat) (n : nat) : (term165 m n) = (term166 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5405690 : term162 = term167.
Proof. exact (@lem5405689 term96 term96). Qed.
Lemma lem5405691 : (term146 = (BIT1 0)) = (term147 = term96).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5405692 : term147 = term96.
Proof. exact (EQ_MP (@lem5405691) (@lem940073)). Qed.
Lemma lem5405693 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5405694 : term145 = term95.
Proof. exact (MK_COMB (@lem5405693) (@lem5405692)). Qed.
Lemma lem5405695 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5405696 : term167 = term135.
Proof. exact (MK_COMB (@lem5405695) (@lem5405694)). Qed.
Lemma lem5405697 : term162 = term135.
Proof. exact (TRANS (@lem5405690) (@lem5405696)). Qed.
Lemma lem5405698 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5405699 : term259 = term251.
Proof. exact (MK_COMB (@lem5405698) (@lem5405697)). Qed.
Lemma lem5405700 : term260 = term253.
Proof. exact (MK_COMB (@lem5405699) (@lem5405687)). Qed.
Lemma lem5405702 (m : nat) : (term261 m) = term78.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5405703 : term253 = term78.
Proof. exact (@lem5405702 term96). Qed.
Lemma lem5405704 : term260 = term78.
Proof. exact (TRANS (@lem5405700) (@lem5405703)). Qed.
Lemma lem5405705 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5405706 : term262 = term263.
Proof. exact (MK_COMB (@lem5405705) (@lem5405704)). Qed.
Lemma lem5405707 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem5405708 : term264 = term230.
Proof. exact (MK_COMB (@lem5405706) (@lem5405707)). Qed.
Lemma lem5405710 (x : nat) : (term229 x) = term78.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5405711 : term230 = term78.
Proof. exact (@lem5405710 term96). Qed.
Lemma lem5405712 : term264 = term78.
Proof. exact (TRANS (@lem5405708) (@lem5405711)). Qed.
Lemma lem5405714 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5405715 : term144 = term145.
Proof. exact (@lem5405714 term96 term96). Qed.
Lemma lem5405716 : (term146 = (BIT1 0)) = (term147 = term96).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5405717 : term147 = term96.
Proof. exact (EQ_MP (@lem5405716) (@lem940073)). Qed.
Lemma lem5405718 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5405719 : term145 = term95.
Proof. exact (MK_COMB (@lem5405718) (@lem5405717)). Qed.
Lemma lem5405720 : term144 = term95.
Proof. exact (TRANS (@lem5405715) (@lem5405719)). Qed.
Lemma lem5405721 : term263 = term263.
Proof. exact (eq_refl term263). Qed.
Lemma lem5405722 : term265 = term230.
Proof. exact (MK_COMB (@lem5405721) (@lem5405720)). Qed.
Lemma lem5405724 (x : nat) : (term229 x) = term78.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5405725 : term230 = term78.
Proof. exact (@lem5405724 term96). Qed.
Lemma lem5405726 : term265 = term78.
Proof. exact (TRANS (@lem5405722) (@lem5405725)). Qed.
Lemma lem5405727 : term78 = term265.
Proof. exact (SYM (@lem5405726)). Qed.
Lemma lem5405728 : term264 = term265.
Proof. exact (TRANS (@lem5405712) (@lem5405727)). Qed.
Lemma lem5405729 : term254 = term132.
Proof. exact (@lem5405679 (@lem5405728)). Qed.
Lemma lem5405730 : term253 = term132.
Proof. exact (TRANS (@lem5405645) (@lem5405729)). Qed.
Lemma lem5405732 (x : real) : (term151 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5405733 : term132 = term78.
Proof. exact (@lem5405732 term78). Qed.
Lemma lem5405734 : term253 = term78.
Proof. exact (TRANS (@lem5405730) (@lem5405733)). Qed.
Lemma lem5405735 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5405736 : term266 = term263.
Proof. exact (MK_COMB (@lem5405735) (@lem5405734)). Qed.
Lemma lem5405737 (_69900 : int) : (real_of_int _69900) = (real_of_int _69900).
Proof. exact (eq_refl (real_of_int _69900)). Qed.
Lemma lem5405738 (_69900 : int) : (term250 _69900) = (term267 _69900).
Proof. exact (MK_COMB (@lem5405736) (@lem5405737 _69900)). Qed.
Lemma lem5405739 (_69900 : int) : (term249 _69900) = (term267 _69900).
Proof. exact (TRANS (@lem5405636 _69900) (@lem5405738 _69900)). Qed.
Lemma lem5405740 (_69900 : int) : (term267 _69900) = term78.
Proof. exact (@lem1982719 (real_of_int _69900)). Qed.
Lemma lem5405741 (_69900 : int) : (term249 _69900) = term78.
Proof. exact (TRANS (@lem5405739 _69900) (@lem5405740 _69900)). Qed.
Lemma lem5405742 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5405743 (_69900 : int) : (term268 _69900) = term110.
Proof. exact (MK_COMB (@lem5405742) (@lem5405741 _69900)). Qed.
Lemma lem5405744 : term135 = term135.
Proof. exact (eq_refl term135). Qed.
Lemma lem5405745 (_69900 : int) : (term248 _69900) = term269.
Proof. exact (MK_COMB (@lem5405743 _69900) (@lem5405744)). Qed.
Lemma lem5405746 (_69900 : int) : (term310 _69900) = term269.
Proof. exact (TRANS (@lem5405635 _69900) (@lem5405745 _69900)). Qed.
Lemma lem5405747 : term269 = term135.
Proof. exact (@lem1982721 term135). Qed.
Lemma lem5405748 (_69900 : int) : (term310 _69900) = term135.
Proof. exact (TRANS (@lem5405746 _69900) (@lem5405747)). Qed.
Lemma lem5405749 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5405750 (_69900 : int) : (term311 _69900) = term271.
Proof. exact (MK_COMB (@lem5405749) (@lem5405748 _69900)). Qed.
Lemma lem5405751 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem5405752 (_69900 : int) : (term309 _69900) = term272.
Proof. exact (MK_COMB (@lem5405750 _69900) (@lem5405751)). Qed.
Lemma lem5405753 (_69899 : int) (_69900 : int) (h1 : term284 _69899 _69900) : term272.
Proof. exact (EQ_MP (@lem5405752 _69900) (@lem5405634 _69899 _69900 h1)). Qed.
Lemma lem5405755 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5405756 : term272 = term273.
Proof. exact (@lem5405755 term78 term135). Qed.
Lemma lem5405758 (x : nat) : (term133 x) = (term134 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5405759 : term135 = term136.
Proof. exact (@lem5405758 term96). Qed.
Lemma lem5405761 (x : nat) : (real_of_num x) = (term131 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5405762 : term78 = term132.
Proof. exact (@lem5405761 (NUMERAL 0)). Qed.
Lemma lem5405763 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5405764 : term80 = term274.
Proof. exact (MK_COMB (@lem5405763) (@lem5405762)). Qed.
Lemma lem5405765 : term273 = term275.
Proof. exact (MK_COMB (@lem5405764) (@lem5405759)). Qed.
Lemma lem5405766 : term276.
Proof. exact (@lem1980026 term78 term95 term135 term95). Qed.
Lemma lem5405768 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5405769 : term219 = term225.
Proof. exact (@lem5405768 (NUMERAL 0) term96). Qed.
Lemma lem5405770 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5405771 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5405772 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5405771 h1) (fun h1 : term225 = True => @lem5405770)). Qed.
Lemma lem5405773 : term225 = True.
Proof. exact (EQ_MP (@lem5405772) (@lem5405770)). Qed.
Lemma lem5405774 : term219 = True.
Proof. exact (TRANS (@lem5405769) (@lem5405773)). Qed.
Lemma lem5405775 : True = term219.
Proof. exact (SYM (@lem5405774)). Qed.
Lemma lem5405776 : term219.
Proof. exact (EQ_MP (@lem5405775) (@lem0)). Qed.
Lemma lem5405777 : term277.
Proof. exact (@lem5405766 (@lem5405776)). Qed.
Lemma lem5405779 (m : nat) (n : nat) : (term224 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5405780 : term219 = term225.
Proof. exact (@lem5405779 (NUMERAL 0) term96). Qed.
Lemma lem5405781 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5405782 (h1 : term226 = (BIT1 0)) : term225 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5405783 : (term226 = (BIT1 0)) = (term225 = True).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5405782 h1) (fun h1 : term225 = True => @lem5405781)). Qed.
Lemma lem5405784 : term225 = True.
Proof. exact (EQ_MP (@lem5405783) (@lem5405781)). Qed.
Lemma lem5405785 : term219 = True.
Proof. exact (TRANS (@lem5405780) (@lem5405784)). Qed.
Lemma lem5405786 : True = term219.
Proof. exact (SYM (@lem5405785)). Qed.
Lemma lem5405787 : term219.
Proof. exact (EQ_MP (@lem5405786) (@lem0)). Qed.
Lemma lem5405788 : term275 = term278.
Proof. exact (@lem5405777 (@lem5405787)). Qed.
Lemma lem5405790 (m : nat) (n : nat) : (term165 m n) = (term166 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5405791 : term162 = term167.
Proof. exact (@lem5405790 term96 term96). Qed.
Lemma lem5405792 : (term146 = (BIT1 0)) = (term147 = term96).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5405793 : term147 = term96.
Proof. exact (EQ_MP (@lem5405792) (@lem940073)). Qed.
Lemma lem5405794 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5405795 : term145 = term95.
Proof. exact (MK_COMB (@lem5405794) (@lem5405793)). Qed.
Lemma lem5405796 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5405797 : term167 = term135.
Proof. exact (MK_COMB (@lem5405796) (@lem5405795)). Qed.
Lemma lem5405798 : term162 = term135.
Proof. exact (TRANS (@lem5405791) (@lem5405797)). Qed.
Lemma lem5405800 (x : nat) : (term229 x) = term78.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5405801 : term230 = term78.
Proof. exact (@lem5405800 term96). Qed.
Lemma lem5405802 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5405803 : term279 = term80.
Proof. exact (MK_COMB (@lem5405802) (@lem5405801)). Qed.
Lemma lem5405804 : term278 = term273.
Proof. exact (MK_COMB (@lem5405803) (@lem5405798)). Qed.
Lemma lem5405806 (m : nat) (n : nat) : (term280 m n) = (term281 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5405807 : term273 = term282.
Proof. exact (@lem5405806 (NUMERAL 0) term96). Qed.
Lemma lem5405808 : term226 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5405809 (h1 : term226 = (BIT1 0)) : (term96 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5405810 : (term226 = (BIT1 0)) = ((term96 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term226 = (BIT1 0) => @lem5405809 h1) (fun h1 : (term96 = (NUMERAL 0)) = False => @lem5405808)). Qed.
Lemma lem5405811 : (term96 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5405810) (@lem5405808)). Qed.
Lemma lem5405812 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5405813 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5405814 : term283 = (and True).
Proof. exact (MK_COMB (@lem5405813) (@lem5405812)). Qed.
Lemma lem5405815 : term282 = (True /\ False).
Proof. exact (MK_COMB (@lem5405814) (@lem5405811)). Qed.
Lemma lem5405817 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5405818 : term282 = False.
Proof. exact (TRANS (@lem5405815) (@lem5405817)). Qed.
Lemma lem5405819 : term273 = False.
Proof. exact (TRANS (@lem5405807) (@lem5405818)). Qed.
Lemma lem5405820 : term278 = False.
Proof. exact (TRANS (@lem5405804) (@lem5405819)). Qed.
Lemma lem5405821 : term275 = False.
Proof. exact (TRANS (@lem5405788) (@lem5405820)). Qed.
Lemma lem5405822 : term273 = False.
Proof. exact (TRANS (@lem5405765) (@lem5405821)). Qed.
Lemma lem5405823 : term272 = False.
Proof. exact (TRANS (@lem5405756) (@lem5405822)). Qed.
Lemma lem5405824 (_69899 : int) (_69900 : int) (h1 : term284 _69899 _69900) : False.
Proof. exact (EQ_MP (@lem5405823) (@lem5405753 _69899 _69900 h1)). Qed.
Lemma lem5405825 (_69899 : int) (_69900 : int) (h1 : term214 _69899 _69900) : False.
Proof. exact (or_elim (@lem5404848 _69899 _69900 h1) (fun h0 : term217 _69899 _69900 => @lem5405200 _69899 _69900 h0) (fun h0 : term284 _69899 _69900 => @lem5405824 _69899 _69900 h0)). Qed.
Lemma lem5405827 (_69899 : int) (_69900 : int) (h1 : term214 _69899 _69900) : term214 _69899 _69900.
Proof. exact (h1). Qed.
Lemma lem5405828 (_69899 : int) (_69900 : int) (h1 : term214 _69899 _69900) : (term214 _69899 _69900) = False.
Proof. exact (prop_ext (fun h2 : term214 _69899 _69900 => @lem5405825 _69899 _69900 h1) (fun h2 : False => @lem5405827 _69899 _69900 h1)). Qed.
Lemma lem5405829 (_69899 : int) (_69900 : int) (h1 : term214 _69899 _69900) : False.
Proof. exact (EQ_MP (@lem5405828 _69899 _69900 h1) (@lem5405827 _69899 _69900 h1)). Qed.
Lemma lem5405830 (_69899 : int) (_69900 : int) (h1 : term127 _69899 _69900) : term127 _69899 _69900.
Proof. exact (h1). Qed.
Lemma lem5405831 (_69899 : int) (_69900 : int) (h1 : term127 _69899 _69900) : term214 _69899 _69900.
Proof. exact (EQ_MP (@lem5404838 _69899 _69900) (@lem5405830 _69899 _69900 h1)). Qed.
Lemma lem5405832 (_69899 : int) (_69900 : int) (h1 : term127 _69899 _69900) : (term214 _69899 _69900) = False.
Proof. exact (prop_ext (fun h2 : term214 _69899 _69900 => @lem5405829 _69899 _69900 h2) (fun h2 : False => @lem5405831 _69899 _69900 h1)). Qed.
Lemma lem5405833 (_69899 : int) (_69900 : int) (h1 : term127 _69899 _69900) : False.
Proof. exact (EQ_MP (@lem5405832 _69899 _69900 h1) (@lem5405831 _69899 _69900 h1)). Qed.
Lemma lem5405834 (_69899 : int) (_69900 : int) : term312 _69899 _69900.
Proof. exact (fun h0 : term127 _69899 _69900 => @lem5405833 _69899 _69900 h0). Qed.
Lemma lem5405835 (_69899 : int) (_69900 : int) : term313 _69899 _69900.
Proof. exact (@lem1386578 (term314 _69899 _69900)). Qed.
Lemma lem5405838 (_69899 : int) (_69900 : int) : term314 _69899 _69900.
Proof. exact (@lem5405835 _69899 _69900 (@lem5405834 _69899 _69900)). Qed.
Lemma lem5405839 (_69899 : int) (_69900 : int) : (term125 _69899 _69900) = (term72 _69899 _69900).
Proof. exact (SYM (@lem5404446 _69899 _69900)). Qed.
Lemma lem5405840 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5405841 (_69899 : int) (_69900 : int) : (term314 _69899 _69900) = (term47 _69899 _69900).
Proof. exact (MK_COMB (@lem5405840) (@lem5405839 _69899 _69900)). Qed.
Lemma lem5405842 (_69899 : int) (_69900 : int) : term47 _69899 _69900.
Proof. exact (EQ_MP (@lem5405841 _69899 _69900) (@lem5405838 _69899 _69900)). Qed.
Lemma lem5405843 (_69899 : int) (_69900 : int) : term48 _69899 _69900.
Proof. exact (EQ_MP (@lem5404281 _69899 _69900) (@lem5405842 _69899 _69900)). Qed.
Lemma lem5405844 (m : nat) (x : nat) : term315 m x.
Proof. exact (@lem5405843 (int_of_num m) (int_of_num x)). Qed.
Lemma lem5405845 (m : nat) (x : nat) : term316 m x.
Proof. exact (@lem5405844 m x (@lem5404277 m)). Qed.
Lemma lem5405846 (m : nat) (x : nat) : term42 m x.
Proof. exact (@lem5405845 m x (@lem5404280 x)). Qed.
Lemma lem5405847 (m : nat) : term44 m.
Proof. exact (fun x : nat => @lem5405846 m x). Qed.
Lemma lem5405848 (m : nat) : (term44 m) = (term4 m).
Proof. exact (SYM (@lem5404274 m)). Qed.
Lemma lem5405849 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem5405848 m) (@lem5405847 m)). Qed.
Lemma lem5405850 (m : nat) : (term4 m) = ((term4 m) = True).
Proof. exact (@lem7 (term4 m)). Qed.
Lemma lem5405851 (m : nat) : (term4 m) = True.
Proof. exact (EQ_MP (@lem5405850 m) (@lem5405849 m)). Qed.
Lemma lem5405852 (m : nat) : True = (term4 m).
Proof. exact (SYM (@lem5405851 m)). Qed.
Lemma lem5405853 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem5405852 m) (@lem0)). Qed.
