Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_BOUND_LT_GEN_term_abbrevs.
Require Import INT_POS_spec.
Require Import LTE_TRANS_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NSUM_BOUND_GEN_spec.
Require Import NSUM_LT_ALL_spec.
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
Require Import thm16485_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17500_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
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
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm2318495_spec.
Require Import thm2318496_spec.
Require Import thm2318497_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841401_spec.
Require Import thm2841402_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem6980237 (a : nat) (b : nat) : ((term0 a b) = (Peano.lt a b)) = (term1 a b).
Proof. exact (@lem17500 (term0 a b) (Peano.lt a b)). Qed.
Lemma lem6980239 (m : nat) (n : nat) : (Peano.le m n) = (term2 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem6980240 (a : nat) (b : nat) : (term0 a b) = (term3 a b).
Proof. exact (@lem6980239 (term4 a) b). Qed.
Lemma lem6980242 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem6980243 (a : nat) : (term7 a) = (term8 a).
Proof. exact (@lem6980242 a term9). Qed.
Lemma lem6980244 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem6980245 (a : nat) : (term10 a) = (term11 a).
Proof. exact (MK_COMB (@lem6980244) (@lem6980243 a)). Qed.
Lemma lem6980246 (b : nat) : (int_of_num b) = (int_of_num b).
Proof. exact (eq_refl (int_of_num b)). Qed.
Lemma lem6980247 (a : nat) (b : nat) : (term3 a b) = (term12 a b).
Proof. exact (MK_COMB (@lem6980245 a) (@lem6980246 b)). Qed.
Lemma lem6980248 (a : nat) (b : nat) : (term0 a b) = (term12 a b).
Proof. exact (TRANS (@lem6980240 a b) (@lem6980247 a b)). Qed.
Lemma lem6980249 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6980250 (a : nat) (b : nat) : (term13 a b) = (term14 a b).
Proof. exact (MK_COMB (@lem6980249) (@lem6980248 a b)). Qed.
Lemma lem6980252 (m : nat) (n : nat) : (Peano.lt m n) = (term15 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem6980253 (a : nat) (b : nat) : (Peano.lt a b) = (term15 a b).
Proof. exact (@lem6980252 a b). Qed.
Lemma lem6980254 (a : nat) (b : nat) : (term16 a b) = (term17 a b).
Proof. exact (MK_COMB (@lem6980250 a b) (@lem6980253 a b)). Qed.
Lemma lem6980255 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6980256 (a : nat) (b : nat) : (term18 a b) = (term19 a b).
Proof. exact (MK_COMB (@lem6980255) (@lem6980254 a b)). Qed.
Lemma lem6980258 (m : nat) (n : nat) : (Peano.le m n) = (term2 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem6980259 (a : nat) (b : nat) : (term0 a b) = (term3 a b).
Proof. exact (@lem6980258 (term4 a) b). Qed.
Lemma lem6980261 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem6980262 (a : nat) : (term7 a) = (term8 a).
Proof. exact (@lem6980261 a term9). Qed.
Lemma lem6980263 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem6980264 (a : nat) : (term10 a) = (term11 a).
Proof. exact (MK_COMB (@lem6980263) (@lem6980262 a)). Qed.
Lemma lem6980265 (b : nat) : (int_of_num b) = (int_of_num b).
Proof. exact (eq_refl (int_of_num b)). Qed.
Lemma lem6980266 (a : nat) (b : nat) : (term3 a b) = (term12 a b).
Proof. exact (MK_COMB (@lem6980264 a) (@lem6980265 b)). Qed.
Lemma lem6980267 (a : nat) (b : nat) : (term0 a b) = (term12 a b).
Proof. exact (TRANS (@lem6980259 a b) (@lem6980266 a b)). Qed.
Lemma lem6980268 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6980269 (a : nat) (b : nat) : (term20 a b) = (term21 a b).
Proof. exact (MK_COMB (@lem6980268) (@lem6980267 a b)). Qed.
Lemma lem6980270 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6980271 (a : nat) (b : nat) : (term22 a b) = (term23 a b).
Proof. exact (MK_COMB (@lem6980270) (@lem6980269 a b)). Qed.
Lemma lem6980273 (m : nat) (n : nat) : (Peano.lt m n) = (term15 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem6980274 (a : nat) (b : nat) : (Peano.lt a b) = (term15 a b).
Proof. exact (@lem6980273 a b). Qed.
Lemma lem6980275 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6980276 (a : nat) (b : nat) : (term24 a b) = (term25 a b).
Proof. exact (MK_COMB (@lem6980275) (@lem6980274 a b)). Qed.
Lemma lem6980277 (a : nat) (b : nat) : (term26 a b) = (term27 a b).
Proof. exact (MK_COMB (@lem6980271 a b) (@lem6980276 a b)). Qed.
Lemma lem6980278 (a : nat) (b : nat) : (term1 a b) = (term28 a b).
Proof. exact (MK_COMB (@lem6980256 a b) (@lem6980277 a b)). Qed.
Lemma lem6980279 (a : nat) (b : nat) : ((term0 a b) = (Peano.lt a b)) = (term28 a b).
Proof. exact (TRANS (@lem6980237 a b) (@lem6980278 a b)). Qed.
Lemma lem6980280 (a : nat) : term29 a.
Proof. exact (@lem2307535 a). Qed.
Lemma lem6980281 (a : nat) : (term29 a) = (term30 a).
Proof. exact (eq_refl (term29 a)). Qed.
Lemma lem6980282 (a : nat) : term30 a.
Proof. exact (EQ_MP (@lem6980281 a) (@lem6980280 a)). Qed.
Lemma lem6980283 (b : nat) : term29 b.
Proof. exact (@lem2307535 b). Qed.
Lemma lem6980284 (b : nat) : (term29 b) = (term30 b).
Proof. exact (eq_refl (term29 b)). Qed.
Lemma lem6980285 (b : nat) : term30 b.
Proof. exact (EQ_MP (@lem6980284 b) (@lem6980283 b)). Qed.
Lemma lem6980286 (_92986 : int) (_92987 : int) : (term31 _92986 _92987) = (term32 _92986 _92987).
Proof. exact (@lem2318604 (term32 _92986 _92987)). Qed.
Lemma lem6980310 (_92986 : int) (_92987 : int) : (term33 _92986 _92987) = (term34 _92986 _92987).
Proof. exact (@lem17045 (term35 _92986 _92987) (int_lt _92986 _92987)). Qed.
Lemma lem6980313 (_92986 : int) (_92987 : int) : (term36 _92986 _92987) = (term35 _92986 _92987).
Proof. exact (@lem16933 (term35 _92986 _92987)). Qed.
Lemma lem6980316 (_92986 : int) (_92987 : int) : (term37 _92986 _92987) = (int_lt _92986 _92987).
Proof. exact (@lem16933 (int_lt _92986 _92987)). Qed.
Lemma lem6980317 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6980318 (_92986 : int) (_92987 : int) : (term38 _92986 _92987) = (term39 _92986 _92987).
Proof. exact (MK_COMB (@lem6980317) (@lem6980313 _92986 _92987)). Qed.
Lemma lem6980319 (_92986 : int) (_92987 : int) : (term40 _92986 _92987) = (term41 _92986 _92987).
Proof. exact (MK_COMB (@lem6980318 _92986 _92987) (@lem6980316 _92986 _92987)). Qed.
Lemma lem6980320 (_92986 : int) (_92987 : int) : (term42 _92986 _92987) = (term40 _92986 _92987).
Proof. exact (@lem17045 (term43 _92986 _92987) (term44 _92986 _92987)). Qed.
Lemma lem6980321 (_92986 : int) (_92987 : int) : (term42 _92986 _92987) = (term41 _92986 _92987).
Proof. exact (TRANS (@lem6980320 _92986 _92987) (@lem6980319 _92986 _92987)). Qed.
Lemma lem6980322 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6980323 (_92986 : int) (_92987 : int) : (term45 _92986 _92987) = (term46 _92986 _92987).
Proof. exact (MK_COMB (@lem6980322) (@lem6980310 _92986 _92987)). Qed.
Lemma lem6980324 (_92986 : int) (_92987 : int) : (term47 _92986 _92987) = (term48 _92986 _92987).
Proof. exact (MK_COMB (@lem6980323 _92986 _92987) (@lem6980321 _92986 _92987)). Qed.
Lemma lem6980325 (_92986 : int) (_92987 : int) : (term49 _92986 _92987) = (term47 _92986 _92987).
Proof. exact (@lem17160 (term50 _92986 _92987) (term51 _92986 _92987)). Qed.
Lemma lem6980326 (_92986 : int) (_92987 : int) : (term49 _92986 _92987) = (term48 _92986 _92987).
Proof. exact (TRANS (@lem6980325 _92986 _92987) (@lem6980324 _92986 _92987)). Qed.
Lemma lem6980328 (_92987 : int) : (term52 _92987) = (term52 _92987).
Proof. exact (eq_refl (term52 _92987)). Qed.
Lemma lem6980329 (_92986 : int) (_92987 : int) : (term53 _92986 _92987) = (term54 _92986 _92987).
Proof. exact (MK_COMB (@lem6980328 _92987) (@lem6980326 _92986 _92987)). Qed.
Lemma lem6980330 (_92986 : int) (_92987 : int) : (term55 _92986 _92987) = (term53 _92986 _92987).
Proof. exact (@lem17362 (term56 _92987) (term57 _92986 _92987)). Qed.
Lemma lem6980331 (_92986 : int) (_92987 : int) : (term55 _92986 _92987) = (term54 _92986 _92987).
Proof. exact (TRANS (@lem6980330 _92986 _92987) (@lem6980329 _92986 _92987)). Qed.
Lemma lem6980333 (_92986 : int) : (term52 _92986) = (term52 _92986).
Proof. exact (eq_refl (term52 _92986)). Qed.
Lemma lem6980334 (_92986 : int) (_92987 : int) : (term58 _92986 _92987) = (term59 _92986 _92987).
Proof. exact (MK_COMB (@lem6980333 _92986) (@lem6980331 _92986 _92987)). Qed.
Lemma lem6980335 (_92986 : int) (_92987 : int) : (term60 _92986 _92987) = (term58 _92986 _92987).
Proof. exact (@lem17362 (term56 _92986) (term61 _92986 _92987)). Qed.
Lemma lem6980363 (_92986 : int) (_92987 : int) : (term60 _92986 _92987) = (term59 _92986 _92987).
Proof. exact (TRANS (@lem6980335 _92986 _92987) (@lem6980334 _92986 _92987)). Qed.
Lemma lem6980366 (x : int) (y : int) : (int_le x y) = (term62 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6980367 (_92986 : int) : (term56 _92986) = (term63 _92986).
Proof. exact (@lem6980366 term64 _92986). Qed.
Lemma lem6980369 (n : nat) : (term65 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6980370 : term66 = term67.
Proof. exact (@lem6980369 (NUMERAL 0)). Qed.
Lemma lem6980371 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6980372 : term68 = term69.
Proof. exact (MK_COMB (@lem6980371) (@lem6980370)). Qed.
Lemma lem6980373 (_92986 : int) : (real_of_int _92986) = (real_of_int _92986).
Proof. exact (eq_refl (real_of_int _92986)). Qed.
Lemma lem6980374 (_92986 : int) : (term63 _92986) = (term70 _92986).
Proof. exact (MK_COMB (@lem6980372) (@lem6980373 _92986)). Qed.
Lemma lem6980376 (_92986 : int) : (term56 _92986) = (term70 _92986).
Proof. exact (TRANS (@lem6980367 _92986) (@lem6980374 _92986)). Qed.
Lemma lem6980379 (x : int) (y : int) : (int_le x y) = (term62 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6980380 (_92987 : int) : (term56 _92987) = (term63 _92987).
Proof. exact (@lem6980379 term64 _92987). Qed.
Lemma lem6980382 (n : nat) : (term65 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6980383 : term66 = term67.
Proof. exact (@lem6980382 (NUMERAL 0)). Qed.
Lemma lem6980384 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6980385 : term68 = term69.
Proof. exact (MK_COMB (@lem6980384) (@lem6980383)). Qed.
Lemma lem6980386 (_92987 : int) : (real_of_int _92987) = (real_of_int _92987).
Proof. exact (eq_refl (real_of_int _92987)). Qed.
Lemma lem6980387 (_92987 : int) : (term63 _92987) = (term70 _92987).
Proof. exact (MK_COMB (@lem6980385) (@lem6980386 _92987)). Qed.
Lemma lem6980389 (_92987 : int) : (term56 _92987) = (term70 _92987).
Proof. exact (TRANS (@lem6980380 _92987) (@lem6980387 _92987)). Qed.
Lemma lem6980391 (y : int) (x : int) : (term71 x y) = (term35 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem6980392 (_92987 : int) (_92986 : int) : (term43 _92986 _92987) = (term72 _92987 _92986).
Proof. exact (@lem6980391 _92987 (term73 _92986)). Qed.
Lemma lem6980394 (x : int) (y : int) : (int_le x y) = (term62 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6980395 (_92987 : int) (_92986 : int) : (term72 _92987 _92986) = (term74 _92987 _92986).
Proof. exact (@lem6980394 (term73 _92987) (term73 _92986)). Qed.
Lemma lem6980397 (x : int) (y : int) : (term75 x y) = (term76 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6980398 (_92987 : int) : (term77 _92987) = (term78 _92987).
Proof. exact (@lem6980397 _92987 term79). Qed.
Lemma lem6980400 (n : nat) : (term65 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6980401 : term80 = term81.
Proof. exact (@lem6980400 term9). Qed.
Lemma lem6980402 (_92987 : int) : (term82 _92987) = (term82 _92987).
Proof. exact (eq_refl (term82 _92987)). Qed.
Lemma lem6980403 (_92987 : int) : (term78 _92987) = (term83 _92987).
Proof. exact (MK_COMB (@lem6980402 _92987) (@lem6980401)). Qed.
Lemma lem6980404 (_92987 : int) : (term77 _92987) = (term83 _92987).
Proof. exact (TRANS (@lem6980398 _92987) (@lem6980403 _92987)). Qed.
Lemma lem6980405 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6980406 (_92987 : int) : (term84 _92987) = (term85 _92987).
Proof. exact (MK_COMB (@lem6980405) (@lem6980404 _92987)). Qed.
Lemma lem6980408 (x : int) (y : int) : (term75 x y) = (term76 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6980409 (_92986 : int) : (term77 _92986) = (term78 _92986).
Proof. exact (@lem6980408 _92986 term79). Qed.
Lemma lem6980411 (n : nat) : (term65 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6980412 : term80 = term81.
Proof. exact (@lem6980411 term9). Qed.
Lemma lem6980413 (_92986 : int) : (term82 _92986) = (term82 _92986).
Proof. exact (eq_refl (term82 _92986)). Qed.
Lemma lem6980414 (_92986 : int) : (term78 _92986) = (term83 _92986).
Proof. exact (MK_COMB (@lem6980413 _92986) (@lem6980412)). Qed.
Lemma lem6980415 (_92986 : int) : (term77 _92986) = (term83 _92986).
Proof. exact (TRANS (@lem6980409 _92986) (@lem6980414 _92986)). Qed.
Lemma lem6980416 (_92987 : int) (_92986 : int) : (term74 _92987 _92986) = (term86 _92987 _92986).
Proof. exact (MK_COMB (@lem6980406 _92987) (@lem6980415 _92986)). Qed.
Lemma lem6980417 (_92987 : int) (_92986 : int) : (term72 _92987 _92986) = (term86 _92987 _92986).
Proof. exact (TRANS (@lem6980395 _92987 _92986) (@lem6980416 _92987 _92986)). Qed.
Lemma lem6980418 (_92987 : int) (_92986 : int) : (term43 _92986 _92987) = (term86 _92987 _92986).
Proof. exact (TRANS (@lem6980392 _92987 _92986) (@lem6980417 _92987 _92986)). Qed.
Lemma lem6980420 (y : int) (x : int) : (term44 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem6980421 (_92987 : int) (_92986 : int) : (term44 _92986 _92987) = (int_le _92987 _92986).
Proof. exact (@lem6980420 _92987 _92986). Qed.
Lemma lem6980423 (x : int) (y : int) : (int_le x y) = (term62 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6980424 (_92987 : int) (_92986 : int) : (int_le _92987 _92986) = (term62 _92987 _92986).
Proof. exact (@lem6980423 _92987 _92986). Qed.
Lemma lem6980425 (_92987 : int) (_92986 : int) : (term44 _92986 _92987) = (term62 _92987 _92986).
Proof. exact (TRANS (@lem6980421 _92987 _92986) (@lem6980424 _92987 _92986)). Qed.
Lemma lem6980426 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6980427 (_92987 : int) (_92986 : int) : (term87 _92986 _92987) = (term88 _92987 _92986).
Proof. exact (MK_COMB (@lem6980426) (@lem6980418 _92987 _92986)). Qed.
Lemma lem6980428 (_92987 : int) (_92986 : int) : (term34 _92986 _92987) = (term89 _92987 _92986).
Proof. exact (MK_COMB (@lem6980427 _92987 _92986) (@lem6980425 _92987 _92986)). Qed.
Lemma lem6980431 (x : int) (y : int) : (int_le x y) = (term62 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6980432 (_92986 : int) (_92987 : int) : (term35 _92986 _92987) = (term90 _92986 _92987).
Proof. exact (@lem6980431 (term73 _92986) _92987). Qed.
Lemma lem6980434 (x : int) (y : int) : (term75 x y) = (term76 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6980435 (_92986 : int) : (term77 _92986) = (term78 _92986).
Proof. exact (@lem6980434 _92986 term79). Qed.
Lemma lem6980437 (n : nat) : (term65 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6980438 : term80 = term81.
Proof. exact (@lem6980437 term9). Qed.
Lemma lem6980439 (_92986 : int) : (term82 _92986) = (term82 _92986).
Proof. exact (eq_refl (term82 _92986)). Qed.
Lemma lem6980440 (_92986 : int) : (term78 _92986) = (term83 _92986).
Proof. exact (MK_COMB (@lem6980439 _92986) (@lem6980438)). Qed.
Lemma lem6980441 (_92986 : int) : (term77 _92986) = (term83 _92986).
Proof. exact (TRANS (@lem6980435 _92986) (@lem6980440 _92986)). Qed.
Lemma lem6980442 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6980443 (_92986 : int) : (term84 _92986) = (term85 _92986).
Proof. exact (MK_COMB (@lem6980442) (@lem6980441 _92986)). Qed.
Lemma lem6980444 (_92987 : int) : (real_of_int _92987) = (real_of_int _92987).
Proof. exact (eq_refl (real_of_int _92987)). Qed.
Lemma lem6980445 (_92986 : int) (_92987 : int) : (term90 _92986 _92987) = (term91 _92986 _92987).
Proof. exact (MK_COMB (@lem6980443 _92986) (@lem6980444 _92987)). Qed.
Lemma lem6980447 (_92986 : int) (_92987 : int) : (term35 _92986 _92987) = (term91 _92986 _92987).
Proof. exact (TRANS (@lem6980432 _92986 _92987) (@lem6980445 _92986 _92987)). Qed.
Lemma lem6980449 (x : int) (y : int) : (int_lt x y) = (term35 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem6980450 (_92986 : int) (_92987 : int) : (int_lt _92986 _92987) = (term35 _92986 _92987).
Proof. exact (@lem6980449 _92986 _92987). Qed.
Lemma lem6980452 (x : int) (y : int) : (int_le x y) = (term62 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6980453 (_92986 : int) (_92987 : int) : (term35 _92986 _92987) = (term90 _92986 _92987).
Proof. exact (@lem6980452 (term73 _92986) _92987). Qed.
Lemma lem6980455 (x : int) (y : int) : (term75 x y) = (term76 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6980456 (_92986 : int) : (term77 _92986) = (term78 _92986).
Proof. exact (@lem6980455 _92986 term79). Qed.
Lemma lem6980458 (n : nat) : (term65 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6980459 : term80 = term81.
Proof. exact (@lem6980458 term9). Qed.
Lemma lem6980460 (_92986 : int) : (term82 _92986) = (term82 _92986).
Proof. exact (eq_refl (term82 _92986)). Qed.
Lemma lem6980461 (_92986 : int) : (term78 _92986) = (term83 _92986).
Proof. exact (MK_COMB (@lem6980460 _92986) (@lem6980459)). Qed.
Lemma lem6980462 (_92986 : int) : (term77 _92986) = (term83 _92986).
Proof. exact (TRANS (@lem6980456 _92986) (@lem6980461 _92986)). Qed.
Lemma lem6980463 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6980464 (_92986 : int) : (term84 _92986) = (term85 _92986).
Proof. exact (MK_COMB (@lem6980463) (@lem6980462 _92986)). Qed.
Lemma lem6980465 (_92987 : int) : (real_of_int _92987) = (real_of_int _92987).
Proof. exact (eq_refl (real_of_int _92987)). Qed.
Lemma lem6980466 (_92986 : int) (_92987 : int) : (term90 _92986 _92987) = (term91 _92986 _92987).
Proof. exact (MK_COMB (@lem6980464 _92986) (@lem6980465 _92987)). Qed.
Lemma lem6980467 (_92986 : int) (_92987 : int) : (term35 _92986 _92987) = (term91 _92986 _92987).
Proof. exact (TRANS (@lem6980453 _92986 _92987) (@lem6980466 _92986 _92987)). Qed.
Lemma lem6980468 (_92986 : int) (_92987 : int) : (int_lt _92986 _92987) = (term91 _92986 _92987).
Proof. exact (TRANS (@lem6980450 _92986 _92987) (@lem6980467 _92986 _92987)). Qed.
Lemma lem6980469 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6980470 (_92986 : int) (_92987 : int) : (term39 _92986 _92987) = (term92 _92986 _92987).
Proof. exact (MK_COMB (@lem6980469) (@lem6980447 _92986 _92987)). Qed.
Lemma lem6980471 (_92986 : int) (_92987 : int) : (term41 _92986 _92987) = (term93 _92986 _92987).
Proof. exact (MK_COMB (@lem6980470 _92986 _92987) (@lem6980468 _92986 _92987)). Qed.
Lemma lem6980472 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6980473 (_92987 : int) (_92986 : int) : (term46 _92986 _92987) = (term94 _92987 _92986).
Proof. exact (MK_COMB (@lem6980472) (@lem6980428 _92987 _92986)). Qed.
Lemma lem6980474 (_92986 : int) (_92987 : int) : (term48 _92986 _92987) = (term95 _92986 _92987).
Proof. exact (MK_COMB (@lem6980473 _92987 _92986) (@lem6980471 _92986 _92987)). Qed.
Lemma lem6980475 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6980476 (_92987 : int) : (term52 _92987) = (term96 _92987).
Proof. exact (MK_COMB (@lem6980475) (@lem6980389 _92987)). Qed.
Lemma lem6980477 (_92986 : int) (_92987 : int) : (term54 _92986 _92987) = (term97 _92986 _92987).
Proof. exact (MK_COMB (@lem6980476 _92987) (@lem6980474 _92986 _92987)). Qed.
Lemma lem6980478 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6980479 (_92986 : int) : (term52 _92986) = (term96 _92986).
Proof. exact (MK_COMB (@lem6980478) (@lem6980376 _92986)). Qed.
Lemma lem6980480 (_92986 : int) (_92987 : int) : (term59 _92986 _92987) = (term98 _92986 _92987).
Proof. exact (MK_COMB (@lem6980479 _92986) (@lem6980477 _92986 _92987)). Qed.
Lemma lem6980481 (_92986 : int) (_92987 : int) : (term60 _92986 _92987) = (term98 _92986 _92987).
Proof. exact (TRANS (@lem6980363 _92986 _92987) (@lem6980480 _92986 _92987)). Qed.
Lemma lem6980485 (t : Prop) : (term99 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6980486 (_92986 : int) (_92987 : int) : (term100 _92986 _92987) = (term98 _92986 _92987).
Proof. exact (@lem6980485 (term98 _92986 _92987)). Qed.
Lemma lem6980496 (t : Prop) : (t \/ t) = t.
Proof. exact (proj2 (@lem16485 t)). Qed.
Lemma lem6980497 (_92986 : int) (_92987 : int) : (term93 _92986 _92987) = (term91 _92986 _92987).
Proof. exact (@lem6980496 (term91 _92986 _92987)). Qed.
Lemma lem6980498 (_92987 : int) (_92986 : int) : (term94 _92987 _92986) = (term94 _92987 _92986).
Proof. exact (eq_refl (term94 _92987 _92986)). Qed.
Lemma lem6980499 (_92986 : int) (_92987 : int) : (term95 _92986 _92987) = (term101 _92986 _92987).
Proof. exact (MK_COMB (@lem6980498 _92987 _92986) (@lem6980497 _92986 _92987)). Qed.
Lemma lem6980502 (_92987 : int) : (term96 _92987) = (term96 _92987).
Proof. exact (eq_refl (term96 _92987)). Qed.
Lemma lem6980503 (_92986 : int) (_92987 : int) : (term97 _92986 _92987) = (term102 _92986 _92987).
Proof. exact (MK_COMB (@lem6980502 _92987) (@lem6980499 _92986 _92987)). Qed.
Lemma lem6980506 (_92986 : int) : (term96 _92986) = (term96 _92986).
Proof. exact (eq_refl (term96 _92986)). Qed.
Lemma lem6980507 (_92986 : int) (_92987 : int) : (term98 _92986 _92987) = (term103 _92986 _92987).
Proof. exact (MK_COMB (@lem6980506 _92986) (@lem6980503 _92986 _92987)). Qed.
Lemma lem6980547 (_92986 : int) (_92987 : int) : (term100 _92986 _92987) = (term103 _92986 _92987).
Proof. exact (TRANS (@lem6980486 _92986 _92987) (@lem6980507 _92986 _92987)). Qed.
Lemma lem6980548 (_92986 : int) : (term70 _92986) = (term104 _92986).
Proof. exact (@lem1988287 (real_of_int _92986) term67). Qed.
Lemma lem6980554 (_92986 : int) : (term105 _92986) = (term106 _92986).
Proof. exact (@lem1982792 (real_of_int _92986) term67). Qed.
Lemma lem6980556 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6980557 : term67 = term108.
Proof. exact (@lem6980556 (NUMERAL 0)). Qed.
Lemma lem6980559 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6980560 : term111 = term112.
Proof. exact (@lem6980559 term9). Qed.
Lemma lem6980561 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6980562 : term113 = term114.
Proof. exact (MK_COMB (@lem6980561) (@lem6980560)). Qed.
Lemma lem6980563 : term115 = term116.
Proof. exact (MK_COMB (@lem6980562) (@lem6980557)). Qed.
Lemma lem6980564 : term116 = term117.
Proof. exact (@lem1981613 term111 term67 term81 term81). Qed.
Lemma lem6980566 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6980567 : term120 = term121.
Proof. exact (@lem6980566 term9 term9). Qed.
Lemma lem6980568 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6980569 : term123 = term9.
Proof. exact (EQ_MP (@lem6980568) (@lem940073)). Qed.
Lemma lem6980570 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6980571 : term121 = term81.
Proof. exact (MK_COMB (@lem6980570) (@lem6980569)). Qed.
Lemma lem6980572 : term120 = term81.
Proof. exact (TRANS (@lem6980567) (@lem6980571)). Qed.
Lemma lem6980574 (x : nat) : (term124 x) = term67.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6980575 : term115 = term67.
Proof. exact (@lem6980574 term9). Qed.
Lemma lem6980576 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6980577 : term125 = term126.
Proof. exact (MK_COMB (@lem6980576) (@lem6980575)). Qed.
Lemma lem6980578 : term117 = term108.
Proof. exact (MK_COMB (@lem6980577) (@lem6980572)). Qed.
Lemma lem6980579 : term116 = term108.
Proof. exact (TRANS (@lem6980564) (@lem6980578)). Qed.
Lemma lem6980580 : term115 = term108.
Proof. exact (TRANS (@lem6980563) (@lem6980579)). Qed.
Lemma lem6980582 (x : real) : (term127 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6980583 : term108 = term67.
Proof. exact (@lem6980582 term67). Qed.
Lemma lem6980584 : term115 = term67.
Proof. exact (TRANS (@lem6980580) (@lem6980583)). Qed.
Lemma lem6980585 (_92986 : int) : (term82 _92986) = (term82 _92986).
Proof. exact (eq_refl (term82 _92986)). Qed.
Lemma lem6980586 (_92986 : int) : (term106 _92986) = (term128 _92986).
Proof. exact (MK_COMB (@lem6980585 _92986) (@lem6980584)). Qed.
Lemma lem6980587 (_92986 : int) : (term128 _92986) = (real_of_int _92986).
Proof. exact (@lem1982723 (real_of_int _92986)). Qed.
Lemma lem6980588 (_92986 : int) : (term106 _92986) = (real_of_int _92986).
Proof. exact (TRANS (@lem6980586 _92986) (@lem6980587 _92986)). Qed.
Lemma lem6980590 (_92986 : int) : (term105 _92986) = (real_of_int _92986).
Proof. exact (TRANS (@lem6980554 _92986) (@lem6980588 _92986)). Qed.
Lemma lem6980591 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6980592 (_92986 : int) : (term129 _92986) = (term130 _92986).
Proof. exact (MK_COMB (@lem6980591) (@lem6980590 _92986)). Qed.
Lemma lem6980593 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem6980594 (_92986 : int) : (term104 _92986) = (term131 _92986).
Proof. exact (MK_COMB (@lem6980592 _92986) (@lem6980593)). Qed.
Lemma lem6980595 (_92986 : int) : (term70 _92986) = (term131 _92986).
Proof. exact (TRANS (@lem6980548 _92986) (@lem6980594 _92986)). Qed.
Lemma lem6980596 (_92987 : int) : (term70 _92987) = (term104 _92987).
Proof. exact (@lem1988287 (real_of_int _92987) term67). Qed.
Lemma lem6980602 (_92987 : int) : (term105 _92987) = (term106 _92987).
Proof. exact (@lem1982792 (real_of_int _92987) term67). Qed.
Lemma lem6980604 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6980605 : term67 = term108.
Proof. exact (@lem6980604 (NUMERAL 0)). Qed.
Lemma lem6980607 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6980608 : term111 = term112.
Proof. exact (@lem6980607 term9). Qed.
Lemma lem6980609 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6980610 : term113 = term114.
Proof. exact (MK_COMB (@lem6980609) (@lem6980608)). Qed.
Lemma lem6980611 : term115 = term116.
Proof. exact (MK_COMB (@lem6980610) (@lem6980605)). Qed.
Lemma lem6980612 : term116 = term117.
Proof. exact (@lem1981613 term111 term67 term81 term81). Qed.
Lemma lem6980614 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6980615 : term120 = term121.
Proof. exact (@lem6980614 term9 term9). Qed.
Lemma lem6980616 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6980617 : term123 = term9.
Proof. exact (EQ_MP (@lem6980616) (@lem940073)). Qed.
Lemma lem6980618 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6980619 : term121 = term81.
Proof. exact (MK_COMB (@lem6980618) (@lem6980617)). Qed.
Lemma lem6980620 : term120 = term81.
Proof. exact (TRANS (@lem6980615) (@lem6980619)). Qed.
Lemma lem6980622 (x : nat) : (term124 x) = term67.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6980623 : term115 = term67.
Proof. exact (@lem6980622 term9). Qed.
Lemma lem6980624 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6980625 : term125 = term126.
Proof. exact (MK_COMB (@lem6980624) (@lem6980623)). Qed.
Lemma lem6980626 : term117 = term108.
Proof. exact (MK_COMB (@lem6980625) (@lem6980620)). Qed.
Lemma lem6980627 : term116 = term108.
Proof. exact (TRANS (@lem6980612) (@lem6980626)). Qed.
Lemma lem6980628 : term115 = term108.
Proof. exact (TRANS (@lem6980611) (@lem6980627)). Qed.
Lemma lem6980630 (x : real) : (term127 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6980631 : term108 = term67.
Proof. exact (@lem6980630 term67). Qed.
Lemma lem6980632 : term115 = term67.
Proof. exact (TRANS (@lem6980628) (@lem6980631)). Qed.
Lemma lem6980633 (_92987 : int) : (term82 _92987) = (term82 _92987).
Proof. exact (eq_refl (term82 _92987)). Qed.
Lemma lem6980634 (_92987 : int) : (term106 _92987) = (term128 _92987).
Proof. exact (MK_COMB (@lem6980633 _92987) (@lem6980632)). Qed.
Lemma lem6980635 (_92987 : int) : (term128 _92987) = (real_of_int _92987).
Proof. exact (@lem1982723 (real_of_int _92987)). Qed.
Lemma lem6980636 (_92987 : int) : (term106 _92987) = (real_of_int _92987).
Proof. exact (TRANS (@lem6980634 _92987) (@lem6980635 _92987)). Qed.
Lemma lem6980638 (_92987 : int) : (term105 _92987) = (real_of_int _92987).
Proof. exact (TRANS (@lem6980602 _92987) (@lem6980636 _92987)). Qed.
Lemma lem6980639 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6980640 (_92987 : int) : (term129 _92987) = (term130 _92987).
Proof. exact (MK_COMB (@lem6980639) (@lem6980638 _92987)). Qed.
Lemma lem6980641 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem6980642 (_92987 : int) : (term104 _92987) = (term131 _92987).
Proof. exact (MK_COMB (@lem6980640 _92987) (@lem6980641)). Qed.
Lemma lem6980643 (_92987 : int) : (term70 _92987) = (term131 _92987).
Proof. exact (TRANS (@lem6980596 _92987) (@lem6980642 _92987)). Qed.
Lemma lem6980644 (_92986 : int) (_92987 : int) : (term86 _92987 _92986) = (term132 _92986 _92987).
Proof. exact (@lem1988287 (term83 _92986) (term83 _92987)). Qed.
Lemma lem6980662 (_92986 : int) (_92987 : int) : (term133 _92986 _92987) = (term134 _92986 _92987).
Proof. exact (@lem1982792 (term83 _92986) (term83 _92987)). Qed.
Lemma lem6980663 (_92987 : int) : (term135 _92987) = (term136 _92987).
Proof. exact (@lem1982781 (real_of_int _92987) term111 term81). Qed.
Lemma lem6980665 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6980666 : term81 = term137.
Proof. exact (@lem6980665 term9). Qed.
Lemma lem6980668 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6980669 : term111 = term112.
Proof. exact (@lem6980668 term9). Qed.
Lemma lem6980670 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6980671 : term113 = term114.
Proof. exact (MK_COMB (@lem6980670) (@lem6980669)). Qed.
Lemma lem6980672 : term138 = term139.
Proof. exact (MK_COMB (@lem6980671) (@lem6980666)). Qed.
Lemma lem6980673 : term139 = term140.
Proof. exact (@lem1981613 term111 term81 term81 term81). Qed.
Lemma lem6980675 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6980676 : term120 = term121.
Proof. exact (@lem6980675 term9 term9). Qed.
Lemma lem6980677 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6980678 : term123 = term9.
Proof. exact (EQ_MP (@lem6980677) (@lem940073)). Qed.
Lemma lem6980679 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6980680 : term121 = term81.
Proof. exact (MK_COMB (@lem6980679) (@lem6980678)). Qed.
Lemma lem6980681 : term120 = term81.
Proof. exact (TRANS (@lem6980676) (@lem6980680)). Qed.
Lemma lem6980683 (m : nat) (n : nat) : (term141 m n) = (term142 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6980684 : term138 = term143.
Proof. exact (@lem6980683 term9 term9). Qed.
Lemma lem6980685 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6980686 : term123 = term9.
Proof. exact (EQ_MP (@lem6980685) (@lem940073)). Qed.
Lemma lem6980687 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6980688 : term121 = term81.
Proof. exact (MK_COMB (@lem6980687) (@lem6980686)). Qed.
Lemma lem6980689 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6980690 : term143 = term111.
Proof. exact (MK_COMB (@lem6980689) (@lem6980688)). Qed.
Lemma lem6980691 : term138 = term111.
Proof. exact (TRANS (@lem6980684) (@lem6980690)). Qed.
Lemma lem6980692 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6980693 : term144 = term145.
Proof. exact (MK_COMB (@lem6980692) (@lem6980691)). Qed.
Lemma lem6980694 : term140 = term112.
Proof. exact (MK_COMB (@lem6980693) (@lem6980681)). Qed.
Lemma lem6980695 : term139 = term112.
Proof. exact (TRANS (@lem6980673) (@lem6980694)). Qed.
Lemma lem6980696 : term138 = term112.
Proof. exact (TRANS (@lem6980672) (@lem6980695)). Qed.
Lemma lem6980698 (x : real) : (term127 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6980699 : term112 = term111.
Proof. exact (@lem6980698 term111). Qed.
Lemma lem6980700 : term138 = term111.
Proof. exact (TRANS (@lem6980696) (@lem6980699)). Qed.
Lemma lem6980703 (_92987 : int) : (term146 _92987) = (term146 _92987).
Proof. exact (eq_refl (term146 _92987)). Qed.
Lemma lem6980704 (_92987 : int) : (term136 _92987) = (term147 _92987).
Proof. exact (MK_COMB (@lem6980703 _92987) (@lem6980700)). Qed.
Lemma lem6980705 (_92987 : int) : (term135 _92987) = (term147 _92987).
Proof. exact (TRANS (@lem6980663 _92987) (@lem6980704 _92987)). Qed.
Lemma lem6980706 (_92986 : int) : (term148 _92986) = (term148 _92986).
Proof. exact (eq_refl (term148 _92986)). Qed.
Lemma lem6980707 (_92986 : int) (_92987 : int) : (term134 _92986 _92987) = (term149 _92986 _92987).
Proof. exact (MK_COMB (@lem6980706 _92986) (@lem6980705 _92987)). Qed.
Lemma lem6980708 (_92986 : int) (_92987 : int) : (term149 _92986 _92987) = (term150 _92986 _92987).
Proof. exact (@lem1982755 (real_of_int _92986) term81 (term147 _92987)). Qed.
Lemma lem6980709 (_92987 : int) : (term151 _92987) = (term152 _92987).
Proof. exact (@lem1982757 (term153 _92987) term81 term111). Qed.
Lemma lem6980711 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6980712 : term111 = term112.
Proof. exact (@lem6980711 term9). Qed.
Lemma lem6980714 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6980715 : term81 = term137.
Proof. exact (@lem6980714 term9). Qed.
Lemma lem6980716 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6980717 : term154 = term155.
Proof. exact (MK_COMB (@lem6980716) (@lem6980715)). Qed.
Lemma lem6980718 : term156 = term157.
Proof. exact (MK_COMB (@lem6980717) (@lem6980712)). Qed.
Lemma lem6980719 : term158.
Proof. exact (@lem1981473 term81 term81 term111 term81 term67 term81). Qed.
Lemma lem6980721 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6980722 : term160 = term161.
Proof. exact (@lem6980721 (NUMERAL 0) term9). Qed.
Lemma lem6980723 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6980724 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6980725 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6980724 h1) (fun h1 : term161 = True => @lem6980723)). Qed.
Lemma lem6980726 : term161 = True.
Proof. exact (EQ_MP (@lem6980725) (@lem6980723)). Qed.
Lemma lem6980727 : term160 = True.
Proof. exact (TRANS (@lem6980722) (@lem6980726)). Qed.
Lemma lem6980728 : True = term160.
Proof. exact (SYM (@lem6980727)). Qed.
Lemma lem6980729 : term160.
Proof. exact (EQ_MP (@lem6980728) (@lem0)). Qed.
Lemma lem6980730 : term163.
Proof. exact (@lem6980719 (@lem6980729)). Qed.
Lemma lem6980732 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6980733 : term160 = term161.
Proof. exact (@lem6980732 (NUMERAL 0) term9). Qed.
Lemma lem6980734 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6980735 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6980736 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6980735 h1) (fun h1 : term161 = True => @lem6980734)). Qed.
Lemma lem6980737 : term161 = True.
Proof. exact (EQ_MP (@lem6980736) (@lem6980734)). Qed.
Lemma lem6980738 : term160 = True.
Proof. exact (TRANS (@lem6980733) (@lem6980737)). Qed.
Lemma lem6980739 : True = term160.
Proof. exact (SYM (@lem6980738)). Qed.
Lemma lem6980740 : term160.
Proof. exact (EQ_MP (@lem6980739) (@lem0)). Qed.
Lemma lem6980741 : term164.
Proof. exact (@lem6980730 (@lem6980740)). Qed.
Lemma lem6980743 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6980744 : term160 = term161.
Proof. exact (@lem6980743 (NUMERAL 0) term9). Qed.
Lemma lem6980745 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6980746 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6980747 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6980746 h1) (fun h1 : term161 = True => @lem6980745)). Qed.
Lemma lem6980748 : term161 = True.
Proof. exact (EQ_MP (@lem6980747) (@lem6980745)). Qed.
Lemma lem6980749 : term160 = True.
Proof. exact (TRANS (@lem6980744) (@lem6980748)). Qed.
Lemma lem6980750 : True = term160.
Proof. exact (SYM (@lem6980749)). Qed.
Lemma lem6980751 : term160.
Proof. exact (EQ_MP (@lem6980750) (@lem0)). Qed.
Lemma lem6980752 : term165.
Proof. exact (@lem6980741 (@lem6980751)). Qed.
Lemma lem6980754 (m : nat) (n : nat) : (term141 m n) = (term142 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6980755 : term138 = term143.
Proof. exact (@lem6980754 term9 term9). Qed.
Lemma lem6980756 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6980757 : term123 = term9.
Proof. exact (EQ_MP (@lem6980756) (@lem940073)). Qed.
Lemma lem6980758 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6980759 : term121 = term81.
Proof. exact (MK_COMB (@lem6980758) (@lem6980757)). Qed.
Lemma lem6980760 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6980761 : term143 = term111.
Proof. exact (MK_COMB (@lem6980760) (@lem6980759)). Qed.
Lemma lem6980762 : term138 = term111.
Proof. exact (TRANS (@lem6980755) (@lem6980761)). Qed.
Lemma lem6980764 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6980765 : term120 = term121.
Proof. exact (@lem6980764 term9 term9). Qed.
Lemma lem6980766 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6980767 : term123 = term9.
Proof. exact (EQ_MP (@lem6980766) (@lem940073)). Qed.
Lemma lem6980768 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6980769 : term121 = term81.
Proof. exact (MK_COMB (@lem6980768) (@lem6980767)). Qed.
Lemma lem6980770 : term120 = term81.
Proof. exact (TRANS (@lem6980765) (@lem6980769)). Qed.
Lemma lem6980771 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6980772 : term166 = term154.
Proof. exact (MK_COMB (@lem6980771) (@lem6980770)). Qed.
Lemma lem6980773 : term167 = term156.
Proof. exact (MK_COMB (@lem6980772) (@lem6980762)). Qed.
Lemma lem6980775 (m : nat) : (term168 m) = term67.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem6980776 : term156 = term67.
Proof. exact (@lem6980775 term9). Qed.
Lemma lem6980777 : term167 = term67.
Proof. exact (TRANS (@lem6980773) (@lem6980776)). Qed.
Lemma lem6980778 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6980779 : term169 = term170.
Proof. exact (MK_COMB (@lem6980778) (@lem6980777)). Qed.
Lemma lem6980780 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem6980781 : term171 = term172.
Proof. exact (MK_COMB (@lem6980779) (@lem6980780)). Qed.
Lemma lem6980783 (x : nat) : (term173 x) = term67.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6980784 : term172 = term67.
Proof. exact (@lem6980783 term9). Qed.
Lemma lem6980785 : term171 = term67.
Proof. exact (TRANS (@lem6980781) (@lem6980784)). Qed.
Lemma lem6980787 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6980788 : term120 = term121.
Proof. exact (@lem6980787 term9 term9). Qed.
Lemma lem6980789 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6980790 : term123 = term9.
Proof. exact (EQ_MP (@lem6980789) (@lem940073)). Qed.
Lemma lem6980791 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6980792 : term121 = term81.
Proof. exact (MK_COMB (@lem6980791) (@lem6980790)). Qed.
Lemma lem6980793 : term120 = term81.
Proof. exact (TRANS (@lem6980788) (@lem6980792)). Qed.
Lemma lem6980794 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem6980795 : term174 = term172.
Proof. exact (MK_COMB (@lem6980794) (@lem6980793)). Qed.
Lemma lem6980797 (x : nat) : (term173 x) = term67.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6980798 : term172 = term67.
Proof. exact (@lem6980797 term9). Qed.
Lemma lem6980799 : term174 = term67.
Proof. exact (TRANS (@lem6980795) (@lem6980798)). Qed.
Lemma lem6980800 : term67 = term174.
Proof. exact (SYM (@lem6980799)). Qed.
Lemma lem6980801 : term171 = term174.
Proof. exact (TRANS (@lem6980785) (@lem6980800)). Qed.
Lemma lem6980802 : term157 = term108.
Proof. exact (@lem6980752 (@lem6980801)). Qed.
Lemma lem6980803 : term156 = term108.
Proof. exact (TRANS (@lem6980718) (@lem6980802)). Qed.
Lemma lem6980805 (x : real) : (term127 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6980806 : term108 = term67.
Proof. exact (@lem6980805 term67). Qed.
Lemma lem6980807 : term156 = term67.
Proof. exact (TRANS (@lem6980803) (@lem6980806)). Qed.
Lemma lem6980808 (_92987 : int) : (term146 _92987) = (term146 _92987).
Proof. exact (eq_refl (term146 _92987)). Qed.
Lemma lem6980809 (_92987 : int) : (term152 _92987) = (term175 _92987).
Proof. exact (MK_COMB (@lem6980808 _92987) (@lem6980807)). Qed.
Lemma lem6980810 (_92987 : int) : (term151 _92987) = (term175 _92987).
Proof. exact (TRANS (@lem6980709 _92987) (@lem6980809 _92987)). Qed.
Lemma lem6980811 (_92987 : int) : (term175 _92987) = (term153 _92987).
Proof. exact (@lem1982723 (term153 _92987)). Qed.
Lemma lem6980812 (_92987 : int) : (term151 _92987) = (term153 _92987).
Proof. exact (TRANS (@lem6980810 _92987) (@lem6980811 _92987)). Qed.
Lemma lem6980813 (_92986 : int) : (term82 _92986) = (term82 _92986).
Proof. exact (eq_refl (term82 _92986)). Qed.
Lemma lem6980814 (_92986 : int) (_92987 : int) : (term150 _92986 _92987) = (term176 _92986 _92987).
Proof. exact (MK_COMB (@lem6980813 _92986) (@lem6980812 _92987)). Qed.
Lemma lem6980815 (_92986 : int) (_92987 : int) : (term149 _92986 _92987) = (term176 _92986 _92987).
Proof. exact (TRANS (@lem6980708 _92986 _92987) (@lem6980814 _92986 _92987)). Qed.
Lemma lem6980816 (_92986 : int) (_92987 : int) : (term134 _92986 _92987) = (term176 _92986 _92987).
Proof. exact (TRANS (@lem6980707 _92986 _92987) (@lem6980815 _92986 _92987)). Qed.
Lemma lem6980818 (_92986 : int) (_92987 : int) : (term133 _92986 _92987) = (term176 _92986 _92987).
Proof. exact (TRANS (@lem6980662 _92986 _92987) (@lem6980816 _92986 _92987)). Qed.
Lemma lem6980819 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6980820 (_92986 : int) (_92987 : int) : (term177 _92986 _92987) = (term178 _92986 _92987).
Proof. exact (MK_COMB (@lem6980819) (@lem6980818 _92986 _92987)). Qed.
Lemma lem6980821 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem6980822 (_92986 : int) (_92987 : int) : (term132 _92986 _92987) = (term179 _92986 _92987).
Proof. exact (MK_COMB (@lem6980820 _92986 _92987) (@lem6980821)). Qed.
Lemma lem6980823 (_92986 : int) (_92987 : int) : (term86 _92987 _92986) = (term179 _92986 _92987).
Proof. exact (TRANS (@lem6980644 _92986 _92987) (@lem6980822 _92986 _92987)). Qed.
Lemma lem6980824 (_92986 : int) (_92987 : int) : (term62 _92987 _92986) = (term180 _92986 _92987).
Proof. exact (@lem1988287 (real_of_int _92986) (real_of_int _92987)). Qed.
Lemma lem6980837 (_92986 : int) (_92987 : int) : (term181 _92986 _92987) = (term176 _92986 _92987).
Proof. exact (@lem1982792 (real_of_int _92986) (real_of_int _92987)). Qed.
Lemma lem6980838 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6980839 (_92986 : int) (_92987 : int) : (term182 _92986 _92987) = (term178 _92986 _92987).
Proof. exact (MK_COMB (@lem6980838) (@lem6980837 _92986 _92987)). Qed.
Lemma lem6980840 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem6980841 (_92986 : int) (_92987 : int) : (term180 _92986 _92987) = (term179 _92986 _92987).
Proof. exact (MK_COMB (@lem6980839 _92986 _92987) (@lem6980840)). Qed.
Lemma lem6980842 (_92986 : int) (_92987 : int) : (term62 _92987 _92986) = (term179 _92986 _92987).
Proof. exact (TRANS (@lem6980824 _92986 _92987) (@lem6980841 _92986 _92987)). Qed.
Lemma lem6980843 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6980844 (_92986 : int) (_92987 : int) : (term88 _92987 _92986) = (term183 _92986 _92987).
Proof. exact (MK_COMB (@lem6980843) (@lem6980823 _92986 _92987)). Qed.
Lemma lem6980845 (_92986 : int) (_92987 : int) : (term89 _92987 _92986) = (term184 _92986 _92987).
Proof. exact (MK_COMB (@lem6980844 _92986 _92987) (@lem6980842 _92986 _92987)). Qed.
Lemma lem6980846 (_92987 : int) (_92986 : int) : (term91 _92986 _92987) = (term185 _92987 _92986).
Proof. exact (@lem1988287 (real_of_int _92987) (term83 _92986)). Qed.
Lemma lem6980858 (_92987 : int) (_92986 : int) : (term186 _92987 _92986) = (term187 _92987 _92986).
Proof. exact (@lem1982792 (real_of_int _92987) (term83 _92986)). Qed.
Lemma lem6980859 (_92986 : int) : (term135 _92986) = (term136 _92986).
Proof. exact (@lem1982781 (real_of_int _92986) term111 term81). Qed.
Lemma lem6980861 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6980862 : term81 = term137.
Proof. exact (@lem6980861 term9). Qed.
Lemma lem6980864 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6980865 : term111 = term112.
Proof. exact (@lem6980864 term9). Qed.
Lemma lem6980866 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6980867 : term113 = term114.
Proof. exact (MK_COMB (@lem6980866) (@lem6980865)). Qed.
Lemma lem6980868 : term138 = term139.
Proof. exact (MK_COMB (@lem6980867) (@lem6980862)). Qed.
Lemma lem6980869 : term139 = term140.
Proof. exact (@lem1981613 term111 term81 term81 term81). Qed.
Lemma lem6980871 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6980872 : term120 = term121.
Proof. exact (@lem6980871 term9 term9). Qed.
Lemma lem6980873 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6980874 : term123 = term9.
Proof. exact (EQ_MP (@lem6980873) (@lem940073)). Qed.
Lemma lem6980875 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6980876 : term121 = term81.
Proof. exact (MK_COMB (@lem6980875) (@lem6980874)). Qed.
Lemma lem6980877 : term120 = term81.
Proof. exact (TRANS (@lem6980872) (@lem6980876)). Qed.
Lemma lem6980879 (m : nat) (n : nat) : (term141 m n) = (term142 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6980880 : term138 = term143.
Proof. exact (@lem6980879 term9 term9). Qed.
Lemma lem6980881 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6980882 : term123 = term9.
Proof. exact (EQ_MP (@lem6980881) (@lem940073)). Qed.
Lemma lem6980883 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6980884 : term121 = term81.
Proof. exact (MK_COMB (@lem6980883) (@lem6980882)). Qed.
Lemma lem6980885 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6980886 : term143 = term111.
Proof. exact (MK_COMB (@lem6980885) (@lem6980884)). Qed.
Lemma lem6980887 : term138 = term111.
Proof. exact (TRANS (@lem6980880) (@lem6980886)). Qed.
Lemma lem6980888 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6980889 : term144 = term145.
Proof. exact (MK_COMB (@lem6980888) (@lem6980887)). Qed.
Lemma lem6980890 : term140 = term112.
Proof. exact (MK_COMB (@lem6980889) (@lem6980877)). Qed.
Lemma lem6980891 : term139 = term112.
Proof. exact (TRANS (@lem6980869) (@lem6980890)). Qed.
Lemma lem6980892 : term138 = term112.
Proof. exact (TRANS (@lem6980868) (@lem6980891)). Qed.
Lemma lem6980894 (x : real) : (term127 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6980895 : term112 = term111.
Proof. exact (@lem6980894 term111). Qed.
Lemma lem6980896 : term138 = term111.
Proof. exact (TRANS (@lem6980892) (@lem6980895)). Qed.
Lemma lem6980899 (_92986 : int) : (term146 _92986) = (term146 _92986).
Proof. exact (eq_refl (term146 _92986)). Qed.
Lemma lem6980900 (_92986 : int) : (term136 _92986) = (term147 _92986).
Proof. exact (MK_COMB (@lem6980899 _92986) (@lem6980896)). Qed.
Lemma lem6980901 (_92986 : int) : (term135 _92986) = (term147 _92986).
Proof. exact (TRANS (@lem6980859 _92986) (@lem6980900 _92986)). Qed.
Lemma lem6980902 (_92987 : int) : (term82 _92987) = (term82 _92987).
Proof. exact (eq_refl (term82 _92987)). Qed.
Lemma lem6980903 (_92987 : int) (_92986 : int) : (term187 _92987 _92986) = (term188 _92987 _92986).
Proof. exact (MK_COMB (@lem6980902 _92987) (@lem6980901 _92986)). Qed.
Lemma lem6980908 (_92986 : int) (_92987 : int) : (term188 _92987 _92986) = (term189 _92986 _92987).
Proof. exact (@lem1982757 (term153 _92986) (real_of_int _92987) term111). Qed.
Lemma lem6980909 (_92986 : int) (_92987 : int) : (term187 _92987 _92986) = (term189 _92986 _92987).
Proof. exact (TRANS (@lem6980903 _92987 _92986) (@lem6980908 _92986 _92987)). Qed.
Lemma lem6980911 (_92986 : int) (_92987 : int) : (term186 _92987 _92986) = (term189 _92986 _92987).
Proof. exact (TRANS (@lem6980858 _92987 _92986) (@lem6980909 _92986 _92987)). Qed.
Lemma lem6980912 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6980913 (_92986 : int) (_92987 : int) : (term190 _92987 _92986) = (term191 _92986 _92987).
Proof. exact (MK_COMB (@lem6980912) (@lem6980911 _92986 _92987)). Qed.
Lemma lem6980914 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem6980915 (_92986 : int) (_92987 : int) : (term185 _92987 _92986) = (term192 _92986 _92987).
Proof. exact (MK_COMB (@lem6980913 _92986 _92987) (@lem6980914)). Qed.
Lemma lem6980916 (_92986 : int) (_92987 : int) : (term91 _92986 _92987) = (term192 _92986 _92987).
Proof. exact (TRANS (@lem6980846 _92987 _92986) (@lem6980915 _92986 _92987)). Qed.
Lemma lem6980917 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6980918 (_92986 : int) (_92987 : int) : (term94 _92987 _92986) = (term193 _92986 _92987).
Proof. exact (MK_COMB (@lem6980917) (@lem6980845 _92986 _92987)). Qed.
Lemma lem6980919 (_92986 : int) (_92987 : int) : (term101 _92986 _92987) = (term194 _92986 _92987).
Proof. exact (MK_COMB (@lem6980918 _92986 _92987) (@lem6980916 _92986 _92987)). Qed.
Lemma lem6980920 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6980921 (_92987 : int) : (term96 _92987) = (term195 _92987).
Proof. exact (MK_COMB (@lem6980920) (@lem6980643 _92987)). Qed.
Lemma lem6980922 (_92986 : int) (_92987 : int) : (term102 _92986 _92987) = (term196 _92986 _92987).
Proof. exact (MK_COMB (@lem6980921 _92987) (@lem6980919 _92986 _92987)). Qed.
Lemma lem6980923 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6980924 (_92986 : int) : (term96 _92986) = (term195 _92986).
Proof. exact (MK_COMB (@lem6980923) (@lem6980595 _92986)). Qed.
Lemma lem6980925 (_92986 : int) (_92987 : int) : (term103 _92986 _92987) = (term197 _92986 _92987).
Proof. exact (MK_COMB (@lem6980924 _92986) (@lem6980922 _92986 _92987)). Qed.
Lemma lem6980932 (_92986 : int) (_92987 : int) : (term100 _92986 _92987) = (term197 _92986 _92987).
Proof. exact (TRANS (@lem6980547 _92986 _92987) (@lem6980925 _92986 _92987)). Qed.
Lemma lem6980949 (_92986 : int) (_92987 : int) : (term194 _92986 _92987) = (term198 _92986 _92987).
Proof. exact (@lem19367 (term179 _92986 _92987) (term179 _92986 _92987) (term192 _92986 _92987)). Qed.
Lemma lem6980952 (_92987 : int) : (term195 _92987) = (term195 _92987).
Proof. exact (eq_refl (term195 _92987)). Qed.
Lemma lem6980953 (_92986 : int) (_92987 : int) : (term196 _92986 _92987) = (term199 _92986 _92987).
Proof. exact (MK_COMB (@lem6980952 _92987) (@lem6980949 _92986 _92987)). Qed.
Lemma lem6980960 (_92986 : int) (_92987 : int) : (term199 _92986 _92987) = (term200 _92986 _92987).
Proof. exact (@lem19158 (term201 _92986 _92987) (term131 _92987) (term201 _92986 _92987)). Qed.
Lemma lem6980961 (_92986 : int) (_92987 : int) : (term196 _92986 _92987) = (term200 _92986 _92987).
Proof. exact (TRANS (@lem6980953 _92986 _92987) (@lem6980960 _92986 _92987)). Qed.
Lemma lem6980964 (_92986 : int) : (term195 _92986) = (term195 _92986).
Proof. exact (eq_refl (term195 _92986)). Qed.
Lemma lem6980965 (_92986 : int) (_92987 : int) : (term197 _92986 _92987) = (term202 _92986 _92987).
Proof. exact (MK_COMB (@lem6980964 _92986) (@lem6980961 _92986 _92987)). Qed.
Lemma lem6980972 (_92986 : int) (_92987 : int) : (term202 _92986 _92987) = (term203 _92986 _92987).
Proof. exact (@lem19158 (term204 _92986 _92987) (term131 _92986) (term204 _92986 _92987)). Qed.
Lemma lem6980973 (_92986 : int) (_92987 : int) : (term197 _92986 _92987) = (term203 _92986 _92987).
Proof. exact (TRANS (@lem6980965 _92986 _92987) (@lem6980972 _92986 _92987)). Qed.
Lemma lem6980974 (_92986 : int) (_92987 : int) : (term100 _92986 _92987) = (term203 _92986 _92987).
Proof. exact (TRANS (@lem6980932 _92986 _92987) (@lem6980973 _92986 _92987)). Qed.
Lemma lem6980984 (_92986 : int) (_92987 : int) (h1 : term203 _92986 _92987) : term203 _92986 _92987.
Proof. exact (h1). Qed.
Lemma lem6980985 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term205 _92986 _92987.
Proof. exact (h1). Qed.
Lemma lem6980986 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term204 _92986 _92987.
Proof. exact (proj2 (@lem6980985 _92986 _92987 h1)). Qed.
Lemma lem6980988 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term201 _92986 _92987.
Proof. exact (proj2 (@lem6980986 _92986 _92987 h1)). Qed.
Lemma lem6980990 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term192 _92986 _92987.
Proof. exact (proj2 (@lem6980988 _92986 _92987 h1)). Qed.
Lemma lem6980991 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term179 _92986 _92987.
Proof. exact (proj1 (@lem6980988 _92986 _92987 h1)). Qed.
Lemma lem6980993 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6980994 : term206 = term160.
Proof. exact (@lem6980993 term67 term81). Qed.
Lemma lem6980996 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6980997 : term81 = term137.
Proof. exact (@lem6980996 term9). Qed.
Lemma lem6980999 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6981000 : term67 = term108.
Proof. exact (@lem6980999 (NUMERAL 0)). Qed.
Lemma lem6981001 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6981002 : term207 = term208.
Proof. exact (MK_COMB (@lem6981001) (@lem6981000)). Qed.
Lemma lem6981003 : term160 = term209.
Proof. exact (MK_COMB (@lem6981002) (@lem6980997)). Qed.
Lemma lem6981004 : term210.
Proof. exact (@lem1980255 term67 term81 term81 term81). Qed.
Lemma lem6981006 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981007 : term160 = term161.
Proof. exact (@lem6981006 (NUMERAL 0) term9). Qed.
Lemma lem6981008 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981009 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981010 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981009 h1) (fun h1 : term161 = True => @lem6981008)). Qed.
Lemma lem6981011 : term161 = True.
Proof. exact (EQ_MP (@lem6981010) (@lem6981008)). Qed.
Lemma lem6981012 : term160 = True.
Proof. exact (TRANS (@lem6981007) (@lem6981011)). Qed.
Lemma lem6981013 : True = term160.
Proof. exact (SYM (@lem6981012)). Qed.
Lemma lem6981014 : term160.
Proof. exact (EQ_MP (@lem6981013) (@lem0)). Qed.
Lemma lem6981015 : term211.
Proof. exact (@lem6981004 (@lem6981014)). Qed.
Lemma lem6981017 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981018 : term160 = term161.
Proof. exact (@lem6981017 (NUMERAL 0) term9). Qed.
Lemma lem6981019 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981020 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981021 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981020 h1) (fun h1 : term161 = True => @lem6981019)). Qed.
Lemma lem6981022 : term161 = True.
Proof. exact (EQ_MP (@lem6981021) (@lem6981019)). Qed.
Lemma lem6981023 : term160 = True.
Proof. exact (TRANS (@lem6981018) (@lem6981022)). Qed.
Lemma lem6981024 : True = term160.
Proof. exact (SYM (@lem6981023)). Qed.
Lemma lem6981025 : term160.
Proof. exact (EQ_MP (@lem6981024) (@lem0)). Qed.
Lemma lem6981026 : term209 = term212.
Proof. exact (@lem6981015 (@lem6981025)). Qed.
Lemma lem6981028 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6981029 : term120 = term121.
Proof. exact (@lem6981028 term9 term9). Qed.
Lemma lem6981030 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6981031 : term123 = term9.
Proof. exact (EQ_MP (@lem6981030) (@lem940073)). Qed.
Lemma lem6981032 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6981033 : term121 = term81.
Proof. exact (MK_COMB (@lem6981032) (@lem6981031)). Qed.
Lemma lem6981034 : term120 = term81.
Proof. exact (TRANS (@lem6981029) (@lem6981033)). Qed.
Lemma lem6981036 (x : nat) : (term173 x) = term67.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6981037 : term172 = term67.
Proof. exact (@lem6981036 term9). Qed.
Lemma lem6981038 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6981039 : term213 = term207.
Proof. exact (MK_COMB (@lem6981038) (@lem6981037)). Qed.
Lemma lem6981040 : term212 = term160.
Proof. exact (MK_COMB (@lem6981039) (@lem6981034)). Qed.
Lemma lem6981042 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981043 : term160 = term161.
Proof. exact (@lem6981042 (NUMERAL 0) term9). Qed.
Lemma lem6981044 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981045 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981046 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981045 h1) (fun h1 : term161 = True => @lem6981044)). Qed.
Lemma lem6981047 : term161 = True.
Proof. exact (EQ_MP (@lem6981046) (@lem6981044)). Qed.
Lemma lem6981048 : term160 = True.
Proof. exact (TRANS (@lem6981043) (@lem6981047)). Qed.
Lemma lem6981049 : term212 = True.
Proof. exact (TRANS (@lem6981040) (@lem6981048)). Qed.
Lemma lem6981050 : term209 = True.
Proof. exact (TRANS (@lem6981026) (@lem6981049)). Qed.
Lemma lem6981051 : term160 = True.
Proof. exact (TRANS (@lem6981003) (@lem6981050)). Qed.
Lemma lem6981052 : term206 = True.
Proof. exact (TRANS (@lem6980994) (@lem6981051)). Qed.
Lemma lem6981053 : True = term206.
Proof. exact (SYM (@lem6981052)). Qed.
Lemma lem6981054 : term206.
Proof. exact (EQ_MP (@lem6981053) (@lem0)). Qed.
Lemma lem6981055 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term214 _92986 _92987.
Proof. exact (conj (@lem6981054) (@lem6980991 _92986 _92987 h1)). Qed.
Lemma lem6981057 (x : real) (y : real) : term215 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6981058 (_92986 : int) (_92987 : int) : term216 _92986 _92987.
Proof. exact (@lem6981057 term81 (term176 _92986 _92987)). Qed.
Lemma lem6981059 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term217 _92986 _92987.
Proof. exact (@lem6981058 _92986 _92987 (@lem6981055 _92986 _92987 h1)). Qed.
Lemma lem6981060 (_92986 : int) (_92987 : int) : (term218 _92986 _92987) = (term176 _92986 _92987).
Proof. exact (@lem1982733 (term176 _92986 _92987)). Qed.
Lemma lem6981061 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6981062 (_92986 : int) (_92987 : int) : (term219 _92986 _92987) = (term178 _92986 _92987).
Proof. exact (MK_COMB (@lem6981061) (@lem6981060 _92986 _92987)). Qed.
Lemma lem6981063 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem6981064 (_92986 : int) (_92987 : int) : (term217 _92986 _92987) = (term179 _92986 _92987).
Proof. exact (MK_COMB (@lem6981062 _92986 _92987) (@lem6981063)). Qed.
Lemma lem6981065 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term179 _92986 _92987.
Proof. exact (EQ_MP (@lem6981064 _92986 _92987) (@lem6981059 _92986 _92987 h1)). Qed.
Lemma lem6981067 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6981068 : term206 = term160.
Proof. exact (@lem6981067 term67 term81). Qed.
Lemma lem6981070 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6981071 : term81 = term137.
Proof. exact (@lem6981070 term9). Qed.
Lemma lem6981073 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6981074 : term67 = term108.
Proof. exact (@lem6981073 (NUMERAL 0)). Qed.
Lemma lem6981075 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6981076 : term207 = term208.
Proof. exact (MK_COMB (@lem6981075) (@lem6981074)). Qed.
Lemma lem6981077 : term160 = term209.
Proof. exact (MK_COMB (@lem6981076) (@lem6981071)). Qed.
Lemma lem6981078 : term210.
Proof. exact (@lem1980255 term67 term81 term81 term81). Qed.
Lemma lem6981080 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981081 : term160 = term161.
Proof. exact (@lem6981080 (NUMERAL 0) term9). Qed.
Lemma lem6981082 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981083 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981084 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981083 h1) (fun h1 : term161 = True => @lem6981082)). Qed.
Lemma lem6981085 : term161 = True.
Proof. exact (EQ_MP (@lem6981084) (@lem6981082)). Qed.
Lemma lem6981086 : term160 = True.
Proof. exact (TRANS (@lem6981081) (@lem6981085)). Qed.
Lemma lem6981087 : True = term160.
Proof. exact (SYM (@lem6981086)). Qed.
Lemma lem6981088 : term160.
Proof. exact (EQ_MP (@lem6981087) (@lem0)). Qed.
Lemma lem6981089 : term211.
Proof. exact (@lem6981078 (@lem6981088)). Qed.
Lemma lem6981091 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981092 : term160 = term161.
Proof. exact (@lem6981091 (NUMERAL 0) term9). Qed.
Lemma lem6981093 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981094 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981095 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981094 h1) (fun h1 : term161 = True => @lem6981093)). Qed.
Lemma lem6981096 : term161 = True.
Proof. exact (EQ_MP (@lem6981095) (@lem6981093)). Qed.
Lemma lem6981097 : term160 = True.
Proof. exact (TRANS (@lem6981092) (@lem6981096)). Qed.
Lemma lem6981098 : True = term160.
Proof. exact (SYM (@lem6981097)). Qed.
Lemma lem6981099 : term160.
Proof. exact (EQ_MP (@lem6981098) (@lem0)). Qed.
Lemma lem6981100 : term209 = term212.
Proof. exact (@lem6981089 (@lem6981099)). Qed.
Lemma lem6981102 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6981103 : term120 = term121.
Proof. exact (@lem6981102 term9 term9). Qed.
Lemma lem6981104 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6981105 : term123 = term9.
Proof. exact (EQ_MP (@lem6981104) (@lem940073)). Qed.
Lemma lem6981106 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6981107 : term121 = term81.
Proof. exact (MK_COMB (@lem6981106) (@lem6981105)). Qed.
Lemma lem6981108 : term120 = term81.
Proof. exact (TRANS (@lem6981103) (@lem6981107)). Qed.
Lemma lem6981110 (x : nat) : (term173 x) = term67.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6981111 : term172 = term67.
Proof. exact (@lem6981110 term9). Qed.
Lemma lem6981112 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6981113 : term213 = term207.
Proof. exact (MK_COMB (@lem6981112) (@lem6981111)). Qed.
Lemma lem6981114 : term212 = term160.
Proof. exact (MK_COMB (@lem6981113) (@lem6981108)). Qed.
Lemma lem6981116 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981117 : term160 = term161.
Proof. exact (@lem6981116 (NUMERAL 0) term9). Qed.
Lemma lem6981118 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981119 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981120 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981119 h1) (fun h1 : term161 = True => @lem6981118)). Qed.
Lemma lem6981121 : term161 = True.
Proof. exact (EQ_MP (@lem6981120) (@lem6981118)). Qed.
Lemma lem6981122 : term160 = True.
Proof. exact (TRANS (@lem6981117) (@lem6981121)). Qed.
Lemma lem6981123 : term212 = True.
Proof. exact (TRANS (@lem6981114) (@lem6981122)). Qed.
Lemma lem6981124 : term209 = True.
Proof. exact (TRANS (@lem6981100) (@lem6981123)). Qed.
Lemma lem6981125 : term160 = True.
Proof. exact (TRANS (@lem6981077) (@lem6981124)). Qed.
Lemma lem6981126 : term206 = True.
Proof. exact (TRANS (@lem6981068) (@lem6981125)). Qed.
Lemma lem6981127 : True = term206.
Proof. exact (SYM (@lem6981126)). Qed.
Lemma lem6981128 : term206.
Proof. exact (EQ_MP (@lem6981127) (@lem0)). Qed.
Lemma lem6981129 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term220 _92986 _92987.
Proof. exact (conj (@lem6981128) (@lem6980990 _92986 _92987 h1)). Qed.
Lemma lem6981131 (x : real) (y : real) : term215 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6981132 (_92986 : int) (_92987 : int) : term221 _92986 _92987.
Proof. exact (@lem6981131 term81 (term189 _92986 _92987)). Qed.
Lemma lem6981133 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term222 _92986 _92987.
Proof. exact (@lem6981132 _92986 _92987 (@lem6981129 _92986 _92987 h1)). Qed.
Lemma lem6981134 (_92986 : int) (_92987 : int) : (term223 _92986 _92987) = (term189 _92986 _92987).
Proof. exact (@lem1982733 (term189 _92986 _92987)). Qed.
Lemma lem6981135 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6981136 (_92986 : int) (_92987 : int) : (term224 _92986 _92987) = (term191 _92986 _92987).
Proof. exact (MK_COMB (@lem6981135) (@lem6981134 _92986 _92987)). Qed.
Lemma lem6981137 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem6981138 (_92986 : int) (_92987 : int) : (term222 _92986 _92987) = (term192 _92986 _92987).
Proof. exact (MK_COMB (@lem6981136 _92986 _92987) (@lem6981137)). Qed.
Lemma lem6981139 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term192 _92986 _92987.
Proof. exact (EQ_MP (@lem6981138 _92986 _92987) (@lem6981133 _92986 _92987 h1)). Qed.
Lemma lem6981140 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term225 _92986 _92987.
Proof. exact (conj (@lem6981139 _92986 _92987 h1) (@lem6981065 _92986 _92987 h1)). Qed.
Lemma lem6981142 (x : real) (y : real) : term226 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem6981143 (_92986 : int) (_92987 : int) : term227 _92986 _92987.
Proof. exact (@lem6981142 (term189 _92986 _92987) (term176 _92986 _92987)). Qed.
Lemma lem6981144 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term228 _92986 _92987.
Proof. exact (@lem6981143 _92986 _92987 (@lem6981140 _92986 _92987 h1)). Qed.
Lemma lem6981145 (_92986 : int) (_92987 : int) : (term229 _92986 _92987) = (term230 _92986 _92987).
Proof. exact (@lem1982753 (term153 _92986) (real_of_int _92986) (term231 _92987) (term153 _92987)). Qed.
Lemma lem6981146 (_92986 : int) : (term232 _92986) = (term233 _92986).
Proof. exact (@lem1982713 term111 (real_of_int _92986)). Qed.
Lemma lem6981148 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6981149 : term81 = term137.
Proof. exact (@lem6981148 term9). Qed.
Lemma lem6981151 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6981152 : term111 = term112.
Proof. exact (@lem6981151 term9). Qed.
Lemma lem6981153 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6981154 : term234 = term235.
Proof. exact (MK_COMB (@lem6981153) (@lem6981152)). Qed.
Lemma lem6981155 : term236 = term237.
Proof. exact (MK_COMB (@lem6981154) (@lem6981149)). Qed.
Lemma lem6981156 : term238.
Proof. exact (@lem1981473 term111 term81 term81 term81 term67 term81). Qed.
Lemma lem6981158 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981159 : term160 = term161.
Proof. exact (@lem6981158 (NUMERAL 0) term9). Qed.
Lemma lem6981160 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981161 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981162 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981161 h1) (fun h1 : term161 = True => @lem6981160)). Qed.
Lemma lem6981163 : term161 = True.
Proof. exact (EQ_MP (@lem6981162) (@lem6981160)). Qed.
Lemma lem6981164 : term160 = True.
Proof. exact (TRANS (@lem6981159) (@lem6981163)). Qed.
Lemma lem6981165 : True = term160.
Proof. exact (SYM (@lem6981164)). Qed.
Lemma lem6981166 : term160.
Proof. exact (EQ_MP (@lem6981165) (@lem0)). Qed.
Lemma lem6981167 : term239.
Proof. exact (@lem6981156 (@lem6981166)). Qed.
Lemma lem6981169 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981170 : term160 = term161.
Proof. exact (@lem6981169 (NUMERAL 0) term9). Qed.
Lemma lem6981171 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981172 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981173 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981172 h1) (fun h1 : term161 = True => @lem6981171)). Qed.
Lemma lem6981174 : term161 = True.
Proof. exact (EQ_MP (@lem6981173) (@lem6981171)). Qed.
Lemma lem6981175 : term160 = True.
Proof. exact (TRANS (@lem6981170) (@lem6981174)). Qed.
Lemma lem6981176 : True = term160.
Proof. exact (SYM (@lem6981175)). Qed.
Lemma lem6981177 : term160.
Proof. exact (EQ_MP (@lem6981176) (@lem0)). Qed.
Lemma lem6981178 : term240.
Proof. exact (@lem6981167 (@lem6981177)). Qed.
Lemma lem6981180 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981181 : term160 = term161.
Proof. exact (@lem6981180 (NUMERAL 0) term9). Qed.
Lemma lem6981182 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981183 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981184 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981183 h1) (fun h1 : term161 = True => @lem6981182)). Qed.
Lemma lem6981185 : term161 = True.
Proof. exact (EQ_MP (@lem6981184) (@lem6981182)). Qed.
Lemma lem6981186 : term160 = True.
Proof. exact (TRANS (@lem6981181) (@lem6981185)). Qed.
Lemma lem6981187 : True = term160.
Proof. exact (SYM (@lem6981186)). Qed.
Lemma lem6981188 : term160.
Proof. exact (EQ_MP (@lem6981187) (@lem0)). Qed.
Lemma lem6981189 : term241.
Proof. exact (@lem6981178 (@lem6981188)). Qed.
Lemma lem6981191 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6981192 : term120 = term121.
Proof. exact (@lem6981191 term9 term9). Qed.
Lemma lem6981193 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6981194 : term123 = term9.
Proof. exact (EQ_MP (@lem6981193) (@lem940073)). Qed.
Lemma lem6981195 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6981196 : term121 = term81.
Proof. exact (MK_COMB (@lem6981195) (@lem6981194)). Qed.
Lemma lem6981197 : term120 = term81.
Proof. exact (TRANS (@lem6981192) (@lem6981196)). Qed.
Lemma lem6981199 (m : nat) (n : nat) : (term141 m n) = (term142 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6981200 : term138 = term143.
Proof. exact (@lem6981199 term9 term9). Qed.
Lemma lem6981201 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6981202 : term123 = term9.
Proof. exact (EQ_MP (@lem6981201) (@lem940073)). Qed.
Lemma lem6981203 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6981204 : term121 = term81.
Proof. exact (MK_COMB (@lem6981203) (@lem6981202)). Qed.
Lemma lem6981205 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6981206 : term143 = term111.
Proof. exact (MK_COMB (@lem6981205) (@lem6981204)). Qed.
Lemma lem6981207 : term138 = term111.
Proof. exact (TRANS (@lem6981200) (@lem6981206)). Qed.
Lemma lem6981208 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6981209 : term242 = term234.
Proof. exact (MK_COMB (@lem6981208) (@lem6981207)). Qed.
Lemma lem6981210 : term243 = term236.
Proof. exact (MK_COMB (@lem6981209) (@lem6981197)). Qed.
Lemma lem6981212 (m : nat) : (term244 m) = term67.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6981213 : term236 = term67.
Proof. exact (@lem6981212 term9). Qed.
Lemma lem6981214 : term243 = term67.
Proof. exact (TRANS (@lem6981210) (@lem6981213)). Qed.
Lemma lem6981215 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6981216 : term245 = term170.
Proof. exact (MK_COMB (@lem6981215) (@lem6981214)). Qed.
Lemma lem6981217 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem6981218 : term246 = term172.
Proof. exact (MK_COMB (@lem6981216) (@lem6981217)). Qed.
Lemma lem6981220 (x : nat) : (term173 x) = term67.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6981221 : term172 = term67.
Proof. exact (@lem6981220 term9). Qed.
Lemma lem6981222 : term246 = term67.
Proof. exact (TRANS (@lem6981218) (@lem6981221)). Qed.
Lemma lem6981224 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6981225 : term120 = term121.
Proof. exact (@lem6981224 term9 term9). Qed.
Lemma lem6981226 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6981227 : term123 = term9.
Proof. exact (EQ_MP (@lem6981226) (@lem940073)). Qed.
Lemma lem6981228 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6981229 : term121 = term81.
Proof. exact (MK_COMB (@lem6981228) (@lem6981227)). Qed.
Lemma lem6981230 : term120 = term81.
Proof. exact (TRANS (@lem6981225) (@lem6981229)). Qed.
Lemma lem6981231 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem6981232 : term174 = term172.
Proof. exact (MK_COMB (@lem6981231) (@lem6981230)). Qed.
Lemma lem6981234 (x : nat) : (term173 x) = term67.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6981235 : term172 = term67.
Proof. exact (@lem6981234 term9). Qed.
Lemma lem6981236 : term174 = term67.
Proof. exact (TRANS (@lem6981232) (@lem6981235)). Qed.
Lemma lem6981237 : term67 = term174.
Proof. exact (SYM (@lem6981236)). Qed.
Lemma lem6981238 : term246 = term174.
Proof. exact (TRANS (@lem6981222) (@lem6981237)). Qed.
Lemma lem6981239 : term237 = term108.
Proof. exact (@lem6981189 (@lem6981238)). Qed.
Lemma lem6981240 : term236 = term108.
Proof. exact (TRANS (@lem6981155) (@lem6981239)). Qed.
Lemma lem6981242 (x : real) : (term127 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6981243 : term108 = term67.
Proof. exact (@lem6981242 term67). Qed.
Lemma lem6981244 : term236 = term67.
Proof. exact (TRANS (@lem6981240) (@lem6981243)). Qed.
Lemma lem6981245 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6981246 : term247 = term170.
Proof. exact (MK_COMB (@lem6981245) (@lem6981244)). Qed.
Lemma lem6981247 (_92986 : int) : (real_of_int _92986) = (real_of_int _92986).
Proof. exact (eq_refl (real_of_int _92986)). Qed.
Lemma lem6981248 (_92986 : int) : (term233 _92986) = (term248 _92986).
Proof. exact (MK_COMB (@lem6981246) (@lem6981247 _92986)). Qed.
Lemma lem6981249 (_92986 : int) : (term232 _92986) = (term248 _92986).
Proof. exact (TRANS (@lem6981146 _92986) (@lem6981248 _92986)). Qed.
Lemma lem6981250 (_92986 : int) : (term248 _92986) = term67.
Proof. exact (@lem1982719 (real_of_int _92986)). Qed.
Lemma lem6981251 (_92986 : int) : (term232 _92986) = term67.
Proof. exact (TRANS (@lem6981249 _92986) (@lem6981250 _92986)). Qed.
Lemma lem6981252 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6981253 (_92986 : int) : (term249 _92986) = term250.
Proof. exact (MK_COMB (@lem6981252) (@lem6981251 _92986)). Qed.
Lemma lem6981254 (_92987 : int) : (term251 _92987) = (term252 _92987).
Proof. exact (@lem1982759 (real_of_int _92987) (term153 _92987) term111). Qed.
Lemma lem6981255 (_92987 : int) : (term253 _92987) = (term233 _92987).
Proof. exact (@lem1982715 term111 (real_of_int _92987)). Qed.
Lemma lem6981257 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6981258 : term81 = term137.
Proof. exact (@lem6981257 term9). Qed.
Lemma lem6981260 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6981261 : term111 = term112.
Proof. exact (@lem6981260 term9). Qed.
Lemma lem6981262 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6981263 : term234 = term235.
Proof. exact (MK_COMB (@lem6981262) (@lem6981261)). Qed.
Lemma lem6981264 : term236 = term237.
Proof. exact (MK_COMB (@lem6981263) (@lem6981258)). Qed.
Lemma lem6981265 : term238.
Proof. exact (@lem1981473 term111 term81 term81 term81 term67 term81). Qed.
Lemma lem6981267 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981268 : term160 = term161.
Proof. exact (@lem6981267 (NUMERAL 0) term9). Qed.
Lemma lem6981269 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981270 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981271 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981270 h1) (fun h1 : term161 = True => @lem6981269)). Qed.
Lemma lem6981272 : term161 = True.
Proof. exact (EQ_MP (@lem6981271) (@lem6981269)). Qed.
Lemma lem6981273 : term160 = True.
Proof. exact (TRANS (@lem6981268) (@lem6981272)). Qed.
Lemma lem6981274 : True = term160.
Proof. exact (SYM (@lem6981273)). Qed.
Lemma lem6981275 : term160.
Proof. exact (EQ_MP (@lem6981274) (@lem0)). Qed.
Lemma lem6981276 : term239.
Proof. exact (@lem6981265 (@lem6981275)). Qed.
Lemma lem6981278 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981279 : term160 = term161.
Proof. exact (@lem6981278 (NUMERAL 0) term9). Qed.
Lemma lem6981280 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981281 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981282 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981281 h1) (fun h1 : term161 = True => @lem6981280)). Qed.
Lemma lem6981283 : term161 = True.
Proof. exact (EQ_MP (@lem6981282) (@lem6981280)). Qed.
Lemma lem6981284 : term160 = True.
Proof. exact (TRANS (@lem6981279) (@lem6981283)). Qed.
Lemma lem6981285 : True = term160.
Proof. exact (SYM (@lem6981284)). Qed.
Lemma lem6981286 : term160.
Proof. exact (EQ_MP (@lem6981285) (@lem0)). Qed.
Lemma lem6981287 : term240.
Proof. exact (@lem6981276 (@lem6981286)). Qed.
Lemma lem6981289 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981290 : term160 = term161.
Proof. exact (@lem6981289 (NUMERAL 0) term9). Qed.
Lemma lem6981291 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981292 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981293 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981292 h1) (fun h1 : term161 = True => @lem6981291)). Qed.
Lemma lem6981294 : term161 = True.
Proof. exact (EQ_MP (@lem6981293) (@lem6981291)). Qed.
Lemma lem6981295 : term160 = True.
Proof. exact (TRANS (@lem6981290) (@lem6981294)). Qed.
Lemma lem6981296 : True = term160.
Proof. exact (SYM (@lem6981295)). Qed.
Lemma lem6981297 : term160.
Proof. exact (EQ_MP (@lem6981296) (@lem0)). Qed.
Lemma lem6981298 : term241.
Proof. exact (@lem6981287 (@lem6981297)). Qed.
Lemma lem6981300 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6981301 : term120 = term121.
Proof. exact (@lem6981300 term9 term9). Qed.
Lemma lem6981302 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6981303 : term123 = term9.
Proof. exact (EQ_MP (@lem6981302) (@lem940073)). Qed.
Lemma lem6981304 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6981305 : term121 = term81.
Proof. exact (MK_COMB (@lem6981304) (@lem6981303)). Qed.
Lemma lem6981306 : term120 = term81.
Proof. exact (TRANS (@lem6981301) (@lem6981305)). Qed.
Lemma lem6981308 (m : nat) (n : nat) : (term141 m n) = (term142 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6981309 : term138 = term143.
Proof. exact (@lem6981308 term9 term9). Qed.
Lemma lem6981310 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6981311 : term123 = term9.
Proof. exact (EQ_MP (@lem6981310) (@lem940073)). Qed.
Lemma lem6981312 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6981313 : term121 = term81.
Proof. exact (MK_COMB (@lem6981312) (@lem6981311)). Qed.
Lemma lem6981314 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6981315 : term143 = term111.
Proof. exact (MK_COMB (@lem6981314) (@lem6981313)). Qed.
Lemma lem6981316 : term138 = term111.
Proof. exact (TRANS (@lem6981309) (@lem6981315)). Qed.
Lemma lem6981317 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6981318 : term242 = term234.
Proof. exact (MK_COMB (@lem6981317) (@lem6981316)). Qed.
Lemma lem6981319 : term243 = term236.
Proof. exact (MK_COMB (@lem6981318) (@lem6981306)). Qed.
Lemma lem6981321 (m : nat) : (term244 m) = term67.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6981322 : term236 = term67.
Proof. exact (@lem6981321 term9). Qed.
Lemma lem6981323 : term243 = term67.
Proof. exact (TRANS (@lem6981319) (@lem6981322)). Qed.
Lemma lem6981324 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6981325 : term245 = term170.
Proof. exact (MK_COMB (@lem6981324) (@lem6981323)). Qed.
Lemma lem6981326 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem6981327 : term246 = term172.
Proof. exact (MK_COMB (@lem6981325) (@lem6981326)). Qed.
Lemma lem6981329 (x : nat) : (term173 x) = term67.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6981330 : term172 = term67.
Proof. exact (@lem6981329 term9). Qed.
Lemma lem6981331 : term246 = term67.
Proof. exact (TRANS (@lem6981327) (@lem6981330)). Qed.
Lemma lem6981333 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6981334 : term120 = term121.
Proof. exact (@lem6981333 term9 term9). Qed.
Lemma lem6981335 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6981336 : term123 = term9.
Proof. exact (EQ_MP (@lem6981335) (@lem940073)). Qed.
Lemma lem6981337 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6981338 : term121 = term81.
Proof. exact (MK_COMB (@lem6981337) (@lem6981336)). Qed.
Lemma lem6981339 : term120 = term81.
Proof. exact (TRANS (@lem6981334) (@lem6981338)). Qed.
Lemma lem6981340 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem6981341 : term174 = term172.
Proof. exact (MK_COMB (@lem6981340) (@lem6981339)). Qed.
Lemma lem6981343 (x : nat) : (term173 x) = term67.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6981344 : term172 = term67.
Proof. exact (@lem6981343 term9). Qed.
Lemma lem6981345 : term174 = term67.
Proof. exact (TRANS (@lem6981341) (@lem6981344)). Qed.
Lemma lem6981346 : term67 = term174.
Proof. exact (SYM (@lem6981345)). Qed.
Lemma lem6981347 : term246 = term174.
Proof. exact (TRANS (@lem6981331) (@lem6981346)). Qed.
Lemma lem6981348 : term237 = term108.
Proof. exact (@lem6981298 (@lem6981347)). Qed.
Lemma lem6981349 : term236 = term108.
Proof. exact (TRANS (@lem6981264) (@lem6981348)). Qed.
Lemma lem6981351 (x : real) : (term127 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6981352 : term108 = term67.
Proof. exact (@lem6981351 term67). Qed.
Lemma lem6981353 : term236 = term67.
Proof. exact (TRANS (@lem6981349) (@lem6981352)). Qed.
Lemma lem6981354 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6981355 : term247 = term170.
Proof. exact (MK_COMB (@lem6981354) (@lem6981353)). Qed.
Lemma lem6981356 (_92987 : int) : (real_of_int _92987) = (real_of_int _92987).
Proof. exact (eq_refl (real_of_int _92987)). Qed.
Lemma lem6981357 (_92987 : int) : (term233 _92987) = (term248 _92987).
Proof. exact (MK_COMB (@lem6981355) (@lem6981356 _92987)). Qed.
Lemma lem6981358 (_92987 : int) : (term253 _92987) = (term248 _92987).
Proof. exact (TRANS (@lem6981255 _92987) (@lem6981357 _92987)). Qed.
Lemma lem6981359 (_92987 : int) : (term248 _92987) = term67.
Proof. exact (@lem1982719 (real_of_int _92987)). Qed.
Lemma lem6981360 (_92987 : int) : (term253 _92987) = term67.
Proof. exact (TRANS (@lem6981358 _92987) (@lem6981359 _92987)). Qed.
Lemma lem6981361 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6981362 (_92987 : int) : (term254 _92987) = term250.
Proof. exact (MK_COMB (@lem6981361) (@lem6981360 _92987)). Qed.
Lemma lem6981363 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem6981364 (_92987 : int) : (term252 _92987) = term255.
Proof. exact (MK_COMB (@lem6981362 _92987) (@lem6981363)). Qed.
Lemma lem6981365 (_92987 : int) : (term251 _92987) = term255.
Proof. exact (TRANS (@lem6981254 _92987) (@lem6981364 _92987)). Qed.
Lemma lem6981366 : term255 = term111.
Proof. exact (@lem1982721 term111). Qed.
Lemma lem6981367 (_92987 : int) : (term251 _92987) = term111.
Proof. exact (TRANS (@lem6981365 _92987) (@lem6981366)). Qed.
Lemma lem6981368 (_92986 : int) (_92987 : int) : (term230 _92986 _92987) = term255.
Proof. exact (MK_COMB (@lem6981253 _92986) (@lem6981367 _92987)). Qed.
Lemma lem6981369 (_92986 : int) (_92987 : int) : (term229 _92986 _92987) = term255.
Proof. exact (TRANS (@lem6981145 _92986 _92987) (@lem6981368 _92986 _92987)). Qed.
Lemma lem6981370 : term255 = term111.
Proof. exact (@lem1982721 term111). Qed.
Lemma lem6981371 (_92986 : int) (_92987 : int) : (term229 _92986 _92987) = term111.
Proof. exact (TRANS (@lem6981369 _92986 _92987) (@lem6981370)). Qed.
Lemma lem6981372 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6981373 (_92986 : int) (_92987 : int) : (term256 _92986 _92987) = term257.
Proof. exact (MK_COMB (@lem6981372) (@lem6981371 _92986 _92987)). Qed.
Lemma lem6981374 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem6981375 (_92986 : int) (_92987 : int) : (term228 _92986 _92987) = term258.
Proof. exact (MK_COMB (@lem6981373 _92986 _92987) (@lem6981374)). Qed.
Lemma lem6981376 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term258.
Proof. exact (EQ_MP (@lem6981375 _92986 _92987) (@lem6981144 _92986 _92987 h1)). Qed.
Lemma lem6981378 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6981379 : term258 = term259.
Proof. exact (@lem6981378 term67 term111). Qed.
Lemma lem6981381 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6981382 : term111 = term112.
Proof. exact (@lem6981381 term9). Qed.
Lemma lem6981384 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6981385 : term67 = term108.
Proof. exact (@lem6981384 (NUMERAL 0)). Qed.
Lemma lem6981386 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6981387 : term69 = term260.
Proof. exact (MK_COMB (@lem6981386) (@lem6981385)). Qed.
Lemma lem6981388 : term259 = term261.
Proof. exact (MK_COMB (@lem6981387) (@lem6981382)). Qed.
Lemma lem6981389 : term262.
Proof. exact (@lem1980026 term67 term81 term111 term81). Qed.
Lemma lem6981391 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981392 : term160 = term161.
Proof. exact (@lem6981391 (NUMERAL 0) term9). Qed.
Lemma lem6981393 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981394 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981395 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981394 h1) (fun h1 : term161 = True => @lem6981393)). Qed.
Lemma lem6981396 : term161 = True.
Proof. exact (EQ_MP (@lem6981395) (@lem6981393)). Qed.
Lemma lem6981397 : term160 = True.
Proof. exact (TRANS (@lem6981392) (@lem6981396)). Qed.
Lemma lem6981398 : True = term160.
Proof. exact (SYM (@lem6981397)). Qed.
Lemma lem6981399 : term160.
Proof. exact (EQ_MP (@lem6981398) (@lem0)). Qed.
Lemma lem6981400 : term263.
Proof. exact (@lem6981389 (@lem6981399)). Qed.
Lemma lem6981402 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981403 : term160 = term161.
Proof. exact (@lem6981402 (NUMERAL 0) term9). Qed.
Lemma lem6981404 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981405 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981406 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981405 h1) (fun h1 : term161 = True => @lem6981404)). Qed.
Lemma lem6981407 : term161 = True.
Proof. exact (EQ_MP (@lem6981406) (@lem6981404)). Qed.
Lemma lem6981408 : term160 = True.
Proof. exact (TRANS (@lem6981403) (@lem6981407)). Qed.
Lemma lem6981409 : True = term160.
Proof. exact (SYM (@lem6981408)). Qed.
Lemma lem6981410 : term160.
Proof. exact (EQ_MP (@lem6981409) (@lem0)). Qed.
Lemma lem6981411 : term261 = term264.
Proof. exact (@lem6981400 (@lem6981410)). Qed.
Lemma lem6981413 (m : nat) (n : nat) : (term141 m n) = (term142 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6981414 : term138 = term143.
Proof. exact (@lem6981413 term9 term9). Qed.
Lemma lem6981415 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6981416 : term123 = term9.
Proof. exact (EQ_MP (@lem6981415) (@lem940073)). Qed.
Lemma lem6981417 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6981418 : term121 = term81.
Proof. exact (MK_COMB (@lem6981417) (@lem6981416)). Qed.
Lemma lem6981419 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6981420 : term143 = term111.
Proof. exact (MK_COMB (@lem6981419) (@lem6981418)). Qed.
Lemma lem6981421 : term138 = term111.
Proof. exact (TRANS (@lem6981414) (@lem6981420)). Qed.
Lemma lem6981423 (x : nat) : (term173 x) = term67.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6981424 : term172 = term67.
Proof. exact (@lem6981423 term9). Qed.
Lemma lem6981425 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6981426 : term265 = term69.
Proof. exact (MK_COMB (@lem6981425) (@lem6981424)). Qed.
Lemma lem6981427 : term264 = term259.
Proof. exact (MK_COMB (@lem6981426) (@lem6981421)). Qed.
Lemma lem6981429 (m : nat) (n : nat) : (term266 m n) = (term267 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6981430 : term259 = term268.
Proof. exact (@lem6981429 (NUMERAL 0) term9). Qed.
Lemma lem6981431 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981432 (h1 : term162 = (BIT1 0)) : (term9 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6981433 : (term162 = (BIT1 0)) = ((term9 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981432 h1) (fun h1 : (term9 = (NUMERAL 0)) = False => @lem6981431)). Qed.
Lemma lem6981434 : (term9 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6981433) (@lem6981431)). Qed.
Lemma lem6981435 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6981436 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6981437 : term269 = (and True).
Proof. exact (MK_COMB (@lem6981436) (@lem6981435)). Qed.
Lemma lem6981438 : term268 = (True /\ False).
Proof. exact (MK_COMB (@lem6981437) (@lem6981434)). Qed.
Lemma lem6981440 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6981441 : term268 = False.
Proof. exact (TRANS (@lem6981438) (@lem6981440)). Qed.
Lemma lem6981442 : term259 = False.
Proof. exact (TRANS (@lem6981430) (@lem6981441)). Qed.
Lemma lem6981443 : term264 = False.
Proof. exact (TRANS (@lem6981427) (@lem6981442)). Qed.
Lemma lem6981444 : term261 = False.
Proof. exact (TRANS (@lem6981411) (@lem6981443)). Qed.
Lemma lem6981445 : term259 = False.
Proof. exact (TRANS (@lem6981388) (@lem6981444)). Qed.
Lemma lem6981446 : term258 = False.
Proof. exact (TRANS (@lem6981379) (@lem6981445)). Qed.
Lemma lem6981447 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : False.
Proof. exact (EQ_MP (@lem6981446) (@lem6981376 _92986 _92987 h1)). Qed.
Lemma lem6981448 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term205 _92986 _92987.
Proof. exact (h1). Qed.
Lemma lem6981449 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term204 _92986 _92987.
Proof. exact (proj2 (@lem6981448 _92986 _92987 h1)). Qed.
Lemma lem6981451 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term201 _92986 _92987.
Proof. exact (proj2 (@lem6981449 _92986 _92987 h1)). Qed.
Lemma lem6981453 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term192 _92986 _92987.
Proof. exact (proj2 (@lem6981451 _92986 _92987 h1)). Qed.
Lemma lem6981454 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term179 _92986 _92987.
Proof. exact (proj1 (@lem6981451 _92986 _92987 h1)). Qed.
Lemma lem6981456 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6981457 : term206 = term160.
Proof. exact (@lem6981456 term67 term81). Qed.
Lemma lem6981459 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6981460 : term81 = term137.
Proof. exact (@lem6981459 term9). Qed.
Lemma lem6981462 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6981463 : term67 = term108.
Proof. exact (@lem6981462 (NUMERAL 0)). Qed.
Lemma lem6981464 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6981465 : term207 = term208.
Proof. exact (MK_COMB (@lem6981464) (@lem6981463)). Qed.
Lemma lem6981466 : term160 = term209.
Proof. exact (MK_COMB (@lem6981465) (@lem6981460)). Qed.
Lemma lem6981467 : term210.
Proof. exact (@lem1980255 term67 term81 term81 term81). Qed.
Lemma lem6981469 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981470 : term160 = term161.
Proof. exact (@lem6981469 (NUMERAL 0) term9). Qed.
Lemma lem6981471 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981472 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981473 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981472 h1) (fun h1 : term161 = True => @lem6981471)). Qed.
Lemma lem6981474 : term161 = True.
Proof. exact (EQ_MP (@lem6981473) (@lem6981471)). Qed.
Lemma lem6981475 : term160 = True.
Proof. exact (TRANS (@lem6981470) (@lem6981474)). Qed.
Lemma lem6981476 : True = term160.
Proof. exact (SYM (@lem6981475)). Qed.
Lemma lem6981477 : term160.
Proof. exact (EQ_MP (@lem6981476) (@lem0)). Qed.
Lemma lem6981478 : term211.
Proof. exact (@lem6981467 (@lem6981477)). Qed.
Lemma lem6981480 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981481 : term160 = term161.
Proof. exact (@lem6981480 (NUMERAL 0) term9). Qed.
Lemma lem6981482 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981483 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981484 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981483 h1) (fun h1 : term161 = True => @lem6981482)). Qed.
Lemma lem6981485 : term161 = True.
Proof. exact (EQ_MP (@lem6981484) (@lem6981482)). Qed.
Lemma lem6981486 : term160 = True.
Proof. exact (TRANS (@lem6981481) (@lem6981485)). Qed.
Lemma lem6981487 : True = term160.
Proof. exact (SYM (@lem6981486)). Qed.
Lemma lem6981488 : term160.
Proof. exact (EQ_MP (@lem6981487) (@lem0)). Qed.
Lemma lem6981489 : term209 = term212.
Proof. exact (@lem6981478 (@lem6981488)). Qed.
Lemma lem6981491 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6981492 : term120 = term121.
Proof. exact (@lem6981491 term9 term9). Qed.
Lemma lem6981493 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6981494 : term123 = term9.
Proof. exact (EQ_MP (@lem6981493) (@lem940073)). Qed.
Lemma lem6981495 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6981496 : term121 = term81.
Proof. exact (MK_COMB (@lem6981495) (@lem6981494)). Qed.
Lemma lem6981497 : term120 = term81.
Proof. exact (TRANS (@lem6981492) (@lem6981496)). Qed.
Lemma lem6981499 (x : nat) : (term173 x) = term67.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6981500 : term172 = term67.
Proof. exact (@lem6981499 term9). Qed.
Lemma lem6981501 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6981502 : term213 = term207.
Proof. exact (MK_COMB (@lem6981501) (@lem6981500)). Qed.
Lemma lem6981503 : term212 = term160.
Proof. exact (MK_COMB (@lem6981502) (@lem6981497)). Qed.
Lemma lem6981505 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981506 : term160 = term161.
Proof. exact (@lem6981505 (NUMERAL 0) term9). Qed.
Lemma lem6981507 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981508 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981509 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981508 h1) (fun h1 : term161 = True => @lem6981507)). Qed.
Lemma lem6981510 : term161 = True.
Proof. exact (EQ_MP (@lem6981509) (@lem6981507)). Qed.
Lemma lem6981511 : term160 = True.
Proof. exact (TRANS (@lem6981506) (@lem6981510)). Qed.
Lemma lem6981512 : term212 = True.
Proof. exact (TRANS (@lem6981503) (@lem6981511)). Qed.
Lemma lem6981513 : term209 = True.
Proof. exact (TRANS (@lem6981489) (@lem6981512)). Qed.
Lemma lem6981514 : term160 = True.
Proof. exact (TRANS (@lem6981466) (@lem6981513)). Qed.
Lemma lem6981515 : term206 = True.
Proof. exact (TRANS (@lem6981457) (@lem6981514)). Qed.
Lemma lem6981516 : True = term206.
Proof. exact (SYM (@lem6981515)). Qed.
Lemma lem6981517 : term206.
Proof. exact (EQ_MP (@lem6981516) (@lem0)). Qed.
Lemma lem6981518 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term214 _92986 _92987.
Proof. exact (conj (@lem6981517) (@lem6981454 _92986 _92987 h1)). Qed.
Lemma lem6981520 (x : real) (y : real) : term215 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6981521 (_92986 : int) (_92987 : int) : term216 _92986 _92987.
Proof. exact (@lem6981520 term81 (term176 _92986 _92987)). Qed.
Lemma lem6981522 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term217 _92986 _92987.
Proof. exact (@lem6981521 _92986 _92987 (@lem6981518 _92986 _92987 h1)). Qed.
Lemma lem6981523 (_92986 : int) (_92987 : int) : (term218 _92986 _92987) = (term176 _92986 _92987).
Proof. exact (@lem1982733 (term176 _92986 _92987)). Qed.
Lemma lem6981524 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6981525 (_92986 : int) (_92987 : int) : (term219 _92986 _92987) = (term178 _92986 _92987).
Proof. exact (MK_COMB (@lem6981524) (@lem6981523 _92986 _92987)). Qed.
Lemma lem6981526 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem6981527 (_92986 : int) (_92987 : int) : (term217 _92986 _92987) = (term179 _92986 _92987).
Proof. exact (MK_COMB (@lem6981525 _92986 _92987) (@lem6981526)). Qed.
Lemma lem6981528 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term179 _92986 _92987.
Proof. exact (EQ_MP (@lem6981527 _92986 _92987) (@lem6981522 _92986 _92987 h1)). Qed.
Lemma lem6981530 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6981531 : term206 = term160.
Proof. exact (@lem6981530 term67 term81). Qed.
Lemma lem6981533 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6981534 : term81 = term137.
Proof. exact (@lem6981533 term9). Qed.
Lemma lem6981536 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6981537 : term67 = term108.
Proof. exact (@lem6981536 (NUMERAL 0)). Qed.
Lemma lem6981538 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6981539 : term207 = term208.
Proof. exact (MK_COMB (@lem6981538) (@lem6981537)). Qed.
Lemma lem6981540 : term160 = term209.
Proof. exact (MK_COMB (@lem6981539) (@lem6981534)). Qed.
Lemma lem6981541 : term210.
Proof. exact (@lem1980255 term67 term81 term81 term81). Qed.
Lemma lem6981543 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981544 : term160 = term161.
Proof. exact (@lem6981543 (NUMERAL 0) term9). Qed.
Lemma lem6981545 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981546 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981547 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981546 h1) (fun h1 : term161 = True => @lem6981545)). Qed.
Lemma lem6981548 : term161 = True.
Proof. exact (EQ_MP (@lem6981547) (@lem6981545)). Qed.
Lemma lem6981549 : term160 = True.
Proof. exact (TRANS (@lem6981544) (@lem6981548)). Qed.
Lemma lem6981550 : True = term160.
Proof. exact (SYM (@lem6981549)). Qed.
Lemma lem6981551 : term160.
Proof. exact (EQ_MP (@lem6981550) (@lem0)). Qed.
Lemma lem6981552 : term211.
Proof. exact (@lem6981541 (@lem6981551)). Qed.
Lemma lem6981554 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981555 : term160 = term161.
Proof. exact (@lem6981554 (NUMERAL 0) term9). Qed.
Lemma lem6981556 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981557 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981558 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981557 h1) (fun h1 : term161 = True => @lem6981556)). Qed.
Lemma lem6981559 : term161 = True.
Proof. exact (EQ_MP (@lem6981558) (@lem6981556)). Qed.
Lemma lem6981560 : term160 = True.
Proof. exact (TRANS (@lem6981555) (@lem6981559)). Qed.
Lemma lem6981561 : True = term160.
Proof. exact (SYM (@lem6981560)). Qed.
Lemma lem6981562 : term160.
Proof. exact (EQ_MP (@lem6981561) (@lem0)). Qed.
Lemma lem6981563 : term209 = term212.
Proof. exact (@lem6981552 (@lem6981562)). Qed.
Lemma lem6981565 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6981566 : term120 = term121.
Proof. exact (@lem6981565 term9 term9). Qed.
Lemma lem6981567 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6981568 : term123 = term9.
Proof. exact (EQ_MP (@lem6981567) (@lem940073)). Qed.
Lemma lem6981569 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6981570 : term121 = term81.
Proof. exact (MK_COMB (@lem6981569) (@lem6981568)). Qed.
Lemma lem6981571 : term120 = term81.
Proof. exact (TRANS (@lem6981566) (@lem6981570)). Qed.
Lemma lem6981573 (x : nat) : (term173 x) = term67.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6981574 : term172 = term67.
Proof. exact (@lem6981573 term9). Qed.
Lemma lem6981575 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6981576 : term213 = term207.
Proof. exact (MK_COMB (@lem6981575) (@lem6981574)). Qed.
Lemma lem6981577 : term212 = term160.
Proof. exact (MK_COMB (@lem6981576) (@lem6981571)). Qed.
Lemma lem6981579 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981580 : term160 = term161.
Proof. exact (@lem6981579 (NUMERAL 0) term9). Qed.
Lemma lem6981581 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981582 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981583 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981582 h1) (fun h1 : term161 = True => @lem6981581)). Qed.
Lemma lem6981584 : term161 = True.
Proof. exact (EQ_MP (@lem6981583) (@lem6981581)). Qed.
Lemma lem6981585 : term160 = True.
Proof. exact (TRANS (@lem6981580) (@lem6981584)). Qed.
Lemma lem6981586 : term212 = True.
Proof. exact (TRANS (@lem6981577) (@lem6981585)). Qed.
Lemma lem6981587 : term209 = True.
Proof. exact (TRANS (@lem6981563) (@lem6981586)). Qed.
Lemma lem6981588 : term160 = True.
Proof. exact (TRANS (@lem6981540) (@lem6981587)). Qed.
Lemma lem6981589 : term206 = True.
Proof. exact (TRANS (@lem6981531) (@lem6981588)). Qed.
Lemma lem6981590 : True = term206.
Proof. exact (SYM (@lem6981589)). Qed.
Lemma lem6981591 : term206.
Proof. exact (EQ_MP (@lem6981590) (@lem0)). Qed.
Lemma lem6981592 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term220 _92986 _92987.
Proof. exact (conj (@lem6981591) (@lem6981453 _92986 _92987 h1)). Qed.
Lemma lem6981594 (x : real) (y : real) : term215 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6981595 (_92986 : int) (_92987 : int) : term221 _92986 _92987.
Proof. exact (@lem6981594 term81 (term189 _92986 _92987)). Qed.
Lemma lem6981596 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term222 _92986 _92987.
Proof. exact (@lem6981595 _92986 _92987 (@lem6981592 _92986 _92987 h1)). Qed.
Lemma lem6981597 (_92986 : int) (_92987 : int) : (term223 _92986 _92987) = (term189 _92986 _92987).
Proof. exact (@lem1982733 (term189 _92986 _92987)). Qed.
Lemma lem6981598 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6981599 (_92986 : int) (_92987 : int) : (term224 _92986 _92987) = (term191 _92986 _92987).
Proof. exact (MK_COMB (@lem6981598) (@lem6981597 _92986 _92987)). Qed.
Lemma lem6981600 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem6981601 (_92986 : int) (_92987 : int) : (term222 _92986 _92987) = (term192 _92986 _92987).
Proof. exact (MK_COMB (@lem6981599 _92986 _92987) (@lem6981600)). Qed.
Lemma lem6981602 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term192 _92986 _92987.
Proof. exact (EQ_MP (@lem6981601 _92986 _92987) (@lem6981596 _92986 _92987 h1)). Qed.
Lemma lem6981603 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term225 _92986 _92987.
Proof. exact (conj (@lem6981602 _92986 _92987 h1) (@lem6981528 _92986 _92987 h1)). Qed.
Lemma lem6981605 (x : real) (y : real) : term226 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem6981606 (_92986 : int) (_92987 : int) : term227 _92986 _92987.
Proof. exact (@lem6981605 (term189 _92986 _92987) (term176 _92986 _92987)). Qed.
Lemma lem6981607 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term228 _92986 _92987.
Proof. exact (@lem6981606 _92986 _92987 (@lem6981603 _92986 _92987 h1)). Qed.
Lemma lem6981608 (_92986 : int) (_92987 : int) : (term229 _92986 _92987) = (term230 _92986 _92987).
Proof. exact (@lem1982753 (term153 _92986) (real_of_int _92986) (term231 _92987) (term153 _92987)). Qed.
Lemma lem6981609 (_92986 : int) : (term232 _92986) = (term233 _92986).
Proof. exact (@lem1982713 term111 (real_of_int _92986)). Qed.
Lemma lem6981611 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6981612 : term81 = term137.
Proof. exact (@lem6981611 term9). Qed.
Lemma lem6981614 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6981615 : term111 = term112.
Proof. exact (@lem6981614 term9). Qed.
Lemma lem6981616 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6981617 : term234 = term235.
Proof. exact (MK_COMB (@lem6981616) (@lem6981615)). Qed.
Lemma lem6981618 : term236 = term237.
Proof. exact (MK_COMB (@lem6981617) (@lem6981612)). Qed.
Lemma lem6981619 : term238.
Proof. exact (@lem1981473 term111 term81 term81 term81 term67 term81). Qed.
Lemma lem6981621 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981622 : term160 = term161.
Proof. exact (@lem6981621 (NUMERAL 0) term9). Qed.
Lemma lem6981623 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981624 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981625 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981624 h1) (fun h1 : term161 = True => @lem6981623)). Qed.
Lemma lem6981626 : term161 = True.
Proof. exact (EQ_MP (@lem6981625) (@lem6981623)). Qed.
Lemma lem6981627 : term160 = True.
Proof. exact (TRANS (@lem6981622) (@lem6981626)). Qed.
Lemma lem6981628 : True = term160.
Proof. exact (SYM (@lem6981627)). Qed.
Lemma lem6981629 : term160.
Proof. exact (EQ_MP (@lem6981628) (@lem0)). Qed.
Lemma lem6981630 : term239.
Proof. exact (@lem6981619 (@lem6981629)). Qed.
Lemma lem6981632 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981633 : term160 = term161.
Proof. exact (@lem6981632 (NUMERAL 0) term9). Qed.
Lemma lem6981634 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981635 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981636 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981635 h1) (fun h1 : term161 = True => @lem6981634)). Qed.
Lemma lem6981637 : term161 = True.
Proof. exact (EQ_MP (@lem6981636) (@lem6981634)). Qed.
Lemma lem6981638 : term160 = True.
Proof. exact (TRANS (@lem6981633) (@lem6981637)). Qed.
Lemma lem6981639 : True = term160.
Proof. exact (SYM (@lem6981638)). Qed.
Lemma lem6981640 : term160.
Proof. exact (EQ_MP (@lem6981639) (@lem0)). Qed.
Lemma lem6981641 : term240.
Proof. exact (@lem6981630 (@lem6981640)). Qed.
Lemma lem6981643 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981644 : term160 = term161.
Proof. exact (@lem6981643 (NUMERAL 0) term9). Qed.
Lemma lem6981645 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981646 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981647 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981646 h1) (fun h1 : term161 = True => @lem6981645)). Qed.
Lemma lem6981648 : term161 = True.
Proof. exact (EQ_MP (@lem6981647) (@lem6981645)). Qed.
Lemma lem6981649 : term160 = True.
Proof. exact (TRANS (@lem6981644) (@lem6981648)). Qed.
Lemma lem6981650 : True = term160.
Proof. exact (SYM (@lem6981649)). Qed.
Lemma lem6981651 : term160.
Proof. exact (EQ_MP (@lem6981650) (@lem0)). Qed.
Lemma lem6981652 : term241.
Proof. exact (@lem6981641 (@lem6981651)). Qed.
Lemma lem6981654 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6981655 : term120 = term121.
Proof. exact (@lem6981654 term9 term9). Qed.
Lemma lem6981656 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6981657 : term123 = term9.
Proof. exact (EQ_MP (@lem6981656) (@lem940073)). Qed.
Lemma lem6981658 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6981659 : term121 = term81.
Proof. exact (MK_COMB (@lem6981658) (@lem6981657)). Qed.
Lemma lem6981660 : term120 = term81.
Proof. exact (TRANS (@lem6981655) (@lem6981659)). Qed.
Lemma lem6981662 (m : nat) (n : nat) : (term141 m n) = (term142 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6981663 : term138 = term143.
Proof. exact (@lem6981662 term9 term9). Qed.
Lemma lem6981664 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6981665 : term123 = term9.
Proof. exact (EQ_MP (@lem6981664) (@lem940073)). Qed.
Lemma lem6981666 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6981667 : term121 = term81.
Proof. exact (MK_COMB (@lem6981666) (@lem6981665)). Qed.
Lemma lem6981668 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6981669 : term143 = term111.
Proof. exact (MK_COMB (@lem6981668) (@lem6981667)). Qed.
Lemma lem6981670 : term138 = term111.
Proof. exact (TRANS (@lem6981663) (@lem6981669)). Qed.
Lemma lem6981671 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6981672 : term242 = term234.
Proof. exact (MK_COMB (@lem6981671) (@lem6981670)). Qed.
Lemma lem6981673 : term243 = term236.
Proof. exact (MK_COMB (@lem6981672) (@lem6981660)). Qed.
Lemma lem6981675 (m : nat) : (term244 m) = term67.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6981676 : term236 = term67.
Proof. exact (@lem6981675 term9). Qed.
Lemma lem6981677 : term243 = term67.
Proof. exact (TRANS (@lem6981673) (@lem6981676)). Qed.
Lemma lem6981678 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6981679 : term245 = term170.
Proof. exact (MK_COMB (@lem6981678) (@lem6981677)). Qed.
Lemma lem6981680 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem6981681 : term246 = term172.
Proof. exact (MK_COMB (@lem6981679) (@lem6981680)). Qed.
Lemma lem6981683 (x : nat) : (term173 x) = term67.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6981684 : term172 = term67.
Proof. exact (@lem6981683 term9). Qed.
Lemma lem6981685 : term246 = term67.
Proof. exact (TRANS (@lem6981681) (@lem6981684)). Qed.
Lemma lem6981687 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6981688 : term120 = term121.
Proof. exact (@lem6981687 term9 term9). Qed.
Lemma lem6981689 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6981690 : term123 = term9.
Proof. exact (EQ_MP (@lem6981689) (@lem940073)). Qed.
Lemma lem6981691 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6981692 : term121 = term81.
Proof. exact (MK_COMB (@lem6981691) (@lem6981690)). Qed.
Lemma lem6981693 : term120 = term81.
Proof. exact (TRANS (@lem6981688) (@lem6981692)). Qed.
Lemma lem6981694 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem6981695 : term174 = term172.
Proof. exact (MK_COMB (@lem6981694) (@lem6981693)). Qed.
Lemma lem6981697 (x : nat) : (term173 x) = term67.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6981698 : term172 = term67.
Proof. exact (@lem6981697 term9). Qed.
Lemma lem6981699 : term174 = term67.
Proof. exact (TRANS (@lem6981695) (@lem6981698)). Qed.
Lemma lem6981700 : term67 = term174.
Proof. exact (SYM (@lem6981699)). Qed.
Lemma lem6981701 : term246 = term174.
Proof. exact (TRANS (@lem6981685) (@lem6981700)). Qed.
Lemma lem6981702 : term237 = term108.
Proof. exact (@lem6981652 (@lem6981701)). Qed.
Lemma lem6981703 : term236 = term108.
Proof. exact (TRANS (@lem6981618) (@lem6981702)). Qed.
Lemma lem6981705 (x : real) : (term127 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6981706 : term108 = term67.
Proof. exact (@lem6981705 term67). Qed.
Lemma lem6981707 : term236 = term67.
Proof. exact (TRANS (@lem6981703) (@lem6981706)). Qed.
Lemma lem6981708 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6981709 : term247 = term170.
Proof. exact (MK_COMB (@lem6981708) (@lem6981707)). Qed.
Lemma lem6981710 (_92986 : int) : (real_of_int _92986) = (real_of_int _92986).
Proof. exact (eq_refl (real_of_int _92986)). Qed.
Lemma lem6981711 (_92986 : int) : (term233 _92986) = (term248 _92986).
Proof. exact (MK_COMB (@lem6981709) (@lem6981710 _92986)). Qed.
Lemma lem6981712 (_92986 : int) : (term232 _92986) = (term248 _92986).
Proof. exact (TRANS (@lem6981609 _92986) (@lem6981711 _92986)). Qed.
Lemma lem6981713 (_92986 : int) : (term248 _92986) = term67.
Proof. exact (@lem1982719 (real_of_int _92986)). Qed.
Lemma lem6981714 (_92986 : int) : (term232 _92986) = term67.
Proof. exact (TRANS (@lem6981712 _92986) (@lem6981713 _92986)). Qed.
Lemma lem6981715 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6981716 (_92986 : int) : (term249 _92986) = term250.
Proof. exact (MK_COMB (@lem6981715) (@lem6981714 _92986)). Qed.
Lemma lem6981717 (_92987 : int) : (term251 _92987) = (term252 _92987).
Proof. exact (@lem1982759 (real_of_int _92987) (term153 _92987) term111). Qed.
Lemma lem6981718 (_92987 : int) : (term253 _92987) = (term233 _92987).
Proof. exact (@lem1982715 term111 (real_of_int _92987)). Qed.
Lemma lem6981720 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6981721 : term81 = term137.
Proof. exact (@lem6981720 term9). Qed.
Lemma lem6981723 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6981724 : term111 = term112.
Proof. exact (@lem6981723 term9). Qed.
Lemma lem6981725 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6981726 : term234 = term235.
Proof. exact (MK_COMB (@lem6981725) (@lem6981724)). Qed.
Lemma lem6981727 : term236 = term237.
Proof. exact (MK_COMB (@lem6981726) (@lem6981721)). Qed.
Lemma lem6981728 : term238.
Proof. exact (@lem1981473 term111 term81 term81 term81 term67 term81). Qed.
Lemma lem6981730 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981731 : term160 = term161.
Proof. exact (@lem6981730 (NUMERAL 0) term9). Qed.
Lemma lem6981732 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981733 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981734 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981733 h1) (fun h1 : term161 = True => @lem6981732)). Qed.
Lemma lem6981735 : term161 = True.
Proof. exact (EQ_MP (@lem6981734) (@lem6981732)). Qed.
Lemma lem6981736 : term160 = True.
Proof. exact (TRANS (@lem6981731) (@lem6981735)). Qed.
Lemma lem6981737 : True = term160.
Proof. exact (SYM (@lem6981736)). Qed.
Lemma lem6981738 : term160.
Proof. exact (EQ_MP (@lem6981737) (@lem0)). Qed.
Lemma lem6981739 : term239.
Proof. exact (@lem6981728 (@lem6981738)). Qed.
Lemma lem6981741 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981742 : term160 = term161.
Proof. exact (@lem6981741 (NUMERAL 0) term9). Qed.
Lemma lem6981743 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981744 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981745 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981744 h1) (fun h1 : term161 = True => @lem6981743)). Qed.
Lemma lem6981746 : term161 = True.
Proof. exact (EQ_MP (@lem6981745) (@lem6981743)). Qed.
Lemma lem6981747 : term160 = True.
Proof. exact (TRANS (@lem6981742) (@lem6981746)). Qed.
Lemma lem6981748 : True = term160.
Proof. exact (SYM (@lem6981747)). Qed.
Lemma lem6981749 : term160.
Proof. exact (EQ_MP (@lem6981748) (@lem0)). Qed.
Lemma lem6981750 : term240.
Proof. exact (@lem6981739 (@lem6981749)). Qed.
Lemma lem6981752 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981753 : term160 = term161.
Proof. exact (@lem6981752 (NUMERAL 0) term9). Qed.
Lemma lem6981754 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981755 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981756 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981755 h1) (fun h1 : term161 = True => @lem6981754)). Qed.
Lemma lem6981757 : term161 = True.
Proof. exact (EQ_MP (@lem6981756) (@lem6981754)). Qed.
Lemma lem6981758 : term160 = True.
Proof. exact (TRANS (@lem6981753) (@lem6981757)). Qed.
Lemma lem6981759 : True = term160.
Proof. exact (SYM (@lem6981758)). Qed.
Lemma lem6981760 : term160.
Proof. exact (EQ_MP (@lem6981759) (@lem0)). Qed.
Lemma lem6981761 : term241.
Proof. exact (@lem6981750 (@lem6981760)). Qed.
Lemma lem6981763 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6981764 : term120 = term121.
Proof. exact (@lem6981763 term9 term9). Qed.
Lemma lem6981765 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6981766 : term123 = term9.
Proof. exact (EQ_MP (@lem6981765) (@lem940073)). Qed.
Lemma lem6981767 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6981768 : term121 = term81.
Proof. exact (MK_COMB (@lem6981767) (@lem6981766)). Qed.
Lemma lem6981769 : term120 = term81.
Proof. exact (TRANS (@lem6981764) (@lem6981768)). Qed.
Lemma lem6981771 (m : nat) (n : nat) : (term141 m n) = (term142 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6981772 : term138 = term143.
Proof. exact (@lem6981771 term9 term9). Qed.
Lemma lem6981773 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6981774 : term123 = term9.
Proof. exact (EQ_MP (@lem6981773) (@lem940073)). Qed.
Lemma lem6981775 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6981776 : term121 = term81.
Proof. exact (MK_COMB (@lem6981775) (@lem6981774)). Qed.
Lemma lem6981777 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6981778 : term143 = term111.
Proof. exact (MK_COMB (@lem6981777) (@lem6981776)). Qed.
Lemma lem6981779 : term138 = term111.
Proof. exact (TRANS (@lem6981772) (@lem6981778)). Qed.
Lemma lem6981780 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6981781 : term242 = term234.
Proof. exact (MK_COMB (@lem6981780) (@lem6981779)). Qed.
Lemma lem6981782 : term243 = term236.
Proof. exact (MK_COMB (@lem6981781) (@lem6981769)). Qed.
Lemma lem6981784 (m : nat) : (term244 m) = term67.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6981785 : term236 = term67.
Proof. exact (@lem6981784 term9). Qed.
Lemma lem6981786 : term243 = term67.
Proof. exact (TRANS (@lem6981782) (@lem6981785)). Qed.
Lemma lem6981787 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6981788 : term245 = term170.
Proof. exact (MK_COMB (@lem6981787) (@lem6981786)). Qed.
Lemma lem6981789 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem6981790 : term246 = term172.
Proof. exact (MK_COMB (@lem6981788) (@lem6981789)). Qed.
Lemma lem6981792 (x : nat) : (term173 x) = term67.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6981793 : term172 = term67.
Proof. exact (@lem6981792 term9). Qed.
Lemma lem6981794 : term246 = term67.
Proof. exact (TRANS (@lem6981790) (@lem6981793)). Qed.
Lemma lem6981796 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6981797 : term120 = term121.
Proof. exact (@lem6981796 term9 term9). Qed.
Lemma lem6981798 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6981799 : term123 = term9.
Proof. exact (EQ_MP (@lem6981798) (@lem940073)). Qed.
Lemma lem6981800 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6981801 : term121 = term81.
Proof. exact (MK_COMB (@lem6981800) (@lem6981799)). Qed.
Lemma lem6981802 : term120 = term81.
Proof. exact (TRANS (@lem6981797) (@lem6981801)). Qed.
Lemma lem6981803 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem6981804 : term174 = term172.
Proof. exact (MK_COMB (@lem6981803) (@lem6981802)). Qed.
Lemma lem6981806 (x : nat) : (term173 x) = term67.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6981807 : term172 = term67.
Proof. exact (@lem6981806 term9). Qed.
Lemma lem6981808 : term174 = term67.
Proof. exact (TRANS (@lem6981804) (@lem6981807)). Qed.
Lemma lem6981809 : term67 = term174.
Proof. exact (SYM (@lem6981808)). Qed.
Lemma lem6981810 : term246 = term174.
Proof. exact (TRANS (@lem6981794) (@lem6981809)). Qed.
Lemma lem6981811 : term237 = term108.
Proof. exact (@lem6981761 (@lem6981810)). Qed.
Lemma lem6981812 : term236 = term108.
Proof. exact (TRANS (@lem6981727) (@lem6981811)). Qed.
Lemma lem6981814 (x : real) : (term127 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6981815 : term108 = term67.
Proof. exact (@lem6981814 term67). Qed.
Lemma lem6981816 : term236 = term67.
Proof. exact (TRANS (@lem6981812) (@lem6981815)). Qed.
Lemma lem6981817 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6981818 : term247 = term170.
Proof. exact (MK_COMB (@lem6981817) (@lem6981816)). Qed.
Lemma lem6981819 (_92987 : int) : (real_of_int _92987) = (real_of_int _92987).
Proof. exact (eq_refl (real_of_int _92987)). Qed.
Lemma lem6981820 (_92987 : int) : (term233 _92987) = (term248 _92987).
Proof. exact (MK_COMB (@lem6981818) (@lem6981819 _92987)). Qed.
Lemma lem6981821 (_92987 : int) : (term253 _92987) = (term248 _92987).
Proof. exact (TRANS (@lem6981718 _92987) (@lem6981820 _92987)). Qed.
Lemma lem6981822 (_92987 : int) : (term248 _92987) = term67.
Proof. exact (@lem1982719 (real_of_int _92987)). Qed.
Lemma lem6981823 (_92987 : int) : (term253 _92987) = term67.
Proof. exact (TRANS (@lem6981821 _92987) (@lem6981822 _92987)). Qed.
Lemma lem6981824 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6981825 (_92987 : int) : (term254 _92987) = term250.
Proof. exact (MK_COMB (@lem6981824) (@lem6981823 _92987)). Qed.
Lemma lem6981826 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem6981827 (_92987 : int) : (term252 _92987) = term255.
Proof. exact (MK_COMB (@lem6981825 _92987) (@lem6981826)). Qed.
Lemma lem6981828 (_92987 : int) : (term251 _92987) = term255.
Proof. exact (TRANS (@lem6981717 _92987) (@lem6981827 _92987)). Qed.
Lemma lem6981829 : term255 = term111.
Proof. exact (@lem1982721 term111). Qed.
Lemma lem6981830 (_92987 : int) : (term251 _92987) = term111.
Proof. exact (TRANS (@lem6981828 _92987) (@lem6981829)). Qed.
Lemma lem6981831 (_92986 : int) (_92987 : int) : (term230 _92986 _92987) = term255.
Proof. exact (MK_COMB (@lem6981716 _92986) (@lem6981830 _92987)). Qed.
Lemma lem6981832 (_92986 : int) (_92987 : int) : (term229 _92986 _92987) = term255.
Proof. exact (TRANS (@lem6981608 _92986 _92987) (@lem6981831 _92986 _92987)). Qed.
Lemma lem6981833 : term255 = term111.
Proof. exact (@lem1982721 term111). Qed.
Lemma lem6981834 (_92986 : int) (_92987 : int) : (term229 _92986 _92987) = term111.
Proof. exact (TRANS (@lem6981832 _92986 _92987) (@lem6981833)). Qed.
Lemma lem6981835 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6981836 (_92986 : int) (_92987 : int) : (term256 _92986 _92987) = term257.
Proof. exact (MK_COMB (@lem6981835) (@lem6981834 _92986 _92987)). Qed.
Lemma lem6981837 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem6981838 (_92986 : int) (_92987 : int) : (term228 _92986 _92987) = term258.
Proof. exact (MK_COMB (@lem6981836 _92986 _92987) (@lem6981837)). Qed.
Lemma lem6981839 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : term258.
Proof. exact (EQ_MP (@lem6981838 _92986 _92987) (@lem6981607 _92986 _92987 h1)). Qed.
Lemma lem6981841 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6981842 : term258 = term259.
Proof. exact (@lem6981841 term67 term111). Qed.
Lemma lem6981844 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6981845 : term111 = term112.
Proof. exact (@lem6981844 term9). Qed.
Lemma lem6981847 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6981848 : term67 = term108.
Proof. exact (@lem6981847 (NUMERAL 0)). Qed.
Lemma lem6981849 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6981850 : term69 = term260.
Proof. exact (MK_COMB (@lem6981849) (@lem6981848)). Qed.
Lemma lem6981851 : term259 = term261.
Proof. exact (MK_COMB (@lem6981850) (@lem6981845)). Qed.
Lemma lem6981852 : term262.
Proof. exact (@lem1980026 term67 term81 term111 term81). Qed.
Lemma lem6981854 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981855 : term160 = term161.
Proof. exact (@lem6981854 (NUMERAL 0) term9). Qed.
Lemma lem6981856 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981857 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981858 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981857 h1) (fun h1 : term161 = True => @lem6981856)). Qed.
Lemma lem6981859 : term161 = True.
Proof. exact (EQ_MP (@lem6981858) (@lem6981856)). Qed.
Lemma lem6981860 : term160 = True.
Proof. exact (TRANS (@lem6981855) (@lem6981859)). Qed.
Lemma lem6981861 : True = term160.
Proof. exact (SYM (@lem6981860)). Qed.
Lemma lem6981862 : term160.
Proof. exact (EQ_MP (@lem6981861) (@lem0)). Qed.
Lemma lem6981863 : term263.
Proof. exact (@lem6981852 (@lem6981862)). Qed.
Lemma lem6981865 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6981866 : term160 = term161.
Proof. exact (@lem6981865 (NUMERAL 0) term9). Qed.
Lemma lem6981867 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981868 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6981869 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981868 h1) (fun h1 : term161 = True => @lem6981867)). Qed.
Lemma lem6981870 : term161 = True.
Proof. exact (EQ_MP (@lem6981869) (@lem6981867)). Qed.
Lemma lem6981871 : term160 = True.
Proof. exact (TRANS (@lem6981866) (@lem6981870)). Qed.
Lemma lem6981872 : True = term160.
Proof. exact (SYM (@lem6981871)). Qed.
Lemma lem6981873 : term160.
Proof. exact (EQ_MP (@lem6981872) (@lem0)). Qed.
Lemma lem6981874 : term261 = term264.
Proof. exact (@lem6981863 (@lem6981873)). Qed.
Lemma lem6981876 (m : nat) (n : nat) : (term141 m n) = (term142 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6981877 : term138 = term143.
Proof. exact (@lem6981876 term9 term9). Qed.
Lemma lem6981878 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6981879 : term123 = term9.
Proof. exact (EQ_MP (@lem6981878) (@lem940073)). Qed.
Lemma lem6981880 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6981881 : term121 = term81.
Proof. exact (MK_COMB (@lem6981880) (@lem6981879)). Qed.
Lemma lem6981882 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6981883 : term143 = term111.
Proof. exact (MK_COMB (@lem6981882) (@lem6981881)). Qed.
Lemma lem6981884 : term138 = term111.
Proof. exact (TRANS (@lem6981877) (@lem6981883)). Qed.
Lemma lem6981886 (x : nat) : (term173 x) = term67.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6981887 : term172 = term67.
Proof. exact (@lem6981886 term9). Qed.
Lemma lem6981888 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6981889 : term265 = term69.
Proof. exact (MK_COMB (@lem6981888) (@lem6981887)). Qed.
Lemma lem6981890 : term264 = term259.
Proof. exact (MK_COMB (@lem6981889) (@lem6981884)). Qed.
Lemma lem6981892 (m : nat) (n : nat) : (term266 m n) = (term267 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6981893 : term259 = term268.
Proof. exact (@lem6981892 (NUMERAL 0) term9). Qed.
Lemma lem6981894 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6981895 (h1 : term162 = (BIT1 0)) : (term9 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6981896 : (term162 = (BIT1 0)) = ((term9 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6981895 h1) (fun h1 : (term9 = (NUMERAL 0)) = False => @lem6981894)). Qed.
Lemma lem6981897 : (term9 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6981896) (@lem6981894)). Qed.
Lemma lem6981898 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6981899 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6981900 : term269 = (and True).
Proof. exact (MK_COMB (@lem6981899) (@lem6981898)). Qed.
Lemma lem6981901 : term268 = (True /\ False).
Proof. exact (MK_COMB (@lem6981900) (@lem6981897)). Qed.
Lemma lem6981903 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6981904 : term268 = False.
Proof. exact (TRANS (@lem6981901) (@lem6981903)). Qed.
Lemma lem6981905 : term259 = False.
Proof. exact (TRANS (@lem6981893) (@lem6981904)). Qed.
Lemma lem6981906 : term264 = False.
Proof. exact (TRANS (@lem6981890) (@lem6981905)). Qed.
Lemma lem6981907 : term261 = False.
Proof. exact (TRANS (@lem6981874) (@lem6981906)). Qed.
Lemma lem6981908 : term259 = False.
Proof. exact (TRANS (@lem6981851) (@lem6981907)). Qed.
Lemma lem6981909 : term258 = False.
Proof. exact (TRANS (@lem6981842) (@lem6981908)). Qed.
Lemma lem6981910 (_92986 : int) (_92987 : int) (h1 : term205 _92986 _92987) : False.
Proof. exact (EQ_MP (@lem6981909) (@lem6981839 _92986 _92987 h1)). Qed.
Lemma lem6981911 (_92986 : int) (_92987 : int) (h1 : term203 _92986 _92987) : False.
Proof. exact (or_elim (@lem6980984 _92986 _92987 h1) (fun h0 : term205 _92986 _92987 => @lem6981447 _92986 _92987 h0) (fun h0 : term205 _92986 _92987 => @lem6981910 _92986 _92987 h0)). Qed.
Lemma lem6981913 (_92986 : int) (_92987 : int) (h1 : term203 _92986 _92987) : term203 _92986 _92987.
Proof. exact (h1). Qed.
Lemma lem6981914 (_92986 : int) (_92987 : int) (h1 : term203 _92986 _92987) : (term203 _92986 _92987) = False.
Proof. exact (prop_ext (fun h2 : term203 _92986 _92987 => @lem6981911 _92986 _92987 h1) (fun h2 : False => @lem6981913 _92986 _92987 h1)). Qed.
Lemma lem6981915 (_92986 : int) (_92987 : int) (h1 : term203 _92986 _92987) : False.
Proof. exact (EQ_MP (@lem6981914 _92986 _92987 h1) (@lem6981913 _92986 _92987 h1)). Qed.
Lemma lem6981916 (_92986 : int) (_92987 : int) (h1 : term100 _92986 _92987) : term100 _92986 _92987.
Proof. exact (h1). Qed.
Lemma lem6981917 (_92986 : int) (_92987 : int) (h1 : term100 _92986 _92987) : term203 _92986 _92987.
Proof. exact (EQ_MP (@lem6980974 _92986 _92987) (@lem6981916 _92986 _92987 h1)). Qed.
Lemma lem6981918 (_92986 : int) (_92987 : int) (h1 : term100 _92986 _92987) : (term203 _92986 _92987) = False.
Proof. exact (prop_ext (fun h2 : term203 _92986 _92987 => @lem6981915 _92986 _92987 h2) (fun h2 : False => @lem6981917 _92986 _92987 h1)). Qed.
Lemma lem6981919 (_92986 : int) (_92987 : int) (h1 : term100 _92986 _92987) : False.
Proof. exact (EQ_MP (@lem6981918 _92986 _92987 h1) (@lem6981917 _92986 _92987 h1)). Qed.
Lemma lem6981920 (_92986 : int) (_92987 : int) : term270 _92986 _92987.
Proof. exact (fun h0 : term100 _92986 _92987 => @lem6981919 _92986 _92987 h0). Qed.
Lemma lem6981921 (_92986 : int) (_92987 : int) : term271 _92986 _92987.
Proof. exact (@lem1386578 (term272 _92986 _92987)). Qed.
Lemma lem6981924 (_92986 : int) (_92987 : int) : term272 _92986 _92987.
Proof. exact (@lem6981921 _92986 _92987 (@lem6981920 _92986 _92987)). Qed.
Lemma lem6981925 (_92986 : int) (_92987 : int) : (term98 _92986 _92987) = (term60 _92986 _92987).
Proof. exact (SYM (@lem6980481 _92986 _92987)). Qed.
Lemma lem6981926 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6981927 (_92986 : int) (_92987 : int) : (term272 _92986 _92987) = (term31 _92986 _92987).
Proof. exact (MK_COMB (@lem6981926) (@lem6981925 _92986 _92987)). Qed.
Lemma lem6981928 (_92986 : int) (_92987 : int) : term31 _92986 _92987.
Proof. exact (EQ_MP (@lem6981927 _92986 _92987) (@lem6981924 _92986 _92987)). Qed.
Lemma lem6981929 (_92986 : int) (_92987 : int) : term32 _92986 _92987.
Proof. exact (EQ_MP (@lem6980286 _92986 _92987) (@lem6981928 _92986 _92987)). Qed.
Lemma lem6981930 (a : nat) (b : nat) : term273 a b.
Proof. exact (@lem6981929 (int_of_num a) (int_of_num b)). Qed.
Lemma lem6981931 (a : nat) (b : nat) : term274 a b.
Proof. exact (@lem6981930 a b (@lem6980282 a)). Qed.
Lemma lem6981932 (a : nat) (b : nat) : term28 a b.
Proof. exact (@lem6981931 a b (@lem6980285 b)). Qed.
Lemma lem6981933 (a : nat) (b : nat) : (term28 a b) = ((term0 a b) = (Peano.lt a b)).
Proof. exact (SYM (@lem6980279 a b)). Qed.
Lemma lem6981935 {A : Type'} (h1 : term275 A) : term275 A.
Proof. exact (h1). Qed.
Lemma lem6981936 {A : Type'} (s : A -> Prop) (h1 : term275 A) : term276 A s.
Proof. exact (@lem6981935 A h1 s). Qed.
Lemma lem6981937 {A : Type'} (s : A -> Prop) : (term276 A s) = (term277 A s).
Proof. exact (eq_refl (term276 A s)). Qed.
Lemma lem6981938 {A : Type'} (s : A -> Prop) (h1 : term275 A) : term277 A s.
Proof. exact (EQ_MP (@lem6981937 A s) (@lem6981936 A s h1)). Qed.
Lemma lem6981939 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term275 A) : term278 A s f.
Proof. exact (@lem6981938 A s h1 f). Qed.
Lemma lem6981940 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term278 A s f) = (term279 A s f).
Proof. exact (eq_refl (term278 A s f)). Qed.
Lemma lem6981941 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term275 A) : term279 A s f.
Proof. exact (EQ_MP (@lem6981940 A s f) (@lem6981939 A s f h1)). Qed.
Lemma lem6981942 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term275 A) : term280 A s f b.
Proof. exact (@lem6981941 A s f h1 b). Qed.
Lemma lem6981943 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term280 A s f b) = (term281 A s f b).
Proof. exact (eq_refl (term280 A s f b)). Qed.
Lemma lem6981944 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term275 A) : term281 A s f b.
Proof. exact (EQ_MP (@lem6981943 A s f b) (@lem6981942 A s f b h1)). Qed.
Lemma lem6981945 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term282 A f b s) : term282 A f b s.
Proof. exact (h1). Qed.
Lemma lem6981946 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term275 A) (h2 : term282 A f b s) : term283 A s f b.
Proof. exact (@lem6981944 A s f b h1 (@lem6981945 A f b s h2)). Qed.
Lemma lem6981947 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term282 A f b s) : term284 A s f b.
Proof. exact (fun h0 : term275 A => @lem6981946 A f b s h0 h1). Qed.
Lemma lem6981948 {A : Type'} (h1 : term275 A) : term275 A.
Proof. exact (h1). Qed.
Lemma lem6981949 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term275 A) (h2 : term282 A f b s) : term283 A s f b.
Proof. exact (@lem6981947 A f b s h2 (@lem6981948 A h1)). Qed.
Lemma lem6981950 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term275 A) : term281 A s f b.
Proof. exact (fun h0 : term282 A f b s => @lem6981949 A f b s h1 h0). Qed.
Lemma lem6981951 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term275 A) : term279 A s f.
Proof. exact (fun b : nat => @lem6981950 A s f b h1). Qed.
Lemma lem6981952 {A : Type'} (s : A -> Prop) (h1 : term275 A) : term277 A s.
Proof. exact (fun f : A -> nat => @lem6981951 A s f h1). Qed.
Lemma lem6981953 {A : Type'} (h1 : term275 A) : term275 A.
Proof. exact (fun s : A -> Prop => @lem6981952 A s h1). Qed.
Lemma lem6981954 {A : Type'} : term285 A.
Proof. exact (fun h0 : term275 A => @lem6981953 A h0). Qed.
Lemma lem6981955 {A : Type'} : term275 A.
Proof. exact (@lem6981954 A (@lem6974600 A)). Qed.
Lemma lem6981956 {A : Type'} (s : A -> Prop) : term276 A s.
Proof. exact (@lem6981955 A s). Qed.
Lemma lem6981957 {A : Type'} (s : A -> Prop) : (term276 A s) = (term277 A s).
Proof. exact (eq_refl (term276 A s)). Qed.
Lemma lem6981958 {A : Type'} (s : A -> Prop) : term277 A s.
Proof. exact (EQ_MP (@lem6981957 A s) (@lem6981956 A s)). Qed.
Lemma lem6981959 {A : Type'} (s : A -> Prop) (f : A -> nat) : term278 A s f.
Proof. exact (@lem6981958 A s f). Qed.
Lemma lem6981960 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term278 A s f) = (term279 A s f).
Proof. exact (eq_refl (term278 A s f)). Qed.
Lemma lem6981961 {A : Type'} (s : A -> Prop) (f : A -> nat) : term279 A s f.
Proof. exact (EQ_MP (@lem6981960 A s f) (@lem6981959 A s f)). Qed.
Lemma lem6981962 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : term280 A s f b.
Proof. exact (@lem6981961 A s f b). Qed.
Lemma lem6981963 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term280 A s f b) = (term281 A s f b).
Proof. exact (eq_refl (term280 A s f b)). Qed.
Lemma lem6981965 {_127128 : Type'} (h1 : term286 _127128) : term286 _127128.
Proof. exact (h1). Qed.
Lemma lem6981966 {_127128 : Type'} (f : _127128 -> nat) (h1 : term286 _127128) : term287 _127128 f.
Proof. exact (@lem6981965 _127128 h1 f). Qed.
Lemma lem6981967 {_127128 : Type'} (f : _127128 -> nat) : (term287 _127128 f) = (term288 _127128 f).
Proof. exact (eq_refl (term287 _127128 f)). Qed.
Lemma lem6981968 {_127128 : Type'} (f : _127128 -> nat) (h1 : term286 _127128) : term288 _127128 f.
Proof. exact (EQ_MP (@lem6981967 _127128 f) (@lem6981966 _127128 f h1)). Qed.
Lemma lem6981969 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (h1 : term286 _127128) : term289 _127128 f g.
Proof. exact (@lem6981968 _127128 f h1 g). Qed.
Lemma lem6981970 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term289 _127128 f g) = (term290 _127128 f g).
Proof. exact (eq_refl (term289 _127128 f g)). Qed.
Lemma lem6981971 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (h1 : term286 _127128) : term290 _127128 f g.
Proof. exact (EQ_MP (@lem6981970 _127128 f g) (@lem6981969 _127128 f g h1)). Qed.
Lemma lem6981972 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) (h1 : term286 _127128) : term291 _127128 f g s.
Proof. exact (@lem6981971 _127128 f g h1 s). Qed.
Lemma lem6981973 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term291 _127128 f g s) = (term292 _127128 f s g).
Proof. exact (eq_refl (term291 _127128 f g s)). Qed.
Lemma lem6981974 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term286 _127128) : term292 _127128 f s g.
Proof. exact (EQ_MP (@lem6981973 _127128 f s g) (@lem6981972 _127128 f g s h1)). Qed.
Lemma lem6981975 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (h1 : term293 _127128 s f g) : term293 _127128 s f g.
Proof. exact (h1). Qed.
Lemma lem6981976 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (h1 : term286 _127128) (h2 : term293 _127128 s f g) : term294 _127128 f s g.
Proof. exact (@lem6981974 _127128 f s g h1 (@lem6981975 _127128 s f g h2)). Qed.
Lemma lem6981977 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (h1 : term293 _127128 s f g) : term295 _127128 f s g.
Proof. exact (fun h0 : term286 _127128 => @lem6981976 _127128 s f g h0 h1). Qed.
Lemma lem6981978 {_127128 : Type'} (h1 : term286 _127128) : term286 _127128.
Proof. exact (h1). Qed.
Lemma lem6981979 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (h1 : term286 _127128) (h2 : term293 _127128 s f g) : term294 _127128 f s g.
Proof. exact (@lem6981977 _127128 s f g h2 (@lem6981978 _127128 h1)). Qed.
Lemma lem6981980 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term286 _127128) : term292 _127128 f s g.
Proof. exact (fun h0 : term293 _127128 s f g => @lem6981979 _127128 s f g h1 h0). Qed.
Lemma lem6981981 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (h1 : term286 _127128) : term296 _127128 f s.
Proof. exact (fun g : _127128 -> nat => @lem6981980 _127128 f s g h1). Qed.
Lemma lem6981982 {_127128 : Type'} (f : _127128 -> nat) (h1 : term286 _127128) : term297 _127128 f.
Proof. exact (fun s : _127128 -> Prop => @lem6981981 _127128 f s h1). Qed.
Lemma lem6981983 {_127128 : Type'} (h1 : term286 _127128) : term298 _127128.
Proof. exact (fun f : _127128 -> nat => @lem6981982 _127128 f h1). Qed.
Lemma lem6981984 {_127128 : Type'} : term299 _127128.
Proof. exact (fun h0 : term286 _127128 => @lem6981983 _127128 h0). Qed.
Lemma lem6981985 {_127128 : Type'} : term298 _127128.
Proof. exact (@lem6981984 _127128 (@lem6938734 _127128)). Qed.
Lemma lem6981986 {_127128 : Type'} (f : _127128 -> nat) : term300 _127128 f.
Proof. exact (@lem6981985 _127128 f). Qed.
Lemma lem6981987 {_127128 : Type'} (f : _127128 -> nat) : (term300 _127128 f) = (term297 _127128 f).
Proof. exact (eq_refl (term300 _127128 f)). Qed.
Lemma lem6981988 {_127128 : Type'} (f : _127128 -> nat) : term297 _127128 f.
Proof. exact (EQ_MP (@lem6981987 _127128 f) (@lem6981986 _127128 f)). Qed.
Lemma lem6981989 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) : term301 _127128 f s.
Proof. exact (@lem6981988 _127128 f s). Qed.
Lemma lem6981990 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) : (term301 _127128 f s) = (term296 _127128 f s).
Proof. exact (eq_refl (term301 _127128 f s)). Qed.
Lemma lem6981991 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) : term296 _127128 f s.
Proof. exact (EQ_MP (@lem6981990 _127128 f s) (@lem6981989 _127128 f s)). Qed.
Lemma lem6981992 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : term302 _127128 f s g.
Proof. exact (@lem6981991 _127128 f s g). Qed.
Lemma lem6981993 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term302 _127128 f s g) = (term292 _127128 f s g).
Proof. exact (eq_refl (term302 _127128 f s g)). Qed.
Lemma lem6981995 (h1 : term303) : term303.
Proof. exact (h1). Qed.
Lemma lem6981996 (m : nat) (h1 : term303) : term304 m.
Proof. exact (@lem6981995 h1 m). Qed.
Lemma lem6981997 (m : nat) : (term304 m) = (term305 m).
Proof. exact (eq_refl (term304 m)). Qed.
Lemma lem6981998 (m : nat) (h1 : term303) : term305 m.
Proof. exact (EQ_MP (@lem6981997 m) (@lem6981996 m h1)). Qed.
Lemma lem6981999 (m : nat) (n : nat) (h1 : term303) : term306 m n.
Proof. exact (@lem6981998 m h1 n). Qed.
Lemma lem6982000 (n : nat) (m : nat) : (term306 m n) = (term307 n m).
Proof. exact (eq_refl (term306 m n)). Qed.
Lemma lem6982001 (n : nat) (m : nat) (h1 : term303) : term307 n m.
Proof. exact (EQ_MP (@lem6982000 n m) (@lem6981999 m n h1)). Qed.
Lemma lem6982002 (n : nat) (m : nat) (p : nat) (h1 : term303) : term308 n m p.
Proof. exact (@lem6982001 n m h1 p). Qed.
Lemma lem6982003 (n : nat) (m : nat) (p : nat) : (term308 n m p) = (term309 n m p).
Proof. exact (eq_refl (term308 n m p)). Qed.
Lemma lem6982004 (n : nat) (m : nat) (p : nat) (h1 : term303) : term309 n m p.
Proof. exact (EQ_MP (@lem6982003 n m p) (@lem6982002 n m p h1)). Qed.
Lemma lem6982005 (m : nat) (n : nat) (p : nat) (h1 : term310 m n p) : term310 m n p.
Proof. exact (h1). Qed.
Lemma lem6982006 (m : nat) (n : nat) (p : nat) (h1 : term303) (h2 : term310 m n p) : Peano.lt m p.
Proof. exact (@lem6982004 n m p h1 (@lem6982005 m n p h2)). Qed.
Lemma lem6982007 (m : nat) (n : nat) (p : nat) (h1 : term310 m n p) : term311 m p.
Proof. exact (fun h0 : term303 => @lem6982006 m n p h0 h1). Qed.
Lemma lem6982008 (m : nat) (p : nat) (h1 : term312 m p) : term312 m p.
Proof. exact (h1). Qed.
Lemma lem6982009 (m : nat) (p : nat) (h1 : term312 m p) : term311 m p.
Proof. exact (ex_elim (@lem6982008 m p h1) (fun n : nat => fun h0 : term313 m p n => @lem6982007 m n p h0)). Qed.
Lemma lem6982010 (h1 : term303) : term303.
Proof. exact (h1). Qed.
Lemma lem6982011 (m : nat) (p : nat) (h1 : term303) (h2 : term312 m p) : Peano.lt m p.
Proof. exact (@lem6982009 m p h2 (@lem6982010 h1)). Qed.
Lemma lem6982012 (m : nat) (p : nat) (h1 : term303) : term314 m p.
Proof. exact (fun h0 : term312 m p => @lem6982011 m p h1 h0). Qed.
Lemma lem6982013 (m : nat) (h1 : term303) : term315 m.
Proof. exact (fun p : nat => @lem6982012 m p h1). Qed.
Lemma lem6982014 (h1 : term303) : term316.
Proof. exact (fun m : nat => @lem6982013 m h1). Qed.
Lemma lem6982015 : term317.
Proof. exact (fun h0 : term303 => @lem6982014 h0). Qed.
Lemma lem6982016 : term316.
Proof. exact (@lem6982015 (@lem95941)). Qed.
Lemma lem6982017 (m : nat) : term318 m.
Proof. exact (@lem6982016 m). Qed.
Lemma lem6982018 (m : nat) : (term318 m) = (term315 m).
Proof. exact (eq_refl (term318 m)). Qed.
Lemma lem6982019 (m : nat) : term315 m.
Proof. exact (EQ_MP (@lem6982018 m) (@lem6982017 m)). Qed.
Lemma lem6982020 (m : nat) (p : nat) : term319 m p.
Proof. exact (@lem6982019 m p). Qed.
Lemma lem6982021 (m : nat) (p : nat) : (term319 m p) = (term314 m p).
Proof. exact (eq_refl (term319 m p)). Qed.
Lemma lem6982023 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term320 A f b s) : term320 A f b s.
Proof. exact (h1). Qed.
Lemma lem6982024 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term321 A f b s) : term321 A f b s.
Proof. exact (h1). Qed.
Lemma lem6982025 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6982026 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term322 A f b s) : term322 A f b s.
Proof. exact (h1). Qed.
Lemma lem6982027 {A : Type'} (s : A -> Prop) (h1 : term323 A s) : term323 A s.
Proof. exact (h1). Qed.
Lemma lem6982029 (m : nat) (p : nat) : term314 m p.
Proof. exact (EQ_MP (@lem6982021 m p) (@lem6982020 m p)). Qed.
Lemma lem6982030 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : term324 A s f b.
Proof. exact (@lem6982029 (@nsum A s f) b). Qed.
Lemma lem6982032 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : term292 _127128 f s g.
Proof. exact (EQ_MP (@lem6981993 _127128 f s g) (@lem6981992 _127128 f s g)). Qed.
Lemma lem6982033 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : term292 A f s g.
Proof. exact (@lem6982032 A f s g). Qed.
Lemma lem6982034 {A : Type'} (s : A -> Prop) (f : A -> nat) : term325 A s f.
Proof. exact (@lem6982033 A f s (term326 A f)). Qed.
Lemma lem6982035 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem6982037 {A : Type'} (s : A -> Prop) : term327 A s.
Proof. exact (@lem82 (s = (@EMPTY A))). Qed.
Lemma lem6982065 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6982035 A s) (@lem6982025 A s h1)). Qed.
Lemma lem6982066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6982067 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term328 A s) = (and True).
Proof. exact (MK_COMB (@lem6982066) (@lem6982065 A s h1)). Qed.
Lemma lem6982071 {A : Type'} (s : A -> Prop) (h1 : term323 A s) : (s = (@EMPTY A)) = False.
Proof. exact (@lem6982037 A s (@lem6982027 A s h1)). Qed.
Lemma lem6982072 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6982073 {A : Type'} (s : A -> Prop) (h1 : term323 A s) : (term323 A s) = (~ False).
Proof. exact (MK_COMB (@lem6982072) (@lem6982071 A s h1)). Qed.
Lemma lem6982075 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem6982076 {A : Type'} (s : A -> Prop) (h1 : term323 A s) : (term323 A s) = True.
Proof. exact (TRANS (@lem6982073 A s h1) (@lem6982075)). Qed.
Lemma lem6982077 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6982078 {A : Type'} (s : A -> Prop) (h1 : term323 A s) : (term329 A s) = (and True).
Proof. exact (MK_COMB (@lem6982077) (@lem6982076 A s h1)). Qed.
Lemma lem6982086 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term330 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6982087 (p : Prop) (q : Prop) (p' : Prop) : term331 p q p'.
Proof. exact (fun q' : Prop => @lem6982086 p q p' q'). Qed.
Lemma lem6982088 (p : Prop) (q : Prop) : term332 p q.
Proof. exact (fun p' : Prop => @lem6982087 p q p'). Qed.
Lemma lem6982089 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : term333 A s f x.
Proof. exact (@lem6982088 (@IN A x s) (term334 A f x)). Qed.
Lemma lem6982090 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) : term335 A s f x p'.
Proof. exact (@lem6982089 A s f x p'). Qed.
Lemma lem6982091 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) : (term335 A s f x p') = (term336 A s f x p').
Proof. exact (eq_refl (term335 A s f x p')). Qed.
Lemma lem6982092 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) : term336 A s f x p'.
Proof. exact (EQ_MP (@lem6982091 A s f x p') (@lem6982090 A s f x p')). Qed.
Lemma lem6982093 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) (q' : Prop) : term337 A s f x p' q'.
Proof. exact (@lem6982092 A s f x p' q'). Qed.
Lemma lem6982094 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) (q' : Prop) : (term337 A s f x p' q') = (term338 A s f x p' q').
Proof. exact (eq_refl (term337 A s f x p' q')). Qed.
Lemma lem6982095 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) (q' : Prop) : term338 A s f x p' q'.
Proof. exact (EQ_MP (@lem6982094 A s f x p' q') (@lem6982093 A s f x p' q')). Qed.
Lemma lem6982096 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem6982097 {A : Type'} (f : A -> nat) (x : A) (s : A -> Prop) (q' : Prop) : term339 A f x s q'.
Proof. exact (@lem6982095 A s f x (@IN A x s) q'). Qed.
Lemma lem6982098 {A : Type'} (f : A -> nat) (x : A) (s : A -> Prop) (q' : Prop) : term340 A f x s q'.
Proof. exact (@lem6982097 A f x s q' (@lem6982096 A x s)). Qed.
Lemma lem6982103 {A B : Type'} (f : A -> B) (y : A) : (term341 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6982104 {A : Type'} (f : A -> nat) (y : A) : (term342 A f y) = (f y).
Proof. exact (@lem6982103 A nat f y). Qed.
Lemma lem6982105 {A : Type'} (f : A -> nat) (x : A) : (term343 A f x) = (term344 A f x).
Proof. exact (@lem6982104 A (term326 A f) x). Qed.
Lemma lem6982106 {A : Type'} (f : A -> nat) (a : A) : (term344 A f a) = (term345 A f a).
Proof. exact (eq_refl (term344 A f a)). Qed.
Lemma lem6982107 {A : Type'} (f : A -> nat) : (term346 A f) = (term326 A f).
Proof. exact (fun_ext (fun a : A => @lem6982106 A f a)). Qed.
Lemma lem6982108 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6982109 {A : Type'} (f : A -> nat) (x : A) : (term343 A f x) = (term344 A f x).
Proof. exact (MK_COMB (@lem6982107 A f) (@lem6982108 A x)). Qed.
Lemma lem6982110 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6982111 {A : Type'} (f : A -> nat) (x : A) : (term347 A f x) = (term348 A f x).
Proof. exact (MK_COMB (@lem6982110) (@lem6982109 A f x)). Qed.
Lemma lem6982112 {A : Type'} (f : A -> nat) (x : A) : (term344 A f x) = (term345 A f x).
Proof. exact (eq_refl (term344 A f x)). Qed.
Lemma lem6982113 {A : Type'} (f : A -> nat) (x : A) : ((term343 A f x) = (term344 A f x)) = ((term344 A f x) = (term345 A f x)).
Proof. exact (MK_COMB (@lem6982111 A f x) (@lem6982112 A f x)). Qed.
Lemma lem6982114 {A : Type'} (f : A -> nat) (x : A) : (term344 A f x) = (term345 A f x).
Proof. exact (EQ_MP (@lem6982113 A f x) (@lem6982105 A f x)). Qed.
Lemma lem6982115 {A : Type'} (f : A -> nat) (x : A) : (term349 A f x) = (term349 A f x).
Proof. exact (eq_refl (term349 A f x)). Qed.
Lemma lem6982116 {A : Type'} (f : A -> nat) (x : A) : (term334 A f x) = (term350 A f x).
Proof. exact (MK_COMB (@lem6982115 A f x) (@lem6982114 A f x)). Qed.
Lemma lem6982117 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : term351 A s f x.
Proof. exact (fun h0 : @IN A x s => @lem6982116 A f x). Qed.
Lemma lem6982118 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : term352 A s f x.
Proof. exact (@lem6982098 A f x s (term350 A f x)). Qed.
Lemma lem6982119 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term353 A s f x) = (term354 A s f x).
Proof. exact (@lem6982118 A s f x (@lem6982117 A s f x)). Qed.
Lemma lem6982143 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term355 A s f) = (term356 A s f).
Proof. exact (fun_ext (fun x : A => @lem6982119 A s f x)). Qed.
Lemma lem6982167 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6982168 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term357 A s f) = (term358 A s f).
Proof. exact (MK_COMB (@lem6982167 A) (@lem6982143 A s f)). Qed.
Lemma lem6982196 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term323 A s) : (term359 A s f) = (term360 A s f).
Proof. exact (MK_COMB (@lem6982078 A s h1) (@lem6982168 A s f)). Qed.
Lemma lem6982198 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6982199 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term360 A s f) = (term358 A s f).
Proof. exact (@lem6982198 (term358 A s f)). Qed.
Lemma lem6982227 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term323 A s) : (term359 A s f) = (term358 A s f).
Proof. exact (TRANS (@lem6982196 A f s h1) (@lem6982199 A s f)). Qed.
Lemma lem6982228 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term323 A s) : (term361 A s f) = (term360 A s f).
Proof. exact (MK_COMB (@lem6982067 A s h1) (@lem6982227 A f s h2)). Qed.
Lemma lem6982230 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6982231 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term360 A s f) = (term358 A s f).
Proof. exact (@lem6982230 (term358 A s f)). Qed.
Lemma lem6982259 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term323 A s) : (term361 A s f) = (term358 A s f).
Proof. exact (TRANS (@lem6982228 A f s h1 h2) (@lem6982231 A s f)). Qed.
Lemma lem6982260 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term323 A s) : (term358 A s f) = (term361 A s f).
Proof. exact (SYM (@lem6982259 A f s h1 h2)). Qed.
Lemma lem6982272 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term354 A s f x) = (term354 A s f x).
Proof. exact (eq_refl (term354 A s f x)). Qed.
Lemma lem6982273 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term356 A s f) = (term356 A s f).
Proof. exact (fun_ext (fun x : A => @lem6982272 A s f x)). Qed.
Lemma lem6982274 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6982276 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term358 A s f) = (term358 A s f).
Proof. exact (MK_COMB (@lem6982274 A) (@lem6982273 A s f)). Qed.
Lemma lem6982283 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term354 A s f x) = (term362 A s f x).
Proof. exact (@lem17265 (@IN A x s) (term350 A f x)). Qed.
Lemma lem6982284 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term356 A s f) = (term363 A s f).
Proof. exact (fun_ext (fun x : A => @lem6982283 A s f x)). Qed.
Lemma lem6982285 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6982286 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term358 A s f) = (term364 A s f).
Proof. exact (MK_COMB (@lem6982285 A) (@lem6982284 A s f)). Qed.
Lemma lem6982287 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term358 A s f) = (term364 A s f).
Proof. exact (TRANS (@lem6982276 A s f) (@lem6982286 A s f)). Qed.
Lemma lem6982288 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term362 A s f x) = (term362 A s f x).
Proof. exact (eq_refl (term362 A s f x)). Qed.
Lemma lem6982289 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term363 A s f) = (term363 A s f).
Proof. exact (fun_ext (fun x : A => @lem6982288 A s f x)). Qed.
Lemma lem6982290 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6982291 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term364 A s f) = (term364 A s f).
Proof. exact (MK_COMB (@lem6982290 A) (@lem6982289 A s f)). Qed.
Lemma lem6982304 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term358 A s f) = (term364 A s f).
Proof. exact (TRANS (@lem6982287 A s f) (@lem6982291 A s f)). Qed.
Lemma lem6982325 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term362 A s f x) = (term362 A s f x).
Proof. exact (eq_refl (term362 A s f x)). Qed.
Lemma lem6982326 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term363 A s f) = (term363 A s f).
Proof. exact (fun_ext (fun x : A => @lem6982325 A s f x)). Qed.
Lemma lem6982327 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6982328 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term364 A s f) = (term364 A s f).
Proof. exact (MK_COMB (@lem6982327 A) (@lem6982326 A s f)). Qed.
Lemma lem6982331 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term358 A s f) = (term364 A s f).
Proof. exact (TRANS (@lem6982304 A s f) (@lem6982328 A s f)). Qed.
Lemma lem6982333 (m : nat) (n : nat) : (Peano.lt m n) = (term15 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem6982334 {A : Type'} (f : A -> nat) (x : A) : (term350 A f x) = (term365 A f x).
Proof. exact (@lem6982333 (f x) (term345 A f x)). Qed.
Lemma lem6982336 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem6982337 {A : Type'} (f : A -> nat) (x : A) : (term366 A f x) = (term367 A f x).
Proof. exact (@lem6982336 (f x) term9). Qed.
Lemma lem6982338 {A : Type'} (f : A -> nat) (x : A) : (term368 A f x) = (term368 A f x).
Proof. exact (eq_refl (term368 A f x)). Qed.
Lemma lem6982339 {A : Type'} (f : A -> nat) (x : A) : (term365 A f x) = (term369 A f x).
Proof. exact (MK_COMB (@lem6982338 A f x) (@lem6982337 A f x)). Qed.
Lemma lem6982340 {A : Type'} (f : A -> nat) (x : A) : (term350 A f x) = (term369 A f x).
Proof. exact (TRANS (@lem6982334 A f x) (@lem6982339 A f x)). Qed.
Lemma lem6982341 {A : Type'} (x : A) (s : A -> Prop) : (term370 A x s) = (term370 A x s).
Proof. exact (eq_refl (term370 A x s)). Qed.
Lemma lem6982342 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term362 A s f x) = (term371 A s f x).
Proof. exact (MK_COMB (@lem6982341 A x s) (@lem6982340 A f x)). Qed.
Lemma lem6982343 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term363 A s f) = (term372 A s f).
Proof. exact (fun_ext (fun x : A => @lem6982342 A s f x)). Qed.
Lemma lem6982344 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6982345 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term364 A s f) = (term373 A s f).
Proof. exact (MK_COMB (@lem6982344 A) (@lem6982343 A s f)). Qed.
Lemma lem6982346 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term358 A s f) = (term373 A s f).
Proof. exact (TRANS (@lem6982331 A s f) (@lem6982345 A s f)). Qed.
Lemma lem6982347 {A : Type'} (f : A -> nat) (x : A) : term374 A f x.
Proof. exact (@lem2307535 (f x)). Qed.
Lemma lem6982348 {A : Type'} (f : A -> nat) (x : A) : (term374 A f x) = (term375 A f x).
Proof. exact (eq_refl (term374 A f x)). Qed.
Lemma lem6982349 {A : Type'} (f : A -> nat) (x : A) : term375 A f x.
Proof. exact (EQ_MP (@lem6982348 A f x) (@lem6982347 A f x)). Qed.
Lemma lem6982350 {A : Type'} (x : A) (s : A -> Prop) (_92990 : int) : (term376 A x s _92990) = (term377 A x s _92990).
Proof. exact (@lem2318604 (term377 A x s _92990)). Qed.
Lemma lem6982363 {A : Type'} (x : A) (s : A -> Prop) : (term378 A x s) = (@IN A x s).
Proof. exact (@lem16933 (@IN A x s)). Qed.
Lemma lem6982364 (_92990 : int) : (term379 _92990) = (term379 _92990).
Proof. exact (eq_refl (term379 _92990)). Qed.
Lemma lem6982365 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6982366 {A : Type'} (x : A) (s : A -> Prop) : (term380 A x s) = (term381 A x s).
Proof. exact (MK_COMB (@lem6982365) (@lem6982363 A x s)). Qed.
Lemma lem6982367 {A : Type'} (x : A) (s : A -> Prop) (_92990 : int) : (term382 A x s _92990) = (term383 A x s _92990).
Proof. exact (MK_COMB (@lem6982366 A x s) (@lem6982364 _92990)). Qed.
Lemma lem6982368 {A : Type'} (x : A) (s : A -> Prop) (_92990 : int) : (term384 A x s _92990) = (term382 A x s _92990).
Proof. exact (@lem17160 (term385 A x s) (term386 _92990)). Qed.
Lemma lem6982369 {A : Type'} (x : A) (s : A -> Prop) (_92990 : int) : (term384 A x s _92990) = (term383 A x s _92990).
Proof. exact (TRANS (@lem6982368 A x s _92990) (@lem6982367 A x s _92990)). Qed.
Lemma lem6982371 (_92990 : int) : (term52 _92990) = (term52 _92990).
Proof. exact (eq_refl (term52 _92990)). Qed.
Lemma lem6982372 {A : Type'} (x : A) (s : A -> Prop) (_92990 : int) : (term387 A x s _92990) = (term388 A x s _92990).
Proof. exact (MK_COMB (@lem6982371 _92990) (@lem6982369 A x s _92990)). Qed.
Lemma lem6982373 {A : Type'} (x : A) (s : A -> Prop) (_92990 : int) : (term389 A x s _92990) = (term387 A x s _92990).
Proof. exact (@lem17362 (term56 _92990) (term390 A x s _92990)). Qed.
Lemma lem6982387 {A : Type'} (x : A) (s : A -> Prop) (_92990 : int) : (term389 A x s _92990) = (term388 A x s _92990).
Proof. exact (TRANS (@lem6982373 A x s _92990) (@lem6982372 A x s _92990)). Qed.
Lemma lem6982390 (x : int) (y : int) : (int_le x y) = (term62 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6982391 (_92990 : int) : (term56 _92990) = (term63 _92990).
Proof. exact (@lem6982390 term64 _92990). Qed.
Lemma lem6982393 (n : nat) : (term65 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6982394 : term66 = term67.
Proof. exact (@lem6982393 (NUMERAL 0)). Qed.
Lemma lem6982395 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6982396 : term68 = term69.
Proof. exact (MK_COMB (@lem6982395) (@lem6982394)). Qed.
Lemma lem6982397 (_92990 : int) : (real_of_int _92990) = (real_of_int _92990).
Proof. exact (eq_refl (real_of_int _92990)). Qed.
Lemma lem6982398 (_92990 : int) : (term63 _92990) = (term70 _92990).
Proof. exact (MK_COMB (@lem6982396) (@lem6982397 _92990)). Qed.
Lemma lem6982400 (_92990 : int) : (term56 _92990) = (term70 _92990).
Proof. exact (TRANS (@lem6982391 _92990) (@lem6982398 _92990)). Qed.
Lemma lem6982405 (y : int) (x : int) : (term44 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem6982406 (_92990 : int) : (term379 _92990) = (term391 _92990).
Proof. exact (@lem6982405 (term73 _92990) _92990). Qed.
Lemma lem6982408 (x : int) (y : int) : (int_le x y) = (term62 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6982409 (_92990 : int) : (term391 _92990) = (term392 _92990).
Proof. exact (@lem6982408 (term73 _92990) _92990). Qed.
Lemma lem6982411 (x : int) (y : int) : (term75 x y) = (term76 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6982412 (_92990 : int) : (term77 _92990) = (term78 _92990).
Proof. exact (@lem6982411 _92990 term79). Qed.
Lemma lem6982414 (n : nat) : (term65 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6982415 : term80 = term81.
Proof. exact (@lem6982414 term9). Qed.
Lemma lem6982416 (_92990 : int) : (term82 _92990) = (term82 _92990).
Proof. exact (eq_refl (term82 _92990)). Qed.
Lemma lem6982417 (_92990 : int) : (term78 _92990) = (term83 _92990).
Proof. exact (MK_COMB (@lem6982416 _92990) (@lem6982415)). Qed.
Lemma lem6982418 (_92990 : int) : (term77 _92990) = (term83 _92990).
Proof. exact (TRANS (@lem6982412 _92990) (@lem6982417 _92990)). Qed.
Lemma lem6982419 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6982420 (_92990 : int) : (term84 _92990) = (term85 _92990).
Proof. exact (MK_COMB (@lem6982419) (@lem6982418 _92990)). Qed.
Lemma lem6982421 (_92990 : int) : (real_of_int _92990) = (real_of_int _92990).
Proof. exact (eq_refl (real_of_int _92990)). Qed.
Lemma lem6982422 (_92990 : int) : (term392 _92990) = (term393 _92990).
Proof. exact (MK_COMB (@lem6982420 _92990) (@lem6982421 _92990)). Qed.
Lemma lem6982423 (_92990 : int) : (term391 _92990) = (term393 _92990).
Proof. exact (TRANS (@lem6982409 _92990) (@lem6982422 _92990)). Qed.
Lemma lem6982424 (_92990 : int) : (term379 _92990) = (term393 _92990).
Proof. exact (TRANS (@lem6982406 _92990) (@lem6982423 _92990)). Qed.
Lemma lem6982426 {A : Type'} (x : A) (s : A -> Prop) : (term381 A x s) = (term381 A x s).
Proof. exact (eq_refl (term381 A x s)). Qed.
Lemma lem6982427 {A : Type'} (x : A) (s : A -> Prop) (_92990 : int) : (term383 A x s _92990) = (term394 A x s _92990).
Proof. exact (MK_COMB (@lem6982426 A x s) (@lem6982424 _92990)). Qed.
Lemma lem6982428 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6982429 (_92990 : int) : (term52 _92990) = (term96 _92990).
Proof. exact (MK_COMB (@lem6982428) (@lem6982400 _92990)). Qed.
Lemma lem6982430 {A : Type'} (x : A) (s : A -> Prop) (_92990 : int) : (term388 A x s _92990) = (term395 A x s _92990).
Proof. exact (MK_COMB (@lem6982429 _92990) (@lem6982427 A x s _92990)). Qed.
Lemma lem6982431 {A : Type'} (x : A) (s : A -> Prop) (_92990 : int) : (term389 A x s _92990) = (term395 A x s _92990).
Proof. exact (TRANS (@lem6982387 A x s _92990) (@lem6982430 A x s _92990)). Qed.
Lemma lem6982435 (t : Prop) : (term99 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6982461 {A : Type'} (x : A) (s : A -> Prop) (_92990 : int) : (term396 A x s _92990) = (term395 A x s _92990).
Proof. exact (@lem6982435 (term395 A x s _92990)). Qed.
Lemma lem6982462 (_92990 : int) : (term70 _92990) = (term104 _92990).
Proof. exact (@lem1988287 (real_of_int _92990) term67). Qed.
Lemma lem6982468 (_92990 : int) : (term105 _92990) = (term106 _92990).
Proof. exact (@lem1982792 (real_of_int _92990) term67). Qed.
Lemma lem6982470 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6982471 : term67 = term108.
Proof. exact (@lem6982470 (NUMERAL 0)). Qed.
Lemma lem6982473 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6982474 : term111 = term112.
Proof. exact (@lem6982473 term9). Qed.
Lemma lem6982475 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6982476 : term113 = term114.
Proof. exact (MK_COMB (@lem6982475) (@lem6982474)). Qed.
Lemma lem6982477 : term115 = term116.
Proof. exact (MK_COMB (@lem6982476) (@lem6982471)). Qed.
Lemma lem6982478 : term116 = term117.
Proof. exact (@lem1981613 term111 term67 term81 term81). Qed.
Lemma lem6982480 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6982481 : term120 = term121.
Proof. exact (@lem6982480 term9 term9). Qed.
Lemma lem6982482 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6982483 : term123 = term9.
Proof. exact (EQ_MP (@lem6982482) (@lem940073)). Qed.
Lemma lem6982484 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6982485 : term121 = term81.
Proof. exact (MK_COMB (@lem6982484) (@lem6982483)). Qed.
Lemma lem6982486 : term120 = term81.
Proof. exact (TRANS (@lem6982481) (@lem6982485)). Qed.
Lemma lem6982488 (x : nat) : (term124 x) = term67.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6982489 : term115 = term67.
Proof. exact (@lem6982488 term9). Qed.
Lemma lem6982490 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6982491 : term125 = term126.
Proof. exact (MK_COMB (@lem6982490) (@lem6982489)). Qed.
Lemma lem6982492 : term117 = term108.
Proof. exact (MK_COMB (@lem6982491) (@lem6982486)). Qed.
Lemma lem6982493 : term116 = term108.
Proof. exact (TRANS (@lem6982478) (@lem6982492)). Qed.
Lemma lem6982494 : term115 = term108.
Proof. exact (TRANS (@lem6982477) (@lem6982493)). Qed.
Lemma lem6982496 (x : real) : (term127 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6982497 : term108 = term67.
Proof. exact (@lem6982496 term67). Qed.
Lemma lem6982498 : term115 = term67.
Proof. exact (TRANS (@lem6982494) (@lem6982497)). Qed.
Lemma lem6982499 (_92990 : int) : (term82 _92990) = (term82 _92990).
Proof. exact (eq_refl (term82 _92990)). Qed.
Lemma lem6982500 (_92990 : int) : (term106 _92990) = (term128 _92990).
Proof. exact (MK_COMB (@lem6982499 _92990) (@lem6982498)). Qed.
Lemma lem6982501 (_92990 : int) : (term128 _92990) = (real_of_int _92990).
Proof. exact (@lem1982723 (real_of_int _92990)). Qed.
Lemma lem6982502 (_92990 : int) : (term106 _92990) = (real_of_int _92990).
Proof. exact (TRANS (@lem6982500 _92990) (@lem6982501 _92990)). Qed.
Lemma lem6982504 (_92990 : int) : (term105 _92990) = (real_of_int _92990).
Proof. exact (TRANS (@lem6982468 _92990) (@lem6982502 _92990)). Qed.
Lemma lem6982505 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6982506 (_92990 : int) : (term129 _92990) = (term130 _92990).
Proof. exact (MK_COMB (@lem6982505) (@lem6982504 _92990)). Qed.
Lemma lem6982507 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem6982508 (_92990 : int) : (term104 _92990) = (term131 _92990).
Proof. exact (MK_COMB (@lem6982506 _92990) (@lem6982507)). Qed.
Lemma lem6982509 (_92990 : int) : (term70 _92990) = (term131 _92990).
Proof. exact (TRANS (@lem6982462 _92990) (@lem6982508 _92990)). Qed.
Lemma lem6982511 (_92990 : int) : (term393 _92990) = (term397 _92990).
Proof. exact (@lem1988287 (real_of_int _92990) (term83 _92990)). Qed.
Lemma lem6982523 (_92990 : int) : (term398 _92990) = (term399 _92990).
Proof. exact (@lem1982792 (real_of_int _92990) (term83 _92990)). Qed.
Lemma lem6982524 (_92990 : int) : (term135 _92990) = (term136 _92990).
Proof. exact (@lem1982781 (real_of_int _92990) term111 term81). Qed.
Lemma lem6982526 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6982527 : term81 = term137.
Proof. exact (@lem6982526 term9). Qed.
Lemma lem6982529 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6982530 : term111 = term112.
Proof. exact (@lem6982529 term9). Qed.
Lemma lem6982531 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6982532 : term113 = term114.
Proof. exact (MK_COMB (@lem6982531) (@lem6982530)). Qed.
Lemma lem6982533 : term138 = term139.
Proof. exact (MK_COMB (@lem6982532) (@lem6982527)). Qed.
Lemma lem6982534 : term139 = term140.
Proof. exact (@lem1981613 term111 term81 term81 term81). Qed.
Lemma lem6982536 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6982537 : term120 = term121.
Proof. exact (@lem6982536 term9 term9). Qed.
Lemma lem6982538 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6982539 : term123 = term9.
Proof. exact (EQ_MP (@lem6982538) (@lem940073)). Qed.
Lemma lem6982540 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6982541 : term121 = term81.
Proof. exact (MK_COMB (@lem6982540) (@lem6982539)). Qed.
Lemma lem6982542 : term120 = term81.
Proof. exact (TRANS (@lem6982537) (@lem6982541)). Qed.
Lemma lem6982544 (m : nat) (n : nat) : (term141 m n) = (term142 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6982545 : term138 = term143.
Proof. exact (@lem6982544 term9 term9). Qed.
Lemma lem6982546 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6982547 : term123 = term9.
Proof. exact (EQ_MP (@lem6982546) (@lem940073)). Qed.
Lemma lem6982548 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6982549 : term121 = term81.
Proof. exact (MK_COMB (@lem6982548) (@lem6982547)). Qed.
Lemma lem6982550 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6982551 : term143 = term111.
Proof. exact (MK_COMB (@lem6982550) (@lem6982549)). Qed.
Lemma lem6982552 : term138 = term111.
Proof. exact (TRANS (@lem6982545) (@lem6982551)). Qed.
Lemma lem6982553 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6982554 : term144 = term145.
Proof. exact (MK_COMB (@lem6982553) (@lem6982552)). Qed.
Lemma lem6982555 : term140 = term112.
Proof. exact (MK_COMB (@lem6982554) (@lem6982542)). Qed.
Lemma lem6982556 : term139 = term112.
Proof. exact (TRANS (@lem6982534) (@lem6982555)). Qed.
Lemma lem6982557 : term138 = term112.
Proof. exact (TRANS (@lem6982533) (@lem6982556)). Qed.
Lemma lem6982559 (x : real) : (term127 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6982560 : term112 = term111.
Proof. exact (@lem6982559 term111). Qed.
Lemma lem6982561 : term138 = term111.
Proof. exact (TRANS (@lem6982557) (@lem6982560)). Qed.
Lemma lem6982564 (_92990 : int) : (term146 _92990) = (term146 _92990).
Proof. exact (eq_refl (term146 _92990)). Qed.
Lemma lem6982565 (_92990 : int) : (term136 _92990) = (term147 _92990).
Proof. exact (MK_COMB (@lem6982564 _92990) (@lem6982561)). Qed.
Lemma lem6982566 (_92990 : int) : (term135 _92990) = (term147 _92990).
Proof. exact (TRANS (@lem6982524 _92990) (@lem6982565 _92990)). Qed.
Lemma lem6982567 (_92990 : int) : (term82 _92990) = (term82 _92990).
Proof. exact (eq_refl (term82 _92990)). Qed.
Lemma lem6982568 (_92990 : int) : (term399 _92990) = (term400 _92990).
Proof. exact (MK_COMB (@lem6982567 _92990) (@lem6982566 _92990)). Qed.
Lemma lem6982569 (_92990 : int) : (term400 _92990) = (term252 _92990).
Proof. exact (@lem1982763 (real_of_int _92990) (term153 _92990) term111). Qed.
Lemma lem6982570 (_92990 : int) : (term253 _92990) = (term233 _92990).
Proof. exact (@lem1982715 term111 (real_of_int _92990)). Qed.
Lemma lem6982572 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6982573 : term81 = term137.
Proof. exact (@lem6982572 term9). Qed.
Lemma lem6982575 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6982576 : term111 = term112.
Proof. exact (@lem6982575 term9). Qed.
Lemma lem6982577 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6982578 : term234 = term235.
Proof. exact (MK_COMB (@lem6982577) (@lem6982576)). Qed.
Lemma lem6982579 : term236 = term237.
Proof. exact (MK_COMB (@lem6982578) (@lem6982573)). Qed.
Lemma lem6982580 : term238.
Proof. exact (@lem1981473 term111 term81 term81 term81 term67 term81). Qed.
Lemma lem6982582 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6982583 : term160 = term161.
Proof. exact (@lem6982582 (NUMERAL 0) term9). Qed.
Lemma lem6982584 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6982585 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6982586 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6982585 h1) (fun h1 : term161 = True => @lem6982584)). Qed.
Lemma lem6982587 : term161 = True.
Proof. exact (EQ_MP (@lem6982586) (@lem6982584)). Qed.
Lemma lem6982588 : term160 = True.
Proof. exact (TRANS (@lem6982583) (@lem6982587)). Qed.
Lemma lem6982589 : True = term160.
Proof. exact (SYM (@lem6982588)). Qed.
Lemma lem6982590 : term160.
Proof. exact (EQ_MP (@lem6982589) (@lem0)). Qed.
Lemma lem6982591 : term239.
Proof. exact (@lem6982580 (@lem6982590)). Qed.
Lemma lem6982593 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6982594 : term160 = term161.
Proof. exact (@lem6982593 (NUMERAL 0) term9). Qed.
Lemma lem6982595 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6982596 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6982597 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6982596 h1) (fun h1 : term161 = True => @lem6982595)). Qed.
Lemma lem6982598 : term161 = True.
Proof. exact (EQ_MP (@lem6982597) (@lem6982595)). Qed.
Lemma lem6982599 : term160 = True.
Proof. exact (TRANS (@lem6982594) (@lem6982598)). Qed.
Lemma lem6982600 : True = term160.
Proof. exact (SYM (@lem6982599)). Qed.
Lemma lem6982601 : term160.
Proof. exact (EQ_MP (@lem6982600) (@lem0)). Qed.
Lemma lem6982602 : term240.
Proof. exact (@lem6982591 (@lem6982601)). Qed.
Lemma lem6982604 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6982605 : term160 = term161.
Proof. exact (@lem6982604 (NUMERAL 0) term9). Qed.
Lemma lem6982606 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6982607 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6982608 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6982607 h1) (fun h1 : term161 = True => @lem6982606)). Qed.
Lemma lem6982609 : term161 = True.
Proof. exact (EQ_MP (@lem6982608) (@lem6982606)). Qed.
Lemma lem6982610 : term160 = True.
Proof. exact (TRANS (@lem6982605) (@lem6982609)). Qed.
Lemma lem6982611 : True = term160.
Proof. exact (SYM (@lem6982610)). Qed.
Lemma lem6982612 : term160.
Proof. exact (EQ_MP (@lem6982611) (@lem0)). Qed.
Lemma lem6982613 : term241.
Proof. exact (@lem6982602 (@lem6982612)). Qed.
Lemma lem6982615 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6982616 : term120 = term121.
Proof. exact (@lem6982615 term9 term9). Qed.
Lemma lem6982617 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6982618 : term123 = term9.
Proof. exact (EQ_MP (@lem6982617) (@lem940073)). Qed.
Lemma lem6982619 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6982620 : term121 = term81.
Proof. exact (MK_COMB (@lem6982619) (@lem6982618)). Qed.
Lemma lem6982621 : term120 = term81.
Proof. exact (TRANS (@lem6982616) (@lem6982620)). Qed.
Lemma lem6982623 (m : nat) (n : nat) : (term141 m n) = (term142 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6982624 : term138 = term143.
Proof. exact (@lem6982623 term9 term9). Qed.
Lemma lem6982625 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6982626 : term123 = term9.
Proof. exact (EQ_MP (@lem6982625) (@lem940073)). Qed.
Lemma lem6982627 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6982628 : term121 = term81.
Proof. exact (MK_COMB (@lem6982627) (@lem6982626)). Qed.
Lemma lem6982629 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6982630 : term143 = term111.
Proof. exact (MK_COMB (@lem6982629) (@lem6982628)). Qed.
Lemma lem6982631 : term138 = term111.
Proof. exact (TRANS (@lem6982624) (@lem6982630)). Qed.
Lemma lem6982632 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6982633 : term242 = term234.
Proof. exact (MK_COMB (@lem6982632) (@lem6982631)). Qed.
Lemma lem6982634 : term243 = term236.
Proof. exact (MK_COMB (@lem6982633) (@lem6982621)). Qed.
Lemma lem6982636 (m : nat) : (term244 m) = term67.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6982637 : term236 = term67.
Proof. exact (@lem6982636 term9). Qed.
Lemma lem6982638 : term243 = term67.
Proof. exact (TRANS (@lem6982634) (@lem6982637)). Qed.
Lemma lem6982639 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6982640 : term245 = term170.
Proof. exact (MK_COMB (@lem6982639) (@lem6982638)). Qed.
Lemma lem6982641 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem6982642 : term246 = term172.
Proof. exact (MK_COMB (@lem6982640) (@lem6982641)). Qed.
Lemma lem6982644 (x : nat) : (term173 x) = term67.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6982645 : term172 = term67.
Proof. exact (@lem6982644 term9). Qed.
Lemma lem6982646 : term246 = term67.
Proof. exact (TRANS (@lem6982642) (@lem6982645)). Qed.
Lemma lem6982648 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6982649 : term120 = term121.
Proof. exact (@lem6982648 term9 term9). Qed.
Lemma lem6982650 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6982651 : term123 = term9.
Proof. exact (EQ_MP (@lem6982650) (@lem940073)). Qed.
Lemma lem6982652 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6982653 : term121 = term81.
Proof. exact (MK_COMB (@lem6982652) (@lem6982651)). Qed.
Lemma lem6982654 : term120 = term81.
Proof. exact (TRANS (@lem6982649) (@lem6982653)). Qed.
Lemma lem6982655 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem6982656 : term174 = term172.
Proof. exact (MK_COMB (@lem6982655) (@lem6982654)). Qed.
Lemma lem6982658 (x : nat) : (term173 x) = term67.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6982659 : term172 = term67.
Proof. exact (@lem6982658 term9). Qed.
Lemma lem6982660 : term174 = term67.
Proof. exact (TRANS (@lem6982656) (@lem6982659)). Qed.
Lemma lem6982661 : term67 = term174.
Proof. exact (SYM (@lem6982660)). Qed.
Lemma lem6982662 : term246 = term174.
Proof. exact (TRANS (@lem6982646) (@lem6982661)). Qed.
Lemma lem6982663 : term237 = term108.
Proof. exact (@lem6982613 (@lem6982662)). Qed.
Lemma lem6982664 : term236 = term108.
Proof. exact (TRANS (@lem6982579) (@lem6982663)). Qed.
Lemma lem6982666 (x : real) : (term127 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6982667 : term108 = term67.
Proof. exact (@lem6982666 term67). Qed.
Lemma lem6982668 : term236 = term67.
Proof. exact (TRANS (@lem6982664) (@lem6982667)). Qed.
Lemma lem6982669 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6982670 : term247 = term170.
Proof. exact (MK_COMB (@lem6982669) (@lem6982668)). Qed.
Lemma lem6982671 (_92990 : int) : (real_of_int _92990) = (real_of_int _92990).
Proof. exact (eq_refl (real_of_int _92990)). Qed.
Lemma lem6982672 (_92990 : int) : (term233 _92990) = (term248 _92990).
Proof. exact (MK_COMB (@lem6982670) (@lem6982671 _92990)). Qed.
Lemma lem6982673 (_92990 : int) : (term253 _92990) = (term248 _92990).
Proof. exact (TRANS (@lem6982570 _92990) (@lem6982672 _92990)). Qed.
Lemma lem6982674 (_92990 : int) : (term248 _92990) = term67.
Proof. exact (@lem1982719 (real_of_int _92990)). Qed.
Lemma lem6982675 (_92990 : int) : (term253 _92990) = term67.
Proof. exact (TRANS (@lem6982673 _92990) (@lem6982674 _92990)). Qed.
Lemma lem6982676 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6982677 (_92990 : int) : (term254 _92990) = term250.
Proof. exact (MK_COMB (@lem6982676) (@lem6982675 _92990)). Qed.
Lemma lem6982678 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem6982679 (_92990 : int) : (term252 _92990) = term255.
Proof. exact (MK_COMB (@lem6982677 _92990) (@lem6982678)). Qed.
Lemma lem6982680 (_92990 : int) : (term400 _92990) = term255.
Proof. exact (TRANS (@lem6982569 _92990) (@lem6982679 _92990)). Qed.
Lemma lem6982681 : term255 = term111.
Proof. exact (@lem1982721 term111). Qed.
Lemma lem6982682 (_92990 : int) : (term400 _92990) = term111.
Proof. exact (TRANS (@lem6982680 _92990) (@lem6982681)). Qed.
Lemma lem6982683 (_92990 : int) : (term399 _92990) = term111.
Proof. exact (TRANS (@lem6982568 _92990) (@lem6982682 _92990)). Qed.
Lemma lem6982685 (_92990 : int) : (term398 _92990) = term111.
Proof. exact (TRANS (@lem6982523 _92990) (@lem6982683 _92990)). Qed.
Lemma lem6982686 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6982687 (_92990 : int) : (term401 _92990) = term257.
Proof. exact (MK_COMB (@lem6982686) (@lem6982685 _92990)). Qed.
Lemma lem6982688 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem6982689 (_92990 : int) : (term397 _92990) = term258.
Proof. exact (MK_COMB (@lem6982687 _92990) (@lem6982688)). Qed.
Lemma lem6982690 (_92990 : int) : (term393 _92990) = term258.
Proof. exact (TRANS (@lem6982511 _92990) (@lem6982689 _92990)). Qed.
Lemma lem6982692 {A : Type'} (x : A) (s : A -> Prop) : (term381 A x s) = (term381 A x s).
Proof. exact (eq_refl (term381 A x s)). Qed.
Lemma lem6982693 {A : Type'} (_92990 : int) (x : A) (s : A -> Prop) : (term394 A x s _92990) = (term402 A x s).
Proof. exact (MK_COMB (@lem6982692 A x s) (@lem6982690 _92990)). Qed.
Lemma lem6982694 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6982695 (_92990 : int) : (term96 _92990) = (term195 _92990).
Proof. exact (MK_COMB (@lem6982694) (@lem6982509 _92990)). Qed.
Lemma lem6982696 {A : Type'} (_92990 : int) (x : A) (s : A -> Prop) : (term395 A x s _92990) = (term403 A _92990 x s).
Proof. exact (MK_COMB (@lem6982695 _92990) (@lem6982693 A _92990 x s)). Qed.
Lemma lem6982717 {A : Type'} (_92990 : int) (x : A) (s : A -> Prop) : (term396 A x s _92990) = (term403 A _92990 x s).
Proof. exact (TRANS (@lem6982461 A x s _92990) (@lem6982696 A _92990 x s)). Qed.
Lemma lem6982721 {A : Type'} (_92990 : int) (x : A) (s : A -> Prop) (h1 : term403 A _92990 x s) : term403 A _92990 x s.
Proof. exact (h1). Qed.
Lemma lem6982722 {A : Type'} (_92990 : int) (x : A) (s : A -> Prop) (h1 : term403 A _92990 x s) : term402 A x s.
Proof. exact (proj2 (@lem6982721 A _92990 x s h1)). Qed.
Lemma lem6982724 {A : Type'} (_92990 : int) (x : A) (s : A -> Prop) (h1 : term403 A _92990 x s) : term258.
Proof. exact (proj2 (@lem6982722 A _92990 x s h1)). Qed.
Lemma lem6982727 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6982728 : term258 = term259.
Proof. exact (@lem6982727 term67 term111). Qed.
Lemma lem6982730 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6982731 : term111 = term112.
Proof. exact (@lem6982730 term9). Qed.
Lemma lem6982733 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6982734 : term67 = term108.
Proof. exact (@lem6982733 (NUMERAL 0)). Qed.
Lemma lem6982735 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6982736 : term69 = term260.
Proof. exact (MK_COMB (@lem6982735) (@lem6982734)). Qed.
Lemma lem6982737 : term259 = term261.
Proof. exact (MK_COMB (@lem6982736) (@lem6982731)). Qed.
Lemma lem6982738 : term262.
Proof. exact (@lem1980026 term67 term81 term111 term81). Qed.
Lemma lem6982740 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6982741 : term160 = term161.
Proof. exact (@lem6982740 (NUMERAL 0) term9). Qed.
Lemma lem6982742 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6982743 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6982744 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6982743 h1) (fun h1 : term161 = True => @lem6982742)). Qed.
Lemma lem6982745 : term161 = True.
Proof. exact (EQ_MP (@lem6982744) (@lem6982742)). Qed.
Lemma lem6982746 : term160 = True.
Proof. exact (TRANS (@lem6982741) (@lem6982745)). Qed.
Lemma lem6982747 : True = term160.
Proof. exact (SYM (@lem6982746)). Qed.
Lemma lem6982748 : term160.
Proof. exact (EQ_MP (@lem6982747) (@lem0)). Qed.
Lemma lem6982749 : term263.
Proof. exact (@lem6982738 (@lem6982748)). Qed.
Lemma lem6982751 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6982752 : term160 = term161.
Proof. exact (@lem6982751 (NUMERAL 0) term9). Qed.
Lemma lem6982753 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6982754 (h1 : term162 = (BIT1 0)) : term161 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6982755 : (term162 = (BIT1 0)) = (term161 = True).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6982754 h1) (fun h1 : term161 = True => @lem6982753)). Qed.
Lemma lem6982756 : term161 = True.
Proof. exact (EQ_MP (@lem6982755) (@lem6982753)). Qed.
Lemma lem6982757 : term160 = True.
Proof. exact (TRANS (@lem6982752) (@lem6982756)). Qed.
Lemma lem6982758 : True = term160.
Proof. exact (SYM (@lem6982757)). Qed.
Lemma lem6982759 : term160.
Proof. exact (EQ_MP (@lem6982758) (@lem0)). Qed.
Lemma lem6982760 : term261 = term264.
Proof. exact (@lem6982749 (@lem6982759)). Qed.
Lemma lem6982762 (m : nat) (n : nat) : (term141 m n) = (term142 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6982763 : term138 = term143.
Proof. exact (@lem6982762 term9 term9). Qed.
Lemma lem6982764 : (term122 = (BIT1 0)) = (term123 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6982765 : term123 = term9.
Proof. exact (EQ_MP (@lem6982764) (@lem940073)). Qed.
Lemma lem6982766 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6982767 : term121 = term81.
Proof. exact (MK_COMB (@lem6982766) (@lem6982765)). Qed.
Lemma lem6982768 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6982769 : term143 = term111.
Proof. exact (MK_COMB (@lem6982768) (@lem6982767)). Qed.
Lemma lem6982770 : term138 = term111.
Proof. exact (TRANS (@lem6982763) (@lem6982769)). Qed.
Lemma lem6982772 (x : nat) : (term173 x) = term67.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6982773 : term172 = term67.
Proof. exact (@lem6982772 term9). Qed.
Lemma lem6982774 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6982775 : term265 = term69.
Proof. exact (MK_COMB (@lem6982774) (@lem6982773)). Qed.
Lemma lem6982776 : term264 = term259.
Proof. exact (MK_COMB (@lem6982775) (@lem6982770)). Qed.
Lemma lem6982778 (m : nat) (n : nat) : (term266 m n) = (term267 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6982779 : term259 = term268.
Proof. exact (@lem6982778 (NUMERAL 0) term9). Qed.
Lemma lem6982780 : term162 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6982781 (h1 : term162 = (BIT1 0)) : (term9 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6982782 : (term162 = (BIT1 0)) = ((term9 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term162 = (BIT1 0) => @lem6982781 h1) (fun h1 : (term9 = (NUMERAL 0)) = False => @lem6982780)). Qed.
Lemma lem6982783 : (term9 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6982782) (@lem6982780)). Qed.
Lemma lem6982784 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6982785 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6982786 : term269 = (and True).
Proof. exact (MK_COMB (@lem6982785) (@lem6982784)). Qed.
Lemma lem6982787 : term268 = (True /\ False).
Proof. exact (MK_COMB (@lem6982786) (@lem6982783)). Qed.
Lemma lem6982789 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6982790 : term268 = False.
Proof. exact (TRANS (@lem6982787) (@lem6982789)). Qed.
Lemma lem6982791 : term259 = False.
Proof. exact (TRANS (@lem6982779) (@lem6982790)). Qed.
Lemma lem6982792 : term264 = False.
Proof. exact (TRANS (@lem6982776) (@lem6982791)). Qed.
Lemma lem6982793 : term261 = False.
Proof. exact (TRANS (@lem6982760) (@lem6982792)). Qed.
Lemma lem6982794 : term259 = False.
Proof. exact (TRANS (@lem6982737) (@lem6982793)). Qed.
Lemma lem6982795 : term258 = False.
Proof. exact (TRANS (@lem6982728) (@lem6982794)). Qed.
Lemma lem6982796 {A : Type'} (_92990 : int) (x : A) (s : A -> Prop) (h1 : term403 A _92990 x s) : False.
Proof. exact (EQ_MP (@lem6982795) (@lem6982724 A _92990 x s h1)). Qed.
Lemma lem6982798 {A : Type'} (_92990 : int) (x : A) (s : A -> Prop) (h1 : term403 A _92990 x s) : term403 A _92990 x s.
Proof. exact (h1). Qed.
Lemma lem6982799 {A : Type'} (_92990 : int) (x : A) (s : A -> Prop) (h1 : term403 A _92990 x s) : (term403 A _92990 x s) = False.
Proof. exact (prop_ext (fun h2 : term403 A _92990 x s => @lem6982796 A _92990 x s h1) (fun h2 : False => @lem6982798 A _92990 x s h1)). Qed.
Lemma lem6982800 {A : Type'} (_92990 : int) (x : A) (s : A -> Prop) (h1 : term403 A _92990 x s) : False.
Proof. exact (EQ_MP (@lem6982799 A _92990 x s h1) (@lem6982798 A _92990 x s h1)). Qed.
Lemma lem6982801 {A : Type'} (x : A) (s : A -> Prop) (_92990 : int) (h1 : term396 A x s _92990) : term396 A x s _92990.
Proof. exact (h1). Qed.
Lemma lem6982802 {A : Type'} (x : A) (s : A -> Prop) (_92990 : int) (h1 : term396 A x s _92990) : term403 A _92990 x s.
Proof. exact (EQ_MP (@lem6982717 A _92990 x s) (@lem6982801 A x s _92990 h1)). Qed.
Lemma lem6982803 {A : Type'} (x : A) (s : A -> Prop) (_92990 : int) (h1 : term396 A x s _92990) : (term403 A _92990 x s) = False.
Proof. exact (prop_ext (fun h2 : term403 A _92990 x s => @lem6982800 A _92990 x s h2) (fun h2 : False => @lem6982802 A x s _92990 h1)). Qed.
Lemma lem6982804 {A : Type'} (x : A) (s : A -> Prop) (_92990 : int) (h1 : term396 A x s _92990) : False.
Proof. exact (EQ_MP (@lem6982803 A x s _92990 h1) (@lem6982802 A x s _92990 h1)). Qed.
Lemma lem6982805 {A : Type'} (x : A) (s : A -> Prop) (_92990 : int) : term404 A x s _92990.
Proof. exact (fun h0 : term396 A x s _92990 => @lem6982804 A x s _92990 h0). Qed.
Lemma lem6982806 {A : Type'} (x : A) (s : A -> Prop) (_92990 : int) : term405 A x s _92990.
Proof. exact (@lem1386578 (term406 A x s _92990)). Qed.
Lemma lem6982809 {A : Type'} (x : A) (s : A -> Prop) (_92990 : int) : term406 A x s _92990.
Proof. exact (@lem6982806 A x s _92990 (@lem6982805 A x s _92990)). Qed.
Lemma lem6982810 {A : Type'} (x : A) (s : A -> Prop) (_92990 : int) : (term395 A x s _92990) = (term389 A x s _92990).
Proof. exact (SYM (@lem6982431 A x s _92990)). Qed.
Lemma lem6982811 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6982812 {A : Type'} (x : A) (s : A -> Prop) (_92990 : int) : (term406 A x s _92990) = (term376 A x s _92990).
Proof. exact (MK_COMB (@lem6982811) (@lem6982810 A x s _92990)). Qed.
Lemma lem6982813 {A : Type'} (x : A) (s : A -> Prop) (_92990 : int) : term376 A x s _92990.
Proof. exact (EQ_MP (@lem6982812 A x s _92990) (@lem6982809 A x s _92990)). Qed.
Lemma lem6982814 {A : Type'} (x : A) (s : A -> Prop) (_92990 : int) : term377 A x s _92990.
Proof. exact (EQ_MP (@lem6982350 A x s _92990) (@lem6982813 A x s _92990)). Qed.
Lemma lem6982815 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : term407 A s f x.
Proof. exact (@lem6982814 A x s (term408 A f x)). Qed.
Lemma lem6982816 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : term371 A s f x.
Proof. exact (@lem6982815 A s f x (@lem6982349 A f x)). Qed.
Lemma lem6982817 {A : Type'} (s : A -> Prop) (f : A -> nat) : term373 A s f.
Proof. exact (fun x : A => @lem6982816 A s f x). Qed.
Lemma lem6982818 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term373 A s f) = (term358 A s f).
Proof. exact (SYM (@lem6982346 A s f)). Qed.
Lemma lem6982819 {A : Type'} (s : A -> Prop) (f : A -> nat) : term358 A s f.
Proof. exact (EQ_MP (@lem6982818 A s f) (@lem6982817 A s f)). Qed.
Lemma lem6982820 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term358 A s f) = ((term358 A s f) = True).
Proof. exact (@lem7 (term358 A s f)). Qed.
Lemma lem6982821 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term358 A s f) = True.
Proof. exact (EQ_MP (@lem6982820 A s f) (@lem6982819 A s f)). Qed.
Lemma lem6982822 {A : Type'} (s : A -> Prop) (f : A -> nat) : True = (term358 A s f).
Proof. exact (SYM (@lem6982821 A s f)). Qed.
Lemma lem6982823 {A : Type'} (s : A -> Prop) (f : A -> nat) : term358 A s f.
Proof. exact (EQ_MP (@lem6982822 A s f) (@lem0)). Qed.
Lemma lem6982824 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term323 A s) : term361 A s f.
Proof. exact (EQ_MP (@lem6982260 A f s h1 h2) (@lem6982823 A s f)). Qed.
Lemma lem6982825 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term323 A s) : term409 A s f.
Proof. exact (@lem6982034 A s f (@lem6982824 A f s h1 h2)). Qed.
Lemma lem6982827 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : term281 A s f b.
Proof. exact (EQ_MP (@lem6981963 A s f b) (@lem6981962 A s f b)). Qed.
Lemma lem6982828 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : term281 A s f b.
Proof. exact (@lem6982827 A s f b). Qed.
Lemma lem6982829 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : term410 A s f b.
Proof. exact (@lem6982828 A s (term326 A f) b). Qed.
Lemma lem6982830 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem6982832 {A : Type'} (s : A -> Prop) : term327 A s.
Proof. exact (@lem82 (s = (@EMPTY A))). Qed.
Lemma lem6982845 {A : Type'} (x : A) (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term322 A f b s) : term411 A f b s x.
Proof. exact (@lem6982026 A f b s h1 x). Qed.
Lemma lem6982846 {A : Type'} (f : A -> nat) (x : A) (b : nat) (s : A -> Prop) : (term411 A f b s x) = (term412 A f x b s).
Proof. exact (eq_refl (term411 A f b s x)). Qed.
Lemma lem6982847 {A : Type'} (x : A) (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term322 A f b s) : term412 A f x b s.
Proof. exact (EQ_MP (@lem6982846 A f x b s) (@lem6982845 A x f b s h1)). Qed.
Lemma lem6982848 {A : Type'} (f : A -> nat) (x : A) (b : nat) (s : A -> Prop) : (term412 A f x b s) = ((term412 A f x b s) = True).
Proof. exact (@lem7 (term412 A f x b s)). Qed.
Lemma lem6982853 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6982830 A s) (@lem6982025 A s h1)). Qed.
Lemma lem6982854 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6982855 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term328 A s) = (and True).
Proof. exact (MK_COMB (@lem6982854) (@lem6982853 A s h1)). Qed.
Lemma lem6982859 {A : Type'} (s : A -> Prop) (h1 : term323 A s) : (s = (@EMPTY A)) = False.
Proof. exact (@lem6982832 A s (@lem6982027 A s h1)). Qed.
Lemma lem6982860 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6982861 {A : Type'} (s : A -> Prop) (h1 : term323 A s) : (term323 A s) = (~ False).
Proof. exact (MK_COMB (@lem6982860) (@lem6982859 A s h1)). Qed.
Lemma lem6982863 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem6982864 {A : Type'} (s : A -> Prop) (h1 : term323 A s) : (term323 A s) = True.
Proof. exact (TRANS (@lem6982861 A s h1) (@lem6982863)). Qed.
Lemma lem6982865 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6982866 {A : Type'} (s : A -> Prop) (h1 : term323 A s) : (term329 A s) = (and True).
Proof. exact (MK_COMB (@lem6982865) (@lem6982864 A s h1)). Qed.
Lemma lem6982874 {A B : Type'} (f : A -> B) (y : A) : (term341 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6982875 {A : Type'} (f : A -> nat) (y : A) : (term342 A f y) = (f y).
Proof. exact (@lem6982874 A nat f y). Qed.
Lemma lem6982876 {A : Type'} (f : A -> nat) (x : A) : (term343 A f x) = (term344 A f x).
Proof. exact (@lem6982875 A (term326 A f) x). Qed.
Lemma lem6982877 {A : Type'} (f : A -> nat) (a : A) : (term344 A f a) = (term345 A f a).
Proof. exact (eq_refl (term344 A f a)). Qed.
Lemma lem6982878 {A : Type'} (f : A -> nat) : (term346 A f) = (term326 A f).
Proof. exact (fun_ext (fun a : A => @lem6982877 A f a)). Qed.
Lemma lem6982879 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6982880 {A : Type'} (f : A -> nat) (x : A) : (term343 A f x) = (term344 A f x).
Proof. exact (MK_COMB (@lem6982878 A f) (@lem6982879 A x)). Qed.
Lemma lem6982881 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6982882 {A : Type'} (f : A -> nat) (x : A) : (term347 A f x) = (term348 A f x).
Proof. exact (MK_COMB (@lem6982881) (@lem6982880 A f x)). Qed.
Lemma lem6982883 {A : Type'} (f : A -> nat) (x : A) : (term344 A f x) = (term345 A f x).
Proof. exact (eq_refl (term344 A f x)). Qed.
Lemma lem6982884 {A : Type'} (f : A -> nat) (x : A) : ((term343 A f x) = (term344 A f x)) = ((term344 A f x) = (term345 A f x)).
Proof. exact (MK_COMB (@lem6982882 A f x) (@lem6982883 A f x)). Qed.
Lemma lem6982885 {A : Type'} (f : A -> nat) (x : A) : (term344 A f x) = (term345 A f x).
Proof. exact (EQ_MP (@lem6982884 A f x) (@lem6982876 A f x)). Qed.
Lemma lem6982886 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem6982887 {A : Type'} (f : A -> nat) (x : A) : (term413 A f x) = (term414 A f x).
Proof. exact (MK_COMB (@lem6982886) (@lem6982885 A f x)). Qed.
Lemma lem6982888 {A : Type'} (b : nat) (s : A -> Prop) : (term415 A b s) = (term415 A b s).
Proof. exact (eq_refl (term415 A b s)). Qed.
Lemma lem6982889 {A : Type'} (f : A -> nat) (x : A) (b : nat) (s : A -> Prop) : (term416 A f x b s) = (term417 A f x b s).
Proof. exact (MK_COMB (@lem6982887 A f x) (@lem6982888 A b s)). Qed.
Lemma lem6982891 (a : nat) (b : nat) : (term0 a b) = (Peano.lt a b).
Proof. exact (EQ_MP (@lem6981933 a b) (@lem6981932 a b)). Qed.
Lemma lem6982892 {A : Type'} (f : A -> nat) (x : A) (b : nat) (s : A -> Prop) : (term417 A f x b s) = (term418 A f x b s).
Proof. exact (@lem6982891 (f x) (term415 A b s)). Qed.
Lemma lem6982893 {A : Type'} (f : A -> nat) (x : A) (b : nat) (s : A -> Prop) : (term416 A f x b s) = (term418 A f x b s).
Proof. exact (TRANS (@lem6982889 A f x b s) (@lem6982892 A f x b s)). Qed.
Lemma lem6982894 {A : Type'} (x : A) (s : A -> Prop) : (term419 A x s) = (term419 A x s).
Proof. exact (eq_refl (term419 A x s)). Qed.
Lemma lem6982895 {A : Type'} (f : A -> nat) (x : A) (b : nat) (s : A -> Prop) : (term420 A f x b s) = (term412 A f x b s).
Proof. exact (MK_COMB (@lem6982894 A x s) (@lem6982893 A f x b s)). Qed.
Lemma lem6982897 {A : Type'} (x : A) (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term322 A f b s) : (term412 A f x b s) = True.
Proof. exact (EQ_MP (@lem6982848 A f x b s) (@lem6982847 A x f b s h1)). Qed.
Lemma lem6982898 {A : Type'} (x : A) (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term322 A f b s) : (term412 A f x b s) = True.
Proof. exact (@lem6982897 A x f b s h1). Qed.
Lemma lem6982899 {A : Type'} (x : A) (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term322 A f b s) : (term420 A f x b s) = True.
Proof. exact (TRANS (@lem6982895 A f x b s) (@lem6982898 A x f b s h1)). Qed.
Lemma lem6982900 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term322 A f b s) : (term421 A f b s) = (term422 A).
Proof. exact (fun_ext (fun x : A => @lem6982899 A x f b s h1)). Qed.
Lemma lem6982901 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6982902 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term322 A f b s) : (term423 A f b s) = (term424 A).
Proof. exact (MK_COMB (@lem6982901 A) (@lem6982900 A f b s h1)). Qed.
Lemma lem6982904 {A : Type'} (t : Prop) : (term425 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6982905 {A : Type'} (t : Prop) : (term425 A t) = t.
Proof. exact (@lem6982904 A t). Qed.
Lemma lem6982906 {A : Type'} : (term424 A) = True.
Proof. exact (@lem6982905 A True). Qed.
Lemma lem6982907 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term322 A f b s) : (term423 A f b s) = True.
Proof. exact (TRANS (@lem6982902 A f b s h1) (@lem6982906 A)). Qed.
Lemma lem6982908 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term322 A f b s) (h2 : term323 A s) : (term426 A f b s) = (True /\ True).
Proof. exact (MK_COMB (@lem6982866 A s h2) (@lem6982907 A f b s h1)). Qed.
Lemma lem6982910 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6982911 : (True /\ True) = True.
Proof. exact (@lem6982910 True). Qed.
Lemma lem6982912 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term322 A f b s) (h2 : term323 A s) : (term426 A f b s) = True.
Proof. exact (TRANS (@lem6982908 A f b s h1 h2) (@lem6982911)). Qed.
Lemma lem6982913 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term322 A f b s) (h2 : @FINITE A s) (h3 : term323 A s) : (term427 A f b s) = (True /\ True).
Proof. exact (MK_COMB (@lem6982855 A s h2) (@lem6982912 A f b s h1 h3)). Qed.
Lemma lem6982915 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6982916 : (True /\ True) = True.
Proof. exact (@lem6982915 True). Qed.
Lemma lem6982917 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term322 A f b s) (h2 : @FINITE A s) (h3 : term323 A s) : (term427 A f b s) = True.
Proof. exact (TRANS (@lem6982913 A f b s h1 h2 h3) (@lem6982916)). Qed.
Lemma lem6982918 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term322 A f b s) (h2 : @FINITE A s) (h3 : term323 A s) : True = (term427 A f b s).
Proof. exact (SYM (@lem6982917 A f b s h1 h2 h3)). Qed.
Lemma lem6982919 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term322 A f b s) (h2 : @FINITE A s) (h3 : term323 A s) : term427 A f b s.
Proof. exact (EQ_MP (@lem6982918 A f b s h1 h2 h3) (@lem0)). Qed.
Lemma lem6982920 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term322 A f b s) (h2 : @FINITE A s) (h3 : term323 A s) : term428 A s f b.
Proof. exact (@lem6982829 A s f b (@lem6982919 A f b s h1 h2 h3)). Qed.
Lemma lem6982921 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term322 A f b s) (h2 : @FINITE A s) (h3 : term323 A s) : term429 A s f b.
Proof. exact (conj (@lem6982825 A f s h2 h3) (@lem6982920 A f b s h1 h2 h3)). Qed.
Lemma lem6982922 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term322 A f b s) (h2 : @FINITE A s) (h3 : term323 A s) : term430 A s f b.
Proof. exact (ex_intro (term431 A s f b) (term432 A s f) (@lem6982921 A f b s h1 h2 h3)). Qed.
Lemma lem6982923 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term322 A f b s) (h2 : @FINITE A s) (h3 : term323 A s) : term433 A s f b.
Proof. exact (@lem6982030 A s f b (@lem6982922 A f b s h1 h2 h3)). Qed.
Lemma lem6982924 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term320 A f b s) : term321 A f b s.
Proof. exact (proj2 (@lem6982023 A f b s h1)). Qed.
Lemma lem6982925 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term320 A f b s) : @FINITE A s.
Proof. exact (proj1 (@lem6982023 A f b s h1)). Qed.
Lemma lem6982926 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term321 A f b s) : term322 A f b s.
Proof. exact (proj2 (@lem6982024 A f b s h1)). Qed.
Lemma lem6982927 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term321 A f b s) : term323 A s.
Proof. exact (proj1 (@lem6982024 A f b s h1)). Qed.
Lemma lem6982928 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term322 A f b s) (h2 : @FINITE A s) (h3 : term323 A s) : (term322 A f b s) = (term433 A s f b).
Proof. exact (prop_ext (fun h4 : term322 A f b s => @lem6982923 A f b s h1 h2 h3) (fun h4 : term433 A s f b => @lem6982026 A f b s h1)). Qed.
Lemma lem6982929 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term322 A f b s) (h2 : @FINITE A s) (h3 : term323 A s) : term433 A s f b.
Proof. exact (EQ_MP (@lem6982928 A f b s h1 h2 h3) (@lem6982026 A f b s h1)). Qed.
Lemma lem6982930 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term322 A f b s) (h2 : @FINITE A s) (h3 : term323 A s) : (term323 A s) = (term433 A s f b).
Proof. exact (prop_ext (fun h4 : term323 A s => @lem6982929 A f b s h1 h2 h3) (fun h4 : term433 A s f b => @lem6982027 A s h3)). Qed.
Lemma lem6982931 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term322 A f b s) (h2 : @FINITE A s) (h3 : term323 A s) : term433 A s f b.
Proof. exact (EQ_MP (@lem6982930 A f b s h1 h2 h3) (@lem6982027 A s h3)). Qed.
Lemma lem6982932 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term323 A s) (h3 : term321 A f b s) : (term322 A f b s) = (term433 A s f b).
Proof. exact (prop_ext (fun h4 : term322 A f b s => @lem6982931 A f b s h4 h1 h2) (fun h4 : term433 A s f b => @lem6982926 A f b s h3)). Qed.
Lemma lem6982933 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term323 A s) (h3 : term321 A f b s) : term433 A s f b.
Proof. exact (EQ_MP (@lem6982932 A f b s h1 h2 h3) (@lem6982926 A f b s h3)). Qed.
Lemma lem6982934 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term321 A f b s) : (term323 A s) = (term433 A s f b).
Proof. exact (prop_ext (fun h3 : term323 A s => @lem6982933 A f b s h1 h3 h2) (fun h3 : term433 A s f b => @lem6982927 A f b s h2)). Qed.
Lemma lem6982935 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term321 A f b s) : term433 A s f b.
Proof. exact (EQ_MP (@lem6982934 A f b s h1 h2) (@lem6982927 A f b s h2)). Qed.
Lemma lem6982936 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term321 A f b s) : (@FINITE A s) = (term433 A s f b).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem6982935 A f b s h1 h2) (fun h3 : term433 A s f b => @lem6982025 A s h1)). Qed.
Lemma lem6982937 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term321 A f b s) : term433 A s f b.
Proof. exact (EQ_MP (@lem6982936 A f b s h1 h2) (@lem6982025 A s h1)). Qed.
Lemma lem6982938 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term320 A f b s) : (term321 A f b s) = (term433 A s f b).
Proof. exact (prop_ext (fun h3 : term321 A f b s => @lem6982937 A f b s h1 h3) (fun h3 : term433 A s f b => @lem6982924 A f b s h2)). Qed.
Lemma lem6982939 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term320 A f b s) : term433 A s f b.
Proof. exact (EQ_MP (@lem6982938 A f b s h1 h2) (@lem6982924 A f b s h2)). Qed.
Lemma lem6982940 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term320 A f b s) : (@FINITE A s) = (term433 A s f b).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem6982939 A f b s h2 h1) (fun h2 : term433 A s f b => @lem6982925 A f b s h1)). Qed.
Lemma lem6982941 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term320 A f b s) : term433 A s f b.
Proof. exact (EQ_MP (@lem6982940 A f b s h1) (@lem6982925 A f b s h1)). Qed.
Lemma lem6982942 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : term434 A s f b.
Proof. exact (fun h0 : term320 A f b s => @lem6982941 A f b s h0). Qed.
Lemma lem6982947 {A : Type'} (s : A -> Prop) (f : A -> nat) : term435 A s f.
Proof. exact (fun b : nat => @lem6982942 A s f b). Qed.
Lemma lem6982952 {A : Type'} (s : A -> Prop) : term436 A s.
Proof. exact (fun f : A -> nat => @lem6982947 A s f). Qed.
Lemma lem6982957 {A : Type'} : term437 A.
Proof. exact (fun s : A -> Prop => @lem6982952 A s). Qed.
