Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_NUMSEG_LEMMA_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import CARD_CLAUSES_spec.
Require Import FINITE_NUMSEG_spec.
Require Import FINITE_RULES_spec.
Require Import INT_POS_spec.
Require Import IN_NUMSEG_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import NUMSEG_REC_spec.
Require Import NUMSEG_SING_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1032092_spec.
Require Import thm1032098_spec.
Require Import thm12653_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17362_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
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
Require Import thm513079_spec.
Require Import thm521920_spec.
Require Import thm522075_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Require Import thm996238_spec.
Lemma lem5379239 (m : nat) : (S m) = (term0 m).
Proof. exact (EQ_MP (@lem2841417 m) (@lem2841416 m)). Qed.
Lemma lem5379240 (n : nat) : (S n) = (term0 n).
Proof. exact (@lem5379239 n). Qed.
Lemma lem5379241 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem5379242 (n : nat) : (term1 n) = (term2 n).
Proof. exact (MK_COMB (@lem5379241) (@lem5379240 n)). Qed.
Lemma lem5379243 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem5379244 (n : nat) : (term3 n) = (term4 n).
Proof. exact (MK_COMB (@lem5379242 n) (@lem5379243 n)). Qed.
Lemma lem5379245 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5379263 (n : nat) : (term5 n) = (term6 n).
Proof. exact (MK_COMB (@lem5379245) (@lem5379244 n)). Qed.
Lemma lem5379265 (m : nat) (n : nat) : (Peano.le m n) = (term7 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5379266 (n : nat) : (term4 n) = (term8 n).
Proof. exact (@lem5379265 (term0 n) n). Qed.
Lemma lem5379268 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5379269 (n : nat) : (term11 n) = (term12 n).
Proof. exact (@lem5379268 n term13). Qed.
Lemma lem5379270 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem5379271 (n : nat) : (term14 n) = (term15 n).
Proof. exact (MK_COMB (@lem5379270) (@lem5379269 n)). Qed.
Lemma lem5379272 (n : nat) : (int_of_num n) = (int_of_num n).
Proof. exact (eq_refl (int_of_num n)). Qed.
Lemma lem5379273 (n : nat) : (term8 n) = (term16 n).
Proof. exact (MK_COMB (@lem5379271 n) (@lem5379272 n)). Qed.
Lemma lem5379274 (n : nat) : (term4 n) = (term16 n).
Proof. exact (TRANS (@lem5379266 n) (@lem5379273 n)). Qed.
Lemma lem5379275 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5379276 (n : nat) : (term6 n) = (term17 n).
Proof. exact (MK_COMB (@lem5379275) (@lem5379274 n)). Qed.
Lemma lem5379277 (n : nat) : (term5 n) = (term17 n).
Proof. exact (TRANS (@lem5379263 n) (@lem5379276 n)). Qed.
Lemma lem5379278 (n : nat) : term18 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem5379279 (n : nat) : (term18 n) = (term19 n).
Proof. exact (eq_refl (term18 n)). Qed.
Lemma lem5379280 (n : nat) : term19 n.
Proof. exact (EQ_MP (@lem5379279 n) (@lem5379278 n)). Qed.
Lemma lem5379281 (_69785 : int) : (term20 _69785) = (term21 _69785).
Proof. exact (@lem2318604 (term21 _69785)). Qed.
Lemma lem5379292 (_69785 : int) : (term22 _69785) = (term23 _69785).
Proof. exact (@lem16933 (term23 _69785)). Qed.
Lemma lem5379294 (_69785 : int) : (term24 _69785) = (term24 _69785).
Proof. exact (eq_refl (term24 _69785)). Qed.
Lemma lem5379295 (_69785 : int) : (term25 _69785) = (term26 _69785).
Proof. exact (MK_COMB (@lem5379294 _69785) (@lem5379292 _69785)). Qed.
Lemma lem5379296 (_69785 : int) : (term27 _69785) = (term25 _69785).
Proof. exact (@lem17362 (term28 _69785) (term29 _69785)). Qed.
Lemma lem5379304 (_69785 : int) : (term27 _69785) = (term26 _69785).
Proof. exact (TRANS (@lem5379296 _69785) (@lem5379295 _69785)). Qed.
Lemma lem5379307 (x : int) (y : int) : (int_le x y) = (term30 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5379308 (_69785 : int) : (term28 _69785) = (term31 _69785).
Proof. exact (@lem5379307 term32 _69785). Qed.
Lemma lem5379310 (n : nat) : (term33 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5379311 : term34 = term35.
Proof. exact (@lem5379310 (NUMERAL 0)). Qed.
Lemma lem5379312 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5379313 : term36 = term37.
Proof. exact (MK_COMB (@lem5379312) (@lem5379311)). Qed.
Lemma lem5379314 (_69785 : int) : (real_of_int _69785) = (real_of_int _69785).
Proof. exact (eq_refl (real_of_int _69785)). Qed.
Lemma lem5379315 (_69785 : int) : (term31 _69785) = (term38 _69785).
Proof. exact (MK_COMB (@lem5379313) (@lem5379314 _69785)). Qed.
Lemma lem5379317 (_69785 : int) : (term28 _69785) = (term38 _69785).
Proof. exact (TRANS (@lem5379308 _69785) (@lem5379315 _69785)). Qed.
Lemma lem5379320 (x : int) (y : int) : (int_le x y) = (term30 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5379321 (_69785 : int) : (term23 _69785) = (term39 _69785).
Proof. exact (@lem5379320 (term40 _69785) _69785). Qed.
Lemma lem5379323 (x : int) (y : int) : (term41 x y) = (term42 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5379324 (_69785 : int) : (term43 _69785) = (term44 _69785).
Proof. exact (@lem5379323 _69785 term45). Qed.
Lemma lem5379326 (n : nat) : (term33 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5379327 : term46 = term47.
Proof. exact (@lem5379326 term13). Qed.
Lemma lem5379328 (_69785 : int) : (term48 _69785) = (term48 _69785).
Proof. exact (eq_refl (term48 _69785)). Qed.
Lemma lem5379329 (_69785 : int) : (term44 _69785) = (term49 _69785).
Proof. exact (MK_COMB (@lem5379328 _69785) (@lem5379327)). Qed.
Lemma lem5379330 (_69785 : int) : (term43 _69785) = (term49 _69785).
Proof. exact (TRANS (@lem5379324 _69785) (@lem5379329 _69785)). Qed.
Lemma lem5379331 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5379332 (_69785 : int) : (term50 _69785) = (term51 _69785).
Proof. exact (MK_COMB (@lem5379331) (@lem5379330 _69785)). Qed.
Lemma lem5379333 (_69785 : int) : (real_of_int _69785) = (real_of_int _69785).
Proof. exact (eq_refl (real_of_int _69785)). Qed.
Lemma lem5379334 (_69785 : int) : (term39 _69785) = (term52 _69785).
Proof. exact (MK_COMB (@lem5379332 _69785) (@lem5379333 _69785)). Qed.
Lemma lem5379336 (_69785 : int) : (term23 _69785) = (term52 _69785).
Proof. exact (TRANS (@lem5379321 _69785) (@lem5379334 _69785)). Qed.
Lemma lem5379337 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5379338 (_69785 : int) : (term24 _69785) = (term53 _69785).
Proof. exact (MK_COMB (@lem5379337) (@lem5379317 _69785)). Qed.
Lemma lem5379339 (_69785 : int) : (term26 _69785) = (term54 _69785).
Proof. exact (MK_COMB (@lem5379338 _69785) (@lem5379336 _69785)). Qed.
Lemma lem5379340 (_69785 : int) : (term27 _69785) = (term54 _69785).
Proof. exact (TRANS (@lem5379304 _69785) (@lem5379339 _69785)). Qed.
Lemma lem5379344 (t : Prop) : (term55 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5379360 (_69785 : int) : (term56 _69785) = (term54 _69785).
Proof. exact (@lem5379344 (term54 _69785)). Qed.
Lemma lem5379361 (_69785 : int) : (term38 _69785) = (term57 _69785).
Proof. exact (@lem1988287 (real_of_int _69785) term35). Qed.
Lemma lem5379367 (_69785 : int) : (term58 _69785) = (term59 _69785).
Proof. exact (@lem1982792 (real_of_int _69785) term35). Qed.
Lemma lem5379369 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5379370 : term35 = term61.
Proof. exact (@lem5379369 (NUMERAL 0)). Qed.
Lemma lem5379372 (x : nat) : (term62 x) = (term63 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5379373 : term64 = term65.
Proof. exact (@lem5379372 term13). Qed.
Lemma lem5379374 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5379375 : term66 = term67.
Proof. exact (MK_COMB (@lem5379374) (@lem5379373)). Qed.
Lemma lem5379376 : term68 = term69.
Proof. exact (MK_COMB (@lem5379375) (@lem5379370)). Qed.
Lemma lem5379377 : term69 = term70.
Proof. exact (@lem1981613 term64 term35 term47 term47). Qed.
Lemma lem5379379 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5379380 : term73 = term74.
Proof. exact (@lem5379379 term13 term13). Qed.
Lemma lem5379381 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5379382 : term76 = term13.
Proof. exact (EQ_MP (@lem5379381) (@lem940073)). Qed.
Lemma lem5379383 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5379384 : term74 = term47.
Proof. exact (MK_COMB (@lem5379383) (@lem5379382)). Qed.
Lemma lem5379385 : term73 = term47.
Proof. exact (TRANS (@lem5379380) (@lem5379384)). Qed.
Lemma lem5379387 (x : nat) : (term77 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5379388 : term68 = term35.
Proof. exact (@lem5379387 term13). Qed.
Lemma lem5379389 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5379390 : term78 = term79.
Proof. exact (MK_COMB (@lem5379389) (@lem5379388)). Qed.
Lemma lem5379391 : term70 = term61.
Proof. exact (MK_COMB (@lem5379390) (@lem5379385)). Qed.
Lemma lem5379392 : term69 = term61.
Proof. exact (TRANS (@lem5379377) (@lem5379391)). Qed.
Lemma lem5379393 : term68 = term61.
Proof. exact (TRANS (@lem5379376) (@lem5379392)). Qed.
Lemma lem5379395 (x : real) : (term80 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5379396 : term61 = term35.
Proof. exact (@lem5379395 term35). Qed.
Lemma lem5379397 : term68 = term35.
Proof. exact (TRANS (@lem5379393) (@lem5379396)). Qed.
Lemma lem5379398 (_69785 : int) : (term48 _69785) = (term48 _69785).
Proof. exact (eq_refl (term48 _69785)). Qed.
Lemma lem5379399 (_69785 : int) : (term59 _69785) = (term81 _69785).
Proof. exact (MK_COMB (@lem5379398 _69785) (@lem5379397)). Qed.
Lemma lem5379400 (_69785 : int) : (term81 _69785) = (real_of_int _69785).
Proof. exact (@lem1982723 (real_of_int _69785)). Qed.
Lemma lem5379401 (_69785 : int) : (term59 _69785) = (real_of_int _69785).
Proof. exact (TRANS (@lem5379399 _69785) (@lem5379400 _69785)). Qed.
Lemma lem5379403 (_69785 : int) : (term58 _69785) = (real_of_int _69785).
Proof. exact (TRANS (@lem5379367 _69785) (@lem5379401 _69785)). Qed.
Lemma lem5379404 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5379405 (_69785 : int) : (term82 _69785) = (term83 _69785).
Proof. exact (MK_COMB (@lem5379404) (@lem5379403 _69785)). Qed.
Lemma lem5379406 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem5379407 (_69785 : int) : (term57 _69785) = (term84 _69785).
Proof. exact (MK_COMB (@lem5379405 _69785) (@lem5379406)). Qed.
Lemma lem5379408 (_69785 : int) : (term38 _69785) = (term84 _69785).
Proof. exact (TRANS (@lem5379361 _69785) (@lem5379407 _69785)). Qed.
Lemma lem5379409 (_69785 : int) : (term52 _69785) = (term85 _69785).
Proof. exact (@lem1988287 (real_of_int _69785) (term49 _69785)). Qed.
Lemma lem5379421 (_69785 : int) : (term86 _69785) = (term87 _69785).
Proof. exact (@lem1982792 (real_of_int _69785) (term49 _69785)). Qed.
Lemma lem5379422 (_69785 : int) : (term88 _69785) = (term89 _69785).
Proof. exact (@lem1982781 (real_of_int _69785) term64 term47). Qed.
Lemma lem5379424 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5379425 : term47 = term90.
Proof. exact (@lem5379424 term13). Qed.
Lemma lem5379427 (x : nat) : (term62 x) = (term63 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5379428 : term64 = term65.
Proof. exact (@lem5379427 term13). Qed.
Lemma lem5379429 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5379430 : term66 = term67.
Proof. exact (MK_COMB (@lem5379429) (@lem5379428)). Qed.
Lemma lem5379431 : term91 = term92.
Proof. exact (MK_COMB (@lem5379430) (@lem5379425)). Qed.
Lemma lem5379432 : term92 = term93.
Proof. exact (@lem1981613 term64 term47 term47 term47). Qed.
Lemma lem5379434 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5379435 : term73 = term74.
Proof. exact (@lem5379434 term13 term13). Qed.
Lemma lem5379436 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5379437 : term76 = term13.
Proof. exact (EQ_MP (@lem5379436) (@lem940073)). Qed.
Lemma lem5379438 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5379439 : term74 = term47.
Proof. exact (MK_COMB (@lem5379438) (@lem5379437)). Qed.
Lemma lem5379440 : term73 = term47.
Proof. exact (TRANS (@lem5379435) (@lem5379439)). Qed.
Lemma lem5379442 (m : nat) (n : nat) : (term94 m n) = (term95 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5379443 : term91 = term96.
Proof. exact (@lem5379442 term13 term13). Qed.
Lemma lem5379444 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5379445 : term76 = term13.
Proof. exact (EQ_MP (@lem5379444) (@lem940073)). Qed.
Lemma lem5379446 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5379447 : term74 = term47.
Proof. exact (MK_COMB (@lem5379446) (@lem5379445)). Qed.
Lemma lem5379448 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5379449 : term96 = term64.
Proof. exact (MK_COMB (@lem5379448) (@lem5379447)). Qed.
Lemma lem5379450 : term91 = term64.
Proof. exact (TRANS (@lem5379443) (@lem5379449)). Qed.
Lemma lem5379451 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5379452 : term97 = term98.
Proof. exact (MK_COMB (@lem5379451) (@lem5379450)). Qed.
Lemma lem5379453 : term93 = term65.
Proof. exact (MK_COMB (@lem5379452) (@lem5379440)). Qed.
Lemma lem5379454 : term92 = term65.
Proof. exact (TRANS (@lem5379432) (@lem5379453)). Qed.
Lemma lem5379455 : term91 = term65.
Proof. exact (TRANS (@lem5379431) (@lem5379454)). Qed.
Lemma lem5379457 (x : real) : (term80 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5379458 : term65 = term64.
Proof. exact (@lem5379457 term64). Qed.
Lemma lem5379459 : term91 = term64.
Proof. exact (TRANS (@lem5379455) (@lem5379458)). Qed.
Lemma lem5379462 (_69785 : int) : (term99 _69785) = (term99 _69785).
Proof. exact (eq_refl (term99 _69785)). Qed.
Lemma lem5379463 (_69785 : int) : (term89 _69785) = (term100 _69785).
Proof. exact (MK_COMB (@lem5379462 _69785) (@lem5379459)). Qed.
Lemma lem5379464 (_69785 : int) : (term88 _69785) = (term100 _69785).
Proof. exact (TRANS (@lem5379422 _69785) (@lem5379463 _69785)). Qed.
Lemma lem5379465 (_69785 : int) : (term48 _69785) = (term48 _69785).
Proof. exact (eq_refl (term48 _69785)). Qed.
Lemma lem5379466 (_69785 : int) : (term87 _69785) = (term101 _69785).
Proof. exact (MK_COMB (@lem5379465 _69785) (@lem5379464 _69785)). Qed.
Lemma lem5379467 (_69785 : int) : (term101 _69785) = (term102 _69785).
Proof. exact (@lem1982763 (real_of_int _69785) (term103 _69785) term64). Qed.
Lemma lem5379468 (_69785 : int) : (term104 _69785) = (term105 _69785).
Proof. exact (@lem1982715 term64 (real_of_int _69785)). Qed.
Lemma lem5379470 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5379471 : term47 = term90.
Proof. exact (@lem5379470 term13). Qed.
Lemma lem5379473 (x : nat) : (term62 x) = (term63 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5379474 : term64 = term65.
Proof. exact (@lem5379473 term13). Qed.
Lemma lem5379475 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5379476 : term106 = term107.
Proof. exact (MK_COMB (@lem5379475) (@lem5379474)). Qed.
Lemma lem5379477 : term108 = term109.
Proof. exact (MK_COMB (@lem5379476) (@lem5379471)). Qed.
Lemma lem5379478 : term110.
Proof. exact (@lem1981473 term64 term47 term47 term47 term35 term47). Qed.
Lemma lem5379480 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5379481 : term112 = term113.
Proof. exact (@lem5379480 (NUMERAL 0) term13). Qed.
Lemma lem5379482 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5379483 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5379484 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem5379483 h1) (fun h1 : term113 = True => @lem5379482)). Qed.
Lemma lem5379485 : term113 = True.
Proof. exact (EQ_MP (@lem5379484) (@lem5379482)). Qed.
Lemma lem5379486 : term112 = True.
Proof. exact (TRANS (@lem5379481) (@lem5379485)). Qed.
Lemma lem5379487 : True = term112.
Proof. exact (SYM (@lem5379486)). Qed.
Lemma lem5379488 : term112.
Proof. exact (EQ_MP (@lem5379487) (@lem0)). Qed.
Lemma lem5379489 : term115.
Proof. exact (@lem5379478 (@lem5379488)). Qed.
Lemma lem5379491 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5379492 : term112 = term113.
Proof. exact (@lem5379491 (NUMERAL 0) term13). Qed.
Lemma lem5379493 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5379494 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5379495 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem5379494 h1) (fun h1 : term113 = True => @lem5379493)). Qed.
Lemma lem5379496 : term113 = True.
Proof. exact (EQ_MP (@lem5379495) (@lem5379493)). Qed.
Lemma lem5379497 : term112 = True.
Proof. exact (TRANS (@lem5379492) (@lem5379496)). Qed.
Lemma lem5379498 : True = term112.
Proof. exact (SYM (@lem5379497)). Qed.
Lemma lem5379499 : term112.
Proof. exact (EQ_MP (@lem5379498) (@lem0)). Qed.
Lemma lem5379500 : term116.
Proof. exact (@lem5379489 (@lem5379499)). Qed.
Lemma lem5379502 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5379503 : term112 = term113.
Proof. exact (@lem5379502 (NUMERAL 0) term13). Qed.
Lemma lem5379504 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5379505 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5379506 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem5379505 h1) (fun h1 : term113 = True => @lem5379504)). Qed.
Lemma lem5379507 : term113 = True.
Proof. exact (EQ_MP (@lem5379506) (@lem5379504)). Qed.
Lemma lem5379508 : term112 = True.
Proof. exact (TRANS (@lem5379503) (@lem5379507)). Qed.
Lemma lem5379509 : True = term112.
Proof. exact (SYM (@lem5379508)). Qed.
Lemma lem5379510 : term112.
Proof. exact (EQ_MP (@lem5379509) (@lem0)). Qed.
Lemma lem5379511 : term117.
Proof. exact (@lem5379500 (@lem5379510)). Qed.
Lemma lem5379513 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5379514 : term73 = term74.
Proof. exact (@lem5379513 term13 term13). Qed.
Lemma lem5379515 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5379516 : term76 = term13.
Proof. exact (EQ_MP (@lem5379515) (@lem940073)). Qed.
Lemma lem5379517 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5379518 : term74 = term47.
Proof. exact (MK_COMB (@lem5379517) (@lem5379516)). Qed.
Lemma lem5379519 : term73 = term47.
Proof. exact (TRANS (@lem5379514) (@lem5379518)). Qed.
Lemma lem5379521 (m : nat) (n : nat) : (term94 m n) = (term95 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5379522 : term91 = term96.
Proof. exact (@lem5379521 term13 term13). Qed.
Lemma lem5379523 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5379524 : term76 = term13.
Proof. exact (EQ_MP (@lem5379523) (@lem940073)). Qed.
Lemma lem5379525 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5379526 : term74 = term47.
Proof. exact (MK_COMB (@lem5379525) (@lem5379524)). Qed.
Lemma lem5379527 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5379528 : term96 = term64.
Proof. exact (MK_COMB (@lem5379527) (@lem5379526)). Qed.
Lemma lem5379529 : term91 = term64.
Proof. exact (TRANS (@lem5379522) (@lem5379528)). Qed.
Lemma lem5379530 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5379531 : term118 = term106.
Proof. exact (MK_COMB (@lem5379530) (@lem5379529)). Qed.
Lemma lem5379532 : term119 = term108.
Proof. exact (MK_COMB (@lem5379531) (@lem5379519)). Qed.
Lemma lem5379534 (m : nat) : (term120 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5379535 : term108 = term35.
Proof. exact (@lem5379534 term13). Qed.
Lemma lem5379536 : term119 = term35.
Proof. exact (TRANS (@lem5379532) (@lem5379535)). Qed.
Lemma lem5379537 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5379538 : term121 = term122.
Proof. exact (MK_COMB (@lem5379537) (@lem5379536)). Qed.
Lemma lem5379539 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem5379540 : term123 = term124.
Proof. exact (MK_COMB (@lem5379538) (@lem5379539)). Qed.
Lemma lem5379542 (x : nat) : (term125 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5379543 : term124 = term35.
Proof. exact (@lem5379542 term13). Qed.
Lemma lem5379544 : term123 = term35.
Proof. exact (TRANS (@lem5379540) (@lem5379543)). Qed.
Lemma lem5379546 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5379547 : term73 = term74.
Proof. exact (@lem5379546 term13 term13). Qed.
Lemma lem5379548 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5379549 : term76 = term13.
Proof. exact (EQ_MP (@lem5379548) (@lem940073)). Qed.
Lemma lem5379550 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5379551 : term74 = term47.
Proof. exact (MK_COMB (@lem5379550) (@lem5379549)). Qed.
Lemma lem5379552 : term73 = term47.
Proof. exact (TRANS (@lem5379547) (@lem5379551)). Qed.
Lemma lem5379553 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem5379554 : term126 = term124.
Proof. exact (MK_COMB (@lem5379553) (@lem5379552)). Qed.
Lemma lem5379556 (x : nat) : (term125 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5379557 : term124 = term35.
Proof. exact (@lem5379556 term13). Qed.
Lemma lem5379558 : term126 = term35.
Proof. exact (TRANS (@lem5379554) (@lem5379557)). Qed.
Lemma lem5379559 : term35 = term126.
Proof. exact (SYM (@lem5379558)). Qed.
Lemma lem5379560 : term123 = term126.
Proof. exact (TRANS (@lem5379544) (@lem5379559)). Qed.
Lemma lem5379561 : term109 = term61.
Proof. exact (@lem5379511 (@lem5379560)). Qed.
Lemma lem5379562 : term108 = term61.
Proof. exact (TRANS (@lem5379477) (@lem5379561)). Qed.
Lemma lem5379564 (x : real) : (term80 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5379565 : term61 = term35.
Proof. exact (@lem5379564 term35). Qed.
Lemma lem5379566 : term108 = term35.
Proof. exact (TRANS (@lem5379562) (@lem5379565)). Qed.
Lemma lem5379567 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5379568 : term127 = term122.
Proof. exact (MK_COMB (@lem5379567) (@lem5379566)). Qed.
Lemma lem5379569 (_69785 : int) : (real_of_int _69785) = (real_of_int _69785).
Proof. exact (eq_refl (real_of_int _69785)). Qed.
Lemma lem5379570 (_69785 : int) : (term105 _69785) = (term128 _69785).
Proof. exact (MK_COMB (@lem5379568) (@lem5379569 _69785)). Qed.
Lemma lem5379571 (_69785 : int) : (term104 _69785) = (term128 _69785).
Proof. exact (TRANS (@lem5379468 _69785) (@lem5379570 _69785)). Qed.
Lemma lem5379572 (_69785 : int) : (term128 _69785) = term35.
Proof. exact (@lem1982719 (real_of_int _69785)). Qed.
Lemma lem5379573 (_69785 : int) : (term104 _69785) = term35.
Proof. exact (TRANS (@lem5379571 _69785) (@lem5379572 _69785)). Qed.
Lemma lem5379574 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5379575 (_69785 : int) : (term129 _69785) = term130.
Proof. exact (MK_COMB (@lem5379574) (@lem5379573 _69785)). Qed.
Lemma lem5379576 : term64 = term64.
Proof. exact (eq_refl term64). Qed.
Lemma lem5379577 (_69785 : int) : (term102 _69785) = term131.
Proof. exact (MK_COMB (@lem5379575 _69785) (@lem5379576)). Qed.
Lemma lem5379578 (_69785 : int) : (term101 _69785) = term131.
Proof. exact (TRANS (@lem5379467 _69785) (@lem5379577 _69785)). Qed.
Lemma lem5379579 : term131 = term64.
Proof. exact (@lem1982721 term64). Qed.
Lemma lem5379580 (_69785 : int) : (term101 _69785) = term64.
Proof. exact (TRANS (@lem5379578 _69785) (@lem5379579)). Qed.
Lemma lem5379581 (_69785 : int) : (term87 _69785) = term64.
Proof. exact (TRANS (@lem5379466 _69785) (@lem5379580 _69785)). Qed.
Lemma lem5379583 (_69785 : int) : (term86 _69785) = term64.
Proof. exact (TRANS (@lem5379421 _69785) (@lem5379581 _69785)). Qed.
Lemma lem5379584 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5379585 (_69785 : int) : (term132 _69785) = term133.
Proof. exact (MK_COMB (@lem5379584) (@lem5379583 _69785)). Qed.
Lemma lem5379586 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem5379587 (_69785 : int) : (term85 _69785) = term134.
Proof. exact (MK_COMB (@lem5379585 _69785) (@lem5379586)). Qed.
Lemma lem5379588 (_69785 : int) : (term52 _69785) = term134.
Proof. exact (TRANS (@lem5379409 _69785) (@lem5379587 _69785)). Qed.
Lemma lem5379589 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5379590 (_69785 : int) : (term53 _69785) = (term135 _69785).
Proof. exact (MK_COMB (@lem5379589) (@lem5379408 _69785)). Qed.
Lemma lem5379591 (_69785 : int) : (term54 _69785) = (term136 _69785).
Proof. exact (MK_COMB (@lem5379590 _69785) (@lem5379588 _69785)). Qed.
Lemma lem5379606 (_69785 : int) : (term56 _69785) = (term136 _69785).
Proof. exact (TRANS (@lem5379360 _69785) (@lem5379591 _69785)). Qed.
Lemma lem5379610 (_69785 : int) (h1 : term136 _69785) : term136 _69785.
Proof. exact (h1). Qed.
Lemma lem5379611 (_69785 : int) (h1 : term136 _69785) : term134.
Proof. exact (proj2 (@lem5379610 _69785 h1)). Qed.
Lemma lem5379614 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5379615 : term134 = term137.
Proof. exact (@lem5379614 term35 term64). Qed.
Lemma lem5379617 (x : nat) : (term62 x) = (term63 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5379618 : term64 = term65.
Proof. exact (@lem5379617 term13). Qed.
Lemma lem5379620 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5379621 : term35 = term61.
Proof. exact (@lem5379620 (NUMERAL 0)). Qed.
Lemma lem5379622 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5379623 : term37 = term138.
Proof. exact (MK_COMB (@lem5379622) (@lem5379621)). Qed.
Lemma lem5379624 : term137 = term139.
Proof. exact (MK_COMB (@lem5379623) (@lem5379618)). Qed.
Lemma lem5379625 : term140.
Proof. exact (@lem1980026 term35 term47 term64 term47). Qed.
Lemma lem5379627 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5379628 : term112 = term113.
Proof. exact (@lem5379627 (NUMERAL 0) term13). Qed.
Lemma lem5379629 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5379630 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5379631 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem5379630 h1) (fun h1 : term113 = True => @lem5379629)). Qed.
Lemma lem5379632 : term113 = True.
Proof. exact (EQ_MP (@lem5379631) (@lem5379629)). Qed.
Lemma lem5379633 : term112 = True.
Proof. exact (TRANS (@lem5379628) (@lem5379632)). Qed.
Lemma lem5379634 : True = term112.
Proof. exact (SYM (@lem5379633)). Qed.
Lemma lem5379635 : term112.
Proof. exact (EQ_MP (@lem5379634) (@lem0)). Qed.
Lemma lem5379636 : term141.
Proof. exact (@lem5379625 (@lem5379635)). Qed.
Lemma lem5379638 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5379639 : term112 = term113.
Proof. exact (@lem5379638 (NUMERAL 0) term13). Qed.
Lemma lem5379640 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5379641 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5379642 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem5379641 h1) (fun h1 : term113 = True => @lem5379640)). Qed.
Lemma lem5379643 : term113 = True.
Proof. exact (EQ_MP (@lem5379642) (@lem5379640)). Qed.
Lemma lem5379644 : term112 = True.
Proof. exact (TRANS (@lem5379639) (@lem5379643)). Qed.
Lemma lem5379645 : True = term112.
Proof. exact (SYM (@lem5379644)). Qed.
Lemma lem5379646 : term112.
Proof. exact (EQ_MP (@lem5379645) (@lem0)). Qed.
Lemma lem5379647 : term139 = term142.
Proof. exact (@lem5379636 (@lem5379646)). Qed.
Lemma lem5379649 (m : nat) (n : nat) : (term94 m n) = (term95 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5379650 : term91 = term96.
Proof. exact (@lem5379649 term13 term13). Qed.
Lemma lem5379651 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5379652 : term76 = term13.
Proof. exact (EQ_MP (@lem5379651) (@lem940073)). Qed.
Lemma lem5379653 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5379654 : term74 = term47.
Proof. exact (MK_COMB (@lem5379653) (@lem5379652)). Qed.
Lemma lem5379655 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5379656 : term96 = term64.
Proof. exact (MK_COMB (@lem5379655) (@lem5379654)). Qed.
Lemma lem5379657 : term91 = term64.
Proof. exact (TRANS (@lem5379650) (@lem5379656)). Qed.
Lemma lem5379659 (x : nat) : (term125 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5379660 : term124 = term35.
Proof. exact (@lem5379659 term13). Qed.
Lemma lem5379661 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5379662 : term143 = term37.
Proof. exact (MK_COMB (@lem5379661) (@lem5379660)). Qed.
Lemma lem5379663 : term142 = term137.
Proof. exact (MK_COMB (@lem5379662) (@lem5379657)). Qed.
Lemma lem5379665 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5379666 : term137 = term146.
Proof. exact (@lem5379665 (NUMERAL 0) term13). Qed.
Lemma lem5379667 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5379668 (h1 : term114 = (BIT1 0)) : (term13 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5379669 : (term114 = (BIT1 0)) = ((term13 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem5379668 h1) (fun h1 : (term13 = (NUMERAL 0)) = False => @lem5379667)). Qed.
Lemma lem5379670 : (term13 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5379669) (@lem5379667)). Qed.
Lemma lem5379671 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5379672 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5379673 : term147 = (and True).
Proof. exact (MK_COMB (@lem5379672) (@lem5379671)). Qed.
Lemma lem5379674 : term146 = (True /\ False).
Proof. exact (MK_COMB (@lem5379673) (@lem5379670)). Qed.
Lemma lem5379676 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5379677 : term146 = False.
Proof. exact (TRANS (@lem5379674) (@lem5379676)). Qed.
Lemma lem5379678 : term137 = False.
Proof. exact (TRANS (@lem5379666) (@lem5379677)). Qed.
Lemma lem5379679 : term142 = False.
Proof. exact (TRANS (@lem5379663) (@lem5379678)). Qed.
Lemma lem5379680 : term139 = False.
Proof. exact (TRANS (@lem5379647) (@lem5379679)). Qed.
Lemma lem5379681 : term137 = False.
Proof. exact (TRANS (@lem5379624) (@lem5379680)). Qed.
Lemma lem5379682 : term134 = False.
Proof. exact (TRANS (@lem5379615) (@lem5379681)). Qed.
Lemma lem5379683 (_69785 : int) (h1 : term136 _69785) : False.
Proof. exact (EQ_MP (@lem5379682) (@lem5379611 _69785 h1)). Qed.
Lemma lem5379685 (_69785 : int) (h1 : term136 _69785) : term136 _69785.
Proof. exact (h1). Qed.
Lemma lem5379686 (_69785 : int) (h1 : term136 _69785) : (term136 _69785) = False.
Proof. exact (prop_ext (fun h2 : term136 _69785 => @lem5379683 _69785 h1) (fun h2 : False => @lem5379685 _69785 h1)). Qed.
Lemma lem5379687 (_69785 : int) (h1 : term136 _69785) : False.
Proof. exact (EQ_MP (@lem5379686 _69785 h1) (@lem5379685 _69785 h1)). Qed.
Lemma lem5379688 (_69785 : int) (h1 : term56 _69785) : term56 _69785.
Proof. exact (h1). Qed.
Lemma lem5379689 (_69785 : int) (h1 : term56 _69785) : term136 _69785.
Proof. exact (EQ_MP (@lem5379606 _69785) (@lem5379688 _69785 h1)). Qed.
Lemma lem5379690 (_69785 : int) (h1 : term56 _69785) : (term136 _69785) = False.
Proof. exact (prop_ext (fun h2 : term136 _69785 => @lem5379687 _69785 h2) (fun h2 : False => @lem5379689 _69785 h1)). Qed.
Lemma lem5379691 (_69785 : int) (h1 : term56 _69785) : False.
Proof. exact (EQ_MP (@lem5379690 _69785 h1) (@lem5379689 _69785 h1)). Qed.
Lemma lem5379692 (_69785 : int) : term148 _69785.
Proof. exact (fun h0 : term56 _69785 => @lem5379691 _69785 h0). Qed.
Lemma lem5379693 (_69785 : int) : term149 _69785.
Proof. exact (@lem1386578 (term150 _69785)). Qed.
Lemma lem5379696 (_69785 : int) : term150 _69785.
Proof. exact (@lem5379693 _69785 (@lem5379692 _69785)). Qed.
Lemma lem5379697 (_69785 : int) : (term54 _69785) = (term27 _69785).
Proof. exact (SYM (@lem5379340 _69785)). Qed.
Lemma lem5379698 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5379699 (_69785 : int) : (term150 _69785) = (term20 _69785).
Proof. exact (MK_COMB (@lem5379698) (@lem5379697 _69785)). Qed.
Lemma lem5379700 (_69785 : int) : term20 _69785.
Proof. exact (EQ_MP (@lem5379699 _69785) (@lem5379696 _69785)). Qed.
Lemma lem5379701 (_69785 : int) : term21 _69785.
Proof. exact (EQ_MP (@lem5379281 _69785) (@lem5379700 _69785)). Qed.
Lemma lem5379702 (n : nat) : term151 n.
Proof. exact (@lem5379701 (int_of_num n)). Qed.
Lemma lem5379703 (n : nat) : term17 n.
Proof. exact (@lem5379702 n (@lem5379280 n)). Qed.
Lemma lem5379704 (n : nat) : (term17 n) = (term5 n).
Proof. exact (SYM (@lem5379277 n)). Qed.
Lemma lem5379705 (n : nat) : term5 n.
Proof. exact (EQ_MP (@lem5379704 n) (@lem5379703 n)). Qed.
Lemma lem5379718 (m : nat) : (S m) = (term0 m).
Proof. exact (EQ_MP (@lem2841417 m) (@lem2841416 m)). Qed.
Lemma lem5379719 (m : nat) (d : nat) : (term152 m d) = (term153 m d).
Proof. exact (@lem5379718 (Nat.add m d)). Qed.
Lemma lem5379720 (m : nat) : (Peano.le m) = (Peano.le m).
Proof. exact (eq_refl (Peano.le m)). Qed.
Lemma lem5379722 (m : nat) (d : nat) : (term154 m d) = (term155 m d).
Proof. exact (MK_COMB (@lem5379720 m) (@lem5379719 m d)). Qed.
Lemma lem5379723 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem5379730 (d : nat) (m : nat) : (Nat.add m d) = (Nat.add d m).
Proof. exact (@lem1032098 d m). Qed.
Lemma lem5379731 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem5379732 (d : nat) (m : nat) : (term156 m d) = (term156 d m).
Proof. exact (MK_COMB (@lem5379731) (@lem5379730 d m)). Qed.
Lemma lem5379733 (d : nat) (m : nat) : (term153 m d) = (term153 d m).
Proof. exact (MK_COMB (@lem5379732 d m) (@lem5379723)). Qed.
Lemma lem5379738 (d : nat) (m : nat) : (term153 d m) = (term157 d m).
Proof. exact (@lem1032092 d m term13). Qed.
Lemma lem5379739 (d : nat) (m : nat) : (term153 m d) = (term157 d m).
Proof. exact (TRANS (@lem5379733 d m) (@lem5379738 d m)). Qed.
Lemma lem5379742 (m : nat) : (Peano.le m) = (Peano.le m).
Proof. exact (eq_refl (Peano.le m)). Qed.
Lemma lem5379743 (d : nat) (m : nat) : (term155 m d) = (term158 d m).
Proof. exact (MK_COMB (@lem5379742 m) (@lem5379739 d m)). Qed.
Lemma lem5379746 (d : nat) (m : nat) : (term154 m d) = (term158 d m).
Proof. exact (TRANS (@lem5379722 m d) (@lem5379743 d m)). Qed.
Lemma lem5379748 (m : nat) (n : nat) : (Peano.le m n) = (term7 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5379749 (d : nat) (m : nat) : (term158 d m) = (term159 d m).
Proof. exact (@lem5379748 m (term157 d m)). Qed.
Lemma lem5379751 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5379752 (d : nat) (m : nat) : (term160 d m) = (term161 d m).
Proof. exact (@lem5379751 d (term0 m)). Qed.
Lemma lem5379754 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5379755 (m : nat) : (term11 m) = (term12 m).
Proof. exact (@lem5379754 m term13). Qed.
Lemma lem5379756 (d : nat) : (term162 d) = (term162 d).
Proof. exact (eq_refl (term162 d)). Qed.
Lemma lem5379757 (d : nat) (m : nat) : (term161 d m) = (term163 d m).
Proof. exact (MK_COMB (@lem5379756 d) (@lem5379755 m)). Qed.
Lemma lem5379758 (d : nat) (m : nat) : (term160 d m) = (term163 d m).
Proof. exact (TRANS (@lem5379752 d m) (@lem5379757 d m)). Qed.
Lemma lem5379759 (m : nat) : (term164 m) = (term164 m).
Proof. exact (eq_refl (term164 m)). Qed.
Lemma lem5379760 (d : nat) (m : nat) : (term159 d m) = (term165 d m).
Proof. exact (MK_COMB (@lem5379759 m) (@lem5379758 d m)). Qed.
Lemma lem5379761 (d : nat) (m : nat) : (term158 d m) = (term165 d m).
Proof. exact (TRANS (@lem5379749 d m) (@lem5379760 d m)). Qed.
Lemma lem5379762 (d : nat) (m : nat) : (term154 m d) = (term165 d m).
Proof. exact (TRANS (@lem5379746 d m) (@lem5379761 d m)). Qed.
Lemma lem5379763 (d : nat) : term18 d.
Proof. exact (@lem2307535 d). Qed.
Lemma lem5379764 (d : nat) : (term18 d) = (term19 d).
Proof. exact (eq_refl (term18 d)). Qed.
Lemma lem5379765 (d : nat) : term19 d.
Proof. exact (EQ_MP (@lem5379764 d) (@lem5379763 d)). Qed.
Lemma lem5379766 (m : nat) : term18 m.
Proof. exact (@lem2307535 m). Qed.
Lemma lem5379767 (m : nat) : (term18 m) = (term19 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem5379768 (m : nat) : term19 m.
Proof. exact (EQ_MP (@lem5379767 m) (@lem5379766 m)). Qed.
Lemma lem5379769 (_69787 : int) (_69788 : int) : (term166 _69787 _69788) = (term167 _69787 _69788).
Proof. exact (@lem2318604 (term167 _69787 _69788)). Qed.
Lemma lem5379786 (_69787 : int) (_69788 : int) : (term168 _69787 _69788) = (term169 _69787 _69788).
Proof. exact (@lem17362 (term28 _69788) (term170 _69787 _69788)). Qed.
Lemma lem5379788 (_69787 : int) : (term24 _69787) = (term24 _69787).
Proof. exact (eq_refl (term24 _69787)). Qed.
Lemma lem5379789 (_69787 : int) (_69788 : int) : (term171 _69787 _69788) = (term172 _69787 _69788).
Proof. exact (MK_COMB (@lem5379788 _69787) (@lem5379786 _69787 _69788)). Qed.
Lemma lem5379790 (_69787 : int) (_69788 : int) : (term173 _69787 _69788) = (term171 _69787 _69788).
Proof. exact (@lem17362 (term28 _69787) (term174 _69787 _69788)). Qed.
Lemma lem5379804 (_69787 : int) (_69788 : int) : (term173 _69787 _69788) = (term172 _69787 _69788).
Proof. exact (TRANS (@lem5379790 _69787 _69788) (@lem5379789 _69787 _69788)). Qed.
Lemma lem5379807 (x : int) (y : int) : (int_le x y) = (term30 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5379808 (_69787 : int) : (term28 _69787) = (term31 _69787).
Proof. exact (@lem5379807 term32 _69787). Qed.
Lemma lem5379810 (n : nat) : (term33 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5379811 : term34 = term35.
Proof. exact (@lem5379810 (NUMERAL 0)). Qed.
Lemma lem5379812 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5379813 : term36 = term37.
Proof. exact (MK_COMB (@lem5379812) (@lem5379811)). Qed.
Lemma lem5379814 (_69787 : int) : (real_of_int _69787) = (real_of_int _69787).
Proof. exact (eq_refl (real_of_int _69787)). Qed.
Lemma lem5379815 (_69787 : int) : (term31 _69787) = (term38 _69787).
Proof. exact (MK_COMB (@lem5379813) (@lem5379814 _69787)). Qed.
Lemma lem5379817 (_69787 : int) : (term28 _69787) = (term38 _69787).
Proof. exact (TRANS (@lem5379808 _69787) (@lem5379815 _69787)). Qed.
Lemma lem5379820 (x : int) (y : int) : (int_le x y) = (term30 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5379821 (_69788 : int) : (term28 _69788) = (term31 _69788).
Proof. exact (@lem5379820 term32 _69788). Qed.
Lemma lem5379823 (n : nat) : (term33 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5379824 : term34 = term35.
Proof. exact (@lem5379823 (NUMERAL 0)). Qed.
Lemma lem5379825 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5379826 : term36 = term37.
Proof. exact (MK_COMB (@lem5379825) (@lem5379824)). Qed.
Lemma lem5379827 (_69788 : int) : (real_of_int _69788) = (real_of_int _69788).
Proof. exact (eq_refl (real_of_int _69788)). Qed.
Lemma lem5379828 (_69788 : int) : (term31 _69788) = (term38 _69788).
Proof. exact (MK_COMB (@lem5379826) (@lem5379827 _69788)). Qed.
Lemma lem5379830 (_69788 : int) : (term28 _69788) = (term38 _69788).
Proof. exact (TRANS (@lem5379821 _69788) (@lem5379828 _69788)). Qed.
Lemma lem5379832 (y : int) (x : int) : (term175 x y) = (term176 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5379833 (_69787 : int) (_69788 : int) : (term177 _69787 _69788) = (term178 _69787 _69788).
Proof. exact (@lem5379832 (term179 _69787 _69788) _69788). Qed.
Lemma lem5379835 (x : int) (y : int) : (int_le x y) = (term30 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5379836 (_69787 : int) (_69788 : int) : (term178 _69787 _69788) = (term180 _69787 _69788).
Proof. exact (@lem5379835 (term181 _69787 _69788) _69788). Qed.
Lemma lem5379838 (x : int) (y : int) : (term41 x y) = (term42 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5379839 (_69787 : int) (_69788 : int) : (term182 _69787 _69788) = (term183 _69787 _69788).
Proof. exact (@lem5379838 (term179 _69787 _69788) term45). Qed.
Lemma lem5379841 (x : int) (y : int) : (term41 x y) = (term42 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5379842 (_69787 : int) (_69788 : int) : (term184 _69787 _69788) = (term185 _69787 _69788).
Proof. exact (@lem5379841 _69787 (term40 _69788)). Qed.
Lemma lem5379844 (x : int) (y : int) : (term41 x y) = (term42 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5379845 (_69788 : int) : (term43 _69788) = (term44 _69788).
Proof. exact (@lem5379844 _69788 term45). Qed.
Lemma lem5379847 (n : nat) : (term33 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5379848 : term46 = term47.
Proof. exact (@lem5379847 term13). Qed.
Lemma lem5379849 (_69788 : int) : (term48 _69788) = (term48 _69788).
Proof. exact (eq_refl (term48 _69788)). Qed.
Lemma lem5379850 (_69788 : int) : (term44 _69788) = (term49 _69788).
Proof. exact (MK_COMB (@lem5379849 _69788) (@lem5379848)). Qed.
Lemma lem5379851 (_69788 : int) : (term43 _69788) = (term49 _69788).
Proof. exact (TRANS (@lem5379845 _69788) (@lem5379850 _69788)). Qed.
Lemma lem5379852 (_69787 : int) : (term48 _69787) = (term48 _69787).
Proof. exact (eq_refl (term48 _69787)). Qed.
Lemma lem5379853 (_69787 : int) (_69788 : int) : (term185 _69787 _69788) = (term186 _69787 _69788).
Proof. exact (MK_COMB (@lem5379852 _69787) (@lem5379851 _69788)). Qed.
Lemma lem5379854 (_69787 : int) (_69788 : int) : (term184 _69787 _69788) = (term186 _69787 _69788).
Proof. exact (TRANS (@lem5379842 _69787 _69788) (@lem5379853 _69787 _69788)). Qed.
Lemma lem5379855 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5379856 (_69787 : int) (_69788 : int) : (term187 _69787 _69788) = (term188 _69787 _69788).
Proof. exact (MK_COMB (@lem5379855) (@lem5379854 _69787 _69788)). Qed.
Lemma lem5379858 (n : nat) : (term33 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5379859 : term46 = term47.
Proof. exact (@lem5379858 term13). Qed.
Lemma lem5379860 (_69787 : int) (_69788 : int) : (term183 _69787 _69788) = (term189 _69787 _69788).
Proof. exact (MK_COMB (@lem5379856 _69787 _69788) (@lem5379859)). Qed.
Lemma lem5379861 (_69787 : int) (_69788 : int) : (term182 _69787 _69788) = (term189 _69787 _69788).
Proof. exact (TRANS (@lem5379839 _69787 _69788) (@lem5379860 _69787 _69788)). Qed.
Lemma lem5379862 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5379863 (_69787 : int) (_69788 : int) : (term190 _69787 _69788) = (term191 _69787 _69788).
Proof. exact (MK_COMB (@lem5379862) (@lem5379861 _69787 _69788)). Qed.
Lemma lem5379864 (_69788 : int) : (real_of_int _69788) = (real_of_int _69788).
Proof. exact (eq_refl (real_of_int _69788)). Qed.
Lemma lem5379865 (_69787 : int) (_69788 : int) : (term180 _69787 _69788) = (term192 _69787 _69788).
Proof. exact (MK_COMB (@lem5379863 _69787 _69788) (@lem5379864 _69788)). Qed.
Lemma lem5379866 (_69787 : int) (_69788 : int) : (term178 _69787 _69788) = (term192 _69787 _69788).
Proof. exact (TRANS (@lem5379836 _69787 _69788) (@lem5379865 _69787 _69788)). Qed.
Lemma lem5379867 (_69787 : int) (_69788 : int) : (term177 _69787 _69788) = (term192 _69787 _69788).
Proof. exact (TRANS (@lem5379833 _69787 _69788) (@lem5379866 _69787 _69788)). Qed.
Lemma lem5379868 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5379869 (_69788 : int) : (term24 _69788) = (term53 _69788).
Proof. exact (MK_COMB (@lem5379868) (@lem5379830 _69788)). Qed.
Lemma lem5379870 (_69787 : int) (_69788 : int) : (term169 _69787 _69788) = (term193 _69787 _69788).
Proof. exact (MK_COMB (@lem5379869 _69788) (@lem5379867 _69787 _69788)). Qed.
Lemma lem5379871 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5379872 (_69787 : int) : (term24 _69787) = (term53 _69787).
Proof. exact (MK_COMB (@lem5379871) (@lem5379817 _69787)). Qed.
Lemma lem5379873 (_69787 : int) (_69788 : int) : (term172 _69787 _69788) = (term194 _69787 _69788).
Proof. exact (MK_COMB (@lem5379872 _69787) (@lem5379870 _69787 _69788)). Qed.
Lemma lem5379874 (_69787 : int) (_69788 : int) : (term173 _69787 _69788) = (term194 _69787 _69788).
Proof. exact (TRANS (@lem5379804 _69787 _69788) (@lem5379873 _69787 _69788)). Qed.
Lemma lem5379878 (t : Prop) : (term55 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5379904 (_69787 : int) (_69788 : int) : (term195 _69787 _69788) = (term194 _69787 _69788).
Proof. exact (@lem5379878 (term194 _69787 _69788)). Qed.
Lemma lem5379905 (_69787 : int) : (term38 _69787) = (term57 _69787).
Proof. exact (@lem1988287 (real_of_int _69787) term35). Qed.
Lemma lem5379911 (_69787 : int) : (term58 _69787) = (term59 _69787).
Proof. exact (@lem1982792 (real_of_int _69787) term35). Qed.
Lemma lem5379913 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5379914 : term35 = term61.
Proof. exact (@lem5379913 (NUMERAL 0)). Qed.
Lemma lem5379916 (x : nat) : (term62 x) = (term63 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5379917 : term64 = term65.
Proof. exact (@lem5379916 term13). Qed.
Lemma lem5379918 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5379919 : term66 = term67.
Proof. exact (MK_COMB (@lem5379918) (@lem5379917)). Qed.
Lemma lem5379920 : term68 = term69.
Proof. exact (MK_COMB (@lem5379919) (@lem5379914)). Qed.
Lemma lem5379921 : term69 = term70.
Proof. exact (@lem1981613 term64 term35 term47 term47). Qed.
Lemma lem5379923 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5379924 : term73 = term74.
Proof. exact (@lem5379923 term13 term13). Qed.
Lemma lem5379925 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5379926 : term76 = term13.
Proof. exact (EQ_MP (@lem5379925) (@lem940073)). Qed.
Lemma lem5379927 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5379928 : term74 = term47.
Proof. exact (MK_COMB (@lem5379927) (@lem5379926)). Qed.
Lemma lem5379929 : term73 = term47.
Proof. exact (TRANS (@lem5379924) (@lem5379928)). Qed.
Lemma lem5379931 (x : nat) : (term77 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5379932 : term68 = term35.
Proof. exact (@lem5379931 term13). Qed.
Lemma lem5379933 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5379934 : term78 = term79.
Proof. exact (MK_COMB (@lem5379933) (@lem5379932)). Qed.
Lemma lem5379935 : term70 = term61.
Proof. exact (MK_COMB (@lem5379934) (@lem5379929)). Qed.
Lemma lem5379936 : term69 = term61.
Proof. exact (TRANS (@lem5379921) (@lem5379935)). Qed.
Lemma lem5379937 : term68 = term61.
Proof. exact (TRANS (@lem5379920) (@lem5379936)). Qed.
Lemma lem5379939 (x : real) : (term80 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5379940 : term61 = term35.
Proof. exact (@lem5379939 term35). Qed.
Lemma lem5379941 : term68 = term35.
Proof. exact (TRANS (@lem5379937) (@lem5379940)). Qed.
Lemma lem5379942 (_69787 : int) : (term48 _69787) = (term48 _69787).
Proof. exact (eq_refl (term48 _69787)). Qed.
Lemma lem5379943 (_69787 : int) : (term59 _69787) = (term81 _69787).
Proof. exact (MK_COMB (@lem5379942 _69787) (@lem5379941)). Qed.
Lemma lem5379944 (_69787 : int) : (term81 _69787) = (real_of_int _69787).
Proof. exact (@lem1982723 (real_of_int _69787)). Qed.
Lemma lem5379945 (_69787 : int) : (term59 _69787) = (real_of_int _69787).
Proof. exact (TRANS (@lem5379943 _69787) (@lem5379944 _69787)). Qed.
Lemma lem5379947 (_69787 : int) : (term58 _69787) = (real_of_int _69787).
Proof. exact (TRANS (@lem5379911 _69787) (@lem5379945 _69787)). Qed.
Lemma lem5379948 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5379949 (_69787 : int) : (term82 _69787) = (term83 _69787).
Proof. exact (MK_COMB (@lem5379948) (@lem5379947 _69787)). Qed.
Lemma lem5379950 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem5379951 (_69787 : int) : (term57 _69787) = (term84 _69787).
Proof. exact (MK_COMB (@lem5379949 _69787) (@lem5379950)). Qed.
Lemma lem5379952 (_69787 : int) : (term38 _69787) = (term84 _69787).
Proof. exact (TRANS (@lem5379905 _69787) (@lem5379951 _69787)). Qed.
Lemma lem5379953 (_69788 : int) : (term38 _69788) = (term57 _69788).
Proof. exact (@lem1988287 (real_of_int _69788) term35). Qed.
Lemma lem5379959 (_69788 : int) : (term58 _69788) = (term59 _69788).
Proof. exact (@lem1982792 (real_of_int _69788) term35). Qed.
Lemma lem5379961 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5379962 : term35 = term61.
Proof. exact (@lem5379961 (NUMERAL 0)). Qed.
Lemma lem5379964 (x : nat) : (term62 x) = (term63 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5379965 : term64 = term65.
Proof. exact (@lem5379964 term13). Qed.
Lemma lem5379966 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5379967 : term66 = term67.
Proof. exact (MK_COMB (@lem5379966) (@lem5379965)). Qed.
Lemma lem5379968 : term68 = term69.
Proof. exact (MK_COMB (@lem5379967) (@lem5379962)). Qed.
Lemma lem5379969 : term69 = term70.
Proof. exact (@lem1981613 term64 term35 term47 term47). Qed.
Lemma lem5379971 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5379972 : term73 = term74.
Proof. exact (@lem5379971 term13 term13). Qed.
Lemma lem5379973 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5379974 : term76 = term13.
Proof. exact (EQ_MP (@lem5379973) (@lem940073)). Qed.
Lemma lem5379975 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5379976 : term74 = term47.
Proof. exact (MK_COMB (@lem5379975) (@lem5379974)). Qed.
Lemma lem5379977 : term73 = term47.
Proof. exact (TRANS (@lem5379972) (@lem5379976)). Qed.
Lemma lem5379979 (x : nat) : (term77 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5379980 : term68 = term35.
Proof. exact (@lem5379979 term13). Qed.
Lemma lem5379981 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5379982 : term78 = term79.
Proof. exact (MK_COMB (@lem5379981) (@lem5379980)). Qed.
Lemma lem5379983 : term70 = term61.
Proof. exact (MK_COMB (@lem5379982) (@lem5379977)). Qed.
Lemma lem5379984 : term69 = term61.
Proof. exact (TRANS (@lem5379969) (@lem5379983)). Qed.
Lemma lem5379985 : term68 = term61.
Proof. exact (TRANS (@lem5379968) (@lem5379984)). Qed.
Lemma lem5379987 (x : real) : (term80 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5379988 : term61 = term35.
Proof. exact (@lem5379987 term35). Qed.
Lemma lem5379989 : term68 = term35.
Proof. exact (TRANS (@lem5379985) (@lem5379988)). Qed.
Lemma lem5379990 (_69788 : int) : (term48 _69788) = (term48 _69788).
Proof. exact (eq_refl (term48 _69788)). Qed.
Lemma lem5379991 (_69788 : int) : (term59 _69788) = (term81 _69788).
Proof. exact (MK_COMB (@lem5379990 _69788) (@lem5379989)). Qed.
Lemma lem5379992 (_69788 : int) : (term81 _69788) = (real_of_int _69788).
Proof. exact (@lem1982723 (real_of_int _69788)). Qed.
Lemma lem5379993 (_69788 : int) : (term59 _69788) = (real_of_int _69788).
Proof. exact (TRANS (@lem5379991 _69788) (@lem5379992 _69788)). Qed.
Lemma lem5379995 (_69788 : int) : (term58 _69788) = (real_of_int _69788).
Proof. exact (TRANS (@lem5379959 _69788) (@lem5379993 _69788)). Qed.
Lemma lem5379996 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5379997 (_69788 : int) : (term82 _69788) = (term83 _69788).
Proof. exact (MK_COMB (@lem5379996) (@lem5379995 _69788)). Qed.
Lemma lem5379998 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem5379999 (_69788 : int) : (term57 _69788) = (term84 _69788).
Proof. exact (MK_COMB (@lem5379997 _69788) (@lem5379998)). Qed.
Lemma lem5380000 (_69788 : int) : (term38 _69788) = (term84 _69788).
Proof. exact (TRANS (@lem5379953 _69788) (@lem5379999 _69788)). Qed.
Lemma lem5380001 (_69787 : int) (_69788 : int) : (term192 _69787 _69788) = (term196 _69787 _69788).
Proof. exact (@lem1988287 (real_of_int _69788) (term189 _69787 _69788)). Qed.
Lemma lem5380019 (_69787 : int) (_69788 : int) : (term189 _69787 _69788) = (term197 _69787 _69788).
Proof. exact (@lem1982755 (real_of_int _69787) (term49 _69788) term47). Qed.
Lemma lem5380020 (_69788 : int) : (term198 _69788) = (term199 _69788).
Proof. exact (@lem1982755 (real_of_int _69788) term47 term47). Qed.
Lemma lem5380022 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5380023 : term47 = term90.
Proof. exact (@lem5380022 term13). Qed.
Lemma lem5380025 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5380026 : term47 = term90.
Proof. exact (@lem5380025 term13). Qed.
Lemma lem5380027 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5380028 : term200 = term201.
Proof. exact (MK_COMB (@lem5380027) (@lem5380026)). Qed.
Lemma lem5380029 : term202 = term203.
Proof. exact (MK_COMB (@lem5380028) (@lem5380023)). Qed.
Lemma lem5380030 : term204.
Proof. exact (@lem1981473 term47 term47 term47 term47 term205 term47). Qed.
Lemma lem5380032 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5380033 : term112 = term113.
Proof. exact (@lem5380032 (NUMERAL 0) term13). Qed.
Lemma lem5380034 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5380035 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5380036 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem5380035 h1) (fun h1 : term113 = True => @lem5380034)). Qed.
Lemma lem5380037 : term113 = True.
Proof. exact (EQ_MP (@lem5380036) (@lem5380034)). Qed.
Lemma lem5380038 : term112 = True.
Proof. exact (TRANS (@lem5380033) (@lem5380037)). Qed.
Lemma lem5380039 : True = term112.
Proof. exact (SYM (@lem5380038)). Qed.
Lemma lem5380040 : term112.
Proof. exact (EQ_MP (@lem5380039) (@lem0)). Qed.
Lemma lem5380041 : term206.
Proof. exact (@lem5380030 (@lem5380040)). Qed.
Lemma lem5380043 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5380044 : term112 = term113.
Proof. exact (@lem5380043 (NUMERAL 0) term13). Qed.
Lemma lem5380045 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5380046 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5380047 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem5380046 h1) (fun h1 : term113 = True => @lem5380045)). Qed.
Lemma lem5380048 : term113 = True.
Proof. exact (EQ_MP (@lem5380047) (@lem5380045)). Qed.
Lemma lem5380049 : term112 = True.
Proof. exact (TRANS (@lem5380044) (@lem5380048)). Qed.
Lemma lem5380050 : True = term112.
Proof. exact (SYM (@lem5380049)). Qed.
Lemma lem5380051 : term112.
Proof. exact (EQ_MP (@lem5380050) (@lem0)). Qed.
Lemma lem5380052 : term207.
Proof. exact (@lem5380041 (@lem5380051)). Qed.
Lemma lem5380054 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5380055 : term112 = term113.
Proof. exact (@lem5380054 (NUMERAL 0) term13). Qed.
Lemma lem5380056 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5380057 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5380058 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem5380057 h1) (fun h1 : term113 = True => @lem5380056)). Qed.
Lemma lem5380059 : term113 = True.
Proof. exact (EQ_MP (@lem5380058) (@lem5380056)). Qed.
Lemma lem5380060 : term112 = True.
Proof. exact (TRANS (@lem5380055) (@lem5380059)). Qed.
Lemma lem5380061 : True = term112.
Proof. exact (SYM (@lem5380060)). Qed.
Lemma lem5380062 : term112.
Proof. exact (EQ_MP (@lem5380061) (@lem0)). Qed.
Lemma lem5380063 : term208.
Proof. exact (@lem5380052 (@lem5380062)). Qed.
Lemma lem5380065 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5380066 : term73 = term74.
Proof. exact (@lem5380065 term13 term13). Qed.
Lemma lem5380067 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5380068 : term76 = term13.
Proof. exact (EQ_MP (@lem5380067) (@lem940073)). Qed.
Lemma lem5380069 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5380070 : term74 = term47.
Proof. exact (MK_COMB (@lem5380069) (@lem5380068)). Qed.
Lemma lem5380071 : term73 = term47.
Proof. exact (TRANS (@lem5380066) (@lem5380070)). Qed.
Lemma lem5380073 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5380074 : term73 = term74.
Proof. exact (@lem5380073 term13 term13). Qed.
Lemma lem5380075 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5380076 : term76 = term13.
Proof. exact (EQ_MP (@lem5380075) (@lem940073)). Qed.
Lemma lem5380077 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5380078 : term74 = term47.
Proof. exact (MK_COMB (@lem5380077) (@lem5380076)). Qed.
Lemma lem5380079 : term73 = term47.
Proof. exact (TRANS (@lem5380074) (@lem5380078)). Qed.
Lemma lem5380080 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5380081 : term209 = term200.
Proof. exact (MK_COMB (@lem5380080) (@lem5380079)). Qed.
Lemma lem5380082 : term210 = term202.
Proof. exact (MK_COMB (@lem5380081) (@lem5380071)). Qed.
Lemma lem5380083 : term202 = term211.
Proof. exact (@lem1367770 term13 term13). Qed.
Lemma lem5380084 : term212 = term213.
Proof. exact (@lem706885). Qed.
Lemma lem5380085 : (term212 = term213) = (term214 = term215).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term213). Qed.
Lemma lem5380086 : term214 = term215.
Proof. exact (EQ_MP (@lem5380085) (@lem5380084)). Qed.
Lemma lem5380087 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5380088 : term211 = term205.
Proof. exact (MK_COMB (@lem5380087) (@lem5380086)). Qed.
Lemma lem5380089 : term202 = term205.
Proof. exact (TRANS (@lem5380083) (@lem5380088)). Qed.
Lemma lem5380090 : term210 = term205.
Proof. exact (TRANS (@lem5380082) (@lem5380089)). Qed.
Lemma lem5380091 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5380092 : term216 = term217.
Proof. exact (MK_COMB (@lem5380091) (@lem5380090)). Qed.
Lemma lem5380093 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem5380094 : term218 = term219.
Proof. exact (MK_COMB (@lem5380092) (@lem5380093)). Qed.
Lemma lem5380096 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5380097 : term219 = term220.
Proof. exact (@lem5380096 term215 term13). Qed.
Lemma lem5380098 : term221 = term213.
Proof. exact (@lem996237 term213). Qed.
Lemma lem5380099 : (term221 = term213) = (term222 = term215).
Proof. exact (@lem1007663 term213 (BIT1 0) term213). Qed.
Lemma lem5380100 : term222 = term215.
Proof. exact (EQ_MP (@lem5380099) (@lem5380098)). Qed.
Lemma lem5380101 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5380102 : term220 = term205.
Proof. exact (MK_COMB (@lem5380101) (@lem5380100)). Qed.
Lemma lem5380103 : term219 = term205.
Proof. exact (TRANS (@lem5380097) (@lem5380102)). Qed.
Lemma lem5380104 : term218 = term205.
Proof. exact (TRANS (@lem5380094) (@lem5380103)). Qed.
Lemma lem5380106 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5380107 : term73 = term74.
Proof. exact (@lem5380106 term13 term13). Qed.
Lemma lem5380108 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5380109 : term76 = term13.
Proof. exact (EQ_MP (@lem5380108) (@lem940073)). Qed.
Lemma lem5380110 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5380111 : term74 = term47.
Proof. exact (MK_COMB (@lem5380110) (@lem5380109)). Qed.
Lemma lem5380112 : term73 = term47.
Proof. exact (TRANS (@lem5380107) (@lem5380111)). Qed.
Lemma lem5380113 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem5380114 : term223 = term219.
Proof. exact (MK_COMB (@lem5380113) (@lem5380112)). Qed.
Lemma lem5380116 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5380117 : term219 = term220.
Proof. exact (@lem5380116 term215 term13). Qed.
Lemma lem5380118 : term221 = term213.
Proof. exact (@lem996237 term213). Qed.
Lemma lem5380119 : (term221 = term213) = (term222 = term215).
Proof. exact (@lem1007663 term213 (BIT1 0) term213). Qed.
Lemma lem5380120 : term222 = term215.
Proof. exact (EQ_MP (@lem5380119) (@lem5380118)). Qed.
Lemma lem5380121 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5380122 : term220 = term205.
Proof. exact (MK_COMB (@lem5380121) (@lem5380120)). Qed.
Lemma lem5380123 : term219 = term205.
Proof. exact (TRANS (@lem5380117) (@lem5380122)). Qed.
Lemma lem5380124 : term223 = term205.
Proof. exact (TRANS (@lem5380114) (@lem5380123)). Qed.
Lemma lem5380125 : term205 = term223.
Proof. exact (SYM (@lem5380124)). Qed.
Lemma lem5380126 : term218 = term223.
Proof. exact (TRANS (@lem5380104) (@lem5380125)). Qed.
Lemma lem5380127 : term203 = term224.
Proof. exact (@lem5380063 (@lem5380126)). Qed.
Lemma lem5380128 : term202 = term224.
Proof. exact (TRANS (@lem5380029) (@lem5380127)). Qed.
Lemma lem5380130 (x : real) : (term80 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5380131 : term224 = term205.
Proof. exact (@lem5380130 term205). Qed.
Lemma lem5380132 : term202 = term205.
Proof. exact (TRANS (@lem5380128) (@lem5380131)). Qed.
Lemma lem5380133 (_69788 : int) : (term48 _69788) = (term48 _69788).
Proof. exact (eq_refl (term48 _69788)). Qed.
Lemma lem5380134 (_69788 : int) : (term199 _69788) = (term225 _69788).
Proof. exact (MK_COMB (@lem5380133 _69788) (@lem5380132)). Qed.
Lemma lem5380135 (_69788 : int) : (term198 _69788) = (term225 _69788).
Proof. exact (TRANS (@lem5380020 _69788) (@lem5380134 _69788)). Qed.
Lemma lem5380136 (_69787 : int) : (term48 _69787) = (term48 _69787).
Proof. exact (eq_refl (term48 _69787)). Qed.
Lemma lem5380137 (_69787 : int) (_69788 : int) : (term197 _69787 _69788) = (term226 _69787 _69788).
Proof. exact (MK_COMB (@lem5380136 _69787) (@lem5380135 _69788)). Qed.
Lemma lem5380139 (_69787 : int) (_69788 : int) : (term189 _69787 _69788) = (term226 _69787 _69788).
Proof. exact (TRANS (@lem5380019 _69787 _69788) (@lem5380137 _69787 _69788)). Qed.
Lemma lem5380142 (_69788 : int) : (term227 _69788) = (term227 _69788).
Proof. exact (eq_refl (term227 _69788)). Qed.
Lemma lem5380143 (_69787 : int) (_69788 : int) : (term228 _69787 _69788) = (term229 _69787 _69788).
Proof. exact (MK_COMB (@lem5380142 _69788) (@lem5380139 _69787 _69788)). Qed.
Lemma lem5380144 (_69787 : int) (_69788 : int) : (term229 _69787 _69788) = (term230 _69787 _69788).
Proof. exact (@lem1982792 (real_of_int _69788) (term226 _69787 _69788)). Qed.
Lemma lem5380145 (_69787 : int) (_69788 : int) : (term231 _69787 _69788) = (term232 _69787 _69788).
Proof. exact (@lem1982781 (real_of_int _69787) term64 (term225 _69788)). Qed.
Lemma lem5380146 (_69788 : int) : (term233 _69788) = (term234 _69788).
Proof. exact (@lem1982781 (real_of_int _69788) term64 term205). Qed.
Lemma lem5380148 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5380149 : term205 = term224.
Proof. exact (@lem5380148 term215). Qed.
Lemma lem5380151 (x : nat) : (term62 x) = (term63 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5380152 : term64 = term65.
Proof. exact (@lem5380151 term13). Qed.
Lemma lem5380153 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5380154 : term66 = term67.
Proof. exact (MK_COMB (@lem5380153) (@lem5380152)). Qed.
Lemma lem5380155 : term235 = term236.
Proof. exact (MK_COMB (@lem5380154) (@lem5380149)). Qed.
Lemma lem5380156 : term236 = term237.
Proof. exact (@lem1981613 term64 term205 term47 term47). Qed.
Lemma lem5380158 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5380159 : term73 = term74.
Proof. exact (@lem5380158 term13 term13). Qed.
Lemma lem5380160 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5380161 : term76 = term13.
Proof. exact (EQ_MP (@lem5380160) (@lem940073)). Qed.
Lemma lem5380162 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5380163 : term74 = term47.
Proof. exact (MK_COMB (@lem5380162) (@lem5380161)). Qed.
Lemma lem5380164 : term73 = term47.
Proof. exact (TRANS (@lem5380159) (@lem5380163)). Qed.
Lemma lem5380166 (m : nat) (n : nat) : (term94 m n) = (term95 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5380167 : term235 = term238.
Proof. exact (@lem5380166 term13 term215). Qed.
Lemma lem5380168 : term239 = term213.
Proof. exact (@lem996238 term213). Qed.
Lemma lem5380169 : (term239 = term213) = (term240 = term215).
Proof. exact (@lem1007663 (BIT1 0) term213 term213). Qed.
Lemma lem5380170 : term240 = term215.
Proof. exact (EQ_MP (@lem5380169) (@lem5380168)). Qed.
Lemma lem5380171 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5380172 : term241 = term205.
Proof. exact (MK_COMB (@lem5380171) (@lem5380170)). Qed.
Lemma lem5380173 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5380174 : term238 = term242.
Proof. exact (MK_COMB (@lem5380173) (@lem5380172)). Qed.
Lemma lem5380175 : term235 = term242.
Proof. exact (TRANS (@lem5380167) (@lem5380174)). Qed.
Lemma lem5380176 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5380177 : term243 = term244.
Proof. exact (MK_COMB (@lem5380176) (@lem5380175)). Qed.
Lemma lem5380178 : term237 = term245.
Proof. exact (MK_COMB (@lem5380177) (@lem5380164)). Qed.
Lemma lem5380179 : term236 = term245.
Proof. exact (TRANS (@lem5380156) (@lem5380178)). Qed.
Lemma lem5380180 : term235 = term245.
Proof. exact (TRANS (@lem5380155) (@lem5380179)). Qed.
Lemma lem5380182 (x : real) : (term80 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5380183 : term245 = term242.
Proof. exact (@lem5380182 term242). Qed.
Lemma lem5380184 : term235 = term242.
Proof. exact (TRANS (@lem5380180) (@lem5380183)). Qed.
Lemma lem5380187 (_69788 : int) : (term99 _69788) = (term99 _69788).
Proof. exact (eq_refl (term99 _69788)). Qed.
Lemma lem5380188 (_69788 : int) : (term234 _69788) = (term246 _69788).
Proof. exact (MK_COMB (@lem5380187 _69788) (@lem5380184)). Qed.
Lemma lem5380189 (_69788 : int) : (term233 _69788) = (term246 _69788).
Proof. exact (TRANS (@lem5380146 _69788) (@lem5380188 _69788)). Qed.
Lemma lem5380192 (_69787 : int) : (term99 _69787) = (term99 _69787).
Proof. exact (eq_refl (term99 _69787)). Qed.
Lemma lem5380193 (_69787 : int) (_69788 : int) : (term232 _69787 _69788) = (term247 _69787 _69788).
Proof. exact (MK_COMB (@lem5380192 _69787) (@lem5380189 _69788)). Qed.
Lemma lem5380194 (_69787 : int) (_69788 : int) : (term231 _69787 _69788) = (term247 _69787 _69788).
Proof. exact (TRANS (@lem5380145 _69787 _69788) (@lem5380193 _69787 _69788)). Qed.
Lemma lem5380195 (_69788 : int) : (term48 _69788) = (term48 _69788).
Proof. exact (eq_refl (term48 _69788)). Qed.
Lemma lem5380196 (_69787 : int) (_69788 : int) : (term230 _69787 _69788) = (term248 _69787 _69788).
Proof. exact (MK_COMB (@lem5380195 _69788) (@lem5380194 _69787 _69788)). Qed.
Lemma lem5380197 (_69787 : int) (_69788 : int) : (term248 _69787 _69788) = (term249 _69787 _69788).
Proof. exact (@lem1982757 (term103 _69787) (real_of_int _69788) (term246 _69788)). Qed.
Lemma lem5380198 (_69788 : int) : (term250 _69788) = (term251 _69788).
Proof. exact (@lem1982763 (real_of_int _69788) (term103 _69788) term242). Qed.
Lemma lem5380199 (_69788 : int) : (term104 _69788) = (term105 _69788).
Proof. exact (@lem1982715 term64 (real_of_int _69788)). Qed.
Lemma lem5380201 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5380202 : term47 = term90.
Proof. exact (@lem5380201 term13). Qed.
Lemma lem5380204 (x : nat) : (term62 x) = (term63 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5380205 : term64 = term65.
Proof. exact (@lem5380204 term13). Qed.
Lemma lem5380206 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5380207 : term106 = term107.
Proof. exact (MK_COMB (@lem5380206) (@lem5380205)). Qed.
Lemma lem5380208 : term108 = term109.
Proof. exact (MK_COMB (@lem5380207) (@lem5380202)). Qed.
Lemma lem5380209 : term110.
Proof. exact (@lem1981473 term64 term47 term47 term47 term35 term47). Qed.
Lemma lem5380211 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5380212 : term112 = term113.
Proof. exact (@lem5380211 (NUMERAL 0) term13). Qed.
Lemma lem5380213 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5380214 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5380215 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem5380214 h1) (fun h1 : term113 = True => @lem5380213)). Qed.
Lemma lem5380216 : term113 = True.
Proof. exact (EQ_MP (@lem5380215) (@lem5380213)). Qed.
Lemma lem5380217 : term112 = True.
Proof. exact (TRANS (@lem5380212) (@lem5380216)). Qed.
Lemma lem5380218 : True = term112.
Proof. exact (SYM (@lem5380217)). Qed.
Lemma lem5380219 : term112.
Proof. exact (EQ_MP (@lem5380218) (@lem0)). Qed.
Lemma lem5380220 : term115.
Proof. exact (@lem5380209 (@lem5380219)). Qed.
Lemma lem5380222 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5380223 : term112 = term113.
Proof. exact (@lem5380222 (NUMERAL 0) term13). Qed.
Lemma lem5380224 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5380225 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5380226 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem5380225 h1) (fun h1 : term113 = True => @lem5380224)). Qed.
Lemma lem5380227 : term113 = True.
Proof. exact (EQ_MP (@lem5380226) (@lem5380224)). Qed.
Lemma lem5380228 : term112 = True.
Proof. exact (TRANS (@lem5380223) (@lem5380227)). Qed.
Lemma lem5380229 : True = term112.
Proof. exact (SYM (@lem5380228)). Qed.
Lemma lem5380230 : term112.
Proof. exact (EQ_MP (@lem5380229) (@lem0)). Qed.
Lemma lem5380231 : term116.
Proof. exact (@lem5380220 (@lem5380230)). Qed.
Lemma lem5380233 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5380234 : term112 = term113.
Proof. exact (@lem5380233 (NUMERAL 0) term13). Qed.
Lemma lem5380235 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5380236 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5380237 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem5380236 h1) (fun h1 : term113 = True => @lem5380235)). Qed.
Lemma lem5380238 : term113 = True.
Proof. exact (EQ_MP (@lem5380237) (@lem5380235)). Qed.
Lemma lem5380239 : term112 = True.
Proof. exact (TRANS (@lem5380234) (@lem5380238)). Qed.
Lemma lem5380240 : True = term112.
Proof. exact (SYM (@lem5380239)). Qed.
Lemma lem5380241 : term112.
Proof. exact (EQ_MP (@lem5380240) (@lem0)). Qed.
Lemma lem5380242 : term117.
Proof. exact (@lem5380231 (@lem5380241)). Qed.
Lemma lem5380244 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5380245 : term73 = term74.
Proof. exact (@lem5380244 term13 term13). Qed.
Lemma lem5380246 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5380247 : term76 = term13.
Proof. exact (EQ_MP (@lem5380246) (@lem940073)). Qed.
Lemma lem5380248 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5380249 : term74 = term47.
Proof. exact (MK_COMB (@lem5380248) (@lem5380247)). Qed.
Lemma lem5380250 : term73 = term47.
Proof. exact (TRANS (@lem5380245) (@lem5380249)). Qed.
Lemma lem5380252 (m : nat) (n : nat) : (term94 m n) = (term95 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5380253 : term91 = term96.
Proof. exact (@lem5380252 term13 term13). Qed.
Lemma lem5380254 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5380255 : term76 = term13.
Proof. exact (EQ_MP (@lem5380254) (@lem940073)). Qed.
Lemma lem5380256 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5380257 : term74 = term47.
Proof. exact (MK_COMB (@lem5380256) (@lem5380255)). Qed.
Lemma lem5380258 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5380259 : term96 = term64.
Proof. exact (MK_COMB (@lem5380258) (@lem5380257)). Qed.
Lemma lem5380260 : term91 = term64.
Proof. exact (TRANS (@lem5380253) (@lem5380259)). Qed.
Lemma lem5380261 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5380262 : term118 = term106.
Proof. exact (MK_COMB (@lem5380261) (@lem5380260)). Qed.
Lemma lem5380263 : term119 = term108.
Proof. exact (MK_COMB (@lem5380262) (@lem5380250)). Qed.
Lemma lem5380265 (m : nat) : (term120 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5380266 : term108 = term35.
Proof. exact (@lem5380265 term13). Qed.
Lemma lem5380267 : term119 = term35.
Proof. exact (TRANS (@lem5380263) (@lem5380266)). Qed.
Lemma lem5380268 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5380269 : term121 = term122.
Proof. exact (MK_COMB (@lem5380268) (@lem5380267)). Qed.
Lemma lem5380270 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem5380271 : term123 = term124.
Proof. exact (MK_COMB (@lem5380269) (@lem5380270)). Qed.
Lemma lem5380273 (x : nat) : (term125 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5380274 : term124 = term35.
Proof. exact (@lem5380273 term13). Qed.
Lemma lem5380275 : term123 = term35.
Proof. exact (TRANS (@lem5380271) (@lem5380274)). Qed.
Lemma lem5380277 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5380278 : term73 = term74.
Proof. exact (@lem5380277 term13 term13). Qed.
Lemma lem5380279 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5380280 : term76 = term13.
Proof. exact (EQ_MP (@lem5380279) (@lem940073)). Qed.
Lemma lem5380281 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5380282 : term74 = term47.
Proof. exact (MK_COMB (@lem5380281) (@lem5380280)). Qed.
Lemma lem5380283 : term73 = term47.
Proof. exact (TRANS (@lem5380278) (@lem5380282)). Qed.
Lemma lem5380284 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem5380285 : term126 = term124.
Proof. exact (MK_COMB (@lem5380284) (@lem5380283)). Qed.
Lemma lem5380287 (x : nat) : (term125 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5380288 : term124 = term35.
Proof. exact (@lem5380287 term13). Qed.
Lemma lem5380289 : term126 = term35.
Proof. exact (TRANS (@lem5380285) (@lem5380288)). Qed.
Lemma lem5380290 : term35 = term126.
Proof. exact (SYM (@lem5380289)). Qed.
Lemma lem5380291 : term123 = term126.
Proof. exact (TRANS (@lem5380275) (@lem5380290)). Qed.
Lemma lem5380292 : term109 = term61.
Proof. exact (@lem5380242 (@lem5380291)). Qed.
Lemma lem5380293 : term108 = term61.
Proof. exact (TRANS (@lem5380208) (@lem5380292)). Qed.
Lemma lem5380295 (x : real) : (term80 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5380296 : term61 = term35.
Proof. exact (@lem5380295 term35). Qed.
Lemma lem5380297 : term108 = term35.
Proof. exact (TRANS (@lem5380293) (@lem5380296)). Qed.
Lemma lem5380298 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5380299 : term127 = term122.
Proof. exact (MK_COMB (@lem5380298) (@lem5380297)). Qed.
Lemma lem5380300 (_69788 : int) : (real_of_int _69788) = (real_of_int _69788).
Proof. exact (eq_refl (real_of_int _69788)). Qed.
Lemma lem5380301 (_69788 : int) : (term105 _69788) = (term128 _69788).
Proof. exact (MK_COMB (@lem5380299) (@lem5380300 _69788)). Qed.
Lemma lem5380302 (_69788 : int) : (term104 _69788) = (term128 _69788).
Proof. exact (TRANS (@lem5380199 _69788) (@lem5380301 _69788)). Qed.
Lemma lem5380303 (_69788 : int) : (term128 _69788) = term35.
Proof. exact (@lem1982719 (real_of_int _69788)). Qed.
Lemma lem5380304 (_69788 : int) : (term104 _69788) = term35.
Proof. exact (TRANS (@lem5380302 _69788) (@lem5380303 _69788)). Qed.
Lemma lem5380305 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5380306 (_69788 : int) : (term129 _69788) = term130.
Proof. exact (MK_COMB (@lem5380305) (@lem5380304 _69788)). Qed.
Lemma lem5380307 : term242 = term242.
Proof. exact (eq_refl term242). Qed.
Lemma lem5380308 (_69788 : int) : (term251 _69788) = term252.
Proof. exact (MK_COMB (@lem5380306 _69788) (@lem5380307)). Qed.
Lemma lem5380309 (_69788 : int) : (term250 _69788) = term252.
Proof. exact (TRANS (@lem5380198 _69788) (@lem5380308 _69788)). Qed.
Lemma lem5380310 : term252 = term242.
Proof. exact (@lem1982721 term242). Qed.
Lemma lem5380311 (_69788 : int) : (term250 _69788) = term242.
Proof. exact (TRANS (@lem5380309 _69788) (@lem5380310)). Qed.
Lemma lem5380312 (_69787 : int) : (term99 _69787) = (term99 _69787).
Proof. exact (eq_refl (term99 _69787)). Qed.
Lemma lem5380313 (_69788 : int) (_69787 : int) : (term249 _69787 _69788) = (term246 _69787).
Proof. exact (MK_COMB (@lem5380312 _69787) (@lem5380311 _69788)). Qed.
Lemma lem5380314 (_69788 : int) (_69787 : int) : (term248 _69787 _69788) = (term246 _69787).
Proof. exact (TRANS (@lem5380197 _69787 _69788) (@lem5380313 _69788 _69787)). Qed.
Lemma lem5380315 (_69788 : int) (_69787 : int) : (term230 _69787 _69788) = (term246 _69787).
Proof. exact (TRANS (@lem5380196 _69787 _69788) (@lem5380314 _69788 _69787)). Qed.
Lemma lem5380316 (_69788 : int) (_69787 : int) : (term229 _69787 _69788) = (term246 _69787).
Proof. exact (TRANS (@lem5380144 _69787 _69788) (@lem5380315 _69788 _69787)). Qed.
Lemma lem5380317 (_69788 : int) (_69787 : int) : (term228 _69787 _69788) = (term246 _69787).
Proof. exact (TRANS (@lem5380143 _69787 _69788) (@lem5380316 _69788 _69787)). Qed.
Lemma lem5380318 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5380319 (_69788 : int) (_69787 : int) : (term253 _69787 _69788) = (term254 _69787).
Proof. exact (MK_COMB (@lem5380318) (@lem5380317 _69788 _69787)). Qed.
Lemma lem5380320 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem5380321 (_69788 : int) (_69787 : int) : (term196 _69787 _69788) = (term255 _69787).
Proof. exact (MK_COMB (@lem5380319 _69788 _69787) (@lem5380320)). Qed.
Lemma lem5380322 (_69788 : int) (_69787 : int) : (term192 _69787 _69788) = (term255 _69787).
Proof. exact (TRANS (@lem5380001 _69787 _69788) (@lem5380321 _69788 _69787)). Qed.
Lemma lem5380323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5380324 (_69788 : int) : (term53 _69788) = (term135 _69788).
Proof. exact (MK_COMB (@lem5380323) (@lem5380000 _69788)). Qed.
Lemma lem5380325 (_69788 : int) (_69787 : int) : (term193 _69787 _69788) = (term256 _69788 _69787).
Proof. exact (MK_COMB (@lem5380324 _69788) (@lem5380322 _69788 _69787)). Qed.
Lemma lem5380326 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5380327 (_69787 : int) : (term53 _69787) = (term135 _69787).
Proof. exact (MK_COMB (@lem5380326) (@lem5379952 _69787)). Qed.
Lemma lem5380328 (_69788 : int) (_69787 : int) : (term194 _69787 _69788) = (term257 _69788 _69787).
Proof. exact (MK_COMB (@lem5380327 _69787) (@lem5380325 _69788 _69787)). Qed.
Lemma lem5380349 (_69788 : int) (_69787 : int) : (term195 _69787 _69788) = (term257 _69788 _69787).
Proof. exact (TRANS (@lem5379904 _69787 _69788) (@lem5380328 _69788 _69787)). Qed.
Lemma lem5380353 (_69788 : int) (_69787 : int) (h1 : term257 _69788 _69787) : term257 _69788 _69787.
Proof. exact (h1). Qed.
Lemma lem5380354 (_69788 : int) (_69787 : int) (h1 : term257 _69788 _69787) : term256 _69788 _69787.
Proof. exact (proj2 (@lem5380353 _69788 _69787 h1)). Qed.
Lemma lem5380355 (_69788 : int) (_69787 : int) (h1 : term257 _69788 _69787) : term84 _69787.
Proof. exact (proj1 (@lem5380353 _69788 _69787 h1)). Qed.
Lemma lem5380356 (_69788 : int) (_69787 : int) (h1 : term257 _69788 _69787) : term255 _69787.
Proof. exact (proj2 (@lem5380354 _69788 _69787 h1)). Qed.
Lemma lem5380359 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5380360 : term258 = term112.
Proof. exact (@lem5380359 term35 term47). Qed.
Lemma lem5380362 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5380363 : term47 = term90.
Proof. exact (@lem5380362 term13). Qed.
Lemma lem5380365 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5380366 : term35 = term61.
Proof. exact (@lem5380365 (NUMERAL 0)). Qed.
Lemma lem5380367 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5380368 : term259 = term260.
Proof. exact (MK_COMB (@lem5380367) (@lem5380366)). Qed.
Lemma lem5380369 : term112 = term261.
Proof. exact (MK_COMB (@lem5380368) (@lem5380363)). Qed.
Lemma lem5380370 : term262.
Proof. exact (@lem1980255 term35 term47 term47 term47). Qed.
Lemma lem5380372 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5380373 : term112 = term113.
Proof. exact (@lem5380372 (NUMERAL 0) term13). Qed.
Lemma lem5380374 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5380375 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5380376 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem5380375 h1) (fun h1 : term113 = True => @lem5380374)). Qed.
Lemma lem5380377 : term113 = True.
Proof. exact (EQ_MP (@lem5380376) (@lem5380374)). Qed.
Lemma lem5380378 : term112 = True.
Proof. exact (TRANS (@lem5380373) (@lem5380377)). Qed.
Lemma lem5380379 : True = term112.
Proof. exact (SYM (@lem5380378)). Qed.
Lemma lem5380380 : term112.
Proof. exact (EQ_MP (@lem5380379) (@lem0)). Qed.
Lemma lem5380381 : term263.
Proof. exact (@lem5380370 (@lem5380380)). Qed.
Lemma lem5380383 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5380384 : term112 = term113.
Proof. exact (@lem5380383 (NUMERAL 0) term13). Qed.
Lemma lem5380385 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5380386 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5380387 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem5380386 h1) (fun h1 : term113 = True => @lem5380385)). Qed.
Lemma lem5380388 : term113 = True.
Proof. exact (EQ_MP (@lem5380387) (@lem5380385)). Qed.
Lemma lem5380389 : term112 = True.
Proof. exact (TRANS (@lem5380384) (@lem5380388)). Qed.
Lemma lem5380390 : True = term112.
Proof. exact (SYM (@lem5380389)). Qed.
Lemma lem5380391 : term112.
Proof. exact (EQ_MP (@lem5380390) (@lem0)). Qed.
Lemma lem5380392 : term261 = term264.
Proof. exact (@lem5380381 (@lem5380391)). Qed.
Lemma lem5380394 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5380395 : term73 = term74.
Proof. exact (@lem5380394 term13 term13). Qed.
Lemma lem5380396 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5380397 : term76 = term13.
Proof. exact (EQ_MP (@lem5380396) (@lem940073)). Qed.
Lemma lem5380398 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5380399 : term74 = term47.
Proof. exact (MK_COMB (@lem5380398) (@lem5380397)). Qed.
Lemma lem5380400 : term73 = term47.
Proof. exact (TRANS (@lem5380395) (@lem5380399)). Qed.
Lemma lem5380402 (x : nat) : (term125 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5380403 : term124 = term35.
Proof. exact (@lem5380402 term13). Qed.
Lemma lem5380404 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5380405 : term265 = term259.
Proof. exact (MK_COMB (@lem5380404) (@lem5380403)). Qed.
Lemma lem5380406 : term264 = term112.
Proof. exact (MK_COMB (@lem5380405) (@lem5380400)). Qed.
Lemma lem5380408 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5380409 : term112 = term113.
Proof. exact (@lem5380408 (NUMERAL 0) term13). Qed.
Lemma lem5380410 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5380411 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5380412 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem5380411 h1) (fun h1 : term113 = True => @lem5380410)). Qed.
Lemma lem5380413 : term113 = True.
Proof. exact (EQ_MP (@lem5380412) (@lem5380410)). Qed.
Lemma lem5380414 : term112 = True.
Proof. exact (TRANS (@lem5380409) (@lem5380413)). Qed.
Lemma lem5380415 : term264 = True.
Proof. exact (TRANS (@lem5380406) (@lem5380414)). Qed.
Lemma lem5380416 : term261 = True.
Proof. exact (TRANS (@lem5380392) (@lem5380415)). Qed.
Lemma lem5380417 : term112 = True.
Proof. exact (TRANS (@lem5380369) (@lem5380416)). Qed.
Lemma lem5380418 : term258 = True.
Proof. exact (TRANS (@lem5380360) (@lem5380417)). Qed.
Lemma lem5380419 : True = term258.
Proof. exact (SYM (@lem5380418)). Qed.
Lemma lem5380420 : term258.
Proof. exact (EQ_MP (@lem5380419) (@lem0)). Qed.
Lemma lem5380421 (_69788 : int) (_69787 : int) (h1 : term257 _69788 _69787) : term266 _69787.
Proof. exact (conj (@lem5380420) (@lem5380355 _69788 _69787 h1)). Qed.
Lemma lem5380423 (x : real) (y : real) : term267 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5380424 (_69787 : int) : term268 _69787.
Proof. exact (@lem5380423 term47 (real_of_int _69787)). Qed.
Lemma lem5380425 (_69788 : int) (_69787 : int) (h1 : term257 _69788 _69787) : term269 _69787.
Proof. exact (@lem5380424 _69787 (@lem5380421 _69788 _69787 h1)). Qed.
Lemma lem5380426 (_69787 : int) : (term270 _69787) = (real_of_int _69787).
Proof. exact (@lem1982733 (real_of_int _69787)). Qed.
Lemma lem5380427 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5380428 (_69787 : int) : (term271 _69787) = (term83 _69787).
Proof. exact (MK_COMB (@lem5380427) (@lem5380426 _69787)). Qed.
Lemma lem5380429 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem5380430 (_69787 : int) : (term269 _69787) = (term84 _69787).
Proof. exact (MK_COMB (@lem5380428 _69787) (@lem5380429)). Qed.
Lemma lem5380431 (_69788 : int) (_69787 : int) (h1 : term257 _69788 _69787) : term84 _69787.
Proof. exact (EQ_MP (@lem5380430 _69787) (@lem5380425 _69788 _69787 h1)). Qed.
Lemma lem5380433 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5380434 : term258 = term112.
Proof. exact (@lem5380433 term35 term47). Qed.
Lemma lem5380436 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5380437 : term47 = term90.
Proof. exact (@lem5380436 term13). Qed.
Lemma lem5380439 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5380440 : term35 = term61.
Proof. exact (@lem5380439 (NUMERAL 0)). Qed.
Lemma lem5380441 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5380442 : term259 = term260.
Proof. exact (MK_COMB (@lem5380441) (@lem5380440)). Qed.
Lemma lem5380443 : term112 = term261.
Proof. exact (MK_COMB (@lem5380442) (@lem5380437)). Qed.
Lemma lem5380444 : term262.
Proof. exact (@lem1980255 term35 term47 term47 term47). Qed.
Lemma lem5380446 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5380447 : term112 = term113.
Proof. exact (@lem5380446 (NUMERAL 0) term13). Qed.
Lemma lem5380448 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5380449 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5380450 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem5380449 h1) (fun h1 : term113 = True => @lem5380448)). Qed.
Lemma lem5380451 : term113 = True.
Proof. exact (EQ_MP (@lem5380450) (@lem5380448)). Qed.
Lemma lem5380452 : term112 = True.
Proof. exact (TRANS (@lem5380447) (@lem5380451)). Qed.
Lemma lem5380453 : True = term112.
Proof. exact (SYM (@lem5380452)). Qed.
Lemma lem5380454 : term112.
Proof. exact (EQ_MP (@lem5380453) (@lem0)). Qed.
Lemma lem5380455 : term263.
Proof. exact (@lem5380444 (@lem5380454)). Qed.
Lemma lem5380457 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5380458 : term112 = term113.
Proof. exact (@lem5380457 (NUMERAL 0) term13). Qed.
Lemma lem5380459 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5380460 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5380461 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem5380460 h1) (fun h1 : term113 = True => @lem5380459)). Qed.
Lemma lem5380462 : term113 = True.
Proof. exact (EQ_MP (@lem5380461) (@lem5380459)). Qed.
Lemma lem5380463 : term112 = True.
Proof. exact (TRANS (@lem5380458) (@lem5380462)). Qed.
Lemma lem5380464 : True = term112.
Proof. exact (SYM (@lem5380463)). Qed.
Lemma lem5380465 : term112.
Proof. exact (EQ_MP (@lem5380464) (@lem0)). Qed.
Lemma lem5380466 : term261 = term264.
Proof. exact (@lem5380455 (@lem5380465)). Qed.
Lemma lem5380468 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5380469 : term73 = term74.
Proof. exact (@lem5380468 term13 term13). Qed.
Lemma lem5380470 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5380471 : term76 = term13.
Proof. exact (EQ_MP (@lem5380470) (@lem940073)). Qed.
Lemma lem5380472 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5380473 : term74 = term47.
Proof. exact (MK_COMB (@lem5380472) (@lem5380471)). Qed.
Lemma lem5380474 : term73 = term47.
Proof. exact (TRANS (@lem5380469) (@lem5380473)). Qed.
Lemma lem5380476 (x : nat) : (term125 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5380477 : term124 = term35.
Proof. exact (@lem5380476 term13). Qed.
Lemma lem5380478 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5380479 : term265 = term259.
Proof. exact (MK_COMB (@lem5380478) (@lem5380477)). Qed.
Lemma lem5380480 : term264 = term112.
Proof. exact (MK_COMB (@lem5380479) (@lem5380474)). Qed.
Lemma lem5380482 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5380483 : term112 = term113.
Proof. exact (@lem5380482 (NUMERAL 0) term13). Qed.
Lemma lem5380484 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5380485 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5380486 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem5380485 h1) (fun h1 : term113 = True => @lem5380484)). Qed.
Lemma lem5380487 : term113 = True.
Proof. exact (EQ_MP (@lem5380486) (@lem5380484)). Qed.
Lemma lem5380488 : term112 = True.
Proof. exact (TRANS (@lem5380483) (@lem5380487)). Qed.
Lemma lem5380489 : term264 = True.
Proof. exact (TRANS (@lem5380480) (@lem5380488)). Qed.
Lemma lem5380490 : term261 = True.
Proof. exact (TRANS (@lem5380466) (@lem5380489)). Qed.
Lemma lem5380491 : term112 = True.
Proof. exact (TRANS (@lem5380443) (@lem5380490)). Qed.
Lemma lem5380492 : term258 = True.
Proof. exact (TRANS (@lem5380434) (@lem5380491)). Qed.
Lemma lem5380493 : True = term258.
Proof. exact (SYM (@lem5380492)). Qed.
Lemma lem5380494 : term258.
Proof. exact (EQ_MP (@lem5380493) (@lem0)). Qed.
Lemma lem5380495 (_69788 : int) (_69787 : int) (h1 : term257 _69788 _69787) : term272 _69787.
Proof. exact (conj (@lem5380494) (@lem5380356 _69788 _69787 h1)). Qed.
Lemma lem5380497 (x : real) (y : real) : term267 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5380498 (_69787 : int) : term273 _69787.
Proof. exact (@lem5380497 term47 (term246 _69787)). Qed.
Lemma lem5380499 (_69788 : int) (_69787 : int) (h1 : term257 _69788 _69787) : term274 _69787.
Proof. exact (@lem5380498 _69787 (@lem5380495 _69788 _69787 h1)). Qed.
Lemma lem5380500 (_69787 : int) : (term275 _69787) = (term246 _69787).
Proof. exact (@lem1982733 (term246 _69787)). Qed.
Lemma lem5380501 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5380502 (_69787 : int) : (term276 _69787) = (term254 _69787).
Proof. exact (MK_COMB (@lem5380501) (@lem5380500 _69787)). Qed.
Lemma lem5380503 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem5380504 (_69787 : int) : (term274 _69787) = (term255 _69787).
Proof. exact (MK_COMB (@lem5380502 _69787) (@lem5380503)). Qed.
Lemma lem5380505 (_69788 : int) (_69787 : int) (h1 : term257 _69788 _69787) : term255 _69787.
Proof. exact (EQ_MP (@lem5380504 _69787) (@lem5380499 _69788 _69787 h1)). Qed.
Lemma lem5380506 (_69788 : int) (_69787 : int) (h1 : term257 _69788 _69787) : term277 _69787.
Proof. exact (conj (@lem5380505 _69788 _69787 h1) (@lem5380431 _69788 _69787 h1)). Qed.
Lemma lem5380508 (x : real) (y : real) : term278 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5380509 (_69787 : int) : term279 _69787.
Proof. exact (@lem5380508 (term246 _69787) (real_of_int _69787)). Qed.
Lemma lem5380510 (_69788 : int) (_69787 : int) (h1 : term257 _69788 _69787) : term280 _69787.
Proof. exact (@lem5380509 _69787 (@lem5380506 _69788 _69787 h1)). Qed.
Lemma lem5380511 (_69787 : int) : (term281 _69787) = (term282 _69787).
Proof. exact (@lem1982759 (term103 _69787) (real_of_int _69787) term242). Qed.
Lemma lem5380512 (_69787 : int) : (term283 _69787) = (term105 _69787).
Proof. exact (@lem1982713 term64 (real_of_int _69787)). Qed.
Lemma lem5380514 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5380515 : term47 = term90.
Proof. exact (@lem5380514 term13). Qed.
Lemma lem5380517 (x : nat) : (term62 x) = (term63 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5380518 : term64 = term65.
Proof. exact (@lem5380517 term13). Qed.
Lemma lem5380519 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5380520 : term106 = term107.
Proof. exact (MK_COMB (@lem5380519) (@lem5380518)). Qed.
Lemma lem5380521 : term108 = term109.
Proof. exact (MK_COMB (@lem5380520) (@lem5380515)). Qed.
Lemma lem5380522 : term110.
Proof. exact (@lem1981473 term64 term47 term47 term47 term35 term47). Qed.
Lemma lem5380524 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5380525 : term112 = term113.
Proof. exact (@lem5380524 (NUMERAL 0) term13). Qed.
Lemma lem5380526 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5380527 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5380528 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem5380527 h1) (fun h1 : term113 = True => @lem5380526)). Qed.
Lemma lem5380529 : term113 = True.
Proof. exact (EQ_MP (@lem5380528) (@lem5380526)). Qed.
Lemma lem5380530 : term112 = True.
Proof. exact (TRANS (@lem5380525) (@lem5380529)). Qed.
Lemma lem5380531 : True = term112.
Proof. exact (SYM (@lem5380530)). Qed.
Lemma lem5380532 : term112.
Proof. exact (EQ_MP (@lem5380531) (@lem0)). Qed.
Lemma lem5380533 : term115.
Proof. exact (@lem5380522 (@lem5380532)). Qed.
Lemma lem5380535 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5380536 : term112 = term113.
Proof. exact (@lem5380535 (NUMERAL 0) term13). Qed.
Lemma lem5380537 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5380538 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5380539 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem5380538 h1) (fun h1 : term113 = True => @lem5380537)). Qed.
Lemma lem5380540 : term113 = True.
Proof. exact (EQ_MP (@lem5380539) (@lem5380537)). Qed.
Lemma lem5380541 : term112 = True.
Proof. exact (TRANS (@lem5380536) (@lem5380540)). Qed.
Lemma lem5380542 : True = term112.
Proof. exact (SYM (@lem5380541)). Qed.
Lemma lem5380543 : term112.
Proof. exact (EQ_MP (@lem5380542) (@lem0)). Qed.
Lemma lem5380544 : term116.
Proof. exact (@lem5380533 (@lem5380543)). Qed.
Lemma lem5380546 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5380547 : term112 = term113.
Proof. exact (@lem5380546 (NUMERAL 0) term13). Qed.
Lemma lem5380548 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5380549 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5380550 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem5380549 h1) (fun h1 : term113 = True => @lem5380548)). Qed.
Lemma lem5380551 : term113 = True.
Proof. exact (EQ_MP (@lem5380550) (@lem5380548)). Qed.
Lemma lem5380552 : term112 = True.
Proof. exact (TRANS (@lem5380547) (@lem5380551)). Qed.
Lemma lem5380553 : True = term112.
Proof. exact (SYM (@lem5380552)). Qed.
Lemma lem5380554 : term112.
Proof. exact (EQ_MP (@lem5380553) (@lem0)). Qed.
Lemma lem5380555 : term117.
Proof. exact (@lem5380544 (@lem5380554)). Qed.
Lemma lem5380557 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5380558 : term73 = term74.
Proof. exact (@lem5380557 term13 term13). Qed.
Lemma lem5380559 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5380560 : term76 = term13.
Proof. exact (EQ_MP (@lem5380559) (@lem940073)). Qed.
Lemma lem5380561 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5380562 : term74 = term47.
Proof. exact (MK_COMB (@lem5380561) (@lem5380560)). Qed.
Lemma lem5380563 : term73 = term47.
Proof. exact (TRANS (@lem5380558) (@lem5380562)). Qed.
Lemma lem5380565 (m : nat) (n : nat) : (term94 m n) = (term95 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5380566 : term91 = term96.
Proof. exact (@lem5380565 term13 term13). Qed.
Lemma lem5380567 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5380568 : term76 = term13.
Proof. exact (EQ_MP (@lem5380567) (@lem940073)). Qed.
Lemma lem5380569 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5380570 : term74 = term47.
Proof. exact (MK_COMB (@lem5380569) (@lem5380568)). Qed.
Lemma lem5380571 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5380572 : term96 = term64.
Proof. exact (MK_COMB (@lem5380571) (@lem5380570)). Qed.
Lemma lem5380573 : term91 = term64.
Proof. exact (TRANS (@lem5380566) (@lem5380572)). Qed.
Lemma lem5380574 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5380575 : term118 = term106.
Proof. exact (MK_COMB (@lem5380574) (@lem5380573)). Qed.
Lemma lem5380576 : term119 = term108.
Proof. exact (MK_COMB (@lem5380575) (@lem5380563)). Qed.
Lemma lem5380578 (m : nat) : (term120 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5380579 : term108 = term35.
Proof. exact (@lem5380578 term13). Qed.
Lemma lem5380580 : term119 = term35.
Proof. exact (TRANS (@lem5380576) (@lem5380579)). Qed.
Lemma lem5380581 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5380582 : term121 = term122.
Proof. exact (MK_COMB (@lem5380581) (@lem5380580)). Qed.
Lemma lem5380583 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem5380584 : term123 = term124.
Proof. exact (MK_COMB (@lem5380582) (@lem5380583)). Qed.
Lemma lem5380586 (x : nat) : (term125 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5380587 : term124 = term35.
Proof. exact (@lem5380586 term13). Qed.
Lemma lem5380588 : term123 = term35.
Proof. exact (TRANS (@lem5380584) (@lem5380587)). Qed.
Lemma lem5380590 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5380591 : term73 = term74.
Proof. exact (@lem5380590 term13 term13). Qed.
Lemma lem5380592 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5380593 : term76 = term13.
Proof. exact (EQ_MP (@lem5380592) (@lem940073)). Qed.
Lemma lem5380594 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5380595 : term74 = term47.
Proof. exact (MK_COMB (@lem5380594) (@lem5380593)). Qed.
Lemma lem5380596 : term73 = term47.
Proof. exact (TRANS (@lem5380591) (@lem5380595)). Qed.
Lemma lem5380597 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem5380598 : term126 = term124.
Proof. exact (MK_COMB (@lem5380597) (@lem5380596)). Qed.
Lemma lem5380600 (x : nat) : (term125 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5380601 : term124 = term35.
Proof. exact (@lem5380600 term13). Qed.
Lemma lem5380602 : term126 = term35.
Proof. exact (TRANS (@lem5380598) (@lem5380601)). Qed.
Lemma lem5380603 : term35 = term126.
Proof. exact (SYM (@lem5380602)). Qed.
Lemma lem5380604 : term123 = term126.
Proof. exact (TRANS (@lem5380588) (@lem5380603)). Qed.
Lemma lem5380605 : term109 = term61.
Proof. exact (@lem5380555 (@lem5380604)). Qed.
Lemma lem5380606 : term108 = term61.
Proof. exact (TRANS (@lem5380521) (@lem5380605)). Qed.
Lemma lem5380608 (x : real) : (term80 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5380609 : term61 = term35.
Proof. exact (@lem5380608 term35). Qed.
Lemma lem5380610 : term108 = term35.
Proof. exact (TRANS (@lem5380606) (@lem5380609)). Qed.
Lemma lem5380611 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5380612 : term127 = term122.
Proof. exact (MK_COMB (@lem5380611) (@lem5380610)). Qed.
Lemma lem5380613 (_69787 : int) : (real_of_int _69787) = (real_of_int _69787).
Proof. exact (eq_refl (real_of_int _69787)). Qed.
Lemma lem5380614 (_69787 : int) : (term105 _69787) = (term128 _69787).
Proof. exact (MK_COMB (@lem5380612) (@lem5380613 _69787)). Qed.
Lemma lem5380615 (_69787 : int) : (term283 _69787) = (term128 _69787).
Proof. exact (TRANS (@lem5380512 _69787) (@lem5380614 _69787)). Qed.
Lemma lem5380616 (_69787 : int) : (term128 _69787) = term35.
Proof. exact (@lem1982719 (real_of_int _69787)). Qed.
Lemma lem5380617 (_69787 : int) : (term283 _69787) = term35.
Proof. exact (TRANS (@lem5380615 _69787) (@lem5380616 _69787)). Qed.
Lemma lem5380618 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5380619 (_69787 : int) : (term284 _69787) = term130.
Proof. exact (MK_COMB (@lem5380618) (@lem5380617 _69787)). Qed.
Lemma lem5380620 : term242 = term242.
Proof. exact (eq_refl term242). Qed.
Lemma lem5380621 (_69787 : int) : (term282 _69787) = term252.
Proof. exact (MK_COMB (@lem5380619 _69787) (@lem5380620)). Qed.
Lemma lem5380622 (_69787 : int) : (term281 _69787) = term252.
Proof. exact (TRANS (@lem5380511 _69787) (@lem5380621 _69787)). Qed.
Lemma lem5380623 : term252 = term242.
Proof. exact (@lem1982721 term242). Qed.
Lemma lem5380624 (_69787 : int) : (term281 _69787) = term242.
Proof. exact (TRANS (@lem5380622 _69787) (@lem5380623)). Qed.
Lemma lem5380625 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5380626 (_69787 : int) : (term285 _69787) = term286.
Proof. exact (MK_COMB (@lem5380625) (@lem5380624 _69787)). Qed.
Lemma lem5380627 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem5380628 (_69787 : int) : (term280 _69787) = term287.
Proof. exact (MK_COMB (@lem5380626 _69787) (@lem5380627)). Qed.
Lemma lem5380629 (_69788 : int) (_69787 : int) (h1 : term257 _69788 _69787) : term287.
Proof. exact (EQ_MP (@lem5380628 _69787) (@lem5380510 _69788 _69787 h1)). Qed.
Lemma lem5380631 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5380632 : term287 = term288.
Proof. exact (@lem5380631 term35 term242). Qed.
Lemma lem5380634 (x : nat) : (term62 x) = (term63 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5380635 : term242 = term245.
Proof. exact (@lem5380634 term215). Qed.
Lemma lem5380637 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5380638 : term35 = term61.
Proof. exact (@lem5380637 (NUMERAL 0)). Qed.
Lemma lem5380639 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5380640 : term37 = term138.
Proof. exact (MK_COMB (@lem5380639) (@lem5380638)). Qed.
Lemma lem5380641 : term288 = term289.
Proof. exact (MK_COMB (@lem5380640) (@lem5380635)). Qed.
Lemma lem5380642 : term290.
Proof. exact (@lem1980026 term35 term47 term242 term47). Qed.
Lemma lem5380644 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5380645 : term112 = term113.
Proof. exact (@lem5380644 (NUMERAL 0) term13). Qed.
Lemma lem5380646 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5380647 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5380648 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem5380647 h1) (fun h1 : term113 = True => @lem5380646)). Qed.
Lemma lem5380649 : term113 = True.
Proof. exact (EQ_MP (@lem5380648) (@lem5380646)). Qed.
Lemma lem5380650 : term112 = True.
Proof. exact (TRANS (@lem5380645) (@lem5380649)). Qed.
Lemma lem5380651 : True = term112.
Proof. exact (SYM (@lem5380650)). Qed.
Lemma lem5380652 : term112.
Proof. exact (EQ_MP (@lem5380651) (@lem0)). Qed.
Lemma lem5380653 : term291.
Proof. exact (@lem5380642 (@lem5380652)). Qed.
Lemma lem5380655 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5380656 : term112 = term113.
Proof. exact (@lem5380655 (NUMERAL 0) term13). Qed.
Lemma lem5380657 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5380658 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5380659 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem5380658 h1) (fun h1 : term113 = True => @lem5380657)). Qed.
Lemma lem5380660 : term113 = True.
Proof. exact (EQ_MP (@lem5380659) (@lem5380657)). Qed.
Lemma lem5380661 : term112 = True.
Proof. exact (TRANS (@lem5380656) (@lem5380660)). Qed.
Lemma lem5380662 : True = term112.
Proof. exact (SYM (@lem5380661)). Qed.
Lemma lem5380663 : term112.
Proof. exact (EQ_MP (@lem5380662) (@lem0)). Qed.
Lemma lem5380664 : term289 = term292.
Proof. exact (@lem5380653 (@lem5380663)). Qed.
Lemma lem5380666 (m : nat) (n : nat) : (term94 m n) = (term95 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5380667 : term293 = term294.
Proof. exact (@lem5380666 term215 term13). Qed.
Lemma lem5380668 : term221 = term213.
Proof. exact (@lem996237 term213). Qed.
Lemma lem5380669 : (term221 = term213) = (term222 = term215).
Proof. exact (@lem1007663 term213 (BIT1 0) term213). Qed.
Lemma lem5380670 : term222 = term215.
Proof. exact (EQ_MP (@lem5380669) (@lem5380668)). Qed.
Lemma lem5380671 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5380672 : term220 = term205.
Proof. exact (MK_COMB (@lem5380671) (@lem5380670)). Qed.
Lemma lem5380673 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5380674 : term294 = term242.
Proof. exact (MK_COMB (@lem5380673) (@lem5380672)). Qed.
Lemma lem5380675 : term293 = term242.
Proof. exact (TRANS (@lem5380667) (@lem5380674)). Qed.
Lemma lem5380677 (x : nat) : (term125 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5380678 : term124 = term35.
Proof. exact (@lem5380677 term13). Qed.
Lemma lem5380679 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5380680 : term143 = term37.
Proof. exact (MK_COMB (@lem5380679) (@lem5380678)). Qed.
Lemma lem5380681 : term292 = term288.
Proof. exact (MK_COMB (@lem5380680) (@lem5380675)). Qed.
Lemma lem5380683 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5380684 : term288 = term295.
Proof. exact (@lem5380683 (NUMERAL 0) term215). Qed.
Lemma lem5380685 : term296 = term213.
Proof. exact (@lem912803). Qed.
Lemma lem5380686 (h1 : term296 = term213) : (term215 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term213 h1). Qed.
Lemma lem5380687 : (term296 = term213) = ((term215 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term296 = term213 => @lem5380686 h1) (fun h1 : (term215 = (NUMERAL 0)) = False => @lem5380685)). Qed.
Lemma lem5380688 : (term215 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5380687) (@lem5380685)). Qed.
Lemma lem5380689 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5380690 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5380691 : term147 = (and True).
Proof. exact (MK_COMB (@lem5380690) (@lem5380689)). Qed.
Lemma lem5380692 : term295 = (True /\ False).
Proof. exact (MK_COMB (@lem5380691) (@lem5380688)). Qed.
Lemma lem5380694 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5380695 : term295 = False.
Proof. exact (TRANS (@lem5380692) (@lem5380694)). Qed.
Lemma lem5380696 : term288 = False.
Proof. exact (TRANS (@lem5380684) (@lem5380695)). Qed.
Lemma lem5380697 : term292 = False.
Proof. exact (TRANS (@lem5380681) (@lem5380696)). Qed.
Lemma lem5380698 : term289 = False.
Proof. exact (TRANS (@lem5380664) (@lem5380697)). Qed.
Lemma lem5380699 : term288 = False.
Proof. exact (TRANS (@lem5380641) (@lem5380698)). Qed.
Lemma lem5380700 : term287 = False.
Proof. exact (TRANS (@lem5380632) (@lem5380699)). Qed.
Lemma lem5380701 (_69788 : int) (_69787 : int) (h1 : term257 _69788 _69787) : False.
Proof. exact (EQ_MP (@lem5380700) (@lem5380629 _69788 _69787 h1)). Qed.
Lemma lem5380703 (_69788 : int) (_69787 : int) (h1 : term257 _69788 _69787) : term257 _69788 _69787.
Proof. exact (h1). Qed.
Lemma lem5380704 (_69788 : int) (_69787 : int) (h1 : term257 _69788 _69787) : (term257 _69788 _69787) = False.
Proof. exact (prop_ext (fun h2 : term257 _69788 _69787 => @lem5380701 _69788 _69787 h1) (fun h2 : False => @lem5380703 _69788 _69787 h1)). Qed.
Lemma lem5380705 (_69788 : int) (_69787 : int) (h1 : term257 _69788 _69787) : False.
Proof. exact (EQ_MP (@lem5380704 _69788 _69787 h1) (@lem5380703 _69788 _69787 h1)). Qed.
Lemma lem5380706 (_69787 : int) (_69788 : int) (h1 : term195 _69787 _69788) : term195 _69787 _69788.
Proof. exact (h1). Qed.
Lemma lem5380707 (_69787 : int) (_69788 : int) (h1 : term195 _69787 _69788) : term257 _69788 _69787.
Proof. exact (EQ_MP (@lem5380349 _69788 _69787) (@lem5380706 _69787 _69788 h1)). Qed.
Lemma lem5380708 (_69787 : int) (_69788 : int) (h1 : term195 _69787 _69788) : (term257 _69788 _69787) = False.
Proof. exact (prop_ext (fun h2 : term257 _69788 _69787 => @lem5380705 _69788 _69787 h2) (fun h2 : False => @lem5380707 _69787 _69788 h1)). Qed.
Lemma lem5380709 (_69787 : int) (_69788 : int) (h1 : term195 _69787 _69788) : False.
Proof. exact (EQ_MP (@lem5380708 _69787 _69788 h1) (@lem5380707 _69787 _69788 h1)). Qed.
Lemma lem5380710 (_69787 : int) (_69788 : int) : term297 _69787 _69788.
Proof. exact (fun h0 : term195 _69787 _69788 => @lem5380709 _69787 _69788 h0). Qed.
Lemma lem5380711 (_69787 : int) (_69788 : int) : term298 _69787 _69788.
Proof. exact (@lem1386578 (term299 _69787 _69788)). Qed.
Lemma lem5380714 (_69787 : int) (_69788 : int) : term299 _69787 _69788.
Proof. exact (@lem5380711 _69787 _69788 (@lem5380710 _69787 _69788)). Qed.
Lemma lem5380715 (_69787 : int) (_69788 : int) : (term194 _69787 _69788) = (term173 _69787 _69788).
Proof. exact (SYM (@lem5379874 _69787 _69788)). Qed.
Lemma lem5380716 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5380717 (_69787 : int) (_69788 : int) : (term299 _69787 _69788) = (term166 _69787 _69788).
Proof. exact (MK_COMB (@lem5380716) (@lem5380715 _69787 _69788)). Qed.
Lemma lem5380718 (_69787 : int) (_69788 : int) : term166 _69787 _69788.
Proof. exact (EQ_MP (@lem5380717 _69787 _69788) (@lem5380714 _69787 _69788)). Qed.
Lemma lem5380719 (_69787 : int) (_69788 : int) : term167 _69787 _69788.
Proof. exact (EQ_MP (@lem5379769 _69787 _69788) (@lem5380718 _69787 _69788)). Qed.
Lemma lem5380720 (d : nat) (m : nat) : term300 d m.
Proof. exact (@lem5380719 (int_of_num d) (int_of_num m)). Qed.
Lemma lem5380721 (d : nat) (m : nat) : term301 d m.
Proof. exact (@lem5380720 d m (@lem5379765 d)). Qed.
Lemma lem5380722 (d : nat) (m : nat) : term165 d m.
Proof. exact (@lem5380721 d m (@lem5379768 m)). Qed.
Lemma lem5380723 (m : nat) (d : nat) : (term165 d m) = (term154 m d).
Proof. exact (SYM (@lem5379762 d m)). Qed.
Lemma lem5380724 (m : nat) (d : nat) : term154 m d.
Proof. exact (EQ_MP (@lem5380723 m d) (@lem5380722 d m)). Qed.
Lemma lem5380726 (P : nat -> Prop) : term302 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem5380727 (m : nat) : term303 m.
Proof. exact (@lem5380726 (term304 m)). Qed.
Lemma lem5380728 (m : nat) : (term305 m) = ((term306 m) = term307).
Proof. exact (eq_refl (term305 m)). Qed.
Lemma lem5380729 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5380730 (m : nat) : (term308 m) = (term309 m).
Proof. exact (MK_COMB (@lem5380729) (@lem5380728 m)). Qed.
Lemma lem5380731 (m : nat) (d : nat) : (term310 m d) = ((term311 m d) = (term0 d)).
Proof. exact (eq_refl (term310 m d)). Qed.
Lemma lem5380732 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5380733 (m : nat) (d : nat) : (term312 m d) = (term313 m d).
Proof. exact (MK_COMB (@lem5380732) (@lem5380731 m d)). Qed.
Lemma lem5380734 (m : nat) (d : nat) : (term314 m d) = ((term315 m d) = (term316 d)).
Proof. exact (eq_refl (term314 m d)). Qed.
Lemma lem5380735 (m : nat) (d : nat) : (term317 m d) = (term318 m d).
Proof. exact (MK_COMB (@lem5380733 m d) (@lem5380734 m d)). Qed.
Lemma lem5380736 (m : nat) : (term319 m) = (term320 m).
Proof. exact (fun_ext (fun d : nat => @lem5380735 m d)). Qed.
Lemma lem5380737 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5380738 (m : nat) : (term321 m) = (term322 m).
Proof. exact (MK_COMB (@lem5380737) (@lem5380736 m)). Qed.
Lemma lem5380739 (m : nat) : (term323 m) = (term324 m).
Proof. exact (MK_COMB (@lem5380730 m) (@lem5380738 m)). Qed.
Lemma lem5380740 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5380741 (m : nat) : (term325 m) = (term326 m).
Proof. exact (MK_COMB (@lem5380740) (@lem5380739 m)). Qed.
Lemma lem5380742 (m : nat) (d : nat) : (term310 m d) = ((term311 m d) = (term0 d)).
Proof. exact (eq_refl (term310 m d)). Qed.
Lemma lem5380743 (m : nat) : (term327 m) = (term304 m).
Proof. exact (fun_ext (fun d : nat => @lem5380742 m d)). Qed.
Lemma lem5380744 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5380745 (m : nat) : (term328 m) = (term329 m).
Proof. exact (MK_COMB (@lem5380744) (@lem5380743 m)). Qed.
Lemma lem5380746 (m : nat) : (term303 m) = (term330 m).
Proof. exact (MK_COMB (@lem5380741 m) (@lem5380745 m)). Qed.
Lemma lem5380747 (m : nat) : term330 m.
Proof. exact (EQ_MP (@lem5380746 m) (@lem5380727 m)). Qed.
Lemma lem5381093 : term331.
Proof. exact (EQ_MP (@lem521920) (@lem522075)). Qed.
Lemma lem5381094 : term332.
Proof. exact (proj2 (@lem5381093)). Qed.
Lemma lem5381095 : term333.
Proof. exact (proj2 (@lem5381094)). Qed.
Lemma lem5381096 : term334.
Proof. exact (proj2 (@lem5381095)). Qed.
Lemma lem5381097 : term335.
Proof. exact (proj2 (@lem5381096)). Qed.
Lemma lem5381098 : term336.
Proof. exact (proj2 (@lem5381097)). Qed.
Lemma lem5381099 : term337.
Proof. exact (proj2 (@lem5381098)). Qed.
Lemma lem5381100 : term338.
Proof. exact (proj2 (@lem5381099)). Qed.
Lemma lem5381101 : term339.
Proof. exact (proj2 (@lem5381100)). Qed.
Lemma lem5381102 : term340.
Proof. exact (proj2 (@lem5381101)). Qed.
Lemma lem5381103 (m : nat) : term341 m.
Proof. exact (@lem5381102 m). Qed.
Lemma lem5381104 (m : nat) : (term341 m) = (term342 m).
Proof. exact (eq_refl (term341 m)). Qed.
Lemma lem5381105 (m : nat) : term342 m.
Proof. exact (EQ_MP (@lem5381104 m) (@lem5381103 m)). Qed.
Lemma lem5381106 (m : nat) (n : nat) : term343 m n.
Proof. exact (@lem5381105 m n). Qed.
Lemma lem5381107 (m : nat) (n : nat) : (term343 m n) = (((BIT1 m) = (BIT1 n)) = (m = n)).
Proof. exact (eq_refl (term343 m n)). Qed.
Lemma lem5381147 : term344.
Proof. exact (proj1 (@lem5381093)). Qed.
Lemma lem5381148 (m : nat) : term345 m.
Proof. exact (@lem5381147 m). Qed.
Lemma lem5381149 (m : nat) : (term345 m) = (term346 m).
Proof. exact (eq_refl (term345 m)). Qed.
Lemma lem5381150 (m : nat) : term346 m.
Proof. exact (EQ_MP (@lem5381149 m) (@lem5381148 m)). Qed.
Lemma lem5381151 (m : nat) (n : nat) : term347 m n.
Proof. exact (@lem5381150 m n). Qed.
Lemma lem5381152 (m : nat) (n : nat) : (term347 m n) = (((NUMERAL m) = (NUMERAL n)) = (m = n)).
Proof. exact (eq_refl (term347 m n)). Qed.
Lemma lem5381385 : term348.
Proof. exact (EQ_MP (@lem513079) (@lem0)). Qed.
Lemma lem5381386 : term349.
Proof. exact (proj2 (@lem5381385)). Qed.
Lemma lem5381397 : term350.
Proof. exact (proj1 (@lem5381385)). Qed.
Lemma lem5381398 (n : nat) : term351 n.
Proof. exact (@lem5381397 n). Qed.
Lemma lem5381399 (n : nat) : (term351 n) = ((term352 n) = (term353 n)).
Proof. exact (eq_refl (term351 n)). Qed.
Lemma lem5381404 {A : Type'} (x : A) : term354 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem5381405 {A : Type'} (x : A) : (term354 A x) = (term355 A x).
Proof. exact (eq_refl (term354 A x)). Qed.
Lemma lem5381406 {A : Type'} (x : A) : term355 A x.
Proof. exact (EQ_MP (@lem5381405 A x) (@lem5381404 A x)). Qed.
Lemma lem5381407 {A : Type'} (x : A) : term356 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem5381417 {A : Type'} : term357 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem5381418 {A : Type'} (x : A) : term358 A x.
Proof. exact (@lem5381417 A x). Qed.
Lemma lem5381419 {A : Type'} (x : A) : (term358 A x) = (term359 A x).
Proof. exact (eq_refl (term358 A x)). Qed.
Lemma lem5381420 {A : Type'} (x : A) : term359 A x.
Proof. exact (EQ_MP (@lem5381419 A x) (@lem5381418 A x)). Qed.
Lemma lem5381421 {A : Type'} (x : A) (s : A -> Prop) : term360 A x s.
Proof. exact (@lem5381420 A x s). Qed.
Lemma lem5381422 {A : Type'} (x : A) (s : A -> Prop) : (term360 A x s) = (term361 A x s).
Proof. exact (eq_refl (term360 A x s)). Qed.
Lemma lem5381423 {A : Type'} (x : A) (s : A -> Prop) : term361 A x s.
Proof. exact (EQ_MP (@lem5381422 A x s) (@lem5381421 A x s)). Qed.
Lemma lem5381424 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem5381425 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term362 A x s) = (term363 A x s).
Proof. exact (@lem5381423 A x s (@lem5381424 A s h1)). Qed.
Lemma lem5381450 {A : Type'} : @FINITE A (@EMPTY A).
Proof. exact (proj1 (@lem3197565 A)). Qed.
Lemma lem5381451 {A : Type'} : (@FINITE A (@EMPTY A)) = ((@FINITE A (@EMPTY A)) = True).
Proof. exact (@lem7 (@FINITE A (@EMPTY A))). Qed.
Lemma lem5381453 (n : nat) : term364 n.
Proof. exact (@lem5374366 n). Qed.
Lemma lem5381454 (n : nat) : (term364 n) = ((dotdot n n) = (@INSERT nat n (@EMPTY nat))).
Proof. exact (eq_refl (term364 n)). Qed.
Lemma lem5381469 : term365.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem5381485 : term366.
Proof. exact (proj1 (@lem5381469)). Qed.
Lemma lem5381486 (m : nat) : term367 m.
Proof. exact (@lem5381485 m). Qed.
Lemma lem5381487 (m : nat) : (term367 m) = ((term368 m) = m).
Proof. exact (eq_refl (term367 m)). Qed.
Lemma lem5381489 : term369.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem5381490 (n : nat) : term370 n.
Proof. exact (@lem5381489 n). Qed.
Lemma lem5381491 (n : nat) : (term370 n) = ((term371 n) = n).
Proof. exact (eq_refl (term370 n)). Qed.
Lemma lem5381498 (m : nat) : (term368 m) = m.
Proof. exact (EQ_MP (@lem5381487 m) (@lem5381486 m)). Qed.
Lemma lem5381499 (m : nat) : (dotdot m) = (dotdot m).
Proof. exact (eq_refl (dotdot m)). Qed.
Lemma lem5381500 (m : nat) : (term372 m) = (dotdot m m).
Proof. exact (MK_COMB (@lem5381499 m) (@lem5381498 m)). Qed.
Lemma lem5381502 (n : nat) : (dotdot n n) = (@INSERT nat n (@EMPTY nat)).
Proof. exact (EQ_MP (@lem5381454 n) (@lem5381453 n)). Qed.
Lemma lem5381503 (m : nat) : (dotdot m m) = (@INSERT nat m (@EMPTY nat)).
Proof. exact (@lem5381502 m). Qed.
Lemma lem5381504 (m : nat) : (term372 m) = (@INSERT nat m (@EMPTY nat)).
Proof. exact (TRANS (@lem5381500 m) (@lem5381503 m)). Qed.
Lemma lem5381505 : (@CARD nat) = (@CARD nat).
Proof. exact (eq_refl (@CARD nat)). Qed.
Lemma lem5381506 (m : nat) : (term306 m) = (term373 m).
Proof. exact (MK_COMB (@lem5381505) (@lem5381504 m)). Qed.
Lemma lem5381508 {A : Type'} (x : A) (s : A -> Prop) : term361 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem5381425 A x s h0). Qed.
Lemma lem5381509 (x : nat) (s : nat -> Prop) : term374 x s.
Proof. exact (@lem5381508 nat x s). Qed.
Lemma lem5381510 (m : nat) : term375 m.
Proof. exact (@lem5381509 m (@EMPTY nat)). Qed.
Lemma lem5381512 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem5381451 A) (@lem5381450 A)). Qed.
Lemma lem5381513 : (@FINITE nat (@EMPTY nat)) = True.
Proof. exact (@lem5381512 nat). Qed.
Lemma lem5381514 : True = (@FINITE nat (@EMPTY nat)).
Proof. exact (SYM (@lem5381513)). Qed.
Lemma lem5381515 : @FINITE nat (@EMPTY nat).
Proof. exact (EQ_MP (@lem5381514) (@lem0)). Qed.
Lemma lem5381516 (m : nat) : (term373 m) = (term376 m).
Proof. exact (@lem5381510 m (@lem5381515)). Qed.
Lemma lem5381518 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term377 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem5381519 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term378 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem5381518 _2963 g t e g' t' e'). Qed.
Lemma lem5381520 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term379 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem5381519 _2963 g t e g' t'). Qed.
Lemma lem5381521 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term380 _2963 g t e.
Proof. exact (fun g' : Prop => @lem5381520 _2963 g t e g'). Qed.
Lemma lem5381522 (g : Prop) (t : nat) (e : nat) : term381 g t e.
Proof. exact (@lem5381521 nat g t e). Qed.
Lemma lem5381523 (m : nat) : term382 m.
Proof. exact (@lem5381522 (@IN nat m (@EMPTY nat)) (@CARD nat (@EMPTY nat)) term383). Qed.
Lemma lem5381524 (m : nat) (g' : Prop) : term384 m g'.
Proof. exact (@lem5381523 m g'). Qed.
Lemma lem5381525 (m : nat) (g' : Prop) : (term384 m g') = (term385 m g').
Proof. exact (eq_refl (term384 m g')). Qed.
Lemma lem5381526 (m : nat) (g' : Prop) : term385 m g'.
Proof. exact (EQ_MP (@lem5381525 m g') (@lem5381524 m g')). Qed.
Lemma lem5381527 (m : nat) (g' : Prop) (t' : nat) : term386 m g' t'.
Proof. exact (@lem5381526 m g' t'). Qed.
Lemma lem5381528 (m : nat) (g' : Prop) (t' : nat) : (term386 m g' t') = (term387 m g' t').
Proof. exact (eq_refl (term386 m g' t')). Qed.
Lemma lem5381529 (m : nat) (g' : Prop) (t' : nat) : term387 m g' t'.
Proof. exact (EQ_MP (@lem5381528 m g' t') (@lem5381527 m g' t')). Qed.
Lemma lem5381530 (m : nat) (g' : Prop) (t' : nat) (e' : nat) : term388 m g' t' e'.
Proof. exact (@lem5381529 m g' t' e'). Qed.
Lemma lem5381531 (m : nat) (g' : Prop) (t' : nat) (e' : nat) : (term388 m g' t' e') = (term389 m g' t' e').
Proof. exact (eq_refl (term388 m g' t' e')). Qed.
Lemma lem5381532 (m : nat) (g' : Prop) (t' : nat) (e' : nat) : term389 m g' t' e'.
Proof. exact (EQ_MP (@lem5381531 m g' t' e') (@lem5381530 m g' t' e')). Qed.
Lemma lem5381534 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5381407 A x (@lem5381406 A x)). Qed.
Lemma lem5381535 (x : nat) : (@IN nat x (@EMPTY nat)) = False.
Proof. exact (@lem5381534 nat x). Qed.
Lemma lem5381536 (m : nat) : (@IN nat m (@EMPTY nat)) = False.
Proof. exact (@lem5381535 m). Qed.
Lemma lem5381537 (m : nat) (t' : nat) (e' : nat) : term390 m t' e'.
Proof. exact (@lem5381532 m False t' e'). Qed.
Lemma lem5381538 (m : nat) (t' : nat) (e' : nat) : term391 m t' e'.
Proof. exact (@lem5381537 m t' e' (@lem5381536 m)). Qed.
Lemma lem5381543 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem5381544 : (@CARD nat (@EMPTY nat)) = (NUMERAL 0).
Proof. exact (@lem5381543 nat). Qed.
Lemma lem5381545 : term392.
Proof. exact (fun h0 : False => @lem5381544). Qed.
Lemma lem5381546 (m : nat) (e' : nat) : term393 m e'.
Proof. exact (@lem5381538 m (NUMERAL 0) e'). Qed.
Lemma lem5381547 (m : nat) (e' : nat) : term394 m e'.
Proof. exact (@lem5381546 m e' (@lem5381545)). Qed.
Lemma lem5381554 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem5381555 : (@CARD nat (@EMPTY nat)) = (NUMERAL 0).
Proof. exact (@lem5381554 nat). Qed.
Lemma lem5381556 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem5381557 : term383 = term395.
Proof. exact (MK_COMB (@lem5381556) (@lem5381555)). Qed.
Lemma lem5381559 (n : nat) : (term352 n) = (term353 n).
Proof. exact (EQ_MP (@lem5381399 n) (@lem5381398 n)). Qed.
Lemma lem5381560 : term395 = term396.
Proof. exact (@lem5381559 0). Qed.
Lemma lem5381562 : (S 0) = (BIT1 0).
Proof. exact (proj1 (@lem5381386)). Qed.
Lemma lem5381563 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem5381564 : term396 = term13.
Proof. exact (MK_COMB (@lem5381563) (@lem5381562)). Qed.
Lemma lem5381565 : term395 = term13.
Proof. exact (TRANS (@lem5381560) (@lem5381564)). Qed.
Lemma lem5381566 : term383 = term13.
Proof. exact (TRANS (@lem5381557) (@lem5381565)). Qed.
Lemma lem5381567 : term397.
Proof. exact (fun h0 : ~ False => @lem5381566). Qed.
Lemma lem5381568 (m : nat) : term398 m.
Proof. exact (@lem5381547 m term13). Qed.
Lemma lem5381569 (m : nat) : (term376 m) = term399.
Proof. exact (@lem5381568 m (@lem5381567)). Qed.
Lemma lem5381571 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5381572 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem5381571 nat t1 t2). Qed.
Lemma lem5381573 : term399 = term13.
Proof. exact (@lem5381572 (NUMERAL 0) term13). Qed.
Lemma lem5381574 (m : nat) : (term376 m) = term13.
Proof. exact (TRANS (@lem5381569 m) (@lem5381573)). Qed.
Lemma lem5381575 (m : nat) : (term373 m) = term13.
Proof. exact (TRANS (@lem5381516 m) (@lem5381574 m)). Qed.
Lemma lem5381576 (m : nat) : (term306 m) = term13.
Proof. exact (TRANS (@lem5381506 m) (@lem5381575 m)). Qed.
Lemma lem5381577 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem5381578 (m : nat) : (term400 m) = term401.
Proof. exact (MK_COMB (@lem5381577) (@lem5381576 m)). Qed.
Lemma lem5381580 (n : nat) : (term371 n) = n.
Proof. exact (EQ_MP (@lem5381491 n) (@lem5381490 n)). Qed.
Lemma lem5381581 : term307 = term13.
Proof. exact (@lem5381580 term13). Qed.
Lemma lem5381582 (m : nat) : ((term306 m) = term307) = (term13 = term13).
Proof. exact (MK_COMB (@lem5381578 m) (@lem5381581)). Qed.
Lemma lem5381584 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem5381152 m n) (@lem5381151 m n)). Qed.
Lemma lem5381585 : (term13 = term13) = ((BIT1 0) = (BIT1 0)).
Proof. exact (@lem5381584 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5381587 (m : nat) (n : nat) : ((BIT1 m) = (BIT1 n)) = (m = n).
Proof. exact (EQ_MP (@lem5381107 m n) (@lem5381106 m n)). Qed.
Lemma lem5381588 : ((BIT1 0) = (BIT1 0)) = (0 = 0).
Proof. exact (@lem5381587 0 0). Qed.
Lemma lem5381590 : (0 = 0) = True.
Proof. exact (proj1 (@lem5381094)). Qed.
Lemma lem5381591 : ((BIT1 0) = (BIT1 0)) = True.
Proof. exact (TRANS (@lem5381588) (@lem5381590)). Qed.
Lemma lem5381592 : (term13 = term13) = True.
Proof. exact (TRANS (@lem5381585) (@lem5381591)). Qed.
Lemma lem5381593 (m : nat) : ((term306 m) = term307) = True.
Proof. exact (TRANS (@lem5381582 m) (@lem5381592)). Qed.
Lemma lem5381594 (m : nat) : True = ((term306 m) = term307).
Proof. exact (SYM (@lem5381593 m)). Qed.
Lemma lem5381595 (m : nat) : (term306 m) = term307.
Proof. exact (EQ_MP (@lem5381594 m) (@lem0)). Qed.
Lemma lem5381596 (n : nat) : term402 n.
Proof. exact (@lem82 (term3 n)). Qed.
Lemma lem5381598 (m : nat) : term403 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem5381599 (m : nat) : (term403 m) = (term404 m).
Proof. exact (eq_refl (term403 m)). Qed.
Lemma lem5381600 (m : nat) : term404 m.
Proof. exact (EQ_MP (@lem5381599 m) (@lem5381598 m)). Qed.
Lemma lem5381601 (m : nat) (n : nat) : term405 m n.
Proof. exact (@lem5381600 m n). Qed.
Lemma lem5381602 (m : nat) (n : nat) : (term405 m n) = (term406 m n).
Proof. exact (eq_refl (term405 m n)). Qed.
Lemma lem5381603 (m : nat) (n : nat) : term406 m n.
Proof. exact (EQ_MP (@lem5381602 m n) (@lem5381601 m n)). Qed.
Lemma lem5381604 (m : nat) (n : nat) (p : nat) : term407 m n p.
Proof. exact (@lem5381603 m n p). Qed.
Lemma lem5381605 (m : nat) (p : nat) (n : nat) : (term407 m n p) = ((term408 p m n) = (term409 m p n)).
Proof. exact (eq_refl (term407 m n p)). Qed.
Lemma lem5382256 (m : nat) : term410 m.
Proof. exact (@lem5329299 m). Qed.
Lemma lem5382257 (m : nat) : (term410 m) = (term411 m).
Proof. exact (eq_refl (term410 m)). Qed.
Lemma lem5382258 (m : nat) : term411 m.
Proof. exact (EQ_MP (@lem5382257 m) (@lem5382256 m)). Qed.
Lemma lem5382259 (m : nat) (n : nat) : term412 m n.
Proof. exact (@lem5382258 m n). Qed.
Lemma lem5382260 (m : nat) (n : nat) : (term412 m n) = (term413 m n).
Proof. exact (eq_refl (term412 m n)). Qed.
Lemma lem5382261 (m : nat) (n : nat) : term413 m n.
Proof. exact (EQ_MP (@lem5382260 m n) (@lem5382259 m n)). Qed.
Lemma lem5382262 (m : nat) (n : nat) : (term413 m n) = ((term413 m n) = True).
Proof. exact (@lem7 (term413 m n)). Qed.
Lemma lem5382264 {A : Type'} : term357 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem5382265 {A : Type'} (x : A) : term358 A x.
Proof. exact (@lem5382264 A x). Qed.
Lemma lem5382266 {A : Type'} (x : A) : (term358 A x) = (term359 A x).
Proof. exact (eq_refl (term358 A x)). Qed.
Lemma lem5382267 {A : Type'} (x : A) : term359 A x.
Proof. exact (EQ_MP (@lem5382266 A x) (@lem5382265 A x)). Qed.
Lemma lem5382268 {A : Type'} (x : A) (s : A -> Prop) : term360 A x s.
Proof. exact (@lem5382267 A x s). Qed.
Lemma lem5382269 {A : Type'} (x : A) (s : A -> Prop) : (term360 A x s) = (term361 A x s).
Proof. exact (eq_refl (term360 A x s)). Qed.
Lemma lem5382270 {A : Type'} (x : A) (s : A -> Prop) : term361 A x s.
Proof. exact (EQ_MP (@lem5382269 A x s) (@lem5382268 A x s)). Qed.
Lemma lem5382271 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem5382272 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term362 A x s) = (term363 A x s).
Proof. exact (@lem5382270 A x s (@lem5382271 A s h1)). Qed.
Lemma lem5382279 (m : nat) (d : nat) : (term154 m d) = ((term154 m d) = True).
Proof. exact (@lem7 (term154 m d)). Qed.
Lemma lem5382303 (m : nat) : term414 m.
Proof. exact (@lem5371143 m). Qed.
Lemma lem5382304 (m : nat) : (term414 m) = (term415 m).
Proof. exact (eq_refl (term414 m)). Qed.
Lemma lem5382305 (m : nat) : term415 m.
Proof. exact (EQ_MP (@lem5382304 m) (@lem5382303 m)). Qed.
Lemma lem5382306 (m : nat) (n : nat) : term416 m n.
Proof. exact (@lem5382305 m n). Qed.
Lemma lem5382307 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (eq_refl (term416 m n)). Qed.
Lemma lem5382308 (m : nat) (n : nat) : term417 m n.
Proof. exact (EQ_MP (@lem5382307 m n) (@lem5382306 m n)). Qed.
Lemma lem5382309 (m : nat) (n : nat) (h1 : term418 m n) : term418 m n.
Proof. exact (h1). Qed.
Lemma lem5382310 (m : nat) (n : nat) (h1 : term418 m n) : (term419 m n) = (term420 m n).
Proof. exact (@lem5382308 m n (@lem5382309 m n h1)). Qed.
Lemma lem5382316 : term365.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem5382317 : term421.
Proof. exact (proj2 (@lem5382316)). Qed.
Lemma lem5382318 : term422.
Proof. exact (proj2 (@lem5382317)). Qed.
Lemma lem5382319 (m : nat) : term423 m.
Proof. exact (@lem5382318 m). Qed.
Lemma lem5382320 (m : nat) : (term423 m) = (term424 m).
Proof. exact (eq_refl (term423 m)). Qed.
Lemma lem5382321 (m : nat) : term424 m.
Proof. exact (EQ_MP (@lem5382320 m) (@lem5382319 m)). Qed.
Lemma lem5382322 (m : nat) (n : nat) : term425 m n.
Proof. exact (@lem5382321 m n). Qed.
Lemma lem5382323 (m : nat) (n : nat) : (term425 m n) = ((term426 m n) = (term152 m n)).
Proof. exact (eq_refl (term425 m n)). Qed.
Lemma lem5382325 : term427.
Proof. exact (proj1 (@lem5382317)). Qed.
Lemma lem5382326 (m : nat) : term428 m.
Proof. exact (@lem5382325 m). Qed.
Lemma lem5382327 (m : nat) : (term428 m) = (term429 m).
Proof. exact (eq_refl (term428 m)). Qed.
Lemma lem5382328 (m : nat) : term429 m.
Proof. exact (EQ_MP (@lem5382327 m) (@lem5382326 m)). Qed.
Lemma lem5382329 (m : nat) (n : nat) : term430 m n.
Proof. exact (@lem5382328 m n). Qed.
Lemma lem5382330 (m : nat) (n : nat) : (term430 m n) = ((term431 m n) = (term152 m n)).
Proof. exact (eq_refl (term430 m n)). Qed.
Lemma lem5382345 (m : nat) (n : nat) : (term426 m n) = (term152 m n).
Proof. exact (EQ_MP (@lem5382323 m n) (@lem5382322 m n)). Qed.
Lemma lem5382346 (m : nat) (d : nat) : (term426 m d) = (term152 m d).
Proof. exact (@lem5382345 m d). Qed.
Lemma lem5382347 (m : nat) : (dotdot m) = (dotdot m).
Proof. exact (eq_refl (dotdot m)). Qed.
Lemma lem5382348 (m : nat) (d : nat) : (term432 m d) = (term433 m d).
Proof. exact (MK_COMB (@lem5382347 m) (@lem5382346 m d)). Qed.
Lemma lem5382350 (m : nat) (n : nat) : term417 m n.
Proof. exact (fun h0 : term418 m n => @lem5382310 m n h0). Qed.
Lemma lem5382351 (m : nat) (d : nat) : term434 m d.
Proof. exact (@lem5382350 m (Nat.add m d)). Qed.
Lemma lem5382353 (m : nat) (d : nat) : (term154 m d) = True.
Proof. exact (EQ_MP (@lem5382279 m d) (@lem5380724 m d)). Qed.
Lemma lem5382354 (m : nat) (d : nat) : True = (term154 m d).
Proof. exact (SYM (@lem5382353 m d)). Qed.
Lemma lem5382355 (m : nat) (d : nat) : term154 m d.
Proof. exact (EQ_MP (@lem5382354 m d) (@lem0)). Qed.
Lemma lem5382356 (m : nat) (d : nat) : (term433 m d) = (term435 m d).
Proof. exact (@lem5382351 m d (@lem5382355 m d)). Qed.
Lemma lem5382359 (m : nat) (d : nat) : (term432 m d) = (term435 m d).
Proof. exact (TRANS (@lem5382348 m d) (@lem5382356 m d)). Qed.
Lemma lem5382360 : (@CARD nat) = (@CARD nat).
Proof. exact (eq_refl (@CARD nat)). Qed.
Lemma lem5382361 (m : nat) (d : nat) : (term315 m d) = (term436 m d).
Proof. exact (MK_COMB (@lem5382360) (@lem5382359 m d)). Qed.
Lemma lem5382363 {A : Type'} (x : A) (s : A -> Prop) : term361 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem5382272 A x s h0). Qed.
Lemma lem5382364 (x : nat) (s : nat -> Prop) : term374 x s.
Proof. exact (@lem5382363 nat x s). Qed.
Lemma lem5382365 (m : nat) (d : nat) : term437 m d.
Proof. exact (@lem5382364 (term152 m d) (term438 m d)). Qed.
Lemma lem5382367 (m : nat) (n : nat) : (term413 m n) = True.
Proof. exact (EQ_MP (@lem5382262 m n) (@lem5382261 m n)). Qed.
Lemma lem5382368 (m : nat) (d : nat) : (term439 m d) = True.
Proof. exact (@lem5382367 m (Nat.add m d)). Qed.
Lemma lem5382369 (m : nat) (d : nat) : True = (term439 m d).
Proof. exact (SYM (@lem5382368 m d)). Qed.
Lemma lem5382370 (m : nat) (d : nat) : term439 m d.
Proof. exact (EQ_MP (@lem5382369 m d) (@lem0)). Qed.
Lemma lem5382371 (m : nat) (d : nat) : (term436 m d) = (term440 m d).
Proof. exact (@lem5382365 m d (@lem5382370 m d)). Qed.
Lemma lem5382373 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term377 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem5382374 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term378 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem5382373 _2963 g t e g' t' e'). Qed.
Lemma lem5382375 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term379 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem5382374 _2963 g t e g' t'). Qed.
Lemma lem5382376 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term380 _2963 g t e.
Proof. exact (fun g' : Prop => @lem5382375 _2963 g t e g'). Qed.
Lemma lem5382377 (g : Prop) (t : nat) (e : nat) : term381 g t e.
Proof. exact (@lem5382376 nat g t e). Qed.
Lemma lem5382378 (m : nat) (d : nat) : term441 m d.
Proof. exact (@lem5382377 (term442 m d) (term311 m d) (term443 m d)). Qed.
Lemma lem5382379 (m : nat) (d : nat) (g' : Prop) : term444 m d g'.
Proof. exact (@lem5382378 m d g'). Qed.
Lemma lem5382380 (m : nat) (d : nat) (g' : Prop) : (term444 m d g') = (term445 m d g').
Proof. exact (eq_refl (term444 m d g')). Qed.
Lemma lem5382381 (m : nat) (d : nat) (g' : Prop) : term445 m d g'.
Proof. exact (EQ_MP (@lem5382380 m d g') (@lem5382379 m d g')). Qed.
Lemma lem5382382 (m : nat) (d : nat) (g' : Prop) (t' : nat) : term446 m d g' t'.
Proof. exact (@lem5382381 m d g' t'). Qed.
Lemma lem5382383 (m : nat) (d : nat) (g' : Prop) (t' : nat) : (term446 m d g' t') = (term447 m d g' t').
Proof. exact (eq_refl (term446 m d g' t')). Qed.
Lemma lem5382384 (m : nat) (d : nat) (g' : Prop) (t' : nat) : term447 m d g' t'.
Proof. exact (EQ_MP (@lem5382383 m d g' t') (@lem5382382 m d g' t')). Qed.
Lemma lem5382385 (m : nat) (d : nat) (g' : Prop) (t' : nat) (e' : nat) : term448 m d g' t' e'.
Proof. exact (@lem5382384 m d g' t' e'). Qed.
Lemma lem5382386 (m : nat) (d : nat) (g' : Prop) (t' : nat) (e' : nat) : (term448 m d g' t' e') = (term449 m d g' t' e').
Proof. exact (eq_refl (term448 m d g' t' e')). Qed.
Lemma lem5382387 (m : nat) (d : nat) (g' : Prop) (t' : nat) (e' : nat) : term449 m d g' t' e'.
Proof. exact (EQ_MP (@lem5382386 m d g' t' e') (@lem5382385 m d g' t' e')). Qed.
Lemma lem5382389 (m : nat) (p : nat) (n : nat) : (term408 p m n) = (term409 m p n).
Proof. exact (EQ_MP (@lem5381605 m p n) (@lem5381604 m n p)). Qed.
Lemma lem5382390 (m : nat) (d : nat) : (term442 m d) = (term450 m d).
Proof. exact (@lem5382389 m (term152 m d) (Nat.add m d)). Qed.
Lemma lem5382394 (m : nat) (d : nat) : (term154 m d) = True.
Proof. exact (EQ_MP (@lem5382279 m d) (@lem5380724 m d)). Qed.
Lemma lem5382395 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5382396 (m : nat) (d : nat) : (term451 m d) = (and True).
Proof. exact (MK_COMB (@lem5382395) (@lem5382394 m d)). Qed.
Lemma lem5382398 (n : nat) : (term3 n) = False.
Proof. exact (@lem5381596 n (@lem5379705 n)). Qed.
Lemma lem5382399 (m : nat) (d : nat) : (term452 m d) = False.
Proof. exact (@lem5382398 (Nat.add m d)). Qed.
Lemma lem5382400 (m : nat) (d : nat) : (term450 m d) = (True /\ False).
Proof. exact (MK_COMB (@lem5382396 m d) (@lem5382399 m d)). Qed.
Lemma lem5382402 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5382403 : (True /\ False) = False.
Proof. exact (@lem5382402 False). Qed.
Lemma lem5382404 (m : nat) (d : nat) : (term450 m d) = False.
Proof. exact (TRANS (@lem5382400 m d) (@lem5382403)). Qed.
Lemma lem5382405 (m : nat) (d : nat) : (term442 m d) = False.
Proof. exact (TRANS (@lem5382390 m d) (@lem5382404 m d)). Qed.
Lemma lem5382406 (m : nat) (d : nat) (t' : nat) (e' : nat) : term453 m d t' e'.
Proof. exact (@lem5382387 m d False t' e'). Qed.
Lemma lem5382407 (m : nat) (d : nat) (t' : nat) (e' : nat) : term454 m d t' e'.
Proof. exact (@lem5382406 m d t' e' (@lem5382405 m d)). Qed.
Lemma lem5382412 (m : nat) (d : nat) (h1 : (term311 m d) = (term0 d)) : (term311 m d) = (term0 d).
Proof. exact (h1). Qed.
Lemma lem5382413 (m : nat) (d : nat) (h1 : (term311 m d) = (term0 d)) : term455 m d.
Proof. exact (fun h0 : False => @lem5382412 m d h1). Qed.
Lemma lem5382414 (m : nat) (d : nat) (e' : nat) : term456 m d e'.
Proof. exact (@lem5382407 m d (term0 d) e'). Qed.
Lemma lem5382415 (e' : nat) (m : nat) (d : nat) (h1 : (term311 m d) = (term0 d)) : term457 m d e'.
Proof. exact (@lem5382414 m d e' (@lem5382413 m d h1)). Qed.
Lemma lem5382422 (m : nat) (d : nat) (h1 : (term311 m d) = (term0 d)) : (term311 m d) = (term0 d).
Proof. exact (h1). Qed.
Lemma lem5382423 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem5382424 (m : nat) (d : nat) (h1 : (term311 m d) = (term0 d)) : (term443 m d) = (term458 d).
Proof. exact (MK_COMB (@lem5382423) (@lem5382422 m d h1)). Qed.
Lemma lem5382425 (m : nat) (d : nat) (h1 : (term311 m d) = (term0 d)) : term459 m d.
Proof. exact (fun h0 : ~ False => @lem5382424 m d h1). Qed.
Lemma lem5382426 (m : nat) (d : nat) (h1 : (term311 m d) = (term0 d)) : term460 m d.
Proof. exact (@lem5382415 (term458 d) m d h1). Qed.
Lemma lem5382427 (m : nat) (d : nat) (h1 : (term311 m d) = (term0 d)) : (term440 m d) = (term461 d).
Proof. exact (@lem5382426 m d h1 (@lem5382425 m d h1)). Qed.
Lemma lem5382429 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5382430 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem5382429 nat t1 t2). Qed.
Lemma lem5382431 (d : nat) : (term461 d) = (term458 d).
Proof. exact (@lem5382430 (term0 d) (term458 d)). Qed.
Lemma lem5382432 (m : nat) (d : nat) (h1 : (term311 m d) = (term0 d)) : (term440 m d) = (term458 d).
Proof. exact (TRANS (@lem5382427 m d h1) (@lem5382431 d)). Qed.
Lemma lem5382433 (m : nat) (d : nat) (h1 : (term311 m d) = (term0 d)) : (term436 m d) = (term458 d).
Proof. exact (TRANS (@lem5382371 m d) (@lem5382432 m d h1)). Qed.
Lemma lem5382434 (m : nat) (d : nat) (h1 : (term311 m d) = (term0 d)) : (term315 m d) = (term458 d).
Proof. exact (TRANS (@lem5382361 m d) (@lem5382433 m d h1)). Qed.
Lemma lem5382435 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem5382436 (m : nat) (d : nat) (h1 : (term311 m d) = (term0 d)) : (term462 m d) = (term463 d).
Proof. exact (MK_COMB (@lem5382435) (@lem5382434 m d h1)). Qed.
Lemma lem5382438 (m : nat) (n : nat) : (term431 m n) = (term152 m n).
Proof. exact (EQ_MP (@lem5382330 m n) (@lem5382329 m n)). Qed.
Lemma lem5382439 (d : nat) : (term316 d) = (term458 d).
Proof. exact (@lem5382438 d term13). Qed.
Lemma lem5382440 (m : nat) (d : nat) (h1 : (term311 m d) = (term0 d)) : ((term315 m d) = (term316 d)) = ((term458 d) = (term458 d)).
Proof. exact (MK_COMB (@lem5382436 m d h1) (@lem5382439 d)). Qed.
Lemma lem5382442 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5382443 (x : nat) : (x = x) = True.
Proof. exact (@lem5382442 nat x). Qed.
Lemma lem5382444 (d : nat) : ((term458 d) = (term458 d)) = True.
Proof. exact (@lem5382443 (term458 d)). Qed.
Lemma lem5382445 (m : nat) (d : nat) (h1 : (term311 m d) = (term0 d)) : ((term315 m d) = (term316 d)) = True.
Proof. exact (TRANS (@lem5382440 m d h1) (@lem5382444 d)). Qed.
Lemma lem5382446 (m : nat) (d : nat) (h1 : (term311 m d) = (term0 d)) : True = ((term315 m d) = (term316 d)).
Proof. exact (SYM (@lem5382445 m d h1)). Qed.
Lemma lem5382447 (m : nat) (d : nat) (h1 : (term311 m d) = (term0 d)) : (term315 m d) = (term316 d).
Proof. exact (EQ_MP (@lem5382446 m d h1) (@lem0)). Qed.
Lemma lem5382448 (m : nat) (d : nat) : term318 m d.
Proof. exact (fun h0 : (term311 m d) = (term0 d) => @lem5382447 m d h0). Qed.
Lemma lem5382453 (m : nat) : term322 m.
Proof. exact (fun d : nat => @lem5382448 m d). Qed.
Lemma lem5382454 (m : nat) : term324 m.
Proof. exact (conj (@lem5381595 m) (@lem5382453 m)). Qed.
Lemma lem5382455 (m : nat) : term329 m.
Proof. exact (@lem5380747 m (@lem5382454 m)). Qed.
Lemma lem5382460 : term464.
Proof. exact (fun m : nat => @lem5382455 m). Qed.
