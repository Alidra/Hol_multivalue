Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATO_CLAUSES_NUMSEG_LEFT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FINITE_NUMSEG_spec.
Require Import FINITE_RESTRICT_spec.
Require Import INT_POS_spec.
Require Import IN_NUMSEG_spec.
Require Import ITERATO_CLAUSES_GEN_spec.
Require Import NOT_LE_spec.
Require Import NUMSEG_EMPTY_spec.
Require Import NUMSEG_LREC_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm129_spec.
Require Import thm13473_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm137_spec.
Require Import thm1386578_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm1823_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19030_spec.
Require Import thm19031_spec.
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
Require Import thm1982757_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988332_spec.
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
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm2318495_spec.
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
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm2841413_spec.
Require Import thm2841414_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Lemma lem6889227 (m : nat) (n : nat) : (Peano.le m n) = (term0 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem6889228 (m : nat) : (term1 m) = (term2 m).
Proof. exact (@lem6889227 (term3 m) m). Qed.
Lemma lem6889230 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem6889231 (m : nat) : (term6 m) = (term7 m).
Proof. exact (@lem6889230 m term8). Qed.
Lemma lem6889232 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem6889233 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem6889232) (@lem6889231 m)). Qed.
Lemma lem6889234 (m : nat) : (int_of_num m) = (int_of_num m).
Proof. exact (eq_refl (int_of_num m)). Qed.
Lemma lem6889235 (m : nat) : (term2 m) = (term11 m).
Proof. exact (MK_COMB (@lem6889233 m) (@lem6889234 m)). Qed.
Lemma lem6889236 (m : nat) : (term1 m) = (term11 m).
Proof. exact (TRANS (@lem6889228 m) (@lem6889235 m)). Qed.
Lemma lem6889237 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6889239 (m : nat) : (term12 m) = (term13 m).
Proof. exact (MK_COMB (@lem6889237) (@lem6889236 m)). Qed.
Lemma lem6889240 (m : nat) : term14 m.
Proof. exact (@lem2307535 m). Qed.
Lemma lem6889241 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem6889242 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem6889241 m) (@lem6889240 m)). Qed.
Lemma lem6889243 (_91988 : int) : (term16 _91988) = (term17 _91988).
Proof. exact (@lem2318604 (term17 _91988)). Qed.
Lemma lem6889254 (_91988 : int) : (term18 _91988) = (term19 _91988).
Proof. exact (@lem16933 (term19 _91988)). Qed.
Lemma lem6889256 (_91988 : int) : (term20 _91988) = (term20 _91988).
Proof. exact (eq_refl (term20 _91988)). Qed.
Lemma lem6889257 (_91988 : int) : (term21 _91988) = (term22 _91988).
Proof. exact (MK_COMB (@lem6889256 _91988) (@lem6889254 _91988)). Qed.
Lemma lem6889258 (_91988 : int) : (term23 _91988) = (term21 _91988).
Proof. exact (@lem17362 (term24 _91988) (term25 _91988)). Qed.
Lemma lem6889266 (_91988 : int) : (term23 _91988) = (term22 _91988).
Proof. exact (TRANS (@lem6889258 _91988) (@lem6889257 _91988)). Qed.
Lemma lem6889269 (x : int) (y : int) : (int_le x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6889270 (_91988 : int) : (term24 _91988) = (term27 _91988).
Proof. exact (@lem6889269 term28 _91988). Qed.
Lemma lem6889272 (n : nat) : (term29 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6889273 : term30 = term31.
Proof. exact (@lem6889272 (NUMERAL 0)). Qed.
Lemma lem6889274 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6889275 : term32 = term33.
Proof. exact (MK_COMB (@lem6889274) (@lem6889273)). Qed.
Lemma lem6889276 (_91988 : int) : (real_of_int _91988) = (real_of_int _91988).
Proof. exact (eq_refl (real_of_int _91988)). Qed.
Lemma lem6889277 (_91988 : int) : (term27 _91988) = (term34 _91988).
Proof. exact (MK_COMB (@lem6889275) (@lem6889276 _91988)). Qed.
Lemma lem6889279 (_91988 : int) : (term24 _91988) = (term34 _91988).
Proof. exact (TRANS (@lem6889270 _91988) (@lem6889277 _91988)). Qed.
Lemma lem6889282 (x : int) (y : int) : (int_le x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6889283 (_91988 : int) : (term19 _91988) = (term35 _91988).
Proof. exact (@lem6889282 (term36 _91988) _91988). Qed.
Lemma lem6889285 (x : int) (y : int) : (term37 x y) = (term38 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6889286 (_91988 : int) : (term39 _91988) = (term40 _91988).
Proof. exact (@lem6889285 _91988 term41). Qed.
Lemma lem6889288 (n : nat) : (term29 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6889289 : term42 = term43.
Proof. exact (@lem6889288 term8). Qed.
Lemma lem6889290 (_91988 : int) : (term44 _91988) = (term44 _91988).
Proof. exact (eq_refl (term44 _91988)). Qed.
Lemma lem6889291 (_91988 : int) : (term40 _91988) = (term45 _91988).
Proof. exact (MK_COMB (@lem6889290 _91988) (@lem6889289)). Qed.
Lemma lem6889292 (_91988 : int) : (term39 _91988) = (term45 _91988).
Proof. exact (TRANS (@lem6889286 _91988) (@lem6889291 _91988)). Qed.
Lemma lem6889293 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6889294 (_91988 : int) : (term46 _91988) = (term47 _91988).
Proof. exact (MK_COMB (@lem6889293) (@lem6889292 _91988)). Qed.
Lemma lem6889295 (_91988 : int) : (real_of_int _91988) = (real_of_int _91988).
Proof. exact (eq_refl (real_of_int _91988)). Qed.
Lemma lem6889296 (_91988 : int) : (term35 _91988) = (term48 _91988).
Proof. exact (MK_COMB (@lem6889294 _91988) (@lem6889295 _91988)). Qed.
Lemma lem6889298 (_91988 : int) : (term19 _91988) = (term48 _91988).
Proof. exact (TRANS (@lem6889283 _91988) (@lem6889296 _91988)). Qed.
Lemma lem6889299 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6889300 (_91988 : int) : (term20 _91988) = (term49 _91988).
Proof. exact (MK_COMB (@lem6889299) (@lem6889279 _91988)). Qed.
Lemma lem6889301 (_91988 : int) : (term22 _91988) = (term50 _91988).
Proof. exact (MK_COMB (@lem6889300 _91988) (@lem6889298 _91988)). Qed.
Lemma lem6889302 (_91988 : int) : (term23 _91988) = (term50 _91988).
Proof. exact (TRANS (@lem6889266 _91988) (@lem6889301 _91988)). Qed.
Lemma lem6889306 (t : Prop) : (term51 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6889322 (_91988 : int) : (term52 _91988) = (term50 _91988).
Proof. exact (@lem6889306 (term50 _91988)). Qed.
Lemma lem6889323 (_91988 : int) : (term34 _91988) = (term53 _91988).
Proof. exact (@lem1988287 (real_of_int _91988) term31). Qed.
Lemma lem6889329 (_91988 : int) : (term54 _91988) = (term55 _91988).
Proof. exact (@lem1982792 (real_of_int _91988) term31). Qed.
Lemma lem6889331 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6889332 : term31 = term57.
Proof. exact (@lem6889331 (NUMERAL 0)). Qed.
Lemma lem6889334 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6889335 : term60 = term61.
Proof. exact (@lem6889334 term8). Qed.
Lemma lem6889336 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6889337 : term62 = term63.
Proof. exact (MK_COMB (@lem6889336) (@lem6889335)). Qed.
Lemma lem6889338 : term64 = term65.
Proof. exact (MK_COMB (@lem6889337) (@lem6889332)). Qed.
Lemma lem6889339 : term65 = term66.
Proof. exact (@lem1981613 term60 term31 term43 term43). Qed.
Lemma lem6889341 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6889342 : term69 = term70.
Proof. exact (@lem6889341 term8 term8). Qed.
Lemma lem6889343 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6889344 : term72 = term8.
Proof. exact (EQ_MP (@lem6889343) (@lem940073)). Qed.
Lemma lem6889345 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6889346 : term70 = term43.
Proof. exact (MK_COMB (@lem6889345) (@lem6889344)). Qed.
Lemma lem6889347 : term69 = term43.
Proof. exact (TRANS (@lem6889342) (@lem6889346)). Qed.
Lemma lem6889349 (x : nat) : (term73 x) = term31.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6889350 : term64 = term31.
Proof. exact (@lem6889349 term8). Qed.
Lemma lem6889351 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6889352 : term74 = term75.
Proof. exact (MK_COMB (@lem6889351) (@lem6889350)). Qed.
Lemma lem6889353 : term66 = term57.
Proof. exact (MK_COMB (@lem6889352) (@lem6889347)). Qed.
Lemma lem6889354 : term65 = term57.
Proof. exact (TRANS (@lem6889339) (@lem6889353)). Qed.
Lemma lem6889355 : term64 = term57.
Proof. exact (TRANS (@lem6889338) (@lem6889354)). Qed.
Lemma lem6889357 (x : real) : (term76 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6889358 : term57 = term31.
Proof. exact (@lem6889357 term31). Qed.
Lemma lem6889359 : term64 = term31.
Proof. exact (TRANS (@lem6889355) (@lem6889358)). Qed.
Lemma lem6889360 (_91988 : int) : (term44 _91988) = (term44 _91988).
Proof. exact (eq_refl (term44 _91988)). Qed.
Lemma lem6889361 (_91988 : int) : (term55 _91988) = (term77 _91988).
Proof. exact (MK_COMB (@lem6889360 _91988) (@lem6889359)). Qed.
Lemma lem6889362 (_91988 : int) : (term77 _91988) = (real_of_int _91988).
Proof. exact (@lem1982723 (real_of_int _91988)). Qed.
Lemma lem6889363 (_91988 : int) : (term55 _91988) = (real_of_int _91988).
Proof. exact (TRANS (@lem6889361 _91988) (@lem6889362 _91988)). Qed.
Lemma lem6889365 (_91988 : int) : (term54 _91988) = (real_of_int _91988).
Proof. exact (TRANS (@lem6889329 _91988) (@lem6889363 _91988)). Qed.
Lemma lem6889366 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6889367 (_91988 : int) : (term78 _91988) = (term79 _91988).
Proof. exact (MK_COMB (@lem6889366) (@lem6889365 _91988)). Qed.
Lemma lem6889368 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6889369 (_91988 : int) : (term53 _91988) = (term80 _91988).
Proof. exact (MK_COMB (@lem6889367 _91988) (@lem6889368)). Qed.
Lemma lem6889370 (_91988 : int) : (term34 _91988) = (term80 _91988).
Proof. exact (TRANS (@lem6889323 _91988) (@lem6889369 _91988)). Qed.
Lemma lem6889371 (_91988 : int) : (term48 _91988) = (term81 _91988).
Proof. exact (@lem1988287 (real_of_int _91988) (term45 _91988)). Qed.
Lemma lem6889383 (_91988 : int) : (term82 _91988) = (term83 _91988).
Proof. exact (@lem1982792 (real_of_int _91988) (term45 _91988)). Qed.
Lemma lem6889384 (_91988 : int) : (term84 _91988) = (term85 _91988).
Proof. exact (@lem1982781 (real_of_int _91988) term60 term43). Qed.
Lemma lem6889386 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6889387 : term43 = term86.
Proof. exact (@lem6889386 term8). Qed.
Lemma lem6889389 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6889390 : term60 = term61.
Proof. exact (@lem6889389 term8). Qed.
Lemma lem6889391 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6889392 : term62 = term63.
Proof. exact (MK_COMB (@lem6889391) (@lem6889390)). Qed.
Lemma lem6889393 : term87 = term88.
Proof. exact (MK_COMB (@lem6889392) (@lem6889387)). Qed.
Lemma lem6889394 : term88 = term89.
Proof. exact (@lem1981613 term60 term43 term43 term43). Qed.
Lemma lem6889396 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6889397 : term69 = term70.
Proof. exact (@lem6889396 term8 term8). Qed.
Lemma lem6889398 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6889399 : term72 = term8.
Proof. exact (EQ_MP (@lem6889398) (@lem940073)). Qed.
Lemma lem6889400 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6889401 : term70 = term43.
Proof. exact (MK_COMB (@lem6889400) (@lem6889399)). Qed.
Lemma lem6889402 : term69 = term43.
Proof. exact (TRANS (@lem6889397) (@lem6889401)). Qed.
Lemma lem6889404 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6889405 : term87 = term92.
Proof. exact (@lem6889404 term8 term8). Qed.
Lemma lem6889406 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6889407 : term72 = term8.
Proof. exact (EQ_MP (@lem6889406) (@lem940073)). Qed.
Lemma lem6889408 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6889409 : term70 = term43.
Proof. exact (MK_COMB (@lem6889408) (@lem6889407)). Qed.
Lemma lem6889410 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6889411 : term92 = term60.
Proof. exact (MK_COMB (@lem6889410) (@lem6889409)). Qed.
Lemma lem6889412 : term87 = term60.
Proof. exact (TRANS (@lem6889405) (@lem6889411)). Qed.
Lemma lem6889413 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6889414 : term93 = term94.
Proof. exact (MK_COMB (@lem6889413) (@lem6889412)). Qed.
Lemma lem6889415 : term89 = term61.
Proof. exact (MK_COMB (@lem6889414) (@lem6889402)). Qed.
Lemma lem6889416 : term88 = term61.
Proof. exact (TRANS (@lem6889394) (@lem6889415)). Qed.
Lemma lem6889417 : term87 = term61.
Proof. exact (TRANS (@lem6889393) (@lem6889416)). Qed.
Lemma lem6889419 (x : real) : (term76 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6889420 : term61 = term60.
Proof. exact (@lem6889419 term60). Qed.
Lemma lem6889421 : term87 = term60.
Proof. exact (TRANS (@lem6889417) (@lem6889420)). Qed.
Lemma lem6889424 (_91988 : int) : (term95 _91988) = (term95 _91988).
Proof. exact (eq_refl (term95 _91988)). Qed.
Lemma lem6889425 (_91988 : int) : (term85 _91988) = (term96 _91988).
Proof. exact (MK_COMB (@lem6889424 _91988) (@lem6889421)). Qed.
Lemma lem6889426 (_91988 : int) : (term84 _91988) = (term96 _91988).
Proof. exact (TRANS (@lem6889384 _91988) (@lem6889425 _91988)). Qed.
Lemma lem6889427 (_91988 : int) : (term44 _91988) = (term44 _91988).
Proof. exact (eq_refl (term44 _91988)). Qed.
Lemma lem6889428 (_91988 : int) : (term83 _91988) = (term97 _91988).
Proof. exact (MK_COMB (@lem6889427 _91988) (@lem6889426 _91988)). Qed.
Lemma lem6889429 (_91988 : int) : (term97 _91988) = (term98 _91988).
Proof. exact (@lem1982763 (real_of_int _91988) (term99 _91988) term60). Qed.
Lemma lem6889430 (_91988 : int) : (term100 _91988) = (term101 _91988).
Proof. exact (@lem1982715 term60 (real_of_int _91988)). Qed.
Lemma lem6889432 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6889433 : term43 = term86.
Proof. exact (@lem6889432 term8). Qed.
Lemma lem6889435 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6889436 : term60 = term61.
Proof. exact (@lem6889435 term8). Qed.
Lemma lem6889437 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6889438 : term102 = term103.
Proof. exact (MK_COMB (@lem6889437) (@lem6889436)). Qed.
Lemma lem6889439 : term104 = term105.
Proof. exact (MK_COMB (@lem6889438) (@lem6889433)). Qed.
Lemma lem6889440 : term106.
Proof. exact (@lem1981473 term60 term43 term43 term43 term31 term43). Qed.
Lemma lem6889442 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6889443 : term108 = term109.
Proof. exact (@lem6889442 (NUMERAL 0) term8). Qed.
Lemma lem6889444 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6889445 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6889446 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6889445 h1) (fun h1 : term109 = True => @lem6889444)). Qed.
Lemma lem6889447 : term109 = True.
Proof. exact (EQ_MP (@lem6889446) (@lem6889444)). Qed.
Lemma lem6889448 : term108 = True.
Proof. exact (TRANS (@lem6889443) (@lem6889447)). Qed.
Lemma lem6889449 : True = term108.
Proof. exact (SYM (@lem6889448)). Qed.
Lemma lem6889450 : term108.
Proof. exact (EQ_MP (@lem6889449) (@lem0)). Qed.
Lemma lem6889451 : term111.
Proof. exact (@lem6889440 (@lem6889450)). Qed.
Lemma lem6889453 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6889454 : term108 = term109.
Proof. exact (@lem6889453 (NUMERAL 0) term8). Qed.
Lemma lem6889455 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6889456 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6889457 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6889456 h1) (fun h1 : term109 = True => @lem6889455)). Qed.
Lemma lem6889458 : term109 = True.
Proof. exact (EQ_MP (@lem6889457) (@lem6889455)). Qed.
Lemma lem6889459 : term108 = True.
Proof. exact (TRANS (@lem6889454) (@lem6889458)). Qed.
Lemma lem6889460 : True = term108.
Proof. exact (SYM (@lem6889459)). Qed.
Lemma lem6889461 : term108.
Proof. exact (EQ_MP (@lem6889460) (@lem0)). Qed.
Lemma lem6889462 : term112.
Proof. exact (@lem6889451 (@lem6889461)). Qed.
Lemma lem6889464 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6889465 : term108 = term109.
Proof. exact (@lem6889464 (NUMERAL 0) term8). Qed.
Lemma lem6889466 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6889467 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6889468 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6889467 h1) (fun h1 : term109 = True => @lem6889466)). Qed.
Lemma lem6889469 : term109 = True.
Proof. exact (EQ_MP (@lem6889468) (@lem6889466)). Qed.
Lemma lem6889470 : term108 = True.
Proof. exact (TRANS (@lem6889465) (@lem6889469)). Qed.
Lemma lem6889471 : True = term108.
Proof. exact (SYM (@lem6889470)). Qed.
Lemma lem6889472 : term108.
Proof. exact (EQ_MP (@lem6889471) (@lem0)). Qed.
Lemma lem6889473 : term113.
Proof. exact (@lem6889462 (@lem6889472)). Qed.
Lemma lem6889475 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6889476 : term69 = term70.
Proof. exact (@lem6889475 term8 term8). Qed.
Lemma lem6889477 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6889478 : term72 = term8.
Proof. exact (EQ_MP (@lem6889477) (@lem940073)). Qed.
Lemma lem6889479 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6889480 : term70 = term43.
Proof. exact (MK_COMB (@lem6889479) (@lem6889478)). Qed.
Lemma lem6889481 : term69 = term43.
Proof. exact (TRANS (@lem6889476) (@lem6889480)). Qed.
Lemma lem6889483 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6889484 : term87 = term92.
Proof. exact (@lem6889483 term8 term8). Qed.
Lemma lem6889485 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6889486 : term72 = term8.
Proof. exact (EQ_MP (@lem6889485) (@lem940073)). Qed.
Lemma lem6889487 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6889488 : term70 = term43.
Proof. exact (MK_COMB (@lem6889487) (@lem6889486)). Qed.
Lemma lem6889489 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6889490 : term92 = term60.
Proof. exact (MK_COMB (@lem6889489) (@lem6889488)). Qed.
Lemma lem6889491 : term87 = term60.
Proof. exact (TRANS (@lem6889484) (@lem6889490)). Qed.
Lemma lem6889492 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6889493 : term114 = term102.
Proof. exact (MK_COMB (@lem6889492) (@lem6889491)). Qed.
Lemma lem6889494 : term115 = term104.
Proof. exact (MK_COMB (@lem6889493) (@lem6889481)). Qed.
Lemma lem6889496 (m : nat) : (term116 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6889497 : term104 = term31.
Proof. exact (@lem6889496 term8). Qed.
Lemma lem6889498 : term115 = term31.
Proof. exact (TRANS (@lem6889494) (@lem6889497)). Qed.
Lemma lem6889499 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6889500 : term117 = term118.
Proof. exact (MK_COMB (@lem6889499) (@lem6889498)). Qed.
Lemma lem6889501 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem6889502 : term119 = term120.
Proof. exact (MK_COMB (@lem6889500) (@lem6889501)). Qed.
Lemma lem6889504 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6889505 : term120 = term31.
Proof. exact (@lem6889504 term8). Qed.
Lemma lem6889506 : term119 = term31.
Proof. exact (TRANS (@lem6889502) (@lem6889505)). Qed.
Lemma lem6889508 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6889509 : term69 = term70.
Proof. exact (@lem6889508 term8 term8). Qed.
Lemma lem6889510 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6889511 : term72 = term8.
Proof. exact (EQ_MP (@lem6889510) (@lem940073)). Qed.
Lemma lem6889512 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6889513 : term70 = term43.
Proof. exact (MK_COMB (@lem6889512) (@lem6889511)). Qed.
Lemma lem6889514 : term69 = term43.
Proof. exact (TRANS (@lem6889509) (@lem6889513)). Qed.
Lemma lem6889515 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem6889516 : term122 = term120.
Proof. exact (MK_COMB (@lem6889515) (@lem6889514)). Qed.
Lemma lem6889518 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6889519 : term120 = term31.
Proof. exact (@lem6889518 term8). Qed.
Lemma lem6889520 : term122 = term31.
Proof. exact (TRANS (@lem6889516) (@lem6889519)). Qed.
Lemma lem6889521 : term31 = term122.
Proof. exact (SYM (@lem6889520)). Qed.
Lemma lem6889522 : term119 = term122.
Proof. exact (TRANS (@lem6889506) (@lem6889521)). Qed.
Lemma lem6889523 : term105 = term57.
Proof. exact (@lem6889473 (@lem6889522)). Qed.
Lemma lem6889524 : term104 = term57.
Proof. exact (TRANS (@lem6889439) (@lem6889523)). Qed.
Lemma lem6889526 (x : real) : (term76 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6889527 : term57 = term31.
Proof. exact (@lem6889526 term31). Qed.
Lemma lem6889528 : term104 = term31.
Proof. exact (TRANS (@lem6889524) (@lem6889527)). Qed.
Lemma lem6889529 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6889530 : term123 = term118.
Proof. exact (MK_COMB (@lem6889529) (@lem6889528)). Qed.
Lemma lem6889531 (_91988 : int) : (real_of_int _91988) = (real_of_int _91988).
Proof. exact (eq_refl (real_of_int _91988)). Qed.
Lemma lem6889532 (_91988 : int) : (term101 _91988) = (term124 _91988).
Proof. exact (MK_COMB (@lem6889530) (@lem6889531 _91988)). Qed.
Lemma lem6889533 (_91988 : int) : (term100 _91988) = (term124 _91988).
Proof. exact (TRANS (@lem6889430 _91988) (@lem6889532 _91988)). Qed.
Lemma lem6889534 (_91988 : int) : (term124 _91988) = term31.
Proof. exact (@lem1982719 (real_of_int _91988)). Qed.
Lemma lem6889535 (_91988 : int) : (term100 _91988) = term31.
Proof. exact (TRANS (@lem6889533 _91988) (@lem6889534 _91988)). Qed.
Lemma lem6889536 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6889537 (_91988 : int) : (term125 _91988) = term126.
Proof. exact (MK_COMB (@lem6889536) (@lem6889535 _91988)). Qed.
Lemma lem6889538 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem6889539 (_91988 : int) : (term98 _91988) = term127.
Proof. exact (MK_COMB (@lem6889537 _91988) (@lem6889538)). Qed.
Lemma lem6889540 (_91988 : int) : (term97 _91988) = term127.
Proof. exact (TRANS (@lem6889429 _91988) (@lem6889539 _91988)). Qed.
Lemma lem6889541 : term127 = term60.
Proof. exact (@lem1982721 term60). Qed.
Lemma lem6889542 (_91988 : int) : (term97 _91988) = term60.
Proof. exact (TRANS (@lem6889540 _91988) (@lem6889541)). Qed.
Lemma lem6889543 (_91988 : int) : (term83 _91988) = term60.
Proof. exact (TRANS (@lem6889428 _91988) (@lem6889542 _91988)). Qed.
Lemma lem6889545 (_91988 : int) : (term82 _91988) = term60.
Proof. exact (TRANS (@lem6889383 _91988) (@lem6889543 _91988)). Qed.
Lemma lem6889546 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6889547 (_91988 : int) : (term128 _91988) = term129.
Proof. exact (MK_COMB (@lem6889546) (@lem6889545 _91988)). Qed.
Lemma lem6889548 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6889549 (_91988 : int) : (term81 _91988) = term130.
Proof. exact (MK_COMB (@lem6889547 _91988) (@lem6889548)). Qed.
Lemma lem6889550 (_91988 : int) : (term48 _91988) = term130.
Proof. exact (TRANS (@lem6889371 _91988) (@lem6889549 _91988)). Qed.
Lemma lem6889551 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6889552 (_91988 : int) : (term49 _91988) = (term131 _91988).
Proof. exact (MK_COMB (@lem6889551) (@lem6889370 _91988)). Qed.
Lemma lem6889553 (_91988 : int) : (term50 _91988) = (term132 _91988).
Proof. exact (MK_COMB (@lem6889552 _91988) (@lem6889550 _91988)). Qed.
Lemma lem6889568 (_91988 : int) : (term52 _91988) = (term132 _91988).
Proof. exact (TRANS (@lem6889322 _91988) (@lem6889553 _91988)). Qed.
Lemma lem6889572 (_91988 : int) (h1 : term132 _91988) : term132 _91988.
Proof. exact (h1). Qed.
Lemma lem6889573 (_91988 : int) (h1 : term132 _91988) : term130.
Proof. exact (proj2 (@lem6889572 _91988 h1)). Qed.
Lemma lem6889576 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6889577 : term130 = term133.
Proof. exact (@lem6889576 term31 term60). Qed.
Lemma lem6889579 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6889580 : term60 = term61.
Proof. exact (@lem6889579 term8). Qed.
Lemma lem6889582 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6889583 : term31 = term57.
Proof. exact (@lem6889582 (NUMERAL 0)). Qed.
Lemma lem6889584 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6889585 : term33 = term134.
Proof. exact (MK_COMB (@lem6889584) (@lem6889583)). Qed.
Lemma lem6889586 : term133 = term135.
Proof. exact (MK_COMB (@lem6889585) (@lem6889580)). Qed.
Lemma lem6889587 : term136.
Proof. exact (@lem1980026 term31 term43 term60 term43). Qed.
Lemma lem6889589 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6889590 : term108 = term109.
Proof. exact (@lem6889589 (NUMERAL 0) term8). Qed.
Lemma lem6889591 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6889592 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6889593 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6889592 h1) (fun h1 : term109 = True => @lem6889591)). Qed.
Lemma lem6889594 : term109 = True.
Proof. exact (EQ_MP (@lem6889593) (@lem6889591)). Qed.
Lemma lem6889595 : term108 = True.
Proof. exact (TRANS (@lem6889590) (@lem6889594)). Qed.
Lemma lem6889596 : True = term108.
Proof. exact (SYM (@lem6889595)). Qed.
Lemma lem6889597 : term108.
Proof. exact (EQ_MP (@lem6889596) (@lem0)). Qed.
Lemma lem6889598 : term137.
Proof. exact (@lem6889587 (@lem6889597)). Qed.
Lemma lem6889600 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6889601 : term108 = term109.
Proof. exact (@lem6889600 (NUMERAL 0) term8). Qed.
Lemma lem6889602 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6889603 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6889604 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6889603 h1) (fun h1 : term109 = True => @lem6889602)). Qed.
Lemma lem6889605 : term109 = True.
Proof. exact (EQ_MP (@lem6889604) (@lem6889602)). Qed.
Lemma lem6889606 : term108 = True.
Proof. exact (TRANS (@lem6889601) (@lem6889605)). Qed.
Lemma lem6889607 : True = term108.
Proof. exact (SYM (@lem6889606)). Qed.
Lemma lem6889608 : term108.
Proof. exact (EQ_MP (@lem6889607) (@lem0)). Qed.
Lemma lem6889609 : term135 = term138.
Proof. exact (@lem6889598 (@lem6889608)). Qed.
Lemma lem6889611 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6889612 : term87 = term92.
Proof. exact (@lem6889611 term8 term8). Qed.
Lemma lem6889613 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6889614 : term72 = term8.
Proof. exact (EQ_MP (@lem6889613) (@lem940073)). Qed.
Lemma lem6889615 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6889616 : term70 = term43.
Proof. exact (MK_COMB (@lem6889615) (@lem6889614)). Qed.
Lemma lem6889617 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6889618 : term92 = term60.
Proof. exact (MK_COMB (@lem6889617) (@lem6889616)). Qed.
Lemma lem6889619 : term87 = term60.
Proof. exact (TRANS (@lem6889612) (@lem6889618)). Qed.
Lemma lem6889621 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6889622 : term120 = term31.
Proof. exact (@lem6889621 term8). Qed.
Lemma lem6889623 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6889624 : term139 = term33.
Proof. exact (MK_COMB (@lem6889623) (@lem6889622)). Qed.
Lemma lem6889625 : term138 = term133.
Proof. exact (MK_COMB (@lem6889624) (@lem6889619)). Qed.
Lemma lem6889627 (m : nat) (n : nat) : (term140 m n) = (term141 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6889628 : term133 = term142.
Proof. exact (@lem6889627 (NUMERAL 0) term8). Qed.
Lemma lem6889629 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6889630 (h1 : term110 = (BIT1 0)) : (term8 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6889631 : (term110 = (BIT1 0)) = ((term8 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6889630 h1) (fun h1 : (term8 = (NUMERAL 0)) = False => @lem6889629)). Qed.
Lemma lem6889632 : (term8 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6889631) (@lem6889629)). Qed.
Lemma lem6889633 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6889634 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6889635 : term143 = (and True).
Proof. exact (MK_COMB (@lem6889634) (@lem6889633)). Qed.
Lemma lem6889636 : term142 = (True /\ False).
Proof. exact (MK_COMB (@lem6889635) (@lem6889632)). Qed.
Lemma lem6889638 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6889639 : term142 = False.
Proof. exact (TRANS (@lem6889636) (@lem6889638)). Qed.
Lemma lem6889640 : term133 = False.
Proof. exact (TRANS (@lem6889628) (@lem6889639)). Qed.
Lemma lem6889641 : term138 = False.
Proof. exact (TRANS (@lem6889625) (@lem6889640)). Qed.
Lemma lem6889642 : term135 = False.
Proof. exact (TRANS (@lem6889609) (@lem6889641)). Qed.
Lemma lem6889643 : term133 = False.
Proof. exact (TRANS (@lem6889586) (@lem6889642)). Qed.
Lemma lem6889644 : term130 = False.
Proof. exact (TRANS (@lem6889577) (@lem6889643)). Qed.
Lemma lem6889645 (_91988 : int) (h1 : term132 _91988) : False.
Proof. exact (EQ_MP (@lem6889644) (@lem6889573 _91988 h1)). Qed.
Lemma lem6889647 (_91988 : int) (h1 : term132 _91988) : term132 _91988.
Proof. exact (h1). Qed.
Lemma lem6889648 (_91988 : int) (h1 : term132 _91988) : (term132 _91988) = False.
Proof. exact (prop_ext (fun h2 : term132 _91988 => @lem6889645 _91988 h1) (fun h2 : False => @lem6889647 _91988 h1)). Qed.
Lemma lem6889649 (_91988 : int) (h1 : term132 _91988) : False.
Proof. exact (EQ_MP (@lem6889648 _91988 h1) (@lem6889647 _91988 h1)). Qed.
Lemma lem6889650 (_91988 : int) (h1 : term52 _91988) : term52 _91988.
Proof. exact (h1). Qed.
Lemma lem6889651 (_91988 : int) (h1 : term52 _91988) : term132 _91988.
Proof. exact (EQ_MP (@lem6889568 _91988) (@lem6889650 _91988 h1)). Qed.
Lemma lem6889652 (_91988 : int) (h1 : term52 _91988) : (term132 _91988) = False.
Proof. exact (prop_ext (fun h2 : term132 _91988 => @lem6889649 _91988 h2) (fun h2 : False => @lem6889651 _91988 h1)). Qed.
Lemma lem6889653 (_91988 : int) (h1 : term52 _91988) : False.
Proof. exact (EQ_MP (@lem6889652 _91988 h1) (@lem6889651 _91988 h1)). Qed.
Lemma lem6889654 (_91988 : int) : term144 _91988.
Proof. exact (fun h0 : term52 _91988 => @lem6889653 _91988 h0). Qed.
Lemma lem6889655 (_91988 : int) : term145 _91988.
Proof. exact (@lem1386578 (term146 _91988)). Qed.
Lemma lem6889658 (_91988 : int) : term146 _91988.
Proof. exact (@lem6889655 _91988 (@lem6889654 _91988)). Qed.
Lemma lem6889659 (_91988 : int) : (term50 _91988) = (term23 _91988).
Proof. exact (SYM (@lem6889302 _91988)). Qed.
Lemma lem6889660 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6889661 (_91988 : int) : (term146 _91988) = (term16 _91988).
Proof. exact (MK_COMB (@lem6889660) (@lem6889659 _91988)). Qed.
Lemma lem6889662 (_91988 : int) : term16 _91988.
Proof. exact (EQ_MP (@lem6889661 _91988) (@lem6889658 _91988)). Qed.
Lemma lem6889663 (_91988 : int) : term17 _91988.
Proof. exact (EQ_MP (@lem6889243 _91988) (@lem6889662 _91988)). Qed.
Lemma lem6889664 (m : nat) : term147 m.
Proof. exact (@lem6889663 (int_of_num m)). Qed.
Lemma lem6889665 (m : nat) : term13 m.
Proof. exact (@lem6889664 m (@lem6889242 m)). Qed.
Lemma lem6889666 (m : nat) : (term13 m) = (term12 m).
Proof. exact (SYM (@lem6889239 m)). Qed.
Lemma lem6889667 (m : nat) : term12 m.
Proof. exact (EQ_MP (@lem6889666 m) (@lem6889665 m)). Qed.
Lemma lem6889668 (m : nat) : term148 m.
Proof. exact (@lem82 (term1 m)). Qed.
Lemma lem6889670 (m : nat) : term149 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem6889671 (m : nat) : (term149 m) = (term150 m).
Proof. exact (eq_refl (term149 m)). Qed.
Lemma lem6889672 (m : nat) : term150 m.
Proof. exact (EQ_MP (@lem6889671 m) (@lem6889670 m)). Qed.
Lemma lem6889673 (m : nat) (n : nat) : term151 m n.
Proof. exact (@lem6889672 m n). Qed.
Lemma lem6889674 (m : nat) (n : nat) : (term151 m n) = (term152 m n).
Proof. exact (eq_refl (term151 m n)). Qed.
Lemma lem6889675 (m : nat) (n : nat) : term152 m n.
Proof. exact (EQ_MP (@lem6889674 m n) (@lem6889673 m n)). Qed.
Lemma lem6889676 (m : nat) (n : nat) (p : nat) : term153 m n p.
Proof. exact (@lem6889675 m n p). Qed.
Lemma lem6889677 (m : nat) (p : nat) (n : nat) : (term153 m n p) = ((term154 p m n) = (term155 m p n)).
Proof. exact (eq_refl (term153 m n p)). Qed.
Lemma lem6889679 (m : nat) : term149 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem6889680 (m : nat) : (term149 m) = (term150 m).
Proof. exact (eq_refl (term149 m)). Qed.
Lemma lem6889681 (m : nat) : term150 m.
Proof. exact (EQ_MP (@lem6889680 m) (@lem6889679 m)). Qed.
Lemma lem6889682 (m : nat) (n : nat) : term151 m n.
Proof. exact (@lem6889681 m n). Qed.
Lemma lem6889683 (m : nat) (n : nat) : (term151 m n) = (term152 m n).
Proof. exact (eq_refl (term151 m n)). Qed.
Lemma lem6889684 (m : nat) (n : nat) : term152 m n.
Proof. exact (EQ_MP (@lem6889683 m n) (@lem6889682 m n)). Qed.
Lemma lem6889685 (m : nat) (n : nat) (p : nat) : term153 m n p.
Proof. exact (@lem6889684 m n p). Qed.
Lemma lem6889686 (m : nat) (p : nat) (n : nat) : (term153 m n p) = ((term154 p m n) = (term155 m p n)).
Proof. exact (eq_refl (term153 m n p)). Qed.
Lemma lem6889688 (m : nat) : term156 m.
Proof. exact (@lem5329299 m). Qed.
Lemma lem6889689 (m : nat) : (term156 m) = (term157 m).
Proof. exact (eq_refl (term156 m)). Qed.
Lemma lem6889690 (m : nat) : term157 m.
Proof. exact (EQ_MP (@lem6889689 m) (@lem6889688 m)). Qed.
Lemma lem6889691 (m : nat) (n : nat) : term158 m n.
Proof. exact (@lem6889690 m n). Qed.
Lemma lem6889692 (m : nat) (n : nat) : (term158 m n) = (term159 m n).
Proof. exact (eq_refl (term158 m n)). Qed.
Lemma lem6889693 (m : nat) (n : nat) : term159 m n.
Proof. exact (EQ_MP (@lem6889692 m n) (@lem6889691 m n)). Qed.
Lemma lem6889694 (m : nat) (n : nat) : (term159 m n) = ((term159 m n) = True).
Proof. exact (@lem7 (term159 m n)). Qed.
Lemma lem6889696 {A : Type'} (s : A -> Prop) : term160 A s.
Proof. exact (@lem3603906 A s). Qed.
Lemma lem6889697 {A : Type'} (s : A -> Prop) : (term160 A s) = (term161 A s).
Proof. exact (eq_refl (term160 A s)). Qed.
Lemma lem6889698 {A : Type'} (s : A -> Prop) : term161 A s.
Proof. exact (EQ_MP (@lem6889697 A s) (@lem6889696 A s)). Qed.
Lemma lem6889699 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term162 A s P.
Proof. exact (@lem6889698 A s P). Qed.
Lemma lem6889700 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term162 A s P) = (term163 A s P).
Proof. exact (eq_refl (term162 A s P)). Qed.
Lemma lem6889701 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term163 A s P.
Proof. exact (EQ_MP (@lem6889700 A s P) (@lem6889699 A s P)). Qed.
Lemma lem6889702 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6889703 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : term164 A s P.
Proof. exact (@lem6889701 A s P (@lem6889702 A s h1)). Qed.
Lemma lem6889704 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term164 A s P) = ((term164 A s P) = True).
Proof. exact (@lem7 (term164 A s P)). Qed.
Lemma lem6889705 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term164 A s P) = True.
Proof. exact (EQ_MP (@lem6889704 A s P) (@lem6889703 A P s h1)). Qed.
Lemma lem6889721 {A : Type'} : term165 A.
Proof. exact (@lem6774661 A nat). Qed.
Lemma lem6889722 {A : Type'} (dom : A -> Prop) : term166 A dom.
Proof. exact (@lem6889721 A dom). Qed.
Lemma lem6889723 {A : Type'} (dom : A -> Prop) : (term166 A dom) = (term167 A dom).
Proof. exact (eq_refl (term166 A dom)). Qed.
Lemma lem6889724 {A : Type'} (dom : A -> Prop) : term167 A dom.
Proof. exact (EQ_MP (@lem6889723 A dom) (@lem6889722 A dom)). Qed.
Lemma lem6889725 {A : Type'} (dom : A -> Prop) (neut : A) : term168 A dom neut.
Proof. exact (@lem6889724 A dom neut). Qed.
Lemma lem6889726 {A : Type'} (dom : A -> Prop) (neut : A) : (term168 A dom neut) = (term169 A dom neut).
Proof. exact (eq_refl (term168 A dom neut)). Qed.
Lemma lem6889727 {A : Type'} (dom : A -> Prop) (neut : A) : term169 A dom neut.
Proof. exact (EQ_MP (@lem6889726 A dom neut) (@lem6889725 A dom neut)). Qed.
Lemma lem6889728 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : term170 A dom neut op.
Proof. exact (@lem6889727 A dom neut op). Qed.
Lemma lem6889729 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : (term170 A dom neut op) = (term171 A dom neut op).
Proof. exact (eq_refl (term170 A dom neut op)). Qed.
Lemma lem6889730 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : term171 A dom neut op.
Proof. exact (EQ_MP (@lem6889729 A dom neut op) (@lem6889728 A dom neut op)). Qed.
Lemma lem6889731 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : term172 A dom neut op.
Proof. exact (@lem6889730 A dom neut op Peano.le). Qed.
Lemma lem6889732 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : (term172 A dom neut op) = (term173 A dom neut op).
Proof. exact (eq_refl (term172 A dom neut op)). Qed.
Lemma lem6889733 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : term173 A dom neut op.
Proof. exact (EQ_MP (@lem6889732 A dom neut op) (@lem6889731 A dom neut op)). Qed.
Lemma lem6889734 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) : term174 A dom neut op f.
Proof. exact (@lem6889733 A dom neut op f). Qed.
Lemma lem6889735 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) : (term174 A dom neut op f) = (term175 A dom neut op f).
Proof. exact (eq_refl (term174 A dom neut op f)). Qed.
Lemma lem6889736 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) : term175 A dom neut op f.
Proof. exact (EQ_MP (@lem6889735 A dom neut op f) (@lem6889734 A dom neut op f)). Qed.
Lemma lem6889737 {A : Type'} (_474 : A) (_475 : Prop) (_476 : A -> Prop) (_477 : A) : (term176 A _476 _475 _474 _477) = (term177 A _474 _475 _476 _477).
Proof. exact (@lem13473 A _474 _475 _476 _477). Qed.
Lemma lem6889738 {A : Type'} (_474 : A) (_475 : Prop) (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (_477 : A) : (term178 A dom neut op m n f _475 _474 _477) = (term179 A _474 _475 dom neut op m n f _477).
Proof. exact (@lem6889737 A _474 _475 (term180 A dom neut op m n f) _477). Qed.
Lemma lem6889739 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term181 A dom op m n f neut) = (term182 A dom op m n f neut).
Proof. exact (@lem6889738 A (term183 A dom neut op m n f) (Peano.le m n) dom neut op m n f neut). Qed.
Lemma lem6889740 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term184 A dom op m n f neut) = (term185 A dom op m n f neut).
Proof. exact (eq_refl (term184 A dom op m n f neut)). Qed.
Lemma lem6889741 (m : nat) (n : nat) : (term186 m n) = (term186 m n).
Proof. exact (eq_refl (term186 m n)). Qed.
Lemma lem6889742 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term187 A dom op m n f neut) = (term188 A dom op m n f neut).
Proof. exact (MK_COMB (@lem6889741 m n) (@lem6889740 A dom op m n f neut)). Qed.
Lemma lem6889743 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : (term189 A dom neut op m n f) = (term190 A dom neut op m n f).
Proof. exact (eq_refl (term189 A dom neut op m n f)). Qed.
Lemma lem6889744 (m : nat) (n : nat) : (term191 m n) = (term191 m n).
Proof. exact (eq_refl (term191 m n)). Qed.
Lemma lem6889745 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : (term192 A dom neut op m n f) = (term193 A dom neut op m n f).
Proof. exact (MK_COMB (@lem6889744 m n) (@lem6889743 A dom neut op m n f)). Qed.
Lemma lem6889746 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6889747 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : (term194 A dom neut op m n f) = (term195 A dom neut op m n f).
Proof. exact (MK_COMB (@lem6889746) (@lem6889745 A dom neut op m n f)). Qed.
Lemma lem6889748 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term182 A dom op m n f neut) = (term196 A dom op m n f neut).
Proof. exact (MK_COMB (@lem6889747 A dom neut op m n f) (@lem6889742 A dom op m n f neut)). Qed.
Lemma lem6889749 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term181 A dom op m n f neut) = (term197 A dom op m n f neut).
Proof. exact (eq_refl (term181 A dom op m n f neut)). Qed.
Lemma lem6889750 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6889751 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term198 A dom op m n f neut) = (term199 A dom op m n f neut).
Proof. exact (MK_COMB (@lem6889750) (@lem6889749 A dom op m n f neut)). Qed.
Lemma lem6889752 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : ((term181 A dom op m n f neut) = (term182 A dom op m n f neut)) = ((term197 A dom op m n f neut) = (term196 A dom op m n f neut)).
Proof. exact (MK_COMB (@lem6889751 A dom op m n f neut) (@lem6889748 A dom op m n f neut)). Qed.
Lemma lem6889753 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term197 A dom op m n f neut) = (term196 A dom op m n f neut).
Proof. exact (EQ_MP (@lem6889752 A dom op m n f neut) (@lem6889739 A dom op m n f neut)). Qed.
Lemma lem6889754 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term196 A dom op m n f neut) = (term197 A dom op m n f neut).
Proof. exact (SYM (@lem6889753 A dom op m n f neut)). Qed.
Lemma lem6889755 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem6889772 (m : nat) (n : nat) (h1 : term200 m n) : term200 m n.
Proof. exact (h1). Qed.
Lemma lem6889789 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (h1 : term175 A dom neut op f) : term175 A dom neut op f.
Proof. exact (h1). Qed.
Lemma lem6889794 (m : nat) (n : nat) (h1 : (term201 m n) = (dotdot m n)) : (term201 m n) = (dotdot m n).
Proof. exact (h1). Qed.
Lemma lem6889795 (m : nat) (n : nat) (h1 : (term201 m n) = (dotdot m n)) : (dotdot m n) = (term201 m n).
Proof. exact (SYM (@lem6889794 m n h1)). Qed.
Lemma lem6889796 (m : nat) (n : nat) (h1 : (dotdot m n) = (term201 m n)) : (dotdot m n) = (term201 m n).
Proof. exact (h1). Qed.
Lemma lem6889797 (m : nat) (n : nat) (h1 : (dotdot m n) = (term201 m n)) : (term201 m n) = (dotdot m n).
Proof. exact (SYM (@lem6889796 m n h1)). Qed.
Lemma lem6889798 (m : nat) (n : nat) : ((term201 m n) = (dotdot m n)) = ((dotdot m n) = (term201 m n)).
Proof. exact (prop_ext (fun h1 : (term201 m n) = (dotdot m n) => @lem6889795 m n h1) (fun h1 : (dotdot m n) = (term201 m n) => @lem6889797 m n h1)). Qed.
Lemma lem6889799 (m : nat) (n : nat) : (term191 m n) = (term191 m n).
Proof. exact (eq_refl (term191 m n)). Qed.
Lemma lem6889800 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (MK_COMB (@lem6889799 m n) (@lem6889798 m n)). Qed.
Lemma lem6889801 (m : nat) : (term204 m) = (term205 m).
Proof. exact (fun_ext (fun n : nat => @lem6889800 m n)). Qed.
Lemma lem6889802 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6889803 (m : nat) : (term206 m) = (term207 m).
Proof. exact (MK_COMB (@lem6889802) (@lem6889801 m)). Qed.
Lemma lem6889804 : term208 = term209.
Proof. exact (fun_ext (fun m : nat => @lem6889803 m)). Qed.
Lemma lem6889805 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6889806 : term210 = term211.
Proof. exact (MK_COMB (@lem6889805) (@lem6889804)). Qed.
Lemma lem6889807 : term211.
Proof. exact (EQ_MP (@lem6889806) (@lem5357842)). Qed.
Lemma lem6889808 (m : nat) : term212 m.
Proof. exact (@lem6889807 m). Qed.
Lemma lem6889809 (m : nat) : (term212 m) = (term207 m).
Proof. exact (eq_refl (term212 m)). Qed.
Lemma lem6889810 (m : nat) : term207 m.
Proof. exact (EQ_MP (@lem6889809 m) (@lem6889808 m)). Qed.
Lemma lem6889811 (m : nat) (n : nat) : term213 m n.
Proof. exact (@lem6889810 m n). Qed.
Lemma lem6889812 (m : nat) (n : nat) : (term213 m n) = (term203 m n).
Proof. exact (eq_refl (term213 m n)). Qed.
Lemma lem6889813 (m : nat) (n : nat) : term203 m n.
Proof. exact (EQ_MP (@lem6889812 m n) (@lem6889811 m n)). Qed.
Lemma lem6889814 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem6889815 (m : nat) (n : nat) (h1 : Peano.le m n) : (dotdot m n) = (term201 m n).
Proof. exact (@lem6889813 m n (@lem6889814 m n h1)). Qed.
Lemma lem6889821 (m : nat) (n : nat) : (Peano.le m n) = ((Peano.le m n) = True).
Proof. exact (@lem7 (Peano.le m n)). Qed.
Lemma lem6889826 (m : nat) (n : nat) : term203 m n.
Proof. exact (fun h0 : Peano.le m n => @lem6889815 m n h0). Qed.
Lemma lem6889828 (m : nat) (n : nat) (h1 : Peano.le m n) : (Peano.le m n) = True.
Proof. exact (EQ_MP (@lem6889821 m n) (@lem6889755 m n h1)). Qed.
Lemma lem6889829 (m : nat) (n : nat) (h1 : Peano.le m n) : True = (Peano.le m n).
Proof. exact (SYM (@lem6889828 m n h1)). Qed.
Lemma lem6889830 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (EQ_MP (@lem6889829 m n h1) (@lem0)). Qed.
Lemma lem6889831 (m : nat) (n : nat) (h1 : Peano.le m n) : (dotdot m n) = (term201 m n).
Proof. exact (@lem6889826 m n (@lem6889830 m n h1)). Qed.
Lemma lem6889837 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : (@iterato A nat dom neut op Peano.le) = (@iterato A nat dom neut op Peano.le).
Proof. exact (eq_refl (@iterato A nat dom neut op Peano.le)). Qed.
Lemma lem6889838 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (h1 : Peano.le m n) : (term214 A dom neut op m n) = (term215 A dom neut op m n).
Proof. exact (MK_COMB (@lem6889837 A dom neut op) (@lem6889831 m n h1)). Qed.
Lemma lem6889844 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6889845 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (m : nat) (n : nat) (h1 : Peano.le m n) : (term216 A dom neut op m n f) = (term217 A dom neut op m n f).
Proof. exact (MK_COMB (@lem6889838 A dom neut op m n h1) (@lem6889844 A f)). Qed.
Lemma lem6889851 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem6889852 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (m : nat) (n : nat) (h1 : Peano.le m n) : (term218 A dom neut op m n f) = (term219 A dom neut op m n f).
Proof. exact (MK_COMB (@lem6889851 A) (@lem6889845 A dom neut op f m n h1)). Qed.
Lemma lem6889970 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : (term183 A dom neut op m n f) = (term183 A dom neut op m n f).
Proof. exact (eq_refl (term183 A dom neut op m n f)). Qed.
Lemma lem6889971 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (m : nat) (n : nat) (h1 : Peano.le m n) : ((term216 A dom neut op m n f) = (term183 A dom neut op m n f)) = ((term217 A dom neut op m n f) = (term183 A dom neut op m n f)).
Proof. exact (MK_COMB (@lem6889852 A dom neut op f m n h1) (@lem6889970 A dom neut op m n f)). Qed.
Lemma lem6890091 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (m : nat) (n : nat) (h1 : Peano.le m n) : ((term217 A dom neut op m n f) = (term183 A dom neut op m n f)) = ((term216 A dom neut op m n f) = (term183 A dom neut op m n f)).
Proof. exact (SYM (@lem6889971 A dom neut op f m n h1)). Qed.
Lemma lem6890092 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (h1 : term175 A dom neut op f) : term175 A dom neut op f.
Proof. exact (h1). Qed.
Lemma lem6890093 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (h1 : term175 A dom neut op f) : (@iterato A nat dom neut op Peano.le (@EMPTY nat) f) = neut.
Proof. exact (proj1 (@lem6890092 A dom neut op f h1)). Qed.
Lemma lem6890095 (p : Prop) : p = (term220 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6890096 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term221 A dom op m n f neut) = (term222 A dom op m n f neut).
Proof. exact (@lem6890095 (term221 A dom op m n f neut)). Qed.
Lemma lem6890097 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term222 A dom op m n f neut) = (term221 A dom op m n f neut).
Proof. exact (SYM (@lem6890096 A dom op m n f neut)). Qed.
Lemma lem6890098 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term223 A dom op m n f neut) : term223 A dom op m n f neut.
Proof. exact (h1). Qed.
Lemma lem6890101 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term224 A dom op m n f neut) : term224 A dom op m n f neut.
Proof. exact (h1). Qed.
Lemma lem6890102 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : term225 A dom op m n f neut.
Proof. exact (fun h0 : term224 A dom op m n f neut => @lem6890101 A dom op m n f neut h0). Qed.
Lemma lem6890103 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term225 A dom op m n f neut) : term225 A dom op m n f neut.
Proof. exact (h1). Qed.
Lemma lem6890104 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term224 A dom op m n f neut) : term224 A dom op m n f neut.
Proof. exact (h1). Qed.
Lemma lem6890105 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term224 A dom op m n f neut) (h2 : term225 A dom op m n f neut) : term224 A dom op m n f neut.
Proof. exact (@lem6890103 A dom op m n f neut h2 (@lem6890104 A dom op m n f neut h1)). Qed.
Lemma lem6890106 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term224 A dom op m n f neut) : term226 A dom op m n f neut.
Proof. exact (fun h0 : term225 A dom op m n f neut => @lem6890105 A dom op m n f neut h1 h0). Qed.
Lemma lem6890107 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term225 A dom op m n f neut) : term225 A dom op m n f neut.
Proof. exact (h1). Qed.
Lemma lem6890108 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term224 A dom op m n f neut) (h2 : term225 A dom op m n f neut) : term224 A dom op m n f neut.
Proof. exact (@lem6890106 A dom op m n f neut h1 (@lem6890107 A dom op m n f neut h2)). Qed.
Lemma lem6890109 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term225 A dom op m n f neut) : term225 A dom op m n f neut.
Proof. exact (fun h0 : term224 A dom op m n f neut => @lem6890108 A dom op m n f neut h0 h1). Qed.
Lemma lem6890110 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : term227 A dom op m n f neut.
Proof. exact (fun h0 : term225 A dom op m n f neut => @lem6890109 A dom op m n f neut h0). Qed.
Lemma lem6890113 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : term225 A dom op m n f neut.
Proof. exact (@lem6890110 A dom op m n f neut (@lem6890102 A dom op m n f neut)). Qed.
Lemma lem6890114 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : term225 A dom op m n f neut.
Proof. exact (@lem6890113 A dom op m n f neut). Qed.
Lemma lem6890156 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6890157 : term228 = term229.
Proof. exact (@lem6890156 term230). Qed.
Lemma lem6890166 : term231 = term231.
Proof. exact (eq_refl term231). Qed.
Lemma lem6890167 : term232 = term233.
Proof. exact (MK_COMB (@lem6890166) (@lem6890157)). Qed.
Lemma lem6890170 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term234 A dom op m n f neut) = (term234 A dom op m n f neut).
Proof. exact (eq_refl (term234 A dom op m n f neut)). Qed.
Lemma lem6890171 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term235 A dom op m n f neut) = (term236 A dom op m n f neut).
Proof. exact (MK_COMB (@lem6890170 A dom op m n f neut) (@lem6890167)). Qed.
Lemma lem6890174 (m : nat) (n : nat) : (term186 m n) = (term186 m n).
Proof. exact (eq_refl (term186 m n)). Qed.
Lemma lem6890175 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term224 A dom op m n f neut) = (term237 A dom op m n f neut).
Proof. exact (MK_COMB (@lem6890174 m n) (@lem6890171 A dom op m n f neut)). Qed.
Lemma lem6890178 {A : Type'} (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term238 A op m n f neut) = (term239 A op m n f neut).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6890175 A dom op m n f neut)). Qed.
Lemma lem6890179 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6890180 {A : Type'} (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term240 A op m n f neut) = (term241 A op m n f neut).
Proof. exact (MK_COMB (@lem6890179 A) (@lem6890178 A op m n f neut)). Qed.
Lemma lem6890185 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term242 A m n f neut) = (term243 A m n f neut).
Proof. exact (fun_ext (fun op : type1400 A => @lem6890180 A op m n f neut)). Qed.
Lemma lem6890186 {A : Type'} : (@all (A -> A -> A)) = (@all (A -> A -> A)).
Proof. exact (eq_refl (@all (A -> A -> A))). Qed.
Lemma lem6890187 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term244 A m n f neut) = (term245 A m n f neut).
Proof. exact (MK_COMB (@lem6890186 A) (@lem6890185 A m n f neut)). Qed.
Lemma lem6890192 {A : Type'} (n : nat) (f : nat -> A) (neut : A) : (term246 A n f neut) = (term247 A n f neut).
Proof. exact (fun_ext (fun m : nat => @lem6890187 A m n f neut)). Qed.
Lemma lem6890193 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6890194 {A : Type'} (n : nat) (f : nat -> A) (neut : A) : (term248 A n f neut) = (term249 A n f neut).
Proof. exact (MK_COMB (@lem6890193) (@lem6890192 A n f neut)). Qed.
Lemma lem6890199 {A : Type'} (f : nat -> A) (neut : A) : (term250 A f neut) = (term251 A f neut).
Proof. exact (fun_ext (fun n : nat => @lem6890194 A n f neut)). Qed.
Lemma lem6890200 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6890201 {A : Type'} (f : nat -> A) (neut : A) : (term252 A f neut) = (term253 A f neut).
Proof. exact (MK_COMB (@lem6890200) (@lem6890199 A f neut)). Qed.
Lemma lem6890206 {A : Type'} (neut : A) : (term254 A neut) = (term255 A neut).
Proof. exact (fun_ext (fun f : nat -> A => @lem6890201 A f neut)). Qed.
Lemma lem6890207 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem6890208 {A : Type'} (neut : A) : (term256 A neut) = (term257 A neut).
Proof. exact (MK_COMB (@lem6890207 A) (@lem6890206 A neut)). Qed.
Lemma lem6890213 {A : Type'} : (term258 A) = (term259 A).
Proof. exact (fun_ext (fun neut : A => @lem6890208 A neut)). Qed.
Lemma lem6890214 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6890223 {A : Type'} : (term260 A) = (term261 A).
Proof. exact (MK_COMB (@lem6890214 A) (@lem6890213 A)). Qed.
Lemma lem6890228 (n : nat) (m : nat) : (((dotdot m n) = (@EMPTY nat)) = (Peano.lt n m)) = (((dotdot m n) = (@EMPTY nat)) = (Peano.lt n m)).
Proof. exact (eq_refl (((dotdot m n) = (@EMPTY nat)) = (Peano.lt n m))). Qed.
Lemma lem6890229 (m : nat) : (term262 m) = (term262 m).
Proof. exact (fun_ext (fun n : nat => @lem6890228 n m)). Qed.
Lemma lem6890230 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6890231 (m : nat) : (term263 m) = (term263 m).
Proof. exact (MK_COMB (@lem6890230) (@lem6890229 m)). Qed.
Lemma lem6890232 : term264 = term264.
Proof. exact (fun_ext (fun m : nat => @lem6890231 m)). Qed.
Lemma lem6890233 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6890234 : term230 = term230.
Proof. exact (MK_COMB (@lem6890233) (@lem6890232)). Qed.
Lemma lem6890235 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6890236 : term229 = term229.
Proof. exact (MK_COMB (@lem6890235) (@lem6890234)). Qed.
Lemma lem6890243 (n : nat) (m : nat) : ((term200 m n) = (Peano.lt n m)) = ((term200 m n) = (Peano.lt n m)).
Proof. exact (eq_refl ((term200 m n) = (Peano.lt n m))). Qed.
Lemma lem6890244 (m : nat) : (term265 m) = (term265 m).
Proof. exact (fun_ext (fun n : nat => @lem6890243 n m)). Qed.
Lemma lem6890245 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6890246 (m : nat) : (term266 m) = (term266 m).
Proof. exact (MK_COMB (@lem6890245) (@lem6890244 m)). Qed.
Lemma lem6890247 : term267 = term267.
Proof. exact (fun_ext (fun m : nat => @lem6890246 m)). Qed.
Lemma lem6890248 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6890249 : term268 = term268.
Proof. exact (MK_COMB (@lem6890248) (@lem6890247)). Qed.
Lemma lem6890250 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6890251 : term231 = term231.
Proof. exact (MK_COMB (@lem6890250) (@lem6890249)). Qed.
Lemma lem6890252 : term233 = term233.
Proof. exact (MK_COMB (@lem6890251) (@lem6890236)). Qed.
Lemma lem6890261 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term234 A dom op m n f neut) = (term234 A dom op m n f neut).
Proof. exact (eq_refl (term234 A dom op m n f neut)). Qed.
Lemma lem6890262 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term236 A dom op m n f neut) = (term236 A dom op m n f neut).
Proof. exact (MK_COMB (@lem6890261 A dom op m n f neut) (@lem6890252)). Qed.
Lemma lem6890267 (m : nat) (n : nat) : (term186 m n) = (term186 m n).
Proof. exact (eq_refl (term186 m n)). Qed.
Lemma lem6890268 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term237 A dom op m n f neut) = (term237 A dom op m n f neut).
Proof. exact (MK_COMB (@lem6890267 m n) (@lem6890262 A dom op m n f neut)). Qed.
Lemma lem6890269 {A : Type'} (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term239 A op m n f neut) = (term239 A op m n f neut).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6890268 A dom op m n f neut)). Qed.
Lemma lem6890270 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6890271 {A : Type'} (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term241 A op m n f neut) = (term241 A op m n f neut).
Proof. exact (MK_COMB (@lem6890270 A) (@lem6890269 A op m n f neut)). Qed.
Lemma lem6890272 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term243 A m n f neut) = (term243 A m n f neut).
Proof. exact (fun_ext (fun op : type1400 A => @lem6890271 A op m n f neut)). Qed.
Lemma lem6890273 {A : Type'} : (@all (A -> A -> A)) = (@all (A -> A -> A)).
Proof. exact (eq_refl (@all (A -> A -> A))). Qed.
Lemma lem6890274 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term245 A m n f neut) = (term245 A m n f neut).
Proof. exact (MK_COMB (@lem6890273 A) (@lem6890272 A m n f neut)). Qed.
Lemma lem6890275 {A : Type'} (n : nat) (f : nat -> A) (neut : A) : (term247 A n f neut) = (term247 A n f neut).
Proof. exact (fun_ext (fun m : nat => @lem6890274 A m n f neut)). Qed.
Lemma lem6890276 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6890277 {A : Type'} (n : nat) (f : nat -> A) (neut : A) : (term249 A n f neut) = (term249 A n f neut).
Proof. exact (MK_COMB (@lem6890276) (@lem6890275 A n f neut)). Qed.
Lemma lem6890278 {A : Type'} (f : nat -> A) (neut : A) : (term251 A f neut) = (term251 A f neut).
Proof. exact (fun_ext (fun n : nat => @lem6890277 A n f neut)). Qed.
Lemma lem6890279 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6890280 {A : Type'} (f : nat -> A) (neut : A) : (term253 A f neut) = (term253 A f neut).
Proof. exact (MK_COMB (@lem6890279) (@lem6890278 A f neut)). Qed.
Lemma lem6890281 {A : Type'} (neut : A) : (term255 A neut) = (term255 A neut).
Proof. exact (fun_ext (fun f : nat -> A => @lem6890280 A f neut)). Qed.
Lemma lem6890282 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem6890283 {A : Type'} (neut : A) : (term257 A neut) = (term257 A neut).
Proof. exact (MK_COMB (@lem6890282 A) (@lem6890281 A neut)). Qed.
Lemma lem6890284 {A : Type'} : (term259 A) = (term259 A).
Proof. exact (fun_ext (fun neut : A => @lem6890283 A neut)). Qed.
Lemma lem6890285 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6890286 {A : Type'} : (term261 A) = (term261 A).
Proof. exact (MK_COMB (@lem6890285 A) (@lem6890284 A)). Qed.
Lemma lem6890357 {A : Type'} : (term260 A) = (term261 A).
Proof. exact (TRANS (@lem6890223 A) (@lem6890286 A)). Qed.
Lemma lem6890358 {A : Type'} : (term261 A) = (term260 A).
Proof. exact (SYM (@lem6890357 A)). Qed.
Lemma lem6890360 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term223 A dom op m n f neut) : term223 A dom op m n f neut.
Proof. exact (h1). Qed.
Lemma lem6890361 (h1 : term268) : term268.
Proof. exact (h1). Qed.
Lemma lem6890362 (h1 : term230) : term230.
Proof. exact (h1). Qed.
Lemma lem6890368 (m : nat) (n : nat) (h1 : term200 m n) : term200 m n.
Proof. exact (h1). Qed.
Lemma lem6890379 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term223 A dom op m n f neut) = (term269 A dom op m n f neut).
Proof. exact (@lem17362 ((@iterato A nat dom neut op Peano.le (@EMPTY nat) f) = neut) ((term216 A dom neut op m n f) = neut)). Qed.
Lemma lem6890384 (m : nat) (n : nat) : (term270 m n) = (Peano.le m n).
Proof. exact (@lem16933 (Peano.le m n)). Qed.
Lemma lem6890386 (n : nat) (m : nat) : (Peano.lt n m) = (Peano.lt n m).
Proof. exact (eq_refl (Peano.lt n m)). Qed.
Lemma lem6890387 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6890388 (m : nat) (n : nat) : (term271 m n) = (term272 m n).
Proof. exact (MK_COMB (@lem6890387) (@lem6890384 m n)). Qed.
Lemma lem6890389 (n : nat) (m : nat) : (term273 n m) = (term274 n m).
Proof. exact (MK_COMB (@lem6890388 m n) (@lem6890386 n m)). Qed.
Lemma lem6890394 (n : nat) (m : nat) : (term275 n m) = (term275 n m).
Proof. exact (eq_refl (term275 n m)). Qed.
Lemma lem6890395 (n : nat) (m : nat) : (term276 n m) = (term277 n m).
Proof. exact (MK_COMB (@lem6890394 n m) (@lem6890389 n m)). Qed.
Lemma lem6890396 (n : nat) (m : nat) : ((term200 m n) = (Peano.lt n m)) = (term276 n m).
Proof. exact (@lem17784 (term200 m n) (Peano.lt n m)). Qed.
Lemma lem6890397 (n : nat) (m : nat) : ((term200 m n) = (Peano.lt n m)) = (term277 n m).
Proof. exact (TRANS (@lem6890396 n m) (@lem6890395 n m)). Qed.
Lemma lem6890398 (m : nat) : (term265 m) = (term278 m).
Proof. exact (fun_ext (fun n : nat => @lem6890397 n m)). Qed.
Lemma lem6890399 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6890400 (m : nat) : (term266 m) = (term279 m).
Proof. exact (MK_COMB (@lem6890399) (@lem6890398 m)). Qed.
Lemma lem6890401 : term267 = term280.
Proof. exact (fun_ext (fun m : nat => @lem6890400 m)). Qed.
Lemma lem6890402 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6890403 : term268 = term281.
Proof. exact (MK_COMB (@lem6890402) (@lem6890401)). Qed.
Lemma lem6890409 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term282 A P Q) = (term283 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6890410 (P : nat -> Prop) (Q : nat -> Prop) : (term284 P Q) = (term285 P Q).
Proof. exact (@lem6890409 nat P Q). Qed.
Lemma lem6890411 (m : nat) : (term286 m) = (term287 m).
Proof. exact (@lem6890410 (term288 m) (term289 m)). Qed.
Lemma lem6890412 (n : nat) (m : nat) : (term290 m n) = (term291 n m).
Proof. exact (eq_refl (term290 m n)). Qed.
Lemma lem6890413 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6890414 (n : nat) (m : nat) : (term292 m n) = (term275 n m).
Proof. exact (MK_COMB (@lem6890413) (@lem6890412 n m)). Qed.
Lemma lem6890415 (n : nat) (m : nat) : (term293 m n) = (term274 n m).
Proof. exact (eq_refl (term293 m n)). Qed.
Lemma lem6890416 (n : nat) (m : nat) : (term294 m n) = (term277 n m).
Proof. exact (MK_COMB (@lem6890414 n m) (@lem6890415 n m)). Qed.
Lemma lem6890417 (m : nat) : (term295 m) = (term278 m).
Proof. exact (fun_ext (fun n : nat => @lem6890416 n m)). Qed.
Lemma lem6890418 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6890419 (m : nat) : (term286 m) = (term279 m).
Proof. exact (MK_COMB (@lem6890418) (@lem6890417 m)). Qed.
Lemma lem6890420 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6890421 (m : nat) : (term296 m) = (term297 m).
Proof. exact (MK_COMB (@lem6890420) (@lem6890419 m)). Qed.
Lemma lem6890422 (n : nat) (m : nat) : (term290 m n) = (term291 n m).
Proof. exact (eq_refl (term290 m n)). Qed.
Lemma lem6890423 (m : nat) : (term298 m) = (term288 m).
Proof. exact (fun_ext (fun n : nat => @lem6890422 n m)). Qed.
Lemma lem6890424 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6890425 (m : nat) : (term299 m) = (term300 m).
Proof. exact (MK_COMB (@lem6890424) (@lem6890423 m)). Qed.
Lemma lem6890426 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6890427 (m : nat) : (term301 m) = (term302 m).
Proof. exact (MK_COMB (@lem6890426) (@lem6890425 m)). Qed.
Lemma lem6890428 (n : nat) (m : nat) : (term293 m n) = (term274 n m).
Proof. exact (eq_refl (term293 m n)). Qed.
Lemma lem6890429 (m : nat) : (term303 m) = (term289 m).
Proof. exact (fun_ext (fun n : nat => @lem6890428 n m)). Qed.
Lemma lem6890430 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6890431 (m : nat) : (term304 m) = (term305 m).
Proof. exact (MK_COMB (@lem6890430) (@lem6890429 m)). Qed.
Lemma lem6890432 (m : nat) : (term287 m) = (term306 m).
Proof. exact (MK_COMB (@lem6890427 m) (@lem6890431 m)). Qed.
Lemma lem6890433 (m : nat) : ((term286 m) = (term287 m)) = ((term279 m) = (term306 m)).
Proof. exact (MK_COMB (@lem6890421 m) (@lem6890432 m)). Qed.
Lemma lem6890434 (m : nat) : (term279 m) = (term306 m).
Proof. exact (EQ_MP (@lem6890433 m) (@lem6890411 m)). Qed.
Lemma lem6890531 : term280 = term307.
Proof. exact (fun_ext (fun m : nat => @lem6890434 m)). Qed.
Lemma lem6890532 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6890533 : term281 = term308.
Proof. exact (MK_COMB (@lem6890532) (@lem6890531)). Qed.
Lemma lem6890535 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term282 A P Q) = (term283 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6890536 (P : nat -> Prop) (Q : nat -> Prop) : (term284 P Q) = (term285 P Q).
Proof. exact (@lem6890535 nat P Q). Qed.
Lemma lem6890537 : term309 = term310.
Proof. exact (@lem6890536 term311 term312). Qed.
Lemma lem6890538 (m : nat) : (term313 m) = (term300 m).
Proof. exact (eq_refl (term313 m)). Qed.
Lemma lem6890539 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6890540 (m : nat) : (term314 m) = (term302 m).
Proof. exact (MK_COMB (@lem6890539) (@lem6890538 m)). Qed.
Lemma lem6890541 (m : nat) : (term315 m) = (term305 m).
Proof. exact (eq_refl (term315 m)). Qed.
Lemma lem6890542 (m : nat) : (term316 m) = (term306 m).
Proof. exact (MK_COMB (@lem6890540 m) (@lem6890541 m)). Qed.
Lemma lem6890543 : term317 = term307.
Proof. exact (fun_ext (fun m : nat => @lem6890542 m)). Qed.
Lemma lem6890544 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6890545 : term309 = term308.
Proof. exact (MK_COMB (@lem6890544) (@lem6890543)). Qed.
Lemma lem6890546 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6890547 : term318 = term319.
Proof. exact (MK_COMB (@lem6890546) (@lem6890545)). Qed.
Lemma lem6890548 (m : nat) : (term313 m) = (term300 m).
Proof. exact (eq_refl (term313 m)). Qed.
Lemma lem6890549 : term320 = term311.
Proof. exact (fun_ext (fun m : nat => @lem6890548 m)). Qed.
Lemma lem6890550 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6890551 : term321 = term322.
Proof. exact (MK_COMB (@lem6890550) (@lem6890549)). Qed.
Lemma lem6890552 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6890553 : term323 = term324.
Proof. exact (MK_COMB (@lem6890552) (@lem6890551)). Qed.
Lemma lem6890554 (m : nat) : (term315 m) = (term305 m).
Proof. exact (eq_refl (term315 m)). Qed.
Lemma lem6890555 : term325 = term312.
Proof. exact (fun_ext (fun m : nat => @lem6890554 m)). Qed.
Lemma lem6890556 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6890557 : term326 = term327.
Proof. exact (MK_COMB (@lem6890556) (@lem6890555)). Qed.
Lemma lem6890558 : term310 = term328.
Proof. exact (MK_COMB (@lem6890553) (@lem6890557)). Qed.
Lemma lem6890559 : (term309 = term310) = (term308 = term328).
Proof. exact (MK_COMB (@lem6890547) (@lem6890558)). Qed.
Lemma lem6890560 : term308 = term328.
Proof. exact (EQ_MP (@lem6890559) (@lem6890537)). Qed.
Lemma lem6890667 : term281 = term328.
Proof. exact (TRANS (@lem6890533) (@lem6890560)). Qed.
Lemma lem6890668 : term268 = term328.
Proof. exact (TRANS (@lem6890403) (@lem6890667)). Qed.
Lemma lem6890669 (h1 : term268) : term328.
Proof. exact (EQ_MP (@lem6890668) (@lem6890361 h1)). Qed.
Lemma lem6890684 (n : nat) (m : nat) : (((dotdot m n) = (@EMPTY nat)) = (Peano.lt n m)) = (term329 n m).
Proof. exact (@lem17784 ((dotdot m n) = (@EMPTY nat)) (Peano.lt n m)). Qed.
Lemma lem6890685 (m : nat) : (term262 m) = (term330 m).
Proof. exact (fun_ext (fun n : nat => @lem6890684 n m)). Qed.
Lemma lem6890686 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6890687 (m : nat) : (term263 m) = (term331 m).
Proof. exact (MK_COMB (@lem6890686) (@lem6890685 m)). Qed.
Lemma lem6890688 : term264 = term332.
Proof. exact (fun_ext (fun m : nat => @lem6890687 m)). Qed.
Lemma lem6890689 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6890690 : term230 = term333.
Proof. exact (MK_COMB (@lem6890689) (@lem6890688)). Qed.
Lemma lem6890696 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term282 A P Q) = (term283 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6890697 (P : nat -> Prop) (Q : nat -> Prop) : (term284 P Q) = (term285 P Q).
Proof. exact (@lem6890696 nat P Q). Qed.
Lemma lem6890698 (m : nat) : (term334 m) = (term335 m).
Proof. exact (@lem6890697 (term336 m) (term337 m)). Qed.
Lemma lem6890699 (n : nat) (m : nat) : (term338 m n) = (term339 n m).
Proof. exact (eq_refl (term338 m n)). Qed.
Lemma lem6890700 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6890701 (n : nat) (m : nat) : (term340 m n) = (term341 n m).
Proof. exact (MK_COMB (@lem6890700) (@lem6890699 n m)). Qed.
Lemma lem6890702 (n : nat) (m : nat) : (term342 m n) = (term343 n m).
Proof. exact (eq_refl (term342 m n)). Qed.
Lemma lem6890703 (n : nat) (m : nat) : (term344 m n) = (term329 n m).
Proof. exact (MK_COMB (@lem6890701 n m) (@lem6890702 n m)). Qed.
Lemma lem6890704 (m : nat) : (term345 m) = (term330 m).
Proof. exact (fun_ext (fun n : nat => @lem6890703 n m)). Qed.
Lemma lem6890705 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6890706 (m : nat) : (term334 m) = (term331 m).
Proof. exact (MK_COMB (@lem6890705) (@lem6890704 m)). Qed.
Lemma lem6890707 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6890708 (m : nat) : (term346 m) = (term347 m).
Proof. exact (MK_COMB (@lem6890707) (@lem6890706 m)). Qed.
Lemma lem6890709 (n : nat) (m : nat) : (term338 m n) = (term339 n m).
Proof. exact (eq_refl (term338 m n)). Qed.
Lemma lem6890710 (m : nat) : (term348 m) = (term336 m).
Proof. exact (fun_ext (fun n : nat => @lem6890709 n m)). Qed.
Lemma lem6890711 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6890712 (m : nat) : (term349 m) = (term350 m).
Proof. exact (MK_COMB (@lem6890711) (@lem6890710 m)). Qed.
Lemma lem6890713 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6890714 (m : nat) : (term351 m) = (term352 m).
Proof. exact (MK_COMB (@lem6890713) (@lem6890712 m)). Qed.
Lemma lem6890715 (n : nat) (m : nat) : (term342 m n) = (term343 n m).
Proof. exact (eq_refl (term342 m n)). Qed.
Lemma lem6890716 (m : nat) : (term353 m) = (term337 m).
Proof. exact (fun_ext (fun n : nat => @lem6890715 n m)). Qed.
Lemma lem6890717 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6890718 (m : nat) : (term354 m) = (term355 m).
Proof. exact (MK_COMB (@lem6890717) (@lem6890716 m)). Qed.
Lemma lem6890719 (m : nat) : (term335 m) = (term356 m).
Proof. exact (MK_COMB (@lem6890714 m) (@lem6890718 m)). Qed.
Lemma lem6890720 (m : nat) : ((term334 m) = (term335 m)) = ((term331 m) = (term356 m)).
Proof. exact (MK_COMB (@lem6890708 m) (@lem6890719 m)). Qed.
Lemma lem6890721 (m : nat) : (term331 m) = (term356 m).
Proof. exact (EQ_MP (@lem6890720 m) (@lem6890698 m)). Qed.
Lemma lem6890818 : term332 = term357.
Proof. exact (fun_ext (fun m : nat => @lem6890721 m)). Qed.
Lemma lem6890819 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6890820 : term333 = term358.
Proof. exact (MK_COMB (@lem6890819) (@lem6890818)). Qed.
Lemma lem6890822 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term282 A P Q) = (term283 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6890823 (P : nat -> Prop) (Q : nat -> Prop) : (term284 P Q) = (term285 P Q).
Proof. exact (@lem6890822 nat P Q). Qed.
Lemma lem6890824 : term359 = term360.
Proof. exact (@lem6890823 term361 term362). Qed.
Lemma lem6890825 (m : nat) : (term363 m) = (term350 m).
Proof. exact (eq_refl (term363 m)). Qed.
Lemma lem6890826 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6890827 (m : nat) : (term364 m) = (term352 m).
Proof. exact (MK_COMB (@lem6890826) (@lem6890825 m)). Qed.
Lemma lem6890828 (m : nat) : (term365 m) = (term355 m).
Proof. exact (eq_refl (term365 m)). Qed.
Lemma lem6890829 (m : nat) : (term366 m) = (term356 m).
Proof. exact (MK_COMB (@lem6890827 m) (@lem6890828 m)). Qed.
Lemma lem6890830 : term367 = term357.
Proof. exact (fun_ext (fun m : nat => @lem6890829 m)). Qed.
Lemma lem6890831 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6890832 : term359 = term358.
Proof. exact (MK_COMB (@lem6890831) (@lem6890830)). Qed.
Lemma lem6890833 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6890834 : term368 = term369.
Proof. exact (MK_COMB (@lem6890833) (@lem6890832)). Qed.
Lemma lem6890835 (m : nat) : (term363 m) = (term350 m).
Proof. exact (eq_refl (term363 m)). Qed.
Lemma lem6890836 : term370 = term361.
Proof. exact (fun_ext (fun m : nat => @lem6890835 m)). Qed.
Lemma lem6890837 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6890838 : term371 = term372.
Proof. exact (MK_COMB (@lem6890837) (@lem6890836)). Qed.
Lemma lem6890839 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6890840 : term373 = term374.
Proof. exact (MK_COMB (@lem6890839) (@lem6890838)). Qed.
Lemma lem6890841 (m : nat) : (term365 m) = (term355 m).
Proof. exact (eq_refl (term365 m)). Qed.
Lemma lem6890842 : term375 = term362.
Proof. exact (fun_ext (fun m : nat => @lem6890841 m)). Qed.
Lemma lem6890843 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6890844 : term376 = term377.
Proof. exact (MK_COMB (@lem6890843) (@lem6890842)). Qed.
Lemma lem6890845 : term360 = term378.
Proof. exact (MK_COMB (@lem6890840) (@lem6890844)). Qed.
Lemma lem6890846 : (term359 = term360) = (term358 = term378).
Proof. exact (MK_COMB (@lem6890834) (@lem6890845)). Qed.
Lemma lem6890847 : term358 = term378.
Proof. exact (EQ_MP (@lem6890846) (@lem6890824)). Qed.
Lemma lem6890954 : term333 = term378.
Proof. exact (TRANS (@lem6890820) (@lem6890847)). Qed.
Lemma lem6890955 : term230 = term378.
Proof. exact (TRANS (@lem6890690) (@lem6890954)). Qed.
Lemma lem6890956 (h1 : term230) : term378.
Proof. exact (EQ_MP (@lem6890955) (@lem6890362 h1)). Qed.
Lemma lem6890957 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6890964 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6890965 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem6890964 nat (nat -> Prop) f x). Qed.
Lemma lem6890966 (m : nat) : (Peano.le m) = (@I (nat -> nat -> Prop) Peano.le m).
Proof. exact (@lem6890965 Peano.le m). Qed.
Lemma lem6890967 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem6890968 (m : nat) (n : nat) : (Peano.le m n) = (@I (nat -> nat -> Prop) Peano.le m n).
Proof. exact (MK_COMB (@lem6890966 m) (@lem6890967 n)). Qed.
Lemma lem6890970 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6890971 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem6890970 nat Prop f x). Qed.
Lemma lem6890972 (m : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.le m n) = (term379 m n).
Proof. exact (@lem6890971 (@I (nat -> nat -> Prop) Peano.le m) n). Qed.
Lemma lem6890974 (m : nat) (n : nat) : (Peano.le m n) = (term379 m n).
Proof. exact (TRANS (@lem6890968 m n) (@lem6890972 m n)). Qed.
Lemma lem6890975 (m : nat) (n : nat) : (term200 m n) = (term380 m n).
Proof. exact (MK_COMB (@lem6890957) (@lem6890974 m n)). Qed.
Lemma lem6891020 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term223 A dom op m n f neut) : term269 A dom op m n f neut.
Proof. exact (EQ_MP (@lem6890379 A dom op m n f neut) (@lem6890360 A dom op m n f neut h1)). Qed.
Lemma lem6891025 (n : nat) (m : nat) : (Peano.lt n m) = (Peano.lt n m).
Proof. exact (eq_refl (Peano.lt n m)). Qed.
Lemma lem6891032 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6891033 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem6891032 nat (nat -> Prop) f x). Qed.
Lemma lem6891034 (m : nat) : (Peano.le m) = (@I (nat -> nat -> Prop) Peano.le m).
Proof. exact (@lem6891033 Peano.le m). Qed.
Lemma lem6891035 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem6891036 (m : nat) (n : nat) : (Peano.le m n) = (@I (nat -> nat -> Prop) Peano.le m n).
Proof. exact (MK_COMB (@lem6891034 m) (@lem6891035 n)). Qed.
Lemma lem6891038 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6891039 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem6891038 nat Prop f x). Qed.
Lemma lem6891040 (m : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.le m n) = (term379 m n).
Proof. exact (@lem6891039 (@I (nat -> nat -> Prop) Peano.le m) n). Qed.
Lemma lem6891042 (m : nat) (n : nat) : (Peano.le m n) = (term379 m n).
Proof. exact (TRANS (@lem6891036 m n) (@lem6891040 m n)). Qed.
Lemma lem6891043 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6891044 (m : nat) (n : nat) : (term272 m n) = (term381 m n).
Proof. exact (MK_COMB (@lem6891043) (@lem6891042 m n)). Qed.
Lemma lem6891045 (n : nat) (m : nat) : (term274 n m) = (term382 n m).
Proof. exact (MK_COMB (@lem6891044 m n) (@lem6891025 n m)). Qed.
Lemma lem6891046 (m : nat) : (term289 m) = (term383 m).
Proof. exact (fun_ext (fun n : nat => @lem6891045 n m)). Qed.
Lemma lem6891047 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6891048 (m : nat) : (term305 m) = (term384 m).
Proof. exact (MK_COMB (@lem6891047) (@lem6891046 m)). Qed.
Lemma lem6891049 : term312 = term385.
Proof. exact (fun_ext (fun m : nat => @lem6891048 m)). Qed.
Lemma lem6891050 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6891051 : term327 = term386.
Proof. exact (MK_COMB (@lem6891050) (@lem6891049)). Qed.
Lemma lem6891058 (n : nat) (m : nat) : (term387 n m) = (term387 n m).
Proof. exact (eq_refl (term387 n m)). Qed.
Lemma lem6891059 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6891066 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6891067 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem6891066 nat (nat -> Prop) f x). Qed.
Lemma lem6891068 (m : nat) : (Peano.le m) = (@I (nat -> nat -> Prop) Peano.le m).
Proof. exact (@lem6891067 Peano.le m). Qed.
Lemma lem6891069 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem6891070 (m : nat) (n : nat) : (Peano.le m n) = (@I (nat -> nat -> Prop) Peano.le m n).
Proof. exact (MK_COMB (@lem6891068 m) (@lem6891069 n)). Qed.
Lemma lem6891072 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6891073 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem6891072 nat Prop f x). Qed.
Lemma lem6891074 (m : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.le m n) = (term379 m n).
Proof. exact (@lem6891073 (@I (nat -> nat -> Prop) Peano.le m) n). Qed.
Lemma lem6891076 (m : nat) (n : nat) : (Peano.le m n) = (term379 m n).
Proof. exact (TRANS (@lem6891070 m n) (@lem6891074 m n)). Qed.
Lemma lem6891077 (m : nat) (n : nat) : (term200 m n) = (term380 m n).
Proof. exact (MK_COMB (@lem6891059) (@lem6891076 m n)). Qed.
Lemma lem6891078 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6891079 (m : nat) (n : nat) : (term388 m n) = (term389 m n).
Proof. exact (MK_COMB (@lem6891078) (@lem6891077 m n)). Qed.
Lemma lem6891080 (n : nat) (m : nat) : (term291 n m) = (term390 n m).
Proof. exact (MK_COMB (@lem6891079 m n) (@lem6891058 n m)). Qed.
Lemma lem6891081 (m : nat) : (term288 m) = (term391 m).
Proof. exact (fun_ext (fun n : nat => @lem6891080 n m)). Qed.
Lemma lem6891082 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6891083 (m : nat) : (term300 m) = (term392 m).
Proof. exact (MK_COMB (@lem6891082) (@lem6891081 m)). Qed.
Lemma lem6891084 : term311 = term393.
Proof. exact (fun_ext (fun m : nat => @lem6891083 m)). Qed.
Lemma lem6891085 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6891086 : term322 = term394.
Proof. exact (MK_COMB (@lem6891085) (@lem6891084)). Qed.
Lemma lem6891087 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6891088 : term324 = term395.
Proof. exact (MK_COMB (@lem6891087) (@lem6891086)). Qed.
Lemma lem6891089 : term328 = term396.
Proof. exact (MK_COMB (@lem6891088) (@lem6891051)). Qed.
Lemma lem6891090 (h1 : term268) : term396.
Proof. exact (EQ_MP (@lem6891089) (@lem6890669 h1)). Qed.
Lemma lem6891109 (n : nat) (m : nat) : (term343 n m) = (term343 n m).
Proof. exact (eq_refl (term343 n m)). Qed.
Lemma lem6891110 (m : nat) : (term337 m) = (term337 m).
Proof. exact (fun_ext (fun n : nat => @lem6891109 n m)). Qed.
Lemma lem6891111 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6891112 (m : nat) : (term355 m) = (term355 m).
Proof. exact (MK_COMB (@lem6891111) (@lem6891110 m)). Qed.
Lemma lem6891113 : term362 = term362.
Proof. exact (fun_ext (fun m : nat => @lem6891112 m)). Qed.
Lemma lem6891114 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6891115 : term377 = term377.
Proof. exact (MK_COMB (@lem6891114) (@lem6891113)). Qed.
Lemma lem6891134 (n : nat) (m : nat) : (term339 n m) = (term339 n m).
Proof. exact (eq_refl (term339 n m)). Qed.
Lemma lem6891135 (m : nat) : (term336 m) = (term336 m).
Proof. exact (fun_ext (fun n : nat => @lem6891134 n m)). Qed.
Lemma lem6891136 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6891137 (m : nat) : (term350 m) = (term350 m).
Proof. exact (MK_COMB (@lem6891136) (@lem6891135 m)). Qed.
Lemma lem6891138 : term361 = term361.
Proof. exact (fun_ext (fun m : nat => @lem6891137 m)). Qed.
Lemma lem6891139 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6891140 : term372 = term372.
Proof. exact (MK_COMB (@lem6891139) (@lem6891138)). Qed.
Lemma lem6891141 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6891142 : term374 = term374.
Proof. exact (MK_COMB (@lem6891141) (@lem6891140)). Qed.
Lemma lem6891143 : term378 = term378.
Proof. exact (MK_COMB (@lem6891142) (@lem6891115)). Qed.
Lemma lem6891144 (h1 : term230) : term378.
Proof. exact (EQ_MP (@lem6891143) (@lem6890956 h1)). Qed.
Lemma lem6891146 (h1 : term230) : term372.
Proof. exact (proj1 (@lem6891144 h1)). Qed.
Lemma lem6891147 (h1 : term268) : term386.
Proof. exact (proj2 (@lem6891090 h1)). Qed.
Lemma lem6891162 (n : nat) (m : nat) : (term339 n m) = (term339 n m).
Proof. exact (eq_refl (term339 n m)). Qed.
Lemma lem6891163 (m : nat) : (term336 m) = (term336 m).
Proof. exact (fun_ext (fun n : nat => @lem6891162 n m)). Qed.
Lemma lem6891164 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6891165 (m : nat) : (term350 m) = (term350 m).
Proof. exact (MK_COMB (@lem6891164) (@lem6891163 m)). Qed.
Lemma lem6891166 : term361 = term361.
Proof. exact (fun_ext (fun m : nat => @lem6891165 m)). Qed.
Lemma lem6891167 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6891169 : term372 = term372.
Proof. exact (MK_COMB (@lem6891167) (@lem6891166)). Qed.
Lemma lem6891170 (h1 : term230) : term372.
Proof. exact (EQ_MP (@lem6891169) (@lem6891146 h1)). Qed.
Lemma lem6891210 (n : nat) (m : nat) : (term382 n m) = (term382 n m).
Proof. exact (eq_refl (term382 n m)). Qed.
Lemma lem6891211 (m : nat) : (term383 m) = (term383 m).
Proof. exact (fun_ext (fun n : nat => @lem6891210 n m)). Qed.
Lemma lem6891212 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6891213 (m : nat) : (term384 m) = (term384 m).
Proof. exact (MK_COMB (@lem6891212) (@lem6891211 m)). Qed.
Lemma lem6891214 : term385 = term385.
Proof. exact (fun_ext (fun m : nat => @lem6891213 m)). Qed.
Lemma lem6891215 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6891217 : term386 = term386.
Proof. exact (MK_COMB (@lem6891215) (@lem6891214)). Qed.
Lemma lem6891218 (h1 : term268) : term386.
Proof. exact (EQ_MP (@lem6891217) (@lem6891147 h1)). Qed.
Lemma lem6891227 (_91996 : nat) (h1 : term230) : term363 _91996.
Proof. exact (@lem6891170 h1 _91996). Qed.
Lemma lem6891228 (_91996 : nat) : (term363 _91996) = (term350 _91996).
Proof. exact (eq_refl (term363 _91996)). Qed.
Lemma lem6891229 (_91996 : nat) (h1 : term230) : term350 _91996.
Proof. exact (EQ_MP (@lem6891228 _91996) (@lem6891227 _91996 h1)). Qed.
Lemma lem6891230 (_91996 : nat) (_91997 : nat) (h1 : term230) : term338 _91996 _91997.
Proof. exact (@lem6891229 _91996 h1 _91997). Qed.
Lemma lem6891231 (_91997 : nat) (_91996 : nat) : (term338 _91996 _91997) = (term339 _91997 _91996).
Proof. exact (eq_refl (term338 _91996 _91997)). Qed.
Lemma lem6891245 (_92002 : nat) (h1 : term268) : term397 _92002.
Proof. exact (@lem6891218 h1 _92002). Qed.
Lemma lem6891246 (_92002 : nat) : (term397 _92002) = (term384 _92002).
Proof. exact (eq_refl (term397 _92002)). Qed.
Lemma lem6891247 (_92002 : nat) (h1 : term268) : term384 _92002.
Proof. exact (EQ_MP (@lem6891246 _92002) (@lem6891245 _92002 h1)). Qed.
Lemma lem6891248 (_92002 : nat) (_92003 : nat) (h1 : term268) : term398 _92002 _92003.
Proof. exact (@lem6891247 _92002 h1 _92003). Qed.
Lemma lem6891249 (_92003 : nat) (_92002 : nat) : (term398 _92002 _92003) = (term382 _92003 _92002).
Proof. exact (eq_refl (term398 _92002 _92003)). Qed.
Lemma lem6891258 (_91997 : nat) (_91996 : nat) (h1 : term230) : term339 _91997 _91996.
Proof. exact (EQ_MP (@lem6891231 _91997 _91996) (@lem6891230 _91996 _91997 h1)). Qed.
Lemma lem6891276 (_92003 : nat) (_92002 : nat) (h1 : term268) : term382 _92003 _92002.
Proof. exact (EQ_MP (@lem6891249 _92003 _92002) (@lem6891248 _92002 _92003 h1)). Qed.
Lemma lem6891280 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term223 A dom op m n f neut) : term399 A dom op m n f neut.
Proof. exact (proj2 (@lem6891020 A dom op m n f neut h1)). Qed.
Lemma lem6891319 {A : Type'} : (@iterato A nat) = (@iterato A nat).
Proof. exact (eq_refl (@iterato A nat)). Qed.
Lemma lem6891320 {A : Type'} (_92012 : A -> Prop) (_92018 : A -> Prop) (h1 : _92012 = _92018) : _92012 = _92018.
Proof. exact (h1). Qed.
Lemma lem6891321 {A : Type'} (_92013 : A) (_92019 : A) (h1 : _92013 = _92019) : _92013 = _92019.
Proof. exact (h1). Qed.
Lemma lem6891322 {A : Type'} (_92014 : type1400 A) (_92020 : type1400 A) (h1 : _92014 = _92020) : _92014 = _92020.
Proof. exact (h1). Qed.
Lemma lem6891323 (_92015 : type1605) (_92021 : type1605) (h1 : _92015 = _92021) : _92015 = _92021.
Proof. exact (h1). Qed.
Lemma lem6891324 (_92016 : nat -> Prop) (_92022 : nat -> Prop) (h1 : _92016 = _92022) : _92016 = _92022.
Proof. exact (h1). Qed.
Lemma lem6891325 {A : Type'} (_92017 : nat -> A) (_92023 : nat -> A) (h1 : _92017 = _92023) : _92017 = _92023.
Proof. exact (h1). Qed.
Lemma lem6891326 {A : Type'} (_92012 : A -> Prop) (_92018 : A -> Prop) (h1 : _92012 = _92018) : (@iterato A nat _92012) = (@iterato A nat _92018).
Proof. exact (MK_COMB (@lem6891319 A) (@lem6891320 A _92012 _92018 h1)). Qed.
Lemma lem6891327 {A : Type'} (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (h1 : _92013 = _92019) (h2 : _92012 = _92018) : (@iterato A nat _92012 _92013) = (@iterato A nat _92018 _92019).
Proof. exact (MK_COMB (@lem6891326 A _92012 _92018 h2) (@lem6891321 A _92013 _92019 h1)). Qed.
Lemma lem6891328 {A : Type'} (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (h1 : _92013 = _92019) (h2 : _92012 = _92018) (h3 : _92014 = _92020) : (@iterato A nat _92012 _92013 _92014) = (@iterato A nat _92018 _92019 _92020).
Proof. exact (MK_COMB (@lem6891327 A _92013 _92019 _92012 _92018 h1 h2) (@lem6891322 A _92014 _92020 h3)). Qed.
Lemma lem6891329 {A : Type'} (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (_92015 : type1605) (_92021 : type1605) (h1 : _92013 = _92019) (h2 : _92012 = _92018) (h3 : _92014 = _92020) (h4 : _92015 = _92021) : (@iterato A nat _92012 _92013 _92014 _92015) = (@iterato A nat _92018 _92019 _92020 _92021).
Proof. exact (MK_COMB (@lem6891328 A _92013 _92019 _92012 _92018 _92014 _92020 h1 h2 h3) (@lem6891323 _92015 _92021 h4)). Qed.
Lemma lem6891330 {A : Type'} (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) (h1 : _92013 = _92019) (h2 : _92012 = _92018) (h3 : _92014 = _92020) (h4 : _92016 = _92022) (h5 : _92015 = _92021) : (@iterato A nat _92012 _92013 _92014 _92015 _92016) = (@iterato A nat _92018 _92019 _92020 _92021 _92022).
Proof. exact (MK_COMB (@lem6891329 A _92013 _92019 _92012 _92018 _92014 _92020 _92015 _92021 h1 h2 h3 h5) (@lem6891324 _92016 _92022 h4)). Qed.
Lemma lem6891331 {A : Type'} (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) (h1 : _92013 = _92019) (h2 : _92012 = _92018) (h3 : _92014 = _92020) (h4 : _92017 = _92023) (h5 : _92016 = _92022) (h6 : _92015 = _92021) : (@iterato A nat _92012 _92013 _92014 _92015 _92016 _92017) = (@iterato A nat _92018 _92019 _92020 _92021 _92022 _92023).
Proof. exact (MK_COMB (@lem6891330 A _92013 _92019 _92012 _92018 _92014 _92020 _92016 _92022 _92015 _92021 h1 h2 h3 h5 h6) (@lem6891325 A _92017 _92023 h4)). Qed.
Lemma lem6891332 {A : Type'} (_92015 : type1605) (_92021 : type1605) (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (h1 : _92013 = _92019) (h2 : _92012 = _92018) (h3 : _92014 = _92020) (h4 : _92017 = _92023) (h5 : _92016 = _92022) : term400 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023.
Proof. exact (fun h0 : _92015 = _92021 => @lem6891331 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021 h1 h2 h3 h4 h5 h0). Qed.
Lemma lem6891334 (a : Prop) (b : Prop) : (a -> b) = (term401 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem6891335 {A : Type'} (_92012 : A -> Prop) (_92013 : A) (_92014 : type1400 A) (_92015 : type1605) (_92016 : nat -> Prop) (_92017 : nat -> A) (_92018 : A -> Prop) (_92019 : A) (_92020 : type1400 A) (_92021 : type1605) (_92022 : nat -> Prop) (_92023 : nat -> A) : (term400 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) = (term402 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023).
Proof. exact (@lem6891334 (_92015 = _92021) ((@iterato A nat _92012 _92013 _92014 _92015 _92016 _92017) = (@iterato A nat _92018 _92019 _92020 _92021 _92022 _92023))). Qed.
Lemma lem6891336 {A : Type'} (_92015 : type1605) (_92021 : type1605) (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (h1 : _92013 = _92019) (h2 : _92012 = _92018) (h3 : _92014 = _92020) (h4 : _92017 = _92023) (h5 : _92016 = _92022) : term402 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023.
Proof. exact (EQ_MP (@lem6891335 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) (@lem6891332 A _92015 _92021 _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 h1 h2 h3 h4 h5)). Qed.
Lemma lem6891337 {A : Type'} (_92015 : type1605) (_92016 : nat -> Prop) (_92021 : type1605) (_92022 : nat -> Prop) (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (h1 : _92013 = _92019) (h2 : _92012 = _92018) (h3 : _92014 = _92020) (h4 : _92017 = _92023) : term403 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023.
Proof. exact (fun h0 : _92016 = _92022 => @lem6891336 A _92015 _92021 _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 h1 h2 h3 h4 h0). Qed.
Lemma lem6891339 (a : Prop) (b : Prop) : (a -> b) = (term401 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem6891340 {A : Type'} (_92012 : A -> Prop) (_92013 : A) (_92014 : type1400 A) (_92015 : type1605) (_92016 : nat -> Prop) (_92017 : nat -> A) (_92018 : A -> Prop) (_92019 : A) (_92020 : type1400 A) (_92021 : type1605) (_92022 : nat -> Prop) (_92023 : nat -> A) : (term403 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) = (term404 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023).
Proof. exact (@lem6891339 (_92016 = _92022) (term402 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023)). Qed.
Lemma lem6891341 {A : Type'} (_92015 : type1605) (_92016 : nat -> Prop) (_92021 : type1605) (_92022 : nat -> Prop) (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (h1 : _92013 = _92019) (h2 : _92012 = _92018) (h3 : _92014 = _92020) (h4 : _92017 = _92023) : term404 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023.
Proof. exact (EQ_MP (@lem6891340 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) (@lem6891337 A _92015 _92016 _92021 _92022 _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 h1 h2 h3 h4)). Qed.
Lemma lem6891342 {A : Type'} (_92015 : type1605) (_92016 : nat -> Prop) (_92017 : nat -> A) (_92021 : type1605) (_92022 : nat -> Prop) (_92023 : nat -> A) (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (h1 : _92013 = _92019) (h2 : _92012 = _92018) (h3 : _92014 = _92020) : term405 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023.
Proof. exact (fun h0 : _92017 = _92023 => @lem6891341 A _92015 _92016 _92021 _92022 _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 h1 h2 h3 h0). Qed.
Lemma lem6891344 (a : Prop) (b : Prop) : (a -> b) = (term401 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem6891345 {A : Type'} (_92012 : A -> Prop) (_92013 : A) (_92014 : type1400 A) (_92015 : type1605) (_92016 : nat -> Prop) (_92017 : nat -> A) (_92018 : A -> Prop) (_92019 : A) (_92020 : type1400 A) (_92021 : type1605) (_92022 : nat -> Prop) (_92023 : nat -> A) : (term405 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) = (term406 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023).
Proof. exact (@lem6891344 (_92017 = _92023) (term404 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023)). Qed.
Lemma lem6891346 {A : Type'} (_92015 : type1605) (_92016 : nat -> Prop) (_92017 : nat -> A) (_92021 : type1605) (_92022 : nat -> Prop) (_92023 : nat -> A) (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (h1 : _92013 = _92019) (h2 : _92012 = _92018) (h3 : _92014 = _92020) : term406 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023.
Proof. exact (EQ_MP (@lem6891345 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) (@lem6891342 A _92015 _92016 _92017 _92021 _92022 _92023 _92013 _92019 _92012 _92018 _92014 _92020 h1 h2 h3)). Qed.
Lemma lem6891347 {A : Type'} (_92014 : type1400 A) (_92015 : type1605) (_92016 : nat -> Prop) (_92017 : nat -> A) (_92020 : type1400 A) (_92021 : type1605) (_92022 : nat -> Prop) (_92023 : nat -> A) (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (h1 : _92013 = _92019) (h2 : _92012 = _92018) : term407 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023.
Proof. exact (fun h0 : _92014 = _92020 => @lem6891346 A _92015 _92016 _92017 _92021 _92022 _92023 _92013 _92019 _92012 _92018 _92014 _92020 h1 h2 h0). Qed.
Lemma lem6891349 (a : Prop) (b : Prop) : (a -> b) = (term401 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem6891350 {A : Type'} (_92012 : A -> Prop) (_92013 : A) (_92014 : type1400 A) (_92015 : type1605) (_92016 : nat -> Prop) (_92017 : nat -> A) (_92018 : A -> Prop) (_92019 : A) (_92020 : type1400 A) (_92021 : type1605) (_92022 : nat -> Prop) (_92023 : nat -> A) : (term407 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) = (term408 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023).
Proof. exact (@lem6891349 (_92014 = _92020) (term406 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023)). Qed.
Lemma lem6891351 {A : Type'} (_92014 : type1400 A) (_92015 : type1605) (_92016 : nat -> Prop) (_92017 : nat -> A) (_92020 : type1400 A) (_92021 : type1605) (_92022 : nat -> Prop) (_92023 : nat -> A) (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (h1 : _92013 = _92019) (h2 : _92012 = _92018) : term408 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023.
Proof. exact (EQ_MP (@lem6891350 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) (@lem6891347 A _92014 _92015 _92016 _92017 _92020 _92021 _92022 _92023 _92013 _92019 _92012 _92018 h1 h2)). Qed.
Lemma lem6891352 {A : Type'} (_92012 : A -> Prop) (_92014 : type1400 A) (_92015 : type1605) (_92016 : nat -> Prop) (_92017 : nat -> A) (_92018 : A -> Prop) (_92020 : type1400 A) (_92021 : type1605) (_92022 : nat -> Prop) (_92023 : nat -> A) (_92013 : A) (_92019 : A) (h1 : _92013 = _92019) : term409 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023.
Proof. exact (fun h0 : _92012 = _92018 => @lem6891351 A _92014 _92015 _92016 _92017 _92020 _92021 _92022 _92023 _92013 _92019 _92012 _92018 h1 h0). Qed.
Lemma lem6891354 (a : Prop) (b : Prop) : (a -> b) = (term401 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem6891355 {A : Type'} (_92012 : A -> Prop) (_92013 : A) (_92014 : type1400 A) (_92015 : type1605) (_92016 : nat -> Prop) (_92017 : nat -> A) (_92018 : A -> Prop) (_92019 : A) (_92020 : type1400 A) (_92021 : type1605) (_92022 : nat -> Prop) (_92023 : nat -> A) : (term409 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) = (term410 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023).
Proof. exact (@lem6891354 (_92012 = _92018) (term408 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023)). Qed.
Lemma lem6891356 {A : Type'} (_92012 : A -> Prop) (_92014 : type1400 A) (_92015 : type1605) (_92016 : nat -> Prop) (_92017 : nat -> A) (_92018 : A -> Prop) (_92020 : type1400 A) (_92021 : type1605) (_92022 : nat -> Prop) (_92023 : nat -> A) (_92013 : A) (_92019 : A) (h1 : _92013 = _92019) : term410 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023.
Proof. exact (EQ_MP (@lem6891355 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) (@lem6891352 A _92012 _92014 _92015 _92016 _92017 _92018 _92020 _92021 _92022 _92023 _92013 _92019 h1)). Qed.
Lemma lem6891357 {A : Type'} (_92012 : A -> Prop) (_92013 : A) (_92014 : type1400 A) (_92015 : type1605) (_92016 : nat -> Prop) (_92017 : nat -> A) (_92018 : A -> Prop) (_92019 : A) (_92020 : type1400 A) (_92021 : type1605) (_92022 : nat -> Prop) (_92023 : nat -> A) : term411 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023.
Proof. exact (fun h0 : _92013 = _92019 => @lem6891356 A _92012 _92014 _92015 _92016 _92017 _92018 _92020 _92021 _92022 _92023 _92013 _92019 h0). Qed.
Lemma lem6891359 (a : Prop) (b : Prop) : (a -> b) = (term401 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem6891360 {A : Type'} (_92012 : A -> Prop) (_92013 : A) (_92014 : type1400 A) (_92015 : type1605) (_92016 : nat -> Prop) (_92017 : nat -> A) (_92018 : A -> Prop) (_92019 : A) (_92020 : type1400 A) (_92021 : type1605) (_92022 : nat -> Prop) (_92023 : nat -> A) : (term411 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) = (term412 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023).
Proof. exact (@lem6891359 (_92013 = _92019) (term410 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023)). Qed.
Lemma lem6891361 {A : Type'} (_92012 : A -> Prop) (_92013 : A) (_92014 : type1400 A) (_92015 : type1605) (_92016 : nat -> Prop) (_92017 : nat -> A) (_92018 : A -> Prop) (_92019 : A) (_92020 : type1400 A) (_92021 : type1605) (_92022 : nat -> Prop) (_92023 : nat -> A) : term412 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023.
Proof. exact (EQ_MP (@lem6891360 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) (@lem6891357 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023)). Qed.
Lemma lem6891399 {A : Type'} (x : A) (y : A) (z : A) : term413 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem6891407 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem6891408 {A : Type'} (x : A) : x = x.
Proof. exact (@lem6891407 A x). Qed.
Lemma lem6891409 {A : Type'} (neut : A) : neut = neut.
Proof. exact (@lem6891408 A neut). Qed.
Lemma lem6891410 {A : Type'} (neut : A) : term414 A neut.
Proof. exact (fun h0 : term415 A neut => @lem6891409 A neut). Qed.
Lemma lem6891412 (p : Prop) : (term416 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6891413 {A : Type'} (neut : A) : (term414 A neut) = (neut = neut).
Proof. exact (@lem6891412 (neut = neut)). Qed.
Lemma lem6891414 {A : Type'} (neut : A) : neut = neut.
Proof. exact (EQ_MP (@lem6891413 A neut) (@lem6891410 A neut)). Qed.
Lemma lem6891416 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem6891417 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem6891416 A x). Qed.
Lemma lem6891418 {A : Type'} (dom : A -> Prop) : dom = dom.
Proof. exact (@lem6891417 A dom). Qed.
Lemma lem6891419 {A : Type'} (dom : A -> Prop) : term417 A dom.
Proof. exact (fun h0 : term418 A dom => @lem6891418 A dom). Qed.
Lemma lem6891421 (p : Prop) : (term416 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6891422 {A : Type'} (dom : A -> Prop) : (term417 A dom) = (dom = dom).
Proof. exact (@lem6891421 (dom = dom)). Qed.
Lemma lem6891423 {A : Type'} (dom : A -> Prop) : dom = dom.
Proof. exact (EQ_MP (@lem6891422 A dom) (@lem6891419 A dom)). Qed.
Lemma lem6891425 {A : Type'} (x : type1400 A) : x = x.
Proof. exact (@lem21386 (type1400 A) x). Qed.
Lemma lem6891426 {A : Type'} (x : type1400 A) : x = x.
Proof. exact (@lem6891425 A x). Qed.
Lemma lem6891427 {A : Type'} (op : type1400 A) : op = op.
Proof. exact (@lem6891426 A op). Qed.
Lemma lem6891428 {A : Type'} (op : type1400 A) : term419 A op.
Proof. exact (fun h0 : term420 A op => @lem6891427 A op). Qed.
Lemma lem6891430 (p : Prop) : (term416 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6891431 {A : Type'} (op : type1400 A) : (term419 A op) = (op = op).
Proof. exact (@lem6891430 (op = op)). Qed.
Lemma lem6891432 {A : Type'} (op : type1400 A) : op = op.
Proof. exact (EQ_MP (@lem6891431 A op) (@lem6891428 A op)). Qed.
Lemma lem6891434 {A : Type'} (x : nat -> A) : x = x.
Proof. exact (@lem21386 (nat -> A) x). Qed.
Lemma lem6891435 {A : Type'} (x : nat -> A) : x = x.
Proof. exact (@lem6891434 A x). Qed.
Lemma lem6891436 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (@lem6891435 A f). Qed.
Lemma lem6891437 {A : Type'} (f : nat -> A) : term421 A f.
Proof. exact (fun h0 : term422 A f => @lem6891436 A f). Qed.
Lemma lem6891439 (p : Prop) : (term416 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6891440 {A : Type'} (f : nat -> A) : (term421 A f) = (f = f).
Proof. exact (@lem6891439 (f = f)). Qed.
Lemma lem6891441 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (EQ_MP (@lem6891440 A f) (@lem6891437 A f)). Qed.
Lemma lem6891443 (m : nat) (n : nat) (h1 : term200 m n) : term380 m n.
Proof. exact (EQ_MP (@lem6890975 m n) (@lem6890368 m n h1)). Qed.
Lemma lem6891444 (m : nat) (n : nat) (h1 : term200 m n) : term423 m n.
Proof. exact (fun h0 : term379 m n => @lem6891443 m n h1). Qed.
Lemma lem6891446 (p : Prop) : (term424 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6891447 (m : nat) (n : nat) : (term423 m n) = (term380 m n).
Proof. exact (@lem6891446 (term379 m n)). Qed.
Lemma lem6891448 (m : nat) (n : nat) (h1 : term200 m n) : term380 m n.
Proof. exact (EQ_MP (@lem6891447 m n) (@lem6891444 m n h1)). Qed.
Lemma lem6891454 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6891455 (_92002 : nat) (_92003 : nat) : (term382 _92003 _92002) = (term425 _92002 _92003).
Proof. exact (@lem6891454 (Peano.lt _92003 _92002) (term379 _92002 _92003)). Qed.
Lemma lem6891461 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6891462 (_92002 : nat) (_92003 : nat) : (term426 _92003 _92002) = (term427 _92002 _92003).
Proof. exact (MK_COMB (@lem6891461) (@lem6891455 _92002 _92003)). Qed.
Lemma lem6891468 (_92002 : nat) (_92003 : nat) : (term425 _92002 _92003) = (term425 _92002 _92003).
Proof. exact (eq_refl (term425 _92002 _92003)). Qed.
Lemma lem6891469 (_92002 : nat) (_92003 : nat) : ((term382 _92003 _92002) = (term425 _92002 _92003)) = ((term425 _92002 _92003) = (term425 _92002 _92003)).
Proof. exact (MK_COMB (@lem6891462 _92002 _92003) (@lem6891468 _92002 _92003)). Qed.
Lemma lem6891471 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6891472 (x : Prop) : (x = x) = True.
Proof. exact (@lem6891471 Prop x). Qed.
Lemma lem6891473 (_92002 : nat) (_92003 : nat) : ((term425 _92002 _92003) = (term425 _92002 _92003)) = True.
Proof. exact (@lem6891472 (term425 _92002 _92003)). Qed.
Lemma lem6891474 (_92002 : nat) (_92003 : nat) : ((term382 _92003 _92002) = (term425 _92002 _92003)) = True.
Proof. exact (TRANS (@lem6891469 _92002 _92003) (@lem6891473 _92002 _92003)). Qed.
Lemma lem6891475 (_92002 : nat) (_92003 : nat) : True = ((term382 _92003 _92002) = (term425 _92002 _92003)).
Proof. exact (SYM (@lem6891474 _92002 _92003)). Qed.
Lemma lem6891476 (_92002 : nat) (_92003 : nat) : (term382 _92003 _92002) = (term425 _92002 _92003).
Proof. exact (EQ_MP (@lem6891475 _92002 _92003) (@lem0)). Qed.
Lemma lem6891477 (_92002 : nat) (_92003 : nat) (h1 : term268) : term425 _92002 _92003.
Proof. exact (EQ_MP (@lem6891476 _92002 _92003) (@lem6891276 _92003 _92002 h1)). Qed.
Lemma lem6891479 (b : Prop) (a : Prop) : (a \/ b) = (term428 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6891482 (_92003 : nat) (_92002 : nat) : (term425 _92002 _92003) = (term429 _92003 _92002).
Proof. exact (@lem6891479 (term379 _92002 _92003) (Peano.lt _92003 _92002)). Qed.
Lemma lem6891485 (_92003 : nat) (_92002 : nat) (h1 : term268) : term429 _92003 _92002.
Proof. exact (EQ_MP (@lem6891482 _92003 _92002) (@lem6891477 _92002 _92003 h1)). Qed.
Lemma lem6891486 (n : nat) (m : nat) (h1 : term268) : term429 n m.
Proof. exact (@lem6891485 n m h1). Qed.
Lemma lem6891489 (m : nat) (n : nat) (h1 : term268) (h2 : term200 m n) : Peano.lt n m.
Proof. exact (@lem6891486 n m h1 (@lem6891448 m n h2)). Qed.
Lemma lem6891490 (m : nat) (n : nat) (h1 : term268) (h2 : term200 m n) : term430 n m.
Proof. exact (fun h0 : term387 n m => @lem6891489 m n h1 h2). Qed.
Lemma lem6891492 (p : Prop) : (term416 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6891493 (n : nat) (m : nat) : (term430 n m) = (Peano.lt n m).
Proof. exact (@lem6891492 (Peano.lt n m)). Qed.
Lemma lem6891494 (m : nat) (n : nat) (h1 : term268) (h2 : term200 m n) : Peano.lt n m.
Proof. exact (EQ_MP (@lem6891493 n m) (@lem6891490 m n h1 h2)). Qed.
Lemma lem6891496 (b : Prop) (a : Prop) : (a \/ b) = (term428 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6891497 (_91996 : nat) (_91997 : nat) : (term339 _91997 _91996) = (term431 _91996 _91997).
Proof. exact (@lem6891496 (term387 _91997 _91996) ((dotdot _91996 _91997) = (@EMPTY nat))). Qed.
Lemma lem6891499 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6891500 (_91997 : nat) (_91996 : nat) : (term432 _91997 _91996) = (Peano.lt _91997 _91996).
Proof. exact (@lem6891499 (Peano.lt _91997 _91996)). Qed.
Lemma lem6891501 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6891502 (_91997 : nat) (_91996 : nat) : (term433 _91997 _91996) = (term434 _91997 _91996).
Proof. exact (MK_COMB (@lem6891501) (@lem6891500 _91997 _91996)). Qed.
Lemma lem6891503 (_91996 : nat) (_91997 : nat) : ((dotdot _91996 _91997) = (@EMPTY nat)) = ((dotdot _91996 _91997) = (@EMPTY nat)).
Proof. exact (eq_refl ((dotdot _91996 _91997) = (@EMPTY nat))). Qed.
Lemma lem6891504 (_91996 : nat) (_91997 : nat) : (term431 _91996 _91997) = (term435 _91996 _91997).
Proof. exact (MK_COMB (@lem6891502 _91997 _91996) (@lem6891503 _91996 _91997)). Qed.
Lemma lem6891505 (_91996 : nat) (_91997 : nat) : (term339 _91997 _91996) = (term435 _91996 _91997).
Proof. exact (TRANS (@lem6891497 _91996 _91997) (@lem6891504 _91996 _91997)). Qed.
Lemma lem6891508 (_91996 : nat) (_91997 : nat) (h1 : term230) : term435 _91996 _91997.
Proof. exact (EQ_MP (@lem6891505 _91996 _91997) (@lem6891258 _91997 _91996 h1)). Qed.
Lemma lem6891509 (m : nat) (n : nat) (h1 : term230) : term435 m n.
Proof. exact (@lem6891508 m n h1). Qed.
Lemma lem6891512 (m : nat) (n : nat) (h1 : term268) (h2 : term230) (h3 : term200 m n) : (dotdot m n) = (@EMPTY nat).
Proof. exact (@lem6891509 m n h2 (@lem6891494 m n h1 h3)). Qed.
Lemma lem6891513 (m : nat) (n : nat) (h1 : term268) (h2 : term230) (h3 : term200 m n) : term436 m n.
Proof. exact (fun h0 : term437 m n => @lem6891512 m n h1 h2 h3). Qed.
Lemma lem6891515 (p : Prop) : (term416 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6891516 (m : nat) (n : nat) : (term436 m n) = ((dotdot m n) = (@EMPTY nat)).
Proof. exact (@lem6891515 ((dotdot m n) = (@EMPTY nat))). Qed.
Lemma lem6891517 (m : nat) (n : nat) (h1 : term268) (h2 : term230) (h3 : term200 m n) : (dotdot m n) = (@EMPTY nat).
Proof. exact (EQ_MP (@lem6891516 m n) (@lem6891513 m n h1 h2 h3)). Qed.
Lemma lem6891519 (x : type1605) : x = x.
Proof. exact (@lem21386 type1605 x). Qed.
Lemma lem6891520 : Peano.le = Peano.le.
Proof. exact (@lem6891519 Peano.le). Qed.
Lemma lem6891521 : term438.
Proof. exact (fun h0 : term439 => @lem6891520). Qed.
Lemma lem6891523 (p : Prop) : (term416 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6891524 : term438 = (Peano.le = Peano.le).
Proof. exact (@lem6891523 (Peano.le = Peano.le)). Qed.
Lemma lem6891525 : Peano.le = Peano.le.
Proof. exact (EQ_MP (@lem6891524) (@lem6891521)). Qed.
Lemma lem6891591 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6891592 {A : Type'} (_92012 : A -> Prop) (_92013 : A) (_92014 : type1400 A) (_92016 : nat -> Prop) (_92017 : nat -> A) (_92018 : A -> Prop) (_92019 : A) (_92020 : type1400 A) (_92022 : nat -> Prop) (_92023 : nat -> A) (_92015 : type1605) (_92021 : type1605) : (term402 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) = (term440 A _92012 _92013 _92014 _92016 _92017 _92018 _92019 _92020 _92022 _92023 _92015 _92021).
Proof. exact (@lem6891591 ((@iterato A nat _92012 _92013 _92014 _92015 _92016 _92017) = (@iterato A nat _92018 _92019 _92020 _92021 _92022 _92023)) (term441 _92015 _92021)). Qed.
Lemma lem6891602 (_92016 : nat -> Prop) (_92022 : nat -> Prop) : (term442 _92016 _92022) = (term442 _92016 _92022).
Proof. exact (eq_refl (term442 _92016 _92022)). Qed.
Lemma lem6891603 {A : Type'} (_92012 : A -> Prop) (_92013 : A) (_92014 : type1400 A) (_92016 : nat -> Prop) (_92017 : nat -> A) (_92018 : A -> Prop) (_92019 : A) (_92020 : type1400 A) (_92022 : nat -> Prop) (_92023 : nat -> A) (_92015 : type1605) (_92021 : type1605) : (term404 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) = (term443 A _92012 _92013 _92014 _92016 _92017 _92018 _92019 _92020 _92022 _92023 _92015 _92021).
Proof. exact (MK_COMB (@lem6891602 _92016 _92022) (@lem6891592 A _92012 _92013 _92014 _92016 _92017 _92018 _92019 _92020 _92022 _92023 _92015 _92021)). Qed.
Lemma lem6891607 (q : Prop) (p : Prop) (r : Prop) : (term444 p q r) = (term444 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6891608 {A : Type'} (_92012 : A -> Prop) (_92013 : A) (_92014 : type1400 A) (_92017 : nat -> A) (_92018 : A -> Prop) (_92019 : A) (_92020 : type1400 A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term443 A _92012 _92013 _92014 _92016 _92017 _92018 _92019 _92020 _92022 _92023 _92015 _92021) = (term445 A _92012 _92013 _92014 _92017 _92018 _92019 _92020 _92023 _92016 _92022 _92015 _92021).
Proof. exact (@lem6891607 ((@iterato A nat _92012 _92013 _92014 _92015 _92016 _92017) = (@iterato A nat _92018 _92019 _92020 _92021 _92022 _92023)) (term446 _92016 _92022) (term441 _92015 _92021)). Qed.
Lemma lem6891630 {A : Type'} (_92012 : A -> Prop) (_92013 : A) (_92014 : type1400 A) (_92017 : nat -> A) (_92018 : A -> Prop) (_92019 : A) (_92020 : type1400 A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term404 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) = (term445 A _92012 _92013 _92014 _92017 _92018 _92019 _92020 _92023 _92016 _92022 _92015 _92021).
Proof. exact (TRANS (@lem6891603 A _92012 _92013 _92014 _92016 _92017 _92018 _92019 _92020 _92022 _92023 _92015 _92021) (@lem6891608 A _92012 _92013 _92014 _92017 _92018 _92019 _92020 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6891631 {A : Type'} (_92017 : nat -> A) (_92023 : nat -> A) : (term447 A _92017 _92023) = (term447 A _92017 _92023).
Proof. exact (eq_refl (term447 A _92017 _92023)). Qed.
Lemma lem6891632 {A : Type'} (_92012 : A -> Prop) (_92013 : A) (_92014 : type1400 A) (_92017 : nat -> A) (_92018 : A -> Prop) (_92019 : A) (_92020 : type1400 A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term406 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) = (term448 A _92012 _92013 _92014 _92017 _92018 _92019 _92020 _92023 _92016 _92022 _92015 _92021).
Proof. exact (MK_COMB (@lem6891631 A _92017 _92023) (@lem6891630 A _92012 _92013 _92014 _92017 _92018 _92019 _92020 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6891636 (q : Prop) (p : Prop) (r : Prop) : (term444 p q r) = (term444 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6891637 {A : Type'} (_92012 : A -> Prop) (_92013 : A) (_92014 : type1400 A) (_92018 : A -> Prop) (_92019 : A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term448 A _92012 _92013 _92014 _92017 _92018 _92019 _92020 _92023 _92016 _92022 _92015 _92021) = (term449 A _92012 _92013 _92014 _92018 _92019 _92020 _92017 _92023 _92016 _92022 _92015 _92021).
Proof. exact (@lem6891636 ((@iterato A nat _92012 _92013 _92014 _92015 _92016 _92017) = (@iterato A nat _92018 _92019 _92020 _92021 _92022 _92023)) (term450 A _92017 _92023) (term451 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6891671 {A : Type'} (_92012 : A -> Prop) (_92013 : A) (_92014 : type1400 A) (_92018 : A -> Prop) (_92019 : A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term406 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) = (term449 A _92012 _92013 _92014 _92018 _92019 _92020 _92017 _92023 _92016 _92022 _92015 _92021).
Proof. exact (TRANS (@lem6891632 A _92012 _92013 _92014 _92017 _92018 _92019 _92020 _92023 _92016 _92022 _92015 _92021) (@lem6891637 A _92012 _92013 _92014 _92018 _92019 _92020 _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6891672 {A : Type'} (_92014 : type1400 A) (_92020 : type1400 A) : (term452 A _92014 _92020) = (term452 A _92014 _92020).
Proof. exact (eq_refl (term452 A _92014 _92020)). Qed.
Lemma lem6891673 {A : Type'} (_92012 : A -> Prop) (_92013 : A) (_92014 : type1400 A) (_92018 : A -> Prop) (_92019 : A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term408 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) = (term453 A _92012 _92013 _92014 _92018 _92019 _92020 _92017 _92023 _92016 _92022 _92015 _92021).
Proof. exact (MK_COMB (@lem6891672 A _92014 _92020) (@lem6891671 A _92012 _92013 _92014 _92018 _92019 _92020 _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6891677 (q : Prop) (p : Prop) (r : Prop) : (term444 p q r) = (term444 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6891678 {A : Type'} (_92012 : A -> Prop) (_92013 : A) (_92018 : A -> Prop) (_92019 : A) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term453 A _92012 _92013 _92014 _92018 _92019 _92020 _92017 _92023 _92016 _92022 _92015 _92021) = (term454 A _92012 _92013 _92018 _92019 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021).
Proof. exact (@lem6891677 ((@iterato A nat _92012 _92013 _92014 _92015 _92016 _92017) = (@iterato A nat _92018 _92019 _92020 _92021 _92022 _92023)) (term455 A _92014 _92020) (term456 A _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6891724 {A : Type'} (_92012 : A -> Prop) (_92013 : A) (_92018 : A -> Prop) (_92019 : A) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term408 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) = (term454 A _92012 _92013 _92018 _92019 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021).
Proof. exact (TRANS (@lem6891673 A _92012 _92013 _92014 _92018 _92019 _92020 _92017 _92023 _92016 _92022 _92015 _92021) (@lem6891678 A _92012 _92013 _92018 _92019 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6891725 {A : Type'} (_92012 : A -> Prop) (_92018 : A -> Prop) : (term457 A _92012 _92018) = (term457 A _92012 _92018).
Proof. exact (eq_refl (term457 A _92012 _92018)). Qed.
Lemma lem6891726 {A : Type'} (_92012 : A -> Prop) (_92013 : A) (_92018 : A -> Prop) (_92019 : A) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term410 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) = (term458 A _92012 _92013 _92018 _92019 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021).
Proof. exact (MK_COMB (@lem6891725 A _92012 _92018) (@lem6891724 A _92012 _92013 _92018 _92019 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6891730 (q : Prop) (p : Prop) (r : Prop) : (term444 p q r) = (term444 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6891731 {A : Type'} (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term458 A _92012 _92013 _92018 _92019 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) = (term459 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021).
Proof. exact (@lem6891730 ((@iterato A nat _92012 _92013 _92014 _92015 _92016 _92017) = (@iterato A nat _92018 _92019 _92020 _92021 _92022 _92023)) (term460 A _92012 _92018) (term461 A _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6891789 {A : Type'} (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term410 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) = (term459 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021).
Proof. exact (TRANS (@lem6891726 A _92012 _92013 _92018 _92019 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) (@lem6891731 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6891790 {A : Type'} (_92013 : A) (_92019 : A) : (term462 A _92013 _92019) = (term462 A _92013 _92019).
Proof. exact (eq_refl (term462 A _92013 _92019)). Qed.
Lemma lem6891791 {A : Type'} (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term412 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) = (term463 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021).
Proof. exact (MK_COMB (@lem6891790 A _92013 _92019) (@lem6891789 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6891795 (q : Prop) (p : Prop) (r : Prop) : (term444 p q r) = (term444 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6891796 {A : Type'} (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term463 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) = (term464 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021).
Proof. exact (@lem6891795 ((@iterato A nat _92012 _92013 _92014 _92015 _92016 _92017) = (@iterato A nat _92018 _92019 _92020 _92021 _92022 _92023)) (term465 A _92013 _92019) (term466 A _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6891866 {A : Type'} (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term412 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) = (term464 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021).
Proof. exact (TRANS (@lem6891791 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) (@lem6891796 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6891867 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6891868 {A : Type'} (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term467 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) = (term468 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021).
Proof. exact (MK_COMB (@lem6891867) (@lem6891866 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6891938 {A : Type'} (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term464 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) = (term464 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021).
Proof. exact (eq_refl (term464 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6891939 {A : Type'} (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : ((term412 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) = (term464 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021)) = ((term464 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) = (term464 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021)).
Proof. exact (MK_COMB (@lem6891868 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) (@lem6891938 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6891941 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6891942 (x : Prop) : (x = x) = True.
Proof. exact (@lem6891941 Prop x). Qed.
Lemma lem6891943 {A : Type'} (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : ((term464 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) = (term464 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021)) = True.
Proof. exact (@lem6891942 (term464 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6891944 {A : Type'} (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : ((term412 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) = (term464 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021)) = True.
Proof. exact (TRANS (@lem6891939 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) (@lem6891943 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6891945 {A : Type'} (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : True = ((term412 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) = (term464 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021)).
Proof. exact (SYM (@lem6891944 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6891946 {A : Type'} (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term412 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) = (term464 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021).
Proof. exact (EQ_MP (@lem6891945 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) (@lem0)). Qed.
Lemma lem6891947 {A : Type'} (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : term464 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021.
Proof. exact (EQ_MP (@lem6891946 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) (@lem6891361 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023)). Qed.
Lemma lem6891949 (b : Prop) (a : Prop) : (a \/ b) = (term428 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6891950 {A : Type'} (_92012 : A -> Prop) (_92013 : A) (_92014 : type1400 A) (_92015 : type1605) (_92016 : nat -> Prop) (_92017 : nat -> A) (_92018 : A -> Prop) (_92019 : A) (_92020 : type1400 A) (_92021 : type1605) (_92022 : nat -> Prop) (_92023 : nat -> A) : (term464 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) = (term469 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023).
Proof. exact (@lem6891949 (term470 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) ((@iterato A nat _92012 _92013 _92014 _92015 _92016 _92017) = (@iterato A nat _92018 _92019 _92020 _92021 _92022 _92023))). Qed.
Lemma lem6891952 (a : Prop) (b : Prop) : (term471 a b) = (term472 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6891953 {A : Type'} (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term473 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) = (term474 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021).
Proof. exact (@lem6891952 (term465 A _92013 _92019) (term466 A _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6891955 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6891956 {A : Type'} (_92013 : A) (_92019 : A) : (term475 A _92013 _92019) = (_92013 = _92019).
Proof. exact (@lem6891955 (_92013 = _92019)). Qed.
Lemma lem6891957 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6891958 {A : Type'} (_92013 : A) (_92019 : A) : (term476 A _92013 _92019) = (term477 A _92013 _92019).
Proof. exact (MK_COMB (@lem6891957) (@lem6891956 A _92013 _92019)). Qed.
Lemma lem6891960 (a : Prop) (b : Prop) : (term471 a b) = (term472 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6891961 {A : Type'} (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term478 A _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) = (term479 A _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021).
Proof. exact (@lem6891960 (term460 A _92012 _92018) (term461 A _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6891963 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6891964 {A : Type'} (_92012 : A -> Prop) (_92018 : A -> Prop) : (term480 A _92012 _92018) = (_92012 = _92018).
Proof. exact (@lem6891963 (_92012 = _92018)). Qed.
Lemma lem6891965 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6891966 {A : Type'} (_92012 : A -> Prop) (_92018 : A -> Prop) : (term481 A _92012 _92018) = (term482 A _92012 _92018).
Proof. exact (MK_COMB (@lem6891965) (@lem6891964 A _92012 _92018)). Qed.
Lemma lem6891968 (a : Prop) (b : Prop) : (term471 a b) = (term472 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6891969 {A : Type'} (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term483 A _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) = (term484 A _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021).
Proof. exact (@lem6891968 (term455 A _92014 _92020) (term456 A _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6891971 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6891972 {A : Type'} (_92014 : type1400 A) (_92020 : type1400 A) : (term485 A _92014 _92020) = (_92014 = _92020).
Proof. exact (@lem6891971 (_92014 = _92020)). Qed.
Lemma lem6891973 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6891974 {A : Type'} (_92014 : type1400 A) (_92020 : type1400 A) : (term486 A _92014 _92020) = (term487 A _92014 _92020).
Proof. exact (MK_COMB (@lem6891973) (@lem6891972 A _92014 _92020)). Qed.
Lemma lem6891976 (a : Prop) (b : Prop) : (term471 a b) = (term472 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6891977 {A : Type'} (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term488 A _92017 _92023 _92016 _92022 _92015 _92021) = (term489 A _92017 _92023 _92016 _92022 _92015 _92021).
Proof. exact (@lem6891976 (term450 A _92017 _92023) (term451 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6891979 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6891980 {A : Type'} (_92017 : nat -> A) (_92023 : nat -> A) : (term490 A _92017 _92023) = (_92017 = _92023).
Proof. exact (@lem6891979 (_92017 = _92023)). Qed.
Lemma lem6891981 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6891982 {A : Type'} (_92017 : nat -> A) (_92023 : nat -> A) : (term491 A _92017 _92023) = (term492 A _92017 _92023).
Proof. exact (MK_COMB (@lem6891981) (@lem6891980 A _92017 _92023)). Qed.
Lemma lem6891984 (a : Prop) (b : Prop) : (term471 a b) = (term472 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6891985 (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term493 _92016 _92022 _92015 _92021) = (term494 _92016 _92022 _92015 _92021).
Proof. exact (@lem6891984 (term446 _92016 _92022) (term441 _92015 _92021)). Qed.
Lemma lem6891987 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6891988 (_92016 : nat -> Prop) (_92022 : nat -> Prop) : (term495 _92016 _92022) = (_92016 = _92022).
Proof. exact (@lem6891987 (_92016 = _92022)). Qed.
Lemma lem6891989 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6891990 (_92016 : nat -> Prop) (_92022 : nat -> Prop) : (term496 _92016 _92022) = (term497 _92016 _92022).
Proof. exact (MK_COMB (@lem6891989) (@lem6891988 _92016 _92022)). Qed.
Lemma lem6891992 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6891993 (_92015 : type1605) (_92021 : type1605) : (term498 _92015 _92021) = (_92015 = _92021).
Proof. exact (@lem6891992 (_92015 = _92021)). Qed.
Lemma lem6891994 (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term494 _92016 _92022 _92015 _92021) = (term499 _92016 _92022 _92015 _92021).
Proof. exact (MK_COMB (@lem6891990 _92016 _92022) (@lem6891993 _92015 _92021)). Qed.
Lemma lem6891995 (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term493 _92016 _92022 _92015 _92021) = (term499 _92016 _92022 _92015 _92021).
Proof. exact (TRANS (@lem6891985 _92016 _92022 _92015 _92021) (@lem6891994 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6891996 {A : Type'} (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term489 A _92017 _92023 _92016 _92022 _92015 _92021) = (term500 A _92017 _92023 _92016 _92022 _92015 _92021).
Proof. exact (MK_COMB (@lem6891982 A _92017 _92023) (@lem6891995 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6891997 {A : Type'} (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term488 A _92017 _92023 _92016 _92022 _92015 _92021) = (term500 A _92017 _92023 _92016 _92022 _92015 _92021).
Proof. exact (TRANS (@lem6891977 A _92017 _92023 _92016 _92022 _92015 _92021) (@lem6891996 A _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6891998 {A : Type'} (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term484 A _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) = (term501 A _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021).
Proof. exact (MK_COMB (@lem6891974 A _92014 _92020) (@lem6891997 A _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6891999 {A : Type'} (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term483 A _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) = (term501 A _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021).
Proof. exact (TRANS (@lem6891969 A _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) (@lem6891998 A _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6892000 {A : Type'} (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term479 A _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) = (term502 A _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021).
Proof. exact (MK_COMB (@lem6891966 A _92012 _92018) (@lem6891999 A _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6892001 {A : Type'} (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term478 A _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) = (term502 A _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021).
Proof. exact (TRANS (@lem6891961 A _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) (@lem6892000 A _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6892002 {A : Type'} (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term474 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) = (term503 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021).
Proof. exact (MK_COMB (@lem6891958 A _92013 _92019) (@lem6892001 A _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6892003 {A : Type'} (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term473 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) = (term503 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021).
Proof. exact (TRANS (@lem6891953 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) (@lem6892002 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6892004 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6892005 {A : Type'} (_92013 : A) (_92019 : A) (_92012 : A -> Prop) (_92018 : A -> Prop) (_92014 : type1400 A) (_92020 : type1400 A) (_92017 : nat -> A) (_92023 : nat -> A) (_92016 : nat -> Prop) (_92022 : nat -> Prop) (_92015 : type1605) (_92021 : type1605) : (term504 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) = (term505 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021).
Proof. exact (MK_COMB (@lem6892004) (@lem6892003 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6892006 {A : Type'} (_92012 : A -> Prop) (_92013 : A) (_92014 : type1400 A) (_92015 : type1605) (_92016 : nat -> Prop) (_92017 : nat -> A) (_92018 : A -> Prop) (_92019 : A) (_92020 : type1400 A) (_92021 : type1605) (_92022 : nat -> Prop) (_92023 : nat -> A) : ((@iterato A nat _92012 _92013 _92014 _92015 _92016 _92017) = (@iterato A nat _92018 _92019 _92020 _92021 _92022 _92023)) = ((@iterato A nat _92012 _92013 _92014 _92015 _92016 _92017) = (@iterato A nat _92018 _92019 _92020 _92021 _92022 _92023)).
Proof. exact (eq_refl ((@iterato A nat _92012 _92013 _92014 _92015 _92016 _92017) = (@iterato A nat _92018 _92019 _92020 _92021 _92022 _92023))). Qed.
Lemma lem6892007 {A : Type'} (_92012 : A -> Prop) (_92013 : A) (_92014 : type1400 A) (_92015 : type1605) (_92016 : nat -> Prop) (_92017 : nat -> A) (_92018 : A -> Prop) (_92019 : A) (_92020 : type1400 A) (_92021 : type1605) (_92022 : nat -> Prop) (_92023 : nat -> A) : (term469 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) = (term506 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023).
Proof. exact (MK_COMB (@lem6892005 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) (@lem6892006 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023)). Qed.
Lemma lem6892008 {A : Type'} (_92012 : A -> Prop) (_92013 : A) (_92014 : type1400 A) (_92015 : type1605) (_92016 : nat -> Prop) (_92017 : nat -> A) (_92018 : A -> Prop) (_92019 : A) (_92020 : type1400 A) (_92021 : type1605) (_92022 : nat -> Prop) (_92023 : nat -> A) : (term464 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021) = (term506 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023).
Proof. exact (TRANS (@lem6891950 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) (@lem6892007 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023)). Qed.
Lemma lem6892010 (m : nat) (n : nat) (h1 : term268) (h2 : term230) (h3 : term200 m n) : term507 m n.
Proof. exact (conj (@lem6891517 m n h1 h2 h3) (@lem6891525)). Qed.
Lemma lem6892011 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (h1 : term268) (h2 : term230) (h3 : term200 m n) : term508 A f m n.
Proof. exact (conj (@lem6891441 A f) (@lem6892010 m n h1 h2 h3)). Qed.
Lemma lem6892012 {A : Type'} (op : type1400 A) (f : nat -> A) (m : nat) (n : nat) (h1 : term268) (h2 : term230) (h3 : term200 m n) : term509 A op f m n.
Proof. exact (conj (@lem6891432 A op) (@lem6892011 A f m n h1 h2 h3)). Qed.
Lemma lem6892013 {A : Type'} (dom : A -> Prop) (op : type1400 A) (f : nat -> A) (m : nat) (n : nat) (h1 : term268) (h2 : term230) (h3 : term200 m n) : term510 A dom op f m n.
Proof. exact (conj (@lem6891423 A dom) (@lem6892012 A op f m n h1 h2 h3)). Qed.
Lemma lem6892014 {A : Type'} (neut : A) (dom : A -> Prop) (op : type1400 A) (f : nat -> A) (m : nat) (n : nat) (h1 : term268) (h2 : term230) (h3 : term200 m n) : term511 A neut dom op f m n.
Proof. exact (conj (@lem6891414 A neut) (@lem6892013 A dom op f m n h1 h2 h3)). Qed.
Lemma lem6892016 {A : Type'} (_92012 : A -> Prop) (_92013 : A) (_92014 : type1400 A) (_92015 : type1605) (_92016 : nat -> Prop) (_92017 : nat -> A) (_92018 : A -> Prop) (_92019 : A) (_92020 : type1400 A) (_92021 : type1605) (_92022 : nat -> Prop) (_92023 : nat -> A) : term506 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023.
Proof. exact (EQ_MP (@lem6892008 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023) (@lem6891947 A _92013 _92019 _92012 _92018 _92014 _92020 _92017 _92023 _92016 _92022 _92015 _92021)). Qed.
Lemma lem6892017 {A : Type'} (_92012 : A -> Prop) (_92013 : A) (_92014 : type1400 A) (_92015 : type1605) (_92016 : nat -> Prop) (_92017 : nat -> A) (_92018 : A -> Prop) (_92019 : A) (_92020 : type1400 A) (_92021 : type1605) (_92022 : nat -> Prop) (_92023 : nat -> A) : term506 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023.
Proof. exact (@lem6892016 A _92012 _92013 _92014 _92015 _92016 _92017 _92018 _92019 _92020 _92021 _92022 _92023). Qed.
Lemma lem6892018 {A : Type'} (m : nat) (n : nat) (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) : term512 A m n dom neut op f.
Proof. exact (@lem6892017 A dom neut op Peano.le (dotdot m n) f dom neut op Peano.le (@EMPTY nat) f). Qed.
Lemma lem6892021 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (m : nat) (n : nat) (h1 : term268) (h2 : term230) (h3 : term200 m n) : (term216 A dom neut op m n f) = (@iterato A nat dom neut op Peano.le (@EMPTY nat) f).
Proof. exact (@lem6892018 A m n dom neut op f (@lem6892014 A neut dom op f m n h1 h2 h3)). Qed.
Lemma lem6892022 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (m : nat) (n : nat) (h1 : term268) (h2 : term230) (h3 : term200 m n) : (term216 A dom neut op m n f) = (@iterato A nat dom neut op Peano.le (@EMPTY nat) f).
Proof. exact (@lem6892021 A dom neut op f m n h1 h2 h3). Qed.
Lemma lem6892023 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (m : nat) (n : nat) (h1 : term268) (h2 : term230) (h3 : term200 m n) : term513 A m n dom neut op f.
Proof. exact (fun h0 : term514 A m n dom neut op f => @lem6892022 A dom neut op f m n h1 h2 h3). Qed.
Lemma lem6892025 (p : Prop) : (term416 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6892026 {A : Type'} (m : nat) (n : nat) (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) : (term513 A m n dom neut op f) = ((term216 A dom neut op m n f) = (@iterato A nat dom neut op Peano.le (@EMPTY nat) f)).
Proof. exact (@lem6892025 ((term216 A dom neut op m n f) = (@iterato A nat dom neut op Peano.le (@EMPTY nat) f))). Qed.
Lemma lem6892027 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (m : nat) (n : nat) (h1 : term268) (h2 : term230) (h3 : term200 m n) : (term216 A dom neut op m n f) = (@iterato A nat dom neut op Peano.le (@EMPTY nat) f).
Proof. exact (EQ_MP (@lem6892026 A m n dom neut op f) (@lem6892023 A dom neut op f m n h1 h2 h3)). Qed.
Lemma lem6892029 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem6892030 {A : Type'} (x : A) : x = x.
Proof. exact (@lem6892029 A x). Qed.
Lemma lem6892031 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : (term216 A dom neut op m n f) = (term216 A dom neut op m n f).
Proof. exact (@lem6892030 A (term216 A dom neut op m n f)). Qed.
Lemma lem6892032 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : term515 A dom neut op m n f.
Proof. exact (fun h0 : term516 A dom neut op m n f => @lem6892031 A dom neut op m n f). Qed.
Lemma lem6892034 (p : Prop) : (term416 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6892035 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : (term515 A dom neut op m n f) = ((term216 A dom neut op m n f) = (term216 A dom neut op m n f)).
Proof. exact (@lem6892034 ((term216 A dom neut op m n f) = (term216 A dom neut op m n f))). Qed.
Lemma lem6892036 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : (term216 A dom neut op m n f) = (term216 A dom neut op m n f).
Proof. exact (EQ_MP (@lem6892035 A dom neut op m n f) (@lem6892032 A dom neut op m n f)). Qed.
Lemma lem6892054 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6892055 {A : Type'} (y : A) (x : A) (z : A) : (term517 A x y z) = (term518 A y x z).
Proof. exact (@lem6892054 (y = z) (term465 A x z)). Qed.
Lemma lem6892065 {A : Type'} (x : A) (y : A) : (term462 A x y) = (term462 A x y).
Proof. exact (eq_refl (term462 A x y)). Qed.
Lemma lem6892066 {A : Type'} (y : A) (x : A) (z : A) : (term413 A x y z) = (term519 A y x z).
Proof. exact (MK_COMB (@lem6892065 A x y) (@lem6892055 A y x z)). Qed.
Lemma lem6892070 (q : Prop) (p : Prop) (r : Prop) : (term444 p q r) = (term444 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6892071 {A : Type'} (y : A) (x : A) (z : A) : (term519 A y x z) = (term520 A y x z).
Proof. exact (@lem6892070 (y = z) (term465 A x y) (term465 A x z)). Qed.
Lemma lem6892093 {A : Type'} (y : A) (x : A) (z : A) : (term413 A x y z) = (term520 A y x z).
Proof. exact (TRANS (@lem6892066 A y x z) (@lem6892071 A y x z)). Qed.
Lemma lem6892094 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6892095 {A : Type'} (y : A) (x : A) (z : A) : (term521 A x y z) = (term522 A y x z).
Proof. exact (MK_COMB (@lem6892094) (@lem6892093 A y x z)). Qed.
Lemma lem6892117 {A : Type'} (y : A) (x : A) (z : A) : (term520 A y x z) = (term520 A y x z).
Proof. exact (eq_refl (term520 A y x z)). Qed.
Lemma lem6892118 {A : Type'} (y : A) (x : A) (z : A) : ((term413 A x y z) = (term520 A y x z)) = ((term520 A y x z) = (term520 A y x z)).
Proof. exact (MK_COMB (@lem6892095 A y x z) (@lem6892117 A y x z)). Qed.
Lemma lem6892120 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6892121 (x : Prop) : (x = x) = True.
Proof. exact (@lem6892120 Prop x). Qed.
Lemma lem6892122 {A : Type'} (y : A) (x : A) (z : A) : ((term520 A y x z) = (term520 A y x z)) = True.
Proof. exact (@lem6892121 (term520 A y x z)). Qed.
Lemma lem6892123 {A : Type'} (y : A) (x : A) (z : A) : ((term413 A x y z) = (term520 A y x z)) = True.
Proof. exact (TRANS (@lem6892118 A y x z) (@lem6892122 A y x z)). Qed.
Lemma lem6892124 {A : Type'} (y : A) (x : A) (z : A) : True = ((term413 A x y z) = (term520 A y x z)).
Proof. exact (SYM (@lem6892123 A y x z)). Qed.
Lemma lem6892125 {A : Type'} (y : A) (x : A) (z : A) : (term413 A x y z) = (term520 A y x z).
Proof. exact (EQ_MP (@lem6892124 A y x z) (@lem0)). Qed.
Lemma lem6892126 {A : Type'} (y : A) (x : A) (z : A) : term520 A y x z.
Proof. exact (EQ_MP (@lem6892125 A y x z) (@lem6891399 A x y z)). Qed.
Lemma lem6892128 (b : Prop) (a : Prop) : (a \/ b) = (term428 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6892129 {A : Type'} (x : A) (y : A) (z : A) : (term520 A y x z) = (term523 A x y z).
Proof. exact (@lem6892128 (term524 A y x z) (y = z)). Qed.
Lemma lem6892131 (a : Prop) (b : Prop) : (term471 a b) = (term472 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6892132 {A : Type'} (y : A) (x : A) (z : A) : (term525 A y x z) = (term526 A y x z).
Proof. exact (@lem6892131 (term465 A x y) (term465 A x z)). Qed.
Lemma lem6892134 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6892135 {A : Type'} (x : A) (y : A) : (term475 A x y) = (x = y).
Proof. exact (@lem6892134 (x = y)). Qed.
Lemma lem6892136 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6892137 {A : Type'} (x : A) (y : A) : (term476 A x y) = (term477 A x y).
Proof. exact (MK_COMB (@lem6892136) (@lem6892135 A x y)). Qed.
Lemma lem6892139 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6892140 {A : Type'} (x : A) (z : A) : (term475 A x z) = (x = z).
Proof. exact (@lem6892139 (x = z)). Qed.
Lemma lem6892141 {A : Type'} (y : A) (x : A) (z : A) : (term526 A y x z) = (term527 A y x z).
Proof. exact (MK_COMB (@lem6892137 A x y) (@lem6892140 A x z)). Qed.
Lemma lem6892142 {A : Type'} (y : A) (x : A) (z : A) : (term525 A y x z) = (term527 A y x z).
Proof. exact (TRANS (@lem6892132 A y x z) (@lem6892141 A y x z)). Qed.
Lemma lem6892143 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6892144 {A : Type'} (y : A) (x : A) (z : A) : (term528 A y x z) = (term529 A y x z).
Proof. exact (MK_COMB (@lem6892143) (@lem6892142 A y x z)). Qed.
Lemma lem6892145 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem6892146 {A : Type'} (x : A) (y : A) (z : A) : (term523 A x y z) = (term530 A x y z).
Proof. exact (MK_COMB (@lem6892144 A y x z) (@lem6892145 A y z)). Qed.
Lemma lem6892147 {A : Type'} (x : A) (y : A) (z : A) : (term520 A y x z) = (term530 A x y z).
Proof. exact (TRANS (@lem6892129 A x y z) (@lem6892146 A x y z)). Qed.
Lemma lem6892149 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (m : nat) (n : nat) (h1 : term268) (h2 : term230) (h3 : term200 m n) : term531 A dom neut op m n f.
Proof. exact (conj (@lem6892027 A dom neut op f m n h1 h2 h3) (@lem6892036 A dom neut op m n f)). Qed.
Lemma lem6892151 {A : Type'} (x : A) (y : A) (z : A) : term530 A x y z.
Proof. exact (EQ_MP (@lem6892147 A x y z) (@lem6892126 A y x z)). Qed.
Lemma lem6892152 {A : Type'} (x : A) (y : A) (z : A) : term530 A x y z.
Proof. exact (@lem6892151 A x y z). Qed.
Lemma lem6892153 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : term532 A dom neut op m n f.
Proof. exact (@lem6892152 A (term216 A dom neut op m n f) (@iterato A nat dom neut op Peano.le (@EMPTY nat) f) (term216 A dom neut op m n f)). Qed.
Lemma lem6892156 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (m : nat) (n : nat) (h1 : term268) (h2 : term230) (h3 : term200 m n) : (@iterato A nat dom neut op Peano.le (@EMPTY nat) f) = (term216 A dom neut op m n f).
Proof. exact (@lem6892153 A dom neut op m n f (@lem6892149 A dom neut op f m n h1 h2 h3)). Qed.
Lemma lem6892157 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (m : nat) (n : nat) (h1 : term268) (h2 : term230) (h3 : term200 m n) : (@iterato A nat dom neut op Peano.le (@EMPTY nat) f) = (term216 A dom neut op m n f).
Proof. exact (@lem6892156 A dom neut op f m n h1 h2 h3). Qed.
Lemma lem6892158 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (m : nat) (n : nat) (h1 : term268) (h2 : term230) (h3 : term200 m n) : term533 A dom neut op m n f.
Proof. exact (fun h0 : term534 A dom neut op m n f => @lem6892157 A dom neut op f m n h1 h2 h3). Qed.
Lemma lem6892160 (p : Prop) : (term416 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6892161 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : (term533 A dom neut op m n f) = ((@iterato A nat dom neut op Peano.le (@EMPTY nat) f) = (term216 A dom neut op m n f)).
Proof. exact (@lem6892160 ((@iterato A nat dom neut op Peano.le (@EMPTY nat) f) = (term216 A dom neut op m n f))). Qed.
Lemma lem6892162 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (m : nat) (n : nat) (h1 : term268) (h2 : term230) (h3 : term200 m n) : (@iterato A nat dom neut op Peano.le (@EMPTY nat) f) = (term216 A dom neut op m n f).
Proof. exact (EQ_MP (@lem6892161 A dom neut op m n f) (@lem6892158 A dom neut op f m n h1 h2 h3)). Qed.
Lemma lem6892164 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term223 A dom op m n f neut) : (@iterato A nat dom neut op Peano.le (@EMPTY nat) f) = neut.
Proof. exact (proj1 (@lem6891020 A dom op m n f neut h1)). Qed.
Lemma lem6892165 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term223 A dom op m n f neut) : term535 A dom op f neut.
Proof. exact (fun h0 : term536 A dom op f neut => @lem6892164 A dom op m n f neut h1). Qed.
Lemma lem6892167 (p : Prop) : (term416 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6892168 {A : Type'} (dom : A -> Prop) (op : type1400 A) (f : nat -> A) (neut : A) : (term535 A dom op f neut) = ((@iterato A nat dom neut op Peano.le (@EMPTY nat) f) = neut).
Proof. exact (@lem6892167 ((@iterato A nat dom neut op Peano.le (@EMPTY nat) f) = neut)). Qed.
Lemma lem6892169 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term223 A dom op m n f neut) : (@iterato A nat dom neut op Peano.le (@EMPTY nat) f) = neut.
Proof. exact (EQ_MP (@lem6892168 A dom op f neut) (@lem6892165 A dom op m n f neut h1)). Qed.
Lemma lem6892170 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term268) (h2 : term230) (h3 : term200 m n) (h4 : term223 A dom op m n f neut) : term537 A m n dom op f neut.
Proof. exact (conj (@lem6892162 A dom neut op f m n h1 h2 h3) (@lem6892169 A dom op m n f neut h4)). Qed.
Lemma lem6892172 {A : Type'} (x : A) (y : A) (z : A) : term530 A x y z.
Proof. exact (EQ_MP (@lem6892147 A x y z) (@lem6892126 A y x z)). Qed.
Lemma lem6892173 {A : Type'} (x : A) (y : A) (z : A) : term530 A x y z.
Proof. exact (@lem6892172 A x y z). Qed.
Lemma lem6892174 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : term538 A dom op m n f neut.
Proof. exact (@lem6892173 A (@iterato A nat dom neut op Peano.le (@EMPTY nat) f) (term216 A dom neut op m n f) neut). Qed.
Lemma lem6892177 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term268) (h2 : term230) (h3 : term200 m n) (h4 : term223 A dom op m n f neut) : (term216 A dom neut op m n f) = neut.
Proof. exact (@lem6892174 A dom op m n f neut (@lem6892170 A dom op m n f neut h1 h2 h3 h4)). Qed.
Lemma lem6892178 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term268) (h2 : term230) (h3 : term200 m n) (h4 : term223 A dom op m n f neut) : term539 A dom op m n f neut.
Proof. exact (fun h0 : term399 A dom op m n f neut => @lem6892177 A dom op m n f neut h1 h2 h3 h4). Qed.
Lemma lem6892180 (p : Prop) : (term416 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6892181 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term539 A dom op m n f neut) = ((term216 A dom neut op m n f) = neut).
Proof. exact (@lem6892180 ((term216 A dom neut op m n f) = neut)). Qed.
Lemma lem6892182 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term268) (h2 : term230) (h3 : term200 m n) (h4 : term223 A dom op m n f neut) : (term216 A dom neut op m n f) = neut.
Proof. exact (EQ_MP (@lem6892181 A dom op m n f neut) (@lem6892178 A dom op m n f neut h1 h2 h3 h4)). Qed.
Lemma lem6892185 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6892187 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term399 A dom op m n f neut) = (term540 A dom op m n f neut).
Proof. exact (@lem6892185 ((term216 A dom neut op m n f) = neut)). Qed.
Lemma lem6892190 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term223 A dom op m n f neut) : term540 A dom op m n f neut.
Proof. exact (EQ_MP (@lem6892187 A dom op m n f neut) (@lem6891280 A dom op m n f neut h1)). Qed.
Lemma lem6892193 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term268) (h2 : term230) (h3 : term200 m n) (h4 : term223 A dom op m n f neut) : False.
Proof. exact (@lem6892190 A dom op m n f neut h4 (@lem6892182 A dom op m n f neut h1 h2 h3 h4)). Qed.
Lemma lem6892194 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term268) (h2 : term230) (h3 : term200 m n) (h4 : term223 A dom op m n f neut) : term541.
Proof. exact (fun h0 : ~ False => @lem6892193 A dom op m n f neut h1 h2 h3 h4). Qed.
Lemma lem6892196 (p : Prop) : (term416 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6892197 : term541 = False.
Proof. exact (@lem6892196 False). Qed.
Lemma lem6892198 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term268) (h2 : term230) (h3 : term200 m n) (h4 : term223 A dom op m n f neut) : False.
Proof. exact (EQ_MP (@lem6892197) (@lem6892194 A dom op m n f neut h1 h2 h3 h4)). Qed.
Lemma lem6892199 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term268) (h2 : term230) (h3 : term200 m n) (h4 : term223 A dom op m n f neut) : (term200 m n) = False.
Proof. exact (prop_ext (fun h5 : term200 m n => @lem6892198 A dom op m n f neut h1 h2 h3 h4) (fun h5 : False => @lem6890368 m n h3)). Qed.
Lemma lem6892200 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term268) (h2 : term230) (h3 : term200 m n) (h4 : term223 A dom op m n f neut) : False.
Proof. exact (EQ_MP (@lem6892199 A dom op m n f neut h1 h2 h3 h4) (@lem6890368 m n h3)). Qed.
Lemma lem6892201 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term268) (h2 : term200 m n) (h3 : term223 A dom op m n f neut) : term228.
Proof. exact (fun h0 : term230 => @lem6892200 A dom op m n f neut h1 h0 h2 h3). Qed.
Lemma lem6892202 : term228 = term229.
Proof. exact (@lem69 term230). Qed.
Lemma lem6892203 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term268) (h2 : term200 m n) (h3 : term223 A dom op m n f neut) : term229.
Proof. exact (EQ_MP (@lem6892202) (@lem6892201 A dom op m n f neut h1 h2 h3)). Qed.
Lemma lem6892204 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term200 m n) (h2 : term223 A dom op m n f neut) : term233.
Proof. exact (fun h0 : term268 => @lem6892203 A dom op m n f neut h0 h1 h2). Qed.
Lemma lem6892205 {A : Type'} (dom : A -> Prop) (op : type1400 A) (f : nat -> A) (neut : A) (m : nat) (n : nat) (h1 : term200 m n) : term236 A dom op m n f neut.
Proof. exact (fun h0 : term223 A dom op m n f neut => @lem6892204 A dom op m n f neut h1 h0). Qed.
Lemma lem6892206 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : term237 A dom op m n f neut.
Proof. exact (fun h0 : term200 m n => @lem6892205 A dom op f neut m n h0). Qed.
Lemma lem6892211 {A : Type'} (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : term241 A op m n f neut.
Proof. exact (fun dom : A -> Prop => @lem6892206 A dom op m n f neut). Qed.
Lemma lem6892216 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (neut : A) : term245 A m n f neut.
Proof. exact (fun op : type1400 A => @lem6892211 A op m n f neut). Qed.
Lemma lem6892221 {A : Type'} (n : nat) (f : nat -> A) (neut : A) : term249 A n f neut.
Proof. exact (fun m : nat => @lem6892216 A m n f neut). Qed.
Lemma lem6892226 {A : Type'} (f : nat -> A) (neut : A) : term253 A f neut.
Proof. exact (fun n : nat => @lem6892221 A n f neut). Qed.
Lemma lem6892231 {A : Type'} (neut : A) : term257 A neut.
Proof. exact (fun f : nat -> A => @lem6892226 A f neut). Qed.
Lemma lem6892236 {A : Type'} : term261 A.
Proof. exact (fun neut : A => @lem6892231 A neut). Qed.
Lemma lem6892237 {A : Type'} : term260 A.
Proof. exact (EQ_MP (@lem6890358 A) (@lem6892236 A)). Qed.
Lemma lem6892238 {A : Type'} (neut : A) : term542 A neut.
Proof. exact (@lem6892237 A neut). Qed.
Lemma lem6892239 {A : Type'} (neut : A) : (term542 A neut) = (term256 A neut).
Proof. exact (eq_refl (term542 A neut)). Qed.
Lemma lem6892240 {A : Type'} (neut : A) : term256 A neut.
Proof. exact (EQ_MP (@lem6892239 A neut) (@lem6892238 A neut)). Qed.
Lemma lem6892241 {A : Type'} (neut : A) (f : nat -> A) : term543 A neut f.
Proof. exact (@lem6892240 A neut f). Qed.
Lemma lem6892242 {A : Type'} (f : nat -> A) (neut : A) : (term543 A neut f) = (term252 A f neut).
Proof. exact (eq_refl (term543 A neut f)). Qed.
Lemma lem6892243 {A : Type'} (f : nat -> A) (neut : A) : term252 A f neut.
Proof. exact (EQ_MP (@lem6892242 A f neut) (@lem6892241 A neut f)). Qed.
Lemma lem6892244 {A : Type'} (f : nat -> A) (neut : A) (n : nat) : term544 A f neut n.
Proof. exact (@lem6892243 A f neut n). Qed.
Lemma lem6892245 {A : Type'} (n : nat) (f : nat -> A) (neut : A) : (term544 A f neut n) = (term248 A n f neut).
Proof. exact (eq_refl (term544 A f neut n)). Qed.
Lemma lem6892246 {A : Type'} (n : nat) (f : nat -> A) (neut : A) : term248 A n f neut.
Proof. exact (EQ_MP (@lem6892245 A n f neut) (@lem6892244 A f neut n)). Qed.
Lemma lem6892247 {A : Type'} (n : nat) (f : nat -> A) (neut : A) (m : nat) : term545 A n f neut m.
Proof. exact (@lem6892246 A n f neut m). Qed.
Lemma lem6892248 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term545 A n f neut m) = (term244 A m n f neut).
Proof. exact (eq_refl (term545 A n f neut m)). Qed.
Lemma lem6892249 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (neut : A) : term244 A m n f neut.
Proof. exact (EQ_MP (@lem6892248 A m n f neut) (@lem6892247 A n f neut m)). Qed.
Lemma lem6892250 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (neut : A) (op : type1400 A) : term546 A m n f neut op.
Proof. exact (@lem6892249 A m n f neut op). Qed.
Lemma lem6892251 {A : Type'} (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term546 A m n f neut op) = (term240 A op m n f neut).
Proof. exact (eq_refl (term546 A m n f neut op)). Qed.
Lemma lem6892252 {A : Type'} (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : term240 A op m n f neut.
Proof. exact (EQ_MP (@lem6892251 A op m n f neut) (@lem6892250 A m n f neut op)). Qed.
Lemma lem6892253 {A : Type'} (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (dom : A -> Prop) : term547 A op m n f neut dom.
Proof. exact (@lem6892252 A op m n f neut dom). Qed.
Lemma lem6892254 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term547 A op m n f neut dom) = (term224 A dom op m n f neut).
Proof. exact (eq_refl (term547 A op m n f neut dom)). Qed.
Lemma lem6892255 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : term224 A dom op m n f neut.
Proof. exact (EQ_MP (@lem6892254 A dom op m n f neut) (@lem6892253 A op m n f neut dom)). Qed.
Lemma lem6892257 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : term224 A dom op m n f neut.
Proof. exact (@lem6890114 A dom op m n f neut (@lem6892255 A dom op m n f neut)). Qed.
Lemma lem6892258 {A : Type'} (dom : A -> Prop) (op : type1400 A) (f : nat -> A) (neut : A) (m : nat) (n : nat) (h1 : term200 m n) : term235 A dom op m n f neut.
Proof. exact (@lem6892257 A dom op m n f neut (@lem6889772 m n h1)). Qed.
Lemma lem6892259 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term200 m n) (h2 : term223 A dom op m n f neut) : term232.
Proof. exact (@lem6892258 A dom op f neut m n h1 (@lem6890098 A dom op m n f neut h2)). Qed.
Lemma lem6892260 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term200 m n) (h2 : term223 A dom op m n f neut) : term228.
Proof. exact (@lem6892259 A dom op m n f neut h1 h2 (@lem97961)). Qed.
Lemma lem6892261 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term200 m n) (h2 : term223 A dom op m n f neut) : False.
Proof. exact (@lem6892260 A dom op m n f neut h1 h2 (@lem5376447)). Qed.
Lemma lem6892262 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term200 m n) (h2 : term223 A dom op m n f neut) : (term223 A dom op m n f neut) = False.
Proof. exact (prop_ext (fun h3 : term223 A dom op m n f neut => @lem6892261 A dom op m n f neut h1 h2) (fun h3 : False => @lem6890098 A dom op m n f neut h2)). Qed.
Lemma lem6892263 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) (h1 : term200 m n) (h2 : term223 A dom op m n f neut) : False.
Proof. exact (EQ_MP (@lem6892262 A dom op m n f neut h1 h2) (@lem6890098 A dom op m n f neut h2)). Qed.
Lemma lem6892264 {A : Type'} (dom : A -> Prop) (op : type1400 A) (f : nat -> A) (neut : A) (m : nat) (n : nat) (h1 : term200 m n) : term222 A dom op m n f neut.
Proof. exact (fun h0 : term223 A dom op m n f neut => @lem6892263 A dom op m n f neut h1 h0). Qed.
Lemma lem6892265 {A : Type'} (dom : A -> Prop) (op : type1400 A) (f : nat -> A) (neut : A) (m : nat) (n : nat) (h1 : term200 m n) : term221 A dom op m n f neut.
Proof. exact (EQ_MP (@lem6890097 A dom op m n f neut) (@lem6892264 A dom op f neut m n h1)). Qed.
Lemma lem6892266 {A : Type'} (m : nat) (n : nat) (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (h1 : term200 m n) (h2 : term175 A dom neut op f) : (term216 A dom neut op m n f) = neut.
Proof. exact (@lem6892265 A dom op f neut m n h1 (@lem6890093 A dom neut op f h2)). Qed.
Lemma lem6892268 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (h1 : term175 A dom neut op f) : term175 A dom neut op f.
Proof. exact (h1). Qed.
Lemma lem6892269 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (h1 : term175 A dom neut op f) : term548 A dom neut op f.
Proof. exact (proj2 (@lem6892268 A dom neut op f h1)). Qed.
Lemma lem6892270 {A : Type'} (m : nat) (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (h1 : term175 A dom neut op f) : term549 A dom neut op f m.
Proof. exact (@lem6892269 A dom neut op f h1 m). Qed.
Lemma lem6892271 {A : Type'} (m : nat) (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) : (term549 A dom neut op f m) = (term550 A m dom neut op f).
Proof. exact (eq_refl (term549 A dom neut op f m)). Qed.
Lemma lem6892272 {A : Type'} (m : nat) (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (h1 : term175 A dom neut op f) : term550 A m dom neut op f.
Proof. exact (EQ_MP (@lem6892271 A m dom neut op f) (@lem6892270 A m dom neut op f h1)). Qed.
Lemma lem6892273 {A : Type'} (m : nat) (n : nat) (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (h1 : term175 A dom neut op f) : term551 A dom neut op f m n.
Proof. exact (@lem6892272 A m dom neut op f h1 (term552 m n)). Qed.
Lemma lem6892274 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : (term551 A dom neut op f m n) = (term553 A dom neut op m n f).
Proof. exact (eq_refl (term551 A dom neut op f m n)). Qed.
Lemma lem6892275 {A : Type'} (m : nat) (n : nat) (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (h1 : term175 A dom neut op f) : term553 A dom neut op m n f.
Proof. exact (EQ_MP (@lem6892274 A dom neut op m n f) (@lem6892273 A m n dom neut op f h1)). Qed.
Lemma lem6892277 (p : Prop) (q : Prop) (r : Prop) : term554 p q r.
Proof. exact (@lem137 p q r (@lem129 p q r)). Qed.
Lemma lem6892278 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : term555 A dom neut op m n f.
Proof. exact (@lem6892277 (term556 A n f dom neut m) ((term217 A dom neut op m n f) = (term557 A dom neut op m n f)) ((term217 A dom neut op m n f) = (term183 A dom neut op m n f))). Qed.
Lemma lem6892282 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term558 A s P.
Proof. exact (fun h0 : @FINITE A s => @lem6889705 A P s h0). Qed.
Lemma lem6892283 (s : nat -> Prop) (P : nat -> Prop) : term559 s P.
Proof. exact (@lem6892282 nat s P). Qed.
Lemma lem6892284 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) : term560 A m n f dom neut.
Proof. exact (@lem6892283 (term552 m n) (term561 A f dom neut)). Qed.
Lemma lem6892285 {A : Type'} (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term562 A f dom neut j) = (term563 A f j dom neut).
Proof. exact (eq_refl (term562 A f dom neut j)). Qed.
Lemma lem6892286 (j : nat) (m : nat) (n : nat) : (term564 j m n) = (term564 j m n).
Proof. exact (eq_refl (term564 j m n)). Qed.
Lemma lem6892287 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term565 A m n f dom neut j) = (term566 A m n f j dom neut).
Proof. exact (MK_COMB (@lem6892286 j m n) (@lem6892285 A f j dom neut)). Qed.
Lemma lem6892288 (GEN_PVAR_272 : nat) : (@SETSPEC nat GEN_PVAR_272) = (@SETSPEC nat GEN_PVAR_272).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_272)). Qed.
Lemma lem6892289 {A : Type'} (GEN_PVAR_272 : nat) (m : nat) (n : nat) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term567 A GEN_PVAR_272 m n f dom neut j) = (term568 A GEN_PVAR_272 m n f j dom neut).
Proof. exact (MK_COMB (@lem6892288 GEN_PVAR_272) (@lem6892287 A m n f j dom neut)). Qed.
Lemma lem6892290 (j : nat) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem6892291 {A : Type'} (GEN_PVAR_272 : nat) (m : nat) (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (j : nat) : (term569 A GEN_PVAR_272 m n f dom neut j) = (term570 A GEN_PVAR_272 m n f dom neut j).
Proof. exact (MK_COMB (@lem6892289 A GEN_PVAR_272 m n f j dom neut) (@lem6892290 j)). Qed.
Lemma lem6892292 {A : Type'} (GEN_PVAR_272 : nat) (m : nat) (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) : (term571 A GEN_PVAR_272 m n f dom neut) = (term572 A GEN_PVAR_272 m n f dom neut).
Proof. exact (fun_ext (fun j : nat => @lem6892291 A GEN_PVAR_272 m n f dom neut j)). Qed.
Lemma lem6892293 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6892294 {A : Type'} (GEN_PVAR_272 : nat) (m : nat) (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) : (term573 A GEN_PVAR_272 m n f dom neut) = (term574 A GEN_PVAR_272 m n f dom neut).
Proof. exact (MK_COMB (@lem6892293) (@lem6892292 A GEN_PVAR_272 m n f dom neut)). Qed.
Lemma lem6892295 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) : (term575 A m n f dom neut) = (term576 A m n f dom neut).
Proof. exact (fun_ext (fun GEN_PVAR_272 : nat => @lem6892294 A GEN_PVAR_272 m n f dom neut)). Qed.
Lemma lem6892296 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem6892297 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) : (term577 A m n f dom neut) = (term578 A m n f dom neut).
Proof. exact (MK_COMB (@lem6892296) (@lem6892295 A m n f dom neut)). Qed.
Lemma lem6892298 : (@FINITE nat) = (@FINITE nat).
Proof. exact (eq_refl (@FINITE nat)). Qed.
Lemma lem6892299 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) : (term579 A m n f dom neut) = (term580 A m n f dom neut).
Proof. exact (MK_COMB (@lem6892298) (@lem6892297 A m n f dom neut)). Qed.
Lemma lem6892300 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6892301 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) : (term581 A m n f dom neut) = (term582 A m n f dom neut).
Proof. exact (MK_COMB (@lem6892300) (@lem6892299 A m n f dom neut)). Qed.
Lemma lem6892302 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem6892303 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) : ((term579 A m n f dom neut) = True) = ((term580 A m n f dom neut) = True).
Proof. exact (MK_COMB (@lem6892301 A m n f dom neut) (@lem6892302)). Qed.
Lemma lem6892304 (m : nat) (n : nat) : (term583 m n) = (term583 m n).
Proof. exact (eq_refl (term583 m n)). Qed.
Lemma lem6892305 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) : (term560 A m n f dom neut) = (term584 A m n f dom neut).
Proof. exact (MK_COMB (@lem6892304 m n) (@lem6892303 A m n f dom neut)). Qed.
Lemma lem6892306 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) : term584 A m n f dom neut.
Proof. exact (EQ_MP (@lem6892305 A m n f dom neut) (@lem6892284 A m n f dom neut)). Qed.
Lemma lem6892308 (m : nat) (n : nat) : (term159 m n) = True.
Proof. exact (EQ_MP (@lem6889694 m n) (@lem6889693 m n)). Qed.
Lemma lem6892309 (m : nat) (n : nat) : (term585 m n) = True.
Proof. exact (@lem6892308 (term3 m) n). Qed.
Lemma lem6892310 (m : nat) (n : nat) : True = (term585 m n).
Proof. exact (SYM (@lem6892309 m n)). Qed.
Lemma lem6892311 (m : nat) (n : nat) : term585 m n.
Proof. exact (EQ_MP (@lem6892310 m n) (@lem0)). Qed.
Lemma lem6892312 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) : (term580 A m n f dom neut) = True.
Proof. exact (@lem6892306 A m n f dom neut (@lem6892311 m n)). Qed.
Lemma lem6892313 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6892314 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) : (term586 A m n f dom neut) = (and True).
Proof. exact (MK_COMB (@lem6892313) (@lem6892312 A m n f dom neut)). Qed.
Lemma lem6892324 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term587 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6892325 (p : Prop) (q : Prop) (p' : Prop) : term588 p q p'.
Proof. exact (fun q' : Prop => @lem6892324 p q p' q'). Qed.
Lemma lem6892326 (p : Prop) (q : Prop) : term589 p q.
Proof. exact (fun p' : Prop => @lem6892325 p q p'). Qed.
Lemma lem6892327 (n : nat) (j : nat) (m : nat) : term590 n j m.
Proof. exact (@lem6892326 (term591 j m n) (term592 j m)). Qed.
Lemma lem6892328 (n : nat) (j : nat) (m : nat) (p' : Prop) : term593 n j m p'.
Proof. exact (@lem6892327 n j m p'). Qed.
Lemma lem6892329 (n : nat) (j : nat) (m : nat) (p' : Prop) : (term593 n j m p') = (term594 n j m p').
Proof. exact (eq_refl (term593 n j m p')). Qed.
Lemma lem6892330 (n : nat) (j : nat) (m : nat) (p' : Prop) : term594 n j m p'.
Proof. exact (EQ_MP (@lem6892329 n j m p') (@lem6892328 n j m p')). Qed.
Lemma lem6892331 (n : nat) (j : nat) (m : nat) (p' : Prop) (q' : Prop) : term595 n j m p' q'.
Proof. exact (@lem6892330 n j m p' q'). Qed.
Lemma lem6892332 (n : nat) (j : nat) (m : nat) (p' : Prop) (q' : Prop) : (term595 n j m p' q') = (term596 n j m p' q').
Proof. exact (eq_refl (term595 n j m p' q')). Qed.
Lemma lem6892333 (n : nat) (j : nat) (m : nat) (p' : Prop) (q' : Prop) : term596 n j m p' q'.
Proof. exact (EQ_MP (@lem6892332 n j m p' q') (@lem6892331 n j m p' q')). Qed.
Lemma lem6892335 (m : nat) (p : nat) (n : nat) : (term154 p m n) = (term155 m p n).
Proof. exact (EQ_MP (@lem6889686 m p n) (@lem6889685 m n p)). Qed.
Lemma lem6892336 (m : nat) (j : nat) (n : nat) : (term591 j m n) = (term597 m j n).
Proof. exact (@lem6892335 (term3 m) j n). Qed.
Lemma lem6892339 (m : nat) (j : nat) (n : nat) (q' : Prop) : term598 m j n q'.
Proof. exact (@lem6892333 n j m (term597 m j n) q'). Qed.
Lemma lem6892340 (m : nat) (j : nat) (n : nat) (q' : Prop) : term599 m j n q'.
Proof. exact (@lem6892339 m j n q' (@lem6892336 m j n)). Qed.
Lemma lem6892354 (j : nat) (m : nat) : (term592 j m) = (term592 j m).
Proof. exact (eq_refl (term592 j m)). Qed.
Lemma lem6892355 (n : nat) (j : nat) (m : nat) : term600 n j m.
Proof. exact (fun h0 : term597 m j n => @lem6892354 j m). Qed.
Lemma lem6892356 (n : nat) (j : nat) (m : nat) : term601 n j m.
Proof. exact (@lem6892340 m j n (term592 j m)). Qed.
Lemma lem6892357 (n : nat) (j : nat) (m : nat) : (term602 n j m) = (term603 n j m).
Proof. exact (@lem6892356 n j m (@lem6892355 n j m)). Qed.
Lemma lem6892401 (n : nat) (m : nat) : (term604 n m) = (term605 n m).
Proof. exact (fun_ext (fun j : nat => @lem6892357 n j m)). Qed.
Lemma lem6892445 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6892446 (n : nat) (m : nat) : (term606 n m) = (term607 n m).
Proof. exact (MK_COMB (@lem6892445) (@lem6892401 n m)). Qed.
Lemma lem6892494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6892495 (n : nat) (m : nat) : (term608 n m) = (term609 n m).
Proof. exact (MK_COMB (@lem6892494) (@lem6892446 n m)). Qed.
Lemma lem6892550 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term587 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6892551 (p : Prop) (q : Prop) (p' : Prop) : term588 p q p'.
Proof. exact (fun q' : Prop => @lem6892550 p q p' q'). Qed.
Lemma lem6892552 (p : Prop) (q : Prop) : term589 p q.
Proof. exact (fun p' : Prop => @lem6892551 p q p'). Qed.
Lemma lem6892553 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (j : nat) (m : nat) : term610 A n f dom neut j m.
Proof. exact (@lem6892552 (term611 A m n f j dom neut) (j = m)). Qed.
Lemma lem6892554 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (j : nat) (m : nat) (p' : Prop) : term612 A n f dom neut j m p'.
Proof. exact (@lem6892553 A n f dom neut j m p'). Qed.
Lemma lem6892555 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (j : nat) (m : nat) (p' : Prop) : (term612 A n f dom neut j m p') = (term613 A n f dom neut j m p').
Proof. exact (eq_refl (term612 A n f dom neut j m p')). Qed.
Lemma lem6892556 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (j : nat) (m : nat) (p' : Prop) : term613 A n f dom neut j m p'.
Proof. exact (EQ_MP (@lem6892555 A n f dom neut j m p') (@lem6892554 A n f dom neut j m p')). Qed.
Lemma lem6892557 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (j : nat) (m : nat) (p' : Prop) (q' : Prop) : term614 A n f dom neut j m p' q'.
Proof. exact (@lem6892556 A n f dom neut j m p' q'). Qed.
Lemma lem6892558 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (j : nat) (m : nat) (p' : Prop) (q' : Prop) : (term614 A n f dom neut j m p' q') = (term615 A n f dom neut j m p' q').
Proof. exact (eq_refl (term614 A n f dom neut j m p' q')). Qed.
Lemma lem6892559 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (j : nat) (m : nat) (p' : Prop) (q' : Prop) : term615 A n f dom neut j m p' q'.
Proof. exact (EQ_MP (@lem6892558 A n f dom neut j m p' q') (@lem6892557 A n f dom neut j m p' q')). Qed.
Lemma lem6892565 (m : nat) (p : nat) (n : nat) : (term154 p m n) = (term155 m p n).
Proof. exact (EQ_MP (@lem6889686 m p n) (@lem6889685 m n p)). Qed.
Lemma lem6892566 (m : nat) (j : nat) (n : nat) : (term591 j m n) = (term597 m j n).
Proof. exact (@lem6892565 (term3 m) j n). Qed.
Lemma lem6892569 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6892570 (m : nat) (j : nat) (n : nat) : (term564 j m n) = (term616 m j n).
Proof. exact (MK_COMB (@lem6892569) (@lem6892566 m j n)). Qed.
Lemma lem6892573 {A : Type'} (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term563 A f j dom neut) = (term563 A f j dom neut).
Proof. exact (eq_refl (term563 A f j dom neut)). Qed.
Lemma lem6892574 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term566 A m n f j dom neut) = (term617 A m n f j dom neut).
Proof. exact (MK_COMB (@lem6892570 m j n) (@lem6892573 A f j dom neut)). Qed.
Lemma lem6892579 (j : nat) (m : nat) : (term618 j m) = (term618 j m).
Proof. exact (eq_refl (term618 j m)). Qed.
Lemma lem6892580 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term611 A m n f j dom neut) = (term619 A m n f j dom neut).
Proof. exact (MK_COMB (@lem6892579 j m) (@lem6892574 A m n f j dom neut)). Qed.
Lemma lem6892587 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (q' : Prop) : term620 A m n f j dom neut q'.
Proof. exact (@lem6892559 A n f dom neut j m (term619 A m n f j dom neut) q'). Qed.
Lemma lem6892588 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (q' : Prop) : term621 A m n f j dom neut q'.
Proof. exact (@lem6892587 A m n f j dom neut q' (@lem6892580 A m n f j dom neut)). Qed.
Lemma lem6892606 (j : nat) (m : nat) : (j = m) = (j = m).
Proof. exact (eq_refl (j = m)). Qed.
Lemma lem6892607 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (j : nat) (m : nat) : term622 A n f dom neut j m.
Proof. exact (fun h0 : term619 A m n f j dom neut => @lem6892606 j m). Qed.
Lemma lem6892608 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (j : nat) (m : nat) : term623 A n f dom neut j m.
Proof. exact (@lem6892588 A m n f j dom neut (j = m)). Qed.
Lemma lem6892609 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (j : nat) (m : nat) : (term624 A n f dom neut j m) = (term625 A n f dom neut j m).
Proof. exact (@lem6892608 A n f dom neut j m (@lem6892607 A n f dom neut j m)). Qed.
Lemma lem6892661 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term626 A n f dom neut m) = (term627 A n f dom neut m).
Proof. exact (fun_ext (fun j : nat => @lem6892609 A n f dom neut j m)). Qed.
Lemma lem6892713 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6892714 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term628 A n f dom neut m) = (term629 A n f dom neut m).
Proof. exact (MK_COMB (@lem6892713) (@lem6892661 A n f dom neut m)). Qed.
Lemma lem6892770 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term630 A n f dom neut m) = (term631 A n f dom neut m).
Proof. exact (MK_COMB (@lem6892495 n m) (@lem6892714 A n f dom neut m)). Qed.
Lemma lem6892875 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term556 A n f dom neut m) = (term632 A n f dom neut m).
Proof. exact (MK_COMB (@lem6892314 A m n f dom neut) (@lem6892770 A n f dom neut m)). Qed.
Lemma lem6892877 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6892878 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term632 A n f dom neut m) = (term631 A n f dom neut m).
Proof. exact (@lem6892877 (term631 A n f dom neut m)). Qed.
Lemma lem6892983 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term556 A n f dom neut m) = (term631 A n f dom neut m).
Proof. exact (TRANS (@lem6892875 A n f dom neut m) (@lem6892878 A n f dom neut m)). Qed.
Lemma lem6892984 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term631 A n f dom neut m) = (term556 A n f dom neut m).
Proof. exact (SYM (@lem6892983 A n f dom neut m)). Qed.
Lemma lem6893032 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (j : nat) (m : nat) : (term625 A n f dom neut j m) = (term625 A n f dom neut j m).
Proof. exact (eq_refl (term625 A n f dom neut j m)). Qed.
Lemma lem6893033 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term627 A n f dom neut m) = (term627 A n f dom neut m).
Proof. exact (fun_ext (fun j : nat => @lem6893032 A n f dom neut j m)). Qed.
Lemma lem6893034 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6893035 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term629 A n f dom neut m) = (term629 A n f dom neut m).
Proof. exact (MK_COMB (@lem6893034) (@lem6893033 A n f dom neut m)). Qed.
Lemma lem6893052 (n : nat) (j : nat) (m : nat) : (term603 n j m) = (term603 n j m).
Proof. exact (eq_refl (term603 n j m)). Qed.
Lemma lem6893053 (n : nat) (m : nat) : (term605 n m) = (term605 n m).
Proof. exact (fun_ext (fun j : nat => @lem6893052 n j m)). Qed.
Lemma lem6893054 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6893055 (n : nat) (m : nat) : (term607 n m) = (term607 n m).
Proof. exact (MK_COMB (@lem6893054) (@lem6893053 n m)). Qed.
Lemma lem6893056 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6893057 (n : nat) (m : nat) : (term609 n m) = (term609 n m).
Proof. exact (MK_COMB (@lem6893056) (@lem6893055 n m)). Qed.
Lemma lem6893059 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term631 A n f dom neut m) = (term631 A n f dom neut m).
Proof. exact (MK_COMB (@lem6893057 n m) (@lem6893035 A n f dom neut m)). Qed.
Lemma lem6893066 (m : nat) (j : nat) (n : nat) : (term633 m j n) = (term634 m j n).
Proof. exact (@lem17045 (term635 m j) (Peano.le j n)). Qed.
Lemma lem6893075 (j : nat) (m : nat) : (term592 j m) = (term592 j m).
Proof. exact (eq_refl (term592 j m)). Qed.
Lemma lem6893076 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6893077 (m : nat) (j : nat) (n : nat) : (term636 m j n) = (term637 m j n).
Proof. exact (MK_COMB (@lem6893076) (@lem6893066 m j n)). Qed.
Lemma lem6893078 (n : nat) (j : nat) (m : nat) : (term638 n j m) = (term639 n j m).
Proof. exact (MK_COMB (@lem6893077 m j n) (@lem6893075 j m)). Qed.
Lemma lem6893079 (n : nat) (j : nat) (m : nat) : (term603 n j m) = (term638 n j m).
Proof. exact (@lem17265 (term597 m j n) (term592 j m)). Qed.
Lemma lem6893080 (n : nat) (j : nat) (m : nat) : (term603 n j m) = (term639 n j m).
Proof. exact (TRANS (@lem6893079 n j m) (@lem6893078 n j m)). Qed.
Lemma lem6893081 (n : nat) (m : nat) : (term605 n m) = (term640 n m).
Proof. exact (fun_ext (fun j : nat => @lem6893080 n j m)). Qed.
Lemma lem6893082 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6893083 (n : nat) (m : nat) : (term607 n m) = (term641 n m).
Proof. exact (MK_COMB (@lem6893082) (@lem6893081 n m)). Qed.
Lemma lem6893091 (m : nat) (j : nat) (n : nat) : (term633 m j n) = (term634 m j n).
Proof. exact (@lem17045 (term635 m j) (Peano.le j n)). Qed.
Lemma lem6893092 {A : Type'} (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term642 A f j dom neut) = (term642 A f j dom neut).
Proof. exact (eq_refl (term642 A f j dom neut)). Qed.
Lemma lem6893093 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6893094 (m : nat) (j : nat) (n : nat) : (term636 m j n) = (term637 m j n).
Proof. exact (MK_COMB (@lem6893093) (@lem6893091 m j n)). Qed.
Lemma lem6893095 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term643 A m n f j dom neut) = (term644 A m n f j dom neut).
Proof. exact (MK_COMB (@lem6893094 m j n) (@lem6893092 A f j dom neut)). Qed.
Lemma lem6893096 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term645 A m n f j dom neut) = (term643 A m n f j dom neut).
Proof. exact (@lem17045 (term597 m j n) (term563 A f j dom neut)). Qed.
Lemma lem6893097 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term645 A m n f j dom neut) = (term644 A m n f j dom neut).
Proof. exact (TRANS (@lem6893096 A m n f j dom neut) (@lem6893095 A m n f j dom neut)). Qed.
Lemma lem6893099 (j : nat) (m : nat) : (term388 j m) = (term388 j m).
Proof. exact (eq_refl (term388 j m)). Qed.
Lemma lem6893100 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term646 A m n f j dom neut) = (term647 A m n f j dom neut).
Proof. exact (MK_COMB (@lem6893099 j m) (@lem6893097 A m n f j dom neut)). Qed.
Lemma lem6893101 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term648 A m n f j dom neut) = (term646 A m n f j dom neut).
Proof. exact (@lem17045 (Peano.le j m) (term617 A m n f j dom neut)). Qed.
Lemma lem6893102 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term648 A m n f j dom neut) = (term647 A m n f j dom neut).
Proof. exact (TRANS (@lem6893101 A m n f j dom neut) (@lem6893100 A m n f j dom neut)). Qed.
Lemma lem6893103 (j : nat) (m : nat) : (j = m) = (j = m).
Proof. exact (eq_refl (j = m)). Qed.
Lemma lem6893104 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6893105 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term649 A m n f j dom neut) = (term650 A m n f j dom neut).
Proof. exact (MK_COMB (@lem6893104) (@lem6893102 A m n f j dom neut)). Qed.
Lemma lem6893106 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (j : nat) (m : nat) : (term651 A n f dom neut j m) = (term652 A n f dom neut j m).
Proof. exact (MK_COMB (@lem6893105 A m n f j dom neut) (@lem6893103 j m)). Qed.
Lemma lem6893107 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (j : nat) (m : nat) : (term625 A n f dom neut j m) = (term651 A n f dom neut j m).
Proof. exact (@lem17265 (term619 A m n f j dom neut) (j = m)). Qed.
Lemma lem6893108 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (j : nat) (m : nat) : (term625 A n f dom neut j m) = (term652 A n f dom neut j m).
Proof. exact (TRANS (@lem6893107 A n f dom neut j m) (@lem6893106 A n f dom neut j m)). Qed.
Lemma lem6893109 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term627 A n f dom neut m) = (term653 A n f dom neut m).
Proof. exact (fun_ext (fun j : nat => @lem6893108 A n f dom neut j m)). Qed.
Lemma lem6893110 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6893111 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term629 A n f dom neut m) = (term654 A n f dom neut m).
Proof. exact (MK_COMB (@lem6893110) (@lem6893109 A n f dom neut m)). Qed.
Lemma lem6893112 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6893113 (n : nat) (m : nat) : (term609 n m) = (term655 n m).
Proof. exact (MK_COMB (@lem6893112) (@lem6893083 n m)). Qed.
Lemma lem6893114 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term631 A n f dom neut m) = (term656 A n f dom neut m).
Proof. exact (MK_COMB (@lem6893113 n m) (@lem6893111 A n f dom neut m)). Qed.
Lemma lem6893115 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term631 A n f dom neut m) = (term656 A n f dom neut m).
Proof. exact (TRANS (@lem6893059 A n f dom neut m) (@lem6893114 A n f dom neut m)). Qed.
Lemma lem6893116 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (j : nat) (m : nat) : (term652 A n f dom neut j m) = (term652 A n f dom neut j m).
Proof. exact (eq_refl (term652 A n f dom neut j m)). Qed.
Lemma lem6893117 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term653 A n f dom neut m) = (term653 A n f dom neut m).
Proof. exact (fun_ext (fun j : nat => @lem6893116 A n f dom neut j m)). Qed.
Lemma lem6893118 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6893119 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term654 A n f dom neut m) = (term654 A n f dom neut m).
Proof. exact (MK_COMB (@lem6893118) (@lem6893117 A n f dom neut m)). Qed.
Lemma lem6893120 (n : nat) (j : nat) (m : nat) : (term639 n j m) = (term639 n j m).
Proof. exact (eq_refl (term639 n j m)). Qed.
Lemma lem6893121 (n : nat) (m : nat) : (term640 n m) = (term640 n m).
Proof. exact (fun_ext (fun j : nat => @lem6893120 n j m)). Qed.
Lemma lem6893122 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6893123 (n : nat) (m : nat) : (term641 n m) = (term641 n m).
Proof. exact (MK_COMB (@lem6893122) (@lem6893121 n m)). Qed.
Lemma lem6893124 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6893125 (n : nat) (m : nat) : (term655 n m) = (term655 n m).
Proof. exact (MK_COMB (@lem6893124) (@lem6893123 n m)). Qed.
Lemma lem6893126 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term656 A n f dom neut m) = (term656 A n f dom neut m).
Proof. exact (MK_COMB (@lem6893125 n m) (@lem6893119 A n f dom neut m)). Qed.
Lemma lem6893163 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term631 A n f dom neut m) = (term656 A n f dom neut m).
Proof. exact (TRANS (@lem6893115 A n f dom neut m) (@lem6893126 A n f dom neut m)). Qed.
Lemma lem6893214 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (j : nat) (m : nat) : (term652 A n f dom neut j m) = (term652 A n f dom neut j m).
Proof. exact (eq_refl (term652 A n f dom neut j m)). Qed.
Lemma lem6893215 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term653 A n f dom neut m) = (term653 A n f dom neut m).
Proof. exact (fun_ext (fun j : nat => @lem6893214 A n f dom neut j m)). Qed.
Lemma lem6893216 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6893217 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term654 A n f dom neut m) = (term654 A n f dom neut m).
Proof. exact (MK_COMB (@lem6893216) (@lem6893215 A n f dom neut m)). Qed.
Lemma lem6893264 (n : nat) (j : nat) (m : nat) : (term639 n j m) = (term639 n j m).
Proof. exact (eq_refl (term639 n j m)). Qed.
Lemma lem6893265 (n : nat) (m : nat) : (term640 n m) = (term640 n m).
Proof. exact (fun_ext (fun j : nat => @lem6893264 n j m)). Qed.
Lemma lem6893266 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6893267 (n : nat) (m : nat) : (term641 n m) = (term641 n m).
Proof. exact (MK_COMB (@lem6893266) (@lem6893265 n m)). Qed.
Lemma lem6893268 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6893269 (n : nat) (m : nat) : (term655 n m) = (term655 n m).
Proof. exact (MK_COMB (@lem6893268) (@lem6893267 n m)). Qed.
Lemma lem6893270 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term656 A n f dom neut m) = (term656 A n f dom neut m).
Proof. exact (MK_COMB (@lem6893269 n m) (@lem6893217 A n f dom neut m)). Qed.
Lemma lem6893271 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term631 A n f dom neut m) = (term656 A n f dom neut m).
Proof. exact (TRANS (@lem6893163 A n f dom neut m) (@lem6893270 A n f dom neut m)). Qed.
Lemma lem6893273 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term283 A P Q) = (term282 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6893274 (P : nat -> Prop) (Q : nat -> Prop) : (term285 P Q) = (term284 P Q).
Proof. exact (@lem6893273 nat P Q). Qed.
Lemma lem6893275 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term657 A n f dom neut m) = (term658 A n f dom neut m).
Proof. exact (@lem6893274 (term640 n m) (term653 A n f dom neut m)). Qed.
Lemma lem6893276 (n : nat) (j : nat) (m : nat) : (term659 n m j) = (term639 n j m).
Proof. exact (eq_refl (term659 n m j)). Qed.
Lemma lem6893277 (n : nat) (m : nat) : (term660 n m) = (term640 n m).
Proof. exact (fun_ext (fun j : nat => @lem6893276 n j m)). Qed.
Lemma lem6893278 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6893279 (n : nat) (m : nat) : (term661 n m) = (term641 n m).
Proof. exact (MK_COMB (@lem6893278) (@lem6893277 n m)). Qed.
Lemma lem6893280 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6893281 (n : nat) (m : nat) : (term662 n m) = (term655 n m).
Proof. exact (MK_COMB (@lem6893280) (@lem6893279 n m)). Qed.
Lemma lem6893282 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (j : nat) (m : nat) : (term663 A n f dom neut m j) = (term652 A n f dom neut j m).
Proof. exact (eq_refl (term663 A n f dom neut m j)). Qed.
Lemma lem6893283 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term664 A n f dom neut m) = (term653 A n f dom neut m).
Proof. exact (fun_ext (fun j : nat => @lem6893282 A n f dom neut j m)). Qed.
Lemma lem6893284 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6893285 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term665 A n f dom neut m) = (term654 A n f dom neut m).
Proof. exact (MK_COMB (@lem6893284) (@lem6893283 A n f dom neut m)). Qed.
Lemma lem6893286 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term657 A n f dom neut m) = (term656 A n f dom neut m).
Proof. exact (MK_COMB (@lem6893281 n m) (@lem6893285 A n f dom neut m)). Qed.
Lemma lem6893287 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6893288 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term666 A n f dom neut m) = (term667 A n f dom neut m).
Proof. exact (MK_COMB (@lem6893287) (@lem6893286 A n f dom neut m)). Qed.
Lemma lem6893289 (n : nat) (j : nat) (m : nat) : (term659 n m j) = (term639 n j m).
Proof. exact (eq_refl (term659 n m j)). Qed.
Lemma lem6893290 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6893291 (n : nat) (j : nat) (m : nat) : (term668 n m j) = (term669 n j m).
Proof. exact (MK_COMB (@lem6893290) (@lem6893289 n j m)). Qed.
Lemma lem6893292 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (j : nat) (m : nat) : (term663 A n f dom neut m j) = (term652 A n f dom neut j m).
Proof. exact (eq_refl (term663 A n f dom neut m j)). Qed.
Lemma lem6893293 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (j : nat) (m : nat) : (term670 A n f dom neut m j) = (term671 A n f dom neut j m).
Proof. exact (MK_COMB (@lem6893291 n j m) (@lem6893292 A n f dom neut j m)). Qed.
Lemma lem6893294 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term672 A n f dom neut m) = (term673 A n f dom neut m).
Proof. exact (fun_ext (fun j : nat => @lem6893293 A n f dom neut j m)). Qed.
Lemma lem6893295 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6893296 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term658 A n f dom neut m) = (term674 A n f dom neut m).
Proof. exact (MK_COMB (@lem6893295) (@lem6893294 A n f dom neut m)). Qed.
Lemma lem6893297 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : ((term657 A n f dom neut m) = (term658 A n f dom neut m)) = ((term656 A n f dom neut m) = (term674 A n f dom neut m)).
Proof. exact (MK_COMB (@lem6893288 A n f dom neut m) (@lem6893296 A n f dom neut m)). Qed.
Lemma lem6893298 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term656 A n f dom neut m) = (term674 A n f dom neut m).
Proof. exact (EQ_MP (@lem6893297 A n f dom neut m) (@lem6893275 A n f dom neut m)). Qed.
Lemma lem6893299 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term631 A n f dom neut m) = (term674 A n f dom neut m).
Proof. exact (TRANS (@lem6893271 A n f dom neut m) (@lem6893298 A n f dom neut m)). Qed.
Lemma lem6893301 (m : nat) (n : nat) : (Peano.le m n) = (term0 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem6893302 (m : nat) (j : nat) : (term635 m j) = (term675 m j).
Proof. exact (@lem6893301 (term3 m) j). Qed.
Lemma lem6893304 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem6893305 (m : nat) : (term6 m) = (term7 m).
Proof. exact (@lem6893304 m term8). Qed.
Lemma lem6893306 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem6893307 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem6893306) (@lem6893305 m)). Qed.
Lemma lem6893308 (j : nat) : (int_of_num j) = (int_of_num j).
Proof. exact (eq_refl (int_of_num j)). Qed.
Lemma lem6893309 (m : nat) (j : nat) : (term675 m j) = (term676 m j).
Proof. exact (MK_COMB (@lem6893307 m) (@lem6893308 j)). Qed.
Lemma lem6893310 (m : nat) (j : nat) : (term635 m j) = (term676 m j).
Proof. exact (TRANS (@lem6893302 m j) (@lem6893309 m j)). Qed.
Lemma lem6893311 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6893312 (m : nat) (j : nat) : (term677 m j) = (term678 m j).
Proof. exact (MK_COMB (@lem6893311) (@lem6893310 m j)). Qed.
Lemma lem6893313 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6893314 (m : nat) (j : nat) : (term679 m j) = (term680 m j).
Proof. exact (MK_COMB (@lem6893313) (@lem6893312 m j)). Qed.
Lemma lem6893316 (m : nat) (n : nat) : (Peano.le m n) = (term0 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem6893317 (j : nat) (n : nat) : (Peano.le j n) = (term0 j n).
Proof. exact (@lem6893316 j n). Qed.
Lemma lem6893318 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6893319 (j : nat) (n : nat) : (term200 j n) = (term681 j n).
Proof. exact (MK_COMB (@lem6893318) (@lem6893317 j n)). Qed.
Lemma lem6893320 (m : nat) (j : nat) (n : nat) : (term634 m j n) = (term682 m j n).
Proof. exact (MK_COMB (@lem6893314 m j) (@lem6893319 j n)). Qed.
Lemma lem6893321 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6893322 (m : nat) (j : nat) (n : nat) : (term637 m j n) = (term683 m j n).
Proof. exact (MK_COMB (@lem6893321) (@lem6893320 m j n)). Qed.
Lemma lem6893324 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem6893325 (m : nat) (j : nat) : (m = j) = ((int_of_num m) = (int_of_num j)).
Proof. exact (@lem6893324 m j). Qed.
Lemma lem6893328 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6893329 (m : nat) (j : nat) : (term684 m j) = (term685 m j).
Proof. exact (MK_COMB (@lem6893328) (@lem6893325 m j)). Qed.
Lemma lem6893331 (m : nat) (n : nat) : (Peano.le m n) = (term0 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem6893332 (m : nat) (j : nat) : (Peano.le m j) = (term0 m j).
Proof. exact (@lem6893331 m j). Qed.
Lemma lem6893333 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6893334 (m : nat) (j : nat) : (term272 m j) = (term686 m j).
Proof. exact (MK_COMB (@lem6893333) (@lem6893332 m j)). Qed.
Lemma lem6893336 (m : nat) (n : nat) : (Peano.le m n) = (term0 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem6893337 (j : nat) (m : nat) : (Peano.le j m) = (term0 j m).
Proof. exact (@lem6893336 j m). Qed.
Lemma lem6893338 (j : nat) (m : nat) : (term687 j m) = (term688 j m).
Proof. exact (MK_COMB (@lem6893334 m j) (@lem6893337 j m)). Qed.
Lemma lem6893339 (j : nat) (m : nat) : (term592 j m) = (term689 j m).
Proof. exact (MK_COMB (@lem6893329 m j) (@lem6893338 j m)). Qed.
Lemma lem6893340 (n : nat) (j : nat) (m : nat) : (term639 n j m) = (term690 n j m).
Proof. exact (MK_COMB (@lem6893322 m j n) (@lem6893339 j m)). Qed.
Lemma lem6893341 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6893342 (n : nat) (j : nat) (m : nat) : (term669 n j m) = (term691 n j m).
Proof. exact (MK_COMB (@lem6893341) (@lem6893340 n j m)). Qed.
Lemma lem6893344 (m : nat) (n : nat) : (Peano.le m n) = (term0 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem6893345 (j : nat) (m : nat) : (Peano.le j m) = (term0 j m).
Proof. exact (@lem6893344 j m). Qed.
Lemma lem6893346 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6893347 (j : nat) (m : nat) : (term200 j m) = (term681 j m).
Proof. exact (MK_COMB (@lem6893346) (@lem6893345 j m)). Qed.
Lemma lem6893348 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6893349 (j : nat) (m : nat) : (term388 j m) = (term692 j m).
Proof. exact (MK_COMB (@lem6893348) (@lem6893347 j m)). Qed.
Lemma lem6893351 (m : nat) (n : nat) : (Peano.le m n) = (term0 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem6893352 (m : nat) (j : nat) : (term635 m j) = (term675 m j).
Proof. exact (@lem6893351 (term3 m) j). Qed.
Lemma lem6893354 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem6893355 (m : nat) : (term6 m) = (term7 m).
Proof. exact (@lem6893354 m term8). Qed.
Lemma lem6893356 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem6893357 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem6893356) (@lem6893355 m)). Qed.
Lemma lem6893358 (j : nat) : (int_of_num j) = (int_of_num j).
Proof. exact (eq_refl (int_of_num j)). Qed.
Lemma lem6893359 (m : nat) (j : nat) : (term675 m j) = (term676 m j).
Proof. exact (MK_COMB (@lem6893357 m) (@lem6893358 j)). Qed.
Lemma lem6893360 (m : nat) (j : nat) : (term635 m j) = (term676 m j).
Proof. exact (TRANS (@lem6893352 m j) (@lem6893359 m j)). Qed.
Lemma lem6893361 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6893362 (m : nat) (j : nat) : (term677 m j) = (term678 m j).
Proof. exact (MK_COMB (@lem6893361) (@lem6893360 m j)). Qed.
Lemma lem6893363 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6893364 (m : nat) (j : nat) : (term679 m j) = (term680 m j).
Proof. exact (MK_COMB (@lem6893363) (@lem6893362 m j)). Qed.
Lemma lem6893366 (m : nat) (n : nat) : (Peano.le m n) = (term0 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem6893367 (j : nat) (n : nat) : (Peano.le j n) = (term0 j n).
Proof. exact (@lem6893366 j n). Qed.
Lemma lem6893368 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6893369 (j : nat) (n : nat) : (term200 j n) = (term681 j n).
Proof. exact (MK_COMB (@lem6893368) (@lem6893367 j n)). Qed.
Lemma lem6893370 (m : nat) (j : nat) (n : nat) : (term634 m j n) = (term682 m j n).
Proof. exact (MK_COMB (@lem6893364 m j) (@lem6893369 j n)). Qed.
Lemma lem6893371 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6893372 (m : nat) (j : nat) (n : nat) : (term637 m j n) = (term683 m j n).
Proof. exact (MK_COMB (@lem6893371) (@lem6893370 m j n)). Qed.
Lemma lem6893373 {A : Type'} (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term642 A f j dom neut) = (term642 A f j dom neut).
Proof. exact (eq_refl (term642 A f j dom neut)). Qed.
Lemma lem6893374 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term644 A m n f j dom neut) = (term693 A m n f j dom neut).
Proof. exact (MK_COMB (@lem6893372 m j n) (@lem6893373 A f j dom neut)). Qed.
Lemma lem6893375 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term647 A m n f j dom neut) = (term694 A m n f j dom neut).
Proof. exact (MK_COMB (@lem6893349 j m) (@lem6893374 A m n f j dom neut)). Qed.
Lemma lem6893376 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6893377 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term650 A m n f j dom neut) = (term695 A m n f j dom neut).
Proof. exact (MK_COMB (@lem6893376) (@lem6893375 A m n f j dom neut)). Qed.
Lemma lem6893379 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem6893380 (j : nat) (m : nat) : (j = m) = ((int_of_num j) = (int_of_num m)).
Proof. exact (@lem6893379 j m). Qed.
Lemma lem6893383 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (j : nat) (m : nat) : (term652 A n f dom neut j m) = (term696 A n f dom neut j m).
Proof. exact (MK_COMB (@lem6893377 A m n f j dom neut) (@lem6893380 j m)). Qed.
Lemma lem6893384 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (j : nat) (m : nat) : (term671 A n f dom neut j m) = (term697 A n f dom neut j m).
Proof. exact (MK_COMB (@lem6893342 n j m) (@lem6893383 A n f dom neut j m)). Qed.
Lemma lem6893385 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term673 A n f dom neut m) = (term698 A n f dom neut m).
Proof. exact (fun_ext (fun j : nat => @lem6893384 A n f dom neut j m)). Qed.
Lemma lem6893386 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6893387 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term674 A n f dom neut m) = (term699 A n f dom neut m).
Proof. exact (MK_COMB (@lem6893386) (@lem6893385 A n f dom neut m)). Qed.
Lemma lem6893388 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term631 A n f dom neut m) = (term699 A n f dom neut m).
Proof. exact (TRANS (@lem6893299 A n f dom neut m) (@lem6893387 A n f dom neut m)). Qed.
Lemma lem6893389 (j : nat) : term14 j.
Proof. exact (@lem2307535 j). Qed.
Lemma lem6893390 (j : nat) : (term14 j) = (term15 j).
Proof. exact (eq_refl (term14 j)). Qed.
Lemma lem6893391 (j : nat) : term15 j.
Proof. exact (EQ_MP (@lem6893390 j) (@lem6893389 j)). Qed.
Lemma lem6893392 (m : nat) : term14 m.
Proof. exact (@lem2307535 m). Qed.
Lemma lem6893393 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem6893394 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem6893393 m) (@lem6893392 m)). Qed.
Lemma lem6893395 (n : nat) : term14 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem6893396 (n : nat) : (term14 n) = (term15 n).
Proof. exact (eq_refl (term14 n)). Qed.
Lemma lem6893397 (n : nat) : term15 n.
Proof. exact (EQ_MP (@lem6893396 n) (@lem6893395 n)). Qed.
Lemma lem6893398 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term700 A _92034 f j dom neut _92032 _92033) = (term701 A _92034 f j dom neut _92032 _92033).
Proof. exact (@lem2318604 (term701 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6893433 (_92033 : int) (_92032 : int) : (term702 _92033 _92032) = (term703 _92033 _92032).
Proof. exact (@lem16933 (term703 _92033 _92032)). Qed.
Lemma lem6893436 (_92032 : int) (_92034 : int) : (term704 _92032 _92034) = (int_le _92032 _92034).
Proof. exact (@lem16933 (int_le _92032 _92034)). Qed.
Lemma lem6893437 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6893438 (_92033 : int) (_92032 : int) : (term705 _92033 _92032) = (term706 _92033 _92032).
Proof. exact (MK_COMB (@lem6893437) (@lem6893433 _92033 _92032)). Qed.
Lemma lem6893439 (_92033 : int) (_92032 : int) (_92034 : int) : (term707 _92033 _92032 _92034) = (term708 _92033 _92032 _92034).
Proof. exact (MK_COMB (@lem6893438 _92033 _92032) (@lem6893436 _92032 _92034)). Qed.
Lemma lem6893440 (_92033 : int) (_92032 : int) (_92034 : int) : (term709 _92033 _92032 _92034) = (term707 _92033 _92032 _92034).
Proof. exact (@lem17160 (term710 _92033 _92032) (term711 _92032 _92034)). Qed.
Lemma lem6893441 (_92033 : int) (_92032 : int) (_92034 : int) : (term709 _92033 _92032 _92034) = (term708 _92033 _92032 _92034).
Proof. exact (TRANS (@lem6893440 _92033 _92032 _92034) (@lem6893439 _92033 _92032 _92034)). Qed.
Lemma lem6893449 (_92032 : int) (_92033 : int) : (term712 _92032 _92033) = (term713 _92032 _92033).
Proof. exact (@lem17160 (int_le _92033 _92032) (int_le _92032 _92033)). Qed.
Lemma lem6893451 (_92033 : int) (_92032 : int) : (term714 _92033 _92032) = (term714 _92033 _92032).
Proof. exact (eq_refl (term714 _92033 _92032)). Qed.
Lemma lem6893452 (_92032 : int) (_92033 : int) : (term715 _92032 _92033) = (term716 _92032 _92033).
Proof. exact (MK_COMB (@lem6893451 _92033 _92032) (@lem6893449 _92032 _92033)). Qed.
Lemma lem6893453 (_92032 : int) (_92033 : int) : (term717 _92032 _92033) = (term715 _92032 _92033).
Proof. exact (@lem17160 (_92033 = _92032) (term718 _92032 _92033)). Qed.
Lemma lem6893454 (_92032 : int) (_92033 : int) : (term717 _92032 _92033) = (term716 _92032 _92033).
Proof. exact (TRANS (@lem6893453 _92032 _92033) (@lem6893452 _92032 _92033)). Qed.
Lemma lem6893455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6893456 (_92033 : int) (_92032 : int) (_92034 : int) : (term719 _92033 _92032 _92034) = (term720 _92033 _92032 _92034).
Proof. exact (MK_COMB (@lem6893455) (@lem6893441 _92033 _92032 _92034)). Qed.
Lemma lem6893457 (_92034 : int) (_92032 : int) (_92033 : int) : (term721 _92034 _92032 _92033) = (term722 _92034 _92032 _92033).
Proof. exact (MK_COMB (@lem6893456 _92033 _92032 _92034) (@lem6893454 _92032 _92033)). Qed.
Lemma lem6893458 (_92034 : int) (_92032 : int) (_92033 : int) : (term723 _92034 _92032 _92033) = (term721 _92034 _92032 _92033).
Proof. exact (@lem17160 (term724 _92033 _92032 _92034) (term725 _92032 _92033)). Qed.
Lemma lem6893459 (_92034 : int) (_92032 : int) (_92033 : int) : (term723 _92034 _92032 _92033) = (term722 _92034 _92032 _92033).
Proof. exact (TRANS (@lem6893458 _92034 _92032 _92033) (@lem6893457 _92034 _92032 _92033)). Qed.
Lemma lem6893462 (_92032 : int) (_92033 : int) : (term704 _92032 _92033) = (int_le _92032 _92033).
Proof. exact (@lem16933 (int_le _92032 _92033)). Qed.
Lemma lem6893465 (_92033 : int) (_92032 : int) : (term702 _92033 _92032) = (term703 _92033 _92032).
Proof. exact (@lem16933 (term703 _92033 _92032)). Qed.
Lemma lem6893468 (_92032 : int) (_92034 : int) : (term704 _92032 _92034) = (int_le _92032 _92034).
Proof. exact (@lem16933 (int_le _92032 _92034)). Qed.
Lemma lem6893469 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6893470 (_92033 : int) (_92032 : int) : (term705 _92033 _92032) = (term706 _92033 _92032).
Proof. exact (MK_COMB (@lem6893469) (@lem6893465 _92033 _92032)). Qed.
Lemma lem6893471 (_92033 : int) (_92032 : int) (_92034 : int) : (term707 _92033 _92032 _92034) = (term708 _92033 _92032 _92034).
Proof. exact (MK_COMB (@lem6893470 _92033 _92032) (@lem6893468 _92032 _92034)). Qed.
Lemma lem6893472 (_92033 : int) (_92032 : int) (_92034 : int) : (term709 _92033 _92032 _92034) = (term707 _92033 _92032 _92034).
Proof. exact (@lem17160 (term710 _92033 _92032) (term711 _92032 _92034)). Qed.
Lemma lem6893473 (_92033 : int) (_92032 : int) (_92034 : int) : (term709 _92033 _92032 _92034) = (term708 _92033 _92032 _92034).
Proof. exact (TRANS (@lem6893472 _92033 _92032 _92034) (@lem6893471 _92033 _92032 _92034)). Qed.
Lemma lem6893476 {A : Type'} (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term726 A f j dom neut) = (term563 A f j dom neut).
Proof. exact (@lem16933 (term563 A f j dom neut)). Qed.
Lemma lem6893477 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6893478 (_92033 : int) (_92032 : int) (_92034 : int) : (term719 _92033 _92032 _92034) = (term720 _92033 _92032 _92034).
Proof. exact (MK_COMB (@lem6893477) (@lem6893473 _92033 _92032 _92034)). Qed.
Lemma lem6893479 {A : Type'} (_92033 : int) (_92032 : int) (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term727 A _92033 _92032 _92034 f j dom neut) = (term728 A _92033 _92032 _92034 f j dom neut).
Proof. exact (MK_COMB (@lem6893478 _92033 _92032 _92034) (@lem6893476 A f j dom neut)). Qed.
Lemma lem6893480 {A : Type'} (_92033 : int) (_92032 : int) (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term729 A _92033 _92032 _92034 f j dom neut) = (term727 A _92033 _92032 _92034 f j dom neut).
Proof. exact (@lem17160 (term724 _92033 _92032 _92034) (term642 A f j dom neut)). Qed.
Lemma lem6893481 {A : Type'} (_92033 : int) (_92032 : int) (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term729 A _92033 _92032 _92034 f j dom neut) = (term728 A _92033 _92032 _92034 f j dom neut).
Proof. exact (TRANS (@lem6893480 A _92033 _92032 _92034 f j dom neut) (@lem6893479 A _92033 _92032 _92034 f j dom neut)). Qed.
Lemma lem6893482 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6893483 (_92032 : int) (_92033 : int) : (term730 _92032 _92033) = (term731 _92032 _92033).
Proof. exact (MK_COMB (@lem6893482) (@lem6893462 _92032 _92033)). Qed.
Lemma lem6893484 {A : Type'} (_92033 : int) (_92032 : int) (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term732 A _92033 _92032 _92034 f j dom neut) = (term733 A _92033 _92032 _92034 f j dom neut).
Proof. exact (MK_COMB (@lem6893483 _92032 _92033) (@lem6893481 A _92033 _92032 _92034 f j dom neut)). Qed.
Lemma lem6893485 {A : Type'} (_92033 : int) (_92032 : int) (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term734 A _92033 _92032 _92034 f j dom neut) = (term732 A _92033 _92032 _92034 f j dom neut).
Proof. exact (@lem17160 (term711 _92032 _92033) (term735 A _92033 _92032 _92034 f j dom neut)). Qed.
Lemma lem6893486 {A : Type'} (_92033 : int) (_92032 : int) (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term734 A _92033 _92032 _92034 f j dom neut) = (term733 A _92033 _92032 _92034 f j dom neut).
Proof. exact (TRANS (@lem6893485 A _92033 _92032 _92034 f j dom neut) (@lem6893484 A _92033 _92032 _92034 f j dom neut)). Qed.
Lemma lem6893487 (_92032 : int) (_92033 : int) : (term736 _92032 _92033) = (term736 _92032 _92033).
Proof. exact (eq_refl (term736 _92032 _92033)). Qed.
Lemma lem6893488 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6893489 {A : Type'} (_92033 : int) (_92032 : int) (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term737 A _92033 _92032 _92034 f j dom neut) = (term738 A _92033 _92032 _92034 f j dom neut).
Proof. exact (MK_COMB (@lem6893488) (@lem6893486 A _92033 _92032 _92034 f j dom neut)). Qed.
Lemma lem6893490 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term739 A _92034 f j dom neut _92032 _92033) = (term740 A _92034 f j dom neut _92032 _92033).
Proof. exact (MK_COMB (@lem6893489 A _92033 _92032 _92034 f j dom neut) (@lem6893487 _92032 _92033)). Qed.
Lemma lem6893491 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term741 A _92034 f j dom neut _92032 _92033) = (term739 A _92034 f j dom neut _92032 _92033).
Proof. exact (@lem17160 (term742 A _92033 _92032 _92034 f j dom neut) (_92032 = _92033)). Qed.
Lemma lem6893492 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term741 A _92034 f j dom neut _92032 _92033) = (term740 A _92034 f j dom neut _92032 _92033).
Proof. exact (TRANS (@lem6893491 A _92034 f j dom neut _92032 _92033) (@lem6893490 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6893493 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6893494 (_92034 : int) (_92032 : int) (_92033 : int) : (term743 _92034 _92032 _92033) = (term744 _92034 _92032 _92033).
Proof. exact (MK_COMB (@lem6893493) (@lem6893459 _92034 _92032 _92033)). Qed.
Lemma lem6893495 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term745 A _92034 f j dom neut _92032 _92033) = (term746 A _92034 f j dom neut _92032 _92033).
Proof. exact (MK_COMB (@lem6893494 _92034 _92032 _92033) (@lem6893492 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6893496 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term747 A _92034 f j dom neut _92032 _92033) = (term745 A _92034 f j dom neut _92032 _92033).
Proof. exact (@lem17045 (term748 _92034 _92032 _92033) (term749 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6893497 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term747 A _92034 f j dom neut _92032 _92033) = (term746 A _92034 f j dom neut _92032 _92033).
Proof. exact (TRANS (@lem6893496 A _92034 f j dom neut _92032 _92033) (@lem6893495 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6893499 (_92034 : int) : (term20 _92034) = (term20 _92034).
Proof. exact (eq_refl (term20 _92034)). Qed.
Lemma lem6893500 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term750 A _92034 f j dom neut _92032 _92033) = (term751 A _92034 f j dom neut _92032 _92033).
Proof. exact (MK_COMB (@lem6893499 _92034) (@lem6893497 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6893501 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term752 A _92034 f j dom neut _92032 _92033) = (term750 A _92034 f j dom neut _92032 _92033).
Proof. exact (@lem17362 (term24 _92034) (term753 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6893502 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term752 A _92034 f j dom neut _92032 _92033) = (term751 A _92034 f j dom neut _92032 _92033).
Proof. exact (TRANS (@lem6893501 A _92034 f j dom neut _92032 _92033) (@lem6893500 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6893504 (_92033 : int) : (term20 _92033) = (term20 _92033).
Proof. exact (eq_refl (term20 _92033)). Qed.
Lemma lem6893505 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term754 A _92034 f j dom neut _92032 _92033) = (term755 A _92034 f j dom neut _92032 _92033).
Proof. exact (MK_COMB (@lem6893504 _92033) (@lem6893502 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6893506 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term756 A _92034 f j dom neut _92032 _92033) = (term754 A _92034 f j dom neut _92032 _92033).
Proof. exact (@lem17362 (term24 _92033) (term757 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6893507 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term756 A _92034 f j dom neut _92032 _92033) = (term755 A _92034 f j dom neut _92032 _92033).
Proof. exact (TRANS (@lem6893506 A _92034 f j dom neut _92032 _92033) (@lem6893505 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6893509 (_92032 : int) : (term20 _92032) = (term20 _92032).
Proof. exact (eq_refl (term20 _92032)). Qed.
Lemma lem6893510 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term758 A _92034 f j dom neut _92032 _92033) = (term759 A _92034 f j dom neut _92032 _92033).
Proof. exact (MK_COMB (@lem6893509 _92032) (@lem6893507 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6893511 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term760 A _92034 f j dom neut _92032 _92033) = (term758 A _92034 f j dom neut _92032 _92033).
Proof. exact (@lem17362 (term24 _92032) (term761 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6893571 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term760 A _92034 f j dom neut _92032 _92033) = (term759 A _92034 f j dom neut _92032 _92033).
Proof. exact (TRANS (@lem6893511 A _92034 f j dom neut _92032 _92033) (@lem6893510 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6893574 (x : int) (y : int) : (int_le x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6893575 (_92032 : int) : (term24 _92032) = (term27 _92032).
Proof. exact (@lem6893574 term28 _92032). Qed.
Lemma lem6893577 (n : nat) : (term29 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6893578 : term30 = term31.
Proof. exact (@lem6893577 (NUMERAL 0)). Qed.
Lemma lem6893579 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6893580 : term32 = term33.
Proof. exact (MK_COMB (@lem6893579) (@lem6893578)). Qed.
Lemma lem6893581 (_92032 : int) : (real_of_int _92032) = (real_of_int _92032).
Proof. exact (eq_refl (real_of_int _92032)). Qed.
Lemma lem6893582 (_92032 : int) : (term27 _92032) = (term34 _92032).
Proof. exact (MK_COMB (@lem6893580) (@lem6893581 _92032)). Qed.
Lemma lem6893584 (_92032 : int) : (term24 _92032) = (term34 _92032).
Proof. exact (TRANS (@lem6893575 _92032) (@lem6893582 _92032)). Qed.
Lemma lem6893587 (x : int) (y : int) : (int_le x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6893588 (_92033 : int) : (term24 _92033) = (term27 _92033).
Proof. exact (@lem6893587 term28 _92033). Qed.
Lemma lem6893590 (n : nat) : (term29 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6893591 : term30 = term31.
Proof. exact (@lem6893590 (NUMERAL 0)). Qed.
Lemma lem6893592 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6893593 : term32 = term33.
Proof. exact (MK_COMB (@lem6893592) (@lem6893591)). Qed.
Lemma lem6893594 (_92033 : int) : (real_of_int _92033) = (real_of_int _92033).
Proof. exact (eq_refl (real_of_int _92033)). Qed.
Lemma lem6893595 (_92033 : int) : (term27 _92033) = (term34 _92033).
Proof. exact (MK_COMB (@lem6893593) (@lem6893594 _92033)). Qed.
Lemma lem6893597 (_92033 : int) : (term24 _92033) = (term34 _92033).
Proof. exact (TRANS (@lem6893588 _92033) (@lem6893595 _92033)). Qed.
Lemma lem6893600 (x : int) (y : int) : (int_le x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6893601 (_92034 : int) : (term24 _92034) = (term27 _92034).
Proof. exact (@lem6893600 term28 _92034). Qed.
Lemma lem6893603 (n : nat) : (term29 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6893604 : term30 = term31.
Proof. exact (@lem6893603 (NUMERAL 0)). Qed.
Lemma lem6893605 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6893606 : term32 = term33.
Proof. exact (MK_COMB (@lem6893605) (@lem6893604)). Qed.
Lemma lem6893607 (_92034 : int) : (real_of_int _92034) = (real_of_int _92034).
Proof. exact (eq_refl (real_of_int _92034)). Qed.
Lemma lem6893608 (_92034 : int) : (term27 _92034) = (term34 _92034).
Proof. exact (MK_COMB (@lem6893606) (@lem6893607 _92034)). Qed.
Lemma lem6893610 (_92034 : int) : (term24 _92034) = (term34 _92034).
Proof. exact (TRANS (@lem6893601 _92034) (@lem6893608 _92034)). Qed.
Lemma lem6893613 (x : int) (y : int) : (int_le x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6893614 (_92033 : int) (_92032 : int) : (term703 _92033 _92032) = (term762 _92033 _92032).
Proof. exact (@lem6893613 (term36 _92033) _92032). Qed.
Lemma lem6893616 (x : int) (y : int) : (term37 x y) = (term38 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6893617 (_92033 : int) : (term39 _92033) = (term40 _92033).
Proof. exact (@lem6893616 _92033 term41). Qed.
Lemma lem6893619 (n : nat) : (term29 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6893620 : term42 = term43.
Proof. exact (@lem6893619 term8). Qed.
Lemma lem6893621 (_92033 : int) : (term44 _92033) = (term44 _92033).
Proof. exact (eq_refl (term44 _92033)). Qed.
Lemma lem6893622 (_92033 : int) : (term40 _92033) = (term45 _92033).
Proof. exact (MK_COMB (@lem6893621 _92033) (@lem6893620)). Qed.
Lemma lem6893623 (_92033 : int) : (term39 _92033) = (term45 _92033).
Proof. exact (TRANS (@lem6893617 _92033) (@lem6893622 _92033)). Qed.
Lemma lem6893624 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6893625 (_92033 : int) : (term46 _92033) = (term47 _92033).
Proof. exact (MK_COMB (@lem6893624) (@lem6893623 _92033)). Qed.
Lemma lem6893626 (_92032 : int) : (real_of_int _92032) = (real_of_int _92032).
Proof. exact (eq_refl (real_of_int _92032)). Qed.
Lemma lem6893627 (_92033 : int) (_92032 : int) : (term762 _92033 _92032) = (term763 _92033 _92032).
Proof. exact (MK_COMB (@lem6893625 _92033) (@lem6893626 _92032)). Qed.
Lemma lem6893629 (_92033 : int) (_92032 : int) : (term703 _92033 _92032) = (term763 _92033 _92032).
Proof. exact (TRANS (@lem6893614 _92033 _92032) (@lem6893627 _92033 _92032)). Qed.
Lemma lem6893632 (x : int) (y : int) : (int_le x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6893634 (_92032 : int) (_92034 : int) : (int_le _92032 _92034) = (term26 _92032 _92034).
Proof. exact (@lem6893632 _92032 _92034). Qed.
Lemma lem6893635 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6893636 (_92033 : int) (_92032 : int) : (term706 _92033 _92032) = (term764 _92033 _92032).
Proof. exact (MK_COMB (@lem6893635) (@lem6893629 _92033 _92032)). Qed.
Lemma lem6893637 (_92033 : int) (_92032 : int) (_92034 : int) : (term708 _92033 _92032 _92034) = (term765 _92033 _92032 _92034).
Proof. exact (MK_COMB (@lem6893636 _92033 _92032) (@lem6893634 _92032 _92034)). Qed.
Lemma lem6893639 (y : int) (x : int) : (term736 x y) = (term766 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem6893640 (_92032 : int) (_92033 : int) : (term736 _92033 _92032) = (term766 _92032 _92033).
Proof. exact (@lem6893639 _92032 _92033). Qed.
Lemma lem6893642 (x : int) (y : int) : (int_le x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6893643 (_92033 : int) (_92032 : int) : (term703 _92033 _92032) = (term762 _92033 _92032).
Proof. exact (@lem6893642 (term36 _92033) _92032). Qed.
Lemma lem6893645 (x : int) (y : int) : (term37 x y) = (term38 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6893646 (_92033 : int) : (term39 _92033) = (term40 _92033).
Proof. exact (@lem6893645 _92033 term41). Qed.
Lemma lem6893648 (n : nat) : (term29 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6893649 : term42 = term43.
Proof. exact (@lem6893648 term8). Qed.
Lemma lem6893650 (_92033 : int) : (term44 _92033) = (term44 _92033).
Proof. exact (eq_refl (term44 _92033)). Qed.
Lemma lem6893651 (_92033 : int) : (term40 _92033) = (term45 _92033).
Proof. exact (MK_COMB (@lem6893650 _92033) (@lem6893649)). Qed.
Lemma lem6893652 (_92033 : int) : (term39 _92033) = (term45 _92033).
Proof. exact (TRANS (@lem6893646 _92033) (@lem6893651 _92033)). Qed.
Lemma lem6893653 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6893654 (_92033 : int) : (term46 _92033) = (term47 _92033).
Proof. exact (MK_COMB (@lem6893653) (@lem6893652 _92033)). Qed.
Lemma lem6893655 (_92032 : int) : (real_of_int _92032) = (real_of_int _92032).
Proof. exact (eq_refl (real_of_int _92032)). Qed.
Lemma lem6893656 (_92033 : int) (_92032 : int) : (term762 _92033 _92032) = (term763 _92033 _92032).
Proof. exact (MK_COMB (@lem6893654 _92033) (@lem6893655 _92032)). Qed.
Lemma lem6893657 (_92033 : int) (_92032 : int) : (term703 _92033 _92032) = (term763 _92033 _92032).
Proof. exact (TRANS (@lem6893643 _92033 _92032) (@lem6893656 _92033 _92032)). Qed.
Lemma lem6893658 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6893659 (_92033 : int) (_92032 : int) : (term767 _92033 _92032) = (term768 _92033 _92032).
Proof. exact (MK_COMB (@lem6893658) (@lem6893657 _92033 _92032)). Qed.
Lemma lem6893661 (x : int) (y : int) : (int_le x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6893662 (_92032 : int) (_92033 : int) : (term703 _92032 _92033) = (term762 _92032 _92033).
Proof. exact (@lem6893661 (term36 _92032) _92033). Qed.
Lemma lem6893664 (x : int) (y : int) : (term37 x y) = (term38 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6893665 (_92032 : int) : (term39 _92032) = (term40 _92032).
Proof. exact (@lem6893664 _92032 term41). Qed.
Lemma lem6893667 (n : nat) : (term29 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6893668 : term42 = term43.
Proof. exact (@lem6893667 term8). Qed.
Lemma lem6893669 (_92032 : int) : (term44 _92032) = (term44 _92032).
Proof. exact (eq_refl (term44 _92032)). Qed.
Lemma lem6893670 (_92032 : int) : (term40 _92032) = (term45 _92032).
Proof. exact (MK_COMB (@lem6893669 _92032) (@lem6893668)). Qed.
Lemma lem6893671 (_92032 : int) : (term39 _92032) = (term45 _92032).
Proof. exact (TRANS (@lem6893665 _92032) (@lem6893670 _92032)). Qed.
Lemma lem6893672 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6893673 (_92032 : int) : (term46 _92032) = (term47 _92032).
Proof. exact (MK_COMB (@lem6893672) (@lem6893671 _92032)). Qed.
Lemma lem6893674 (_92033 : int) : (real_of_int _92033) = (real_of_int _92033).
Proof. exact (eq_refl (real_of_int _92033)). Qed.
Lemma lem6893675 (_92032 : int) (_92033 : int) : (term762 _92032 _92033) = (term763 _92032 _92033).
Proof. exact (MK_COMB (@lem6893673 _92032) (@lem6893674 _92033)). Qed.
Lemma lem6893676 (_92032 : int) (_92033 : int) : (term703 _92032 _92033) = (term763 _92032 _92033).
Proof. exact (TRANS (@lem6893662 _92032 _92033) (@lem6893675 _92032 _92033)). Qed.
Lemma lem6893677 (_92032 : int) (_92033 : int) : (term766 _92032 _92033) = (term769 _92032 _92033).
Proof. exact (MK_COMB (@lem6893659 _92033 _92032) (@lem6893676 _92032 _92033)). Qed.
Lemma lem6893678 (_92032 : int) (_92033 : int) : (term736 _92033 _92032) = (term769 _92032 _92033).
Proof. exact (TRANS (@lem6893640 _92032 _92033) (@lem6893677 _92032 _92033)). Qed.
Lemma lem6893680 (y : int) (x : int) : (term711 x y) = (term703 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem6893681 (_92032 : int) (_92033 : int) : (term711 _92033 _92032) = (term703 _92032 _92033).
Proof. exact (@lem6893680 _92032 _92033). Qed.
Lemma lem6893683 (x : int) (y : int) : (int_le x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6893684 (_92032 : int) (_92033 : int) : (term703 _92032 _92033) = (term762 _92032 _92033).
Proof. exact (@lem6893683 (term36 _92032) _92033). Qed.
Lemma lem6893686 (x : int) (y : int) : (term37 x y) = (term38 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6893687 (_92032 : int) : (term39 _92032) = (term40 _92032).
Proof. exact (@lem6893686 _92032 term41). Qed.
Lemma lem6893689 (n : nat) : (term29 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6893690 : term42 = term43.
Proof. exact (@lem6893689 term8). Qed.
Lemma lem6893691 (_92032 : int) : (term44 _92032) = (term44 _92032).
Proof. exact (eq_refl (term44 _92032)). Qed.
Lemma lem6893692 (_92032 : int) : (term40 _92032) = (term45 _92032).
Proof. exact (MK_COMB (@lem6893691 _92032) (@lem6893690)). Qed.
Lemma lem6893693 (_92032 : int) : (term39 _92032) = (term45 _92032).
Proof. exact (TRANS (@lem6893687 _92032) (@lem6893692 _92032)). Qed.
Lemma lem6893694 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6893695 (_92032 : int) : (term46 _92032) = (term47 _92032).
Proof. exact (MK_COMB (@lem6893694) (@lem6893693 _92032)). Qed.
Lemma lem6893696 (_92033 : int) : (real_of_int _92033) = (real_of_int _92033).
Proof. exact (eq_refl (real_of_int _92033)). Qed.
Lemma lem6893697 (_92032 : int) (_92033 : int) : (term762 _92032 _92033) = (term763 _92032 _92033).
Proof. exact (MK_COMB (@lem6893695 _92032) (@lem6893696 _92033)). Qed.
Lemma lem6893698 (_92032 : int) (_92033 : int) : (term703 _92032 _92033) = (term763 _92032 _92033).
Proof. exact (TRANS (@lem6893684 _92032 _92033) (@lem6893697 _92032 _92033)). Qed.
Lemma lem6893699 (_92032 : int) (_92033 : int) : (term711 _92033 _92032) = (term763 _92032 _92033).
Proof. exact (TRANS (@lem6893681 _92032 _92033) (@lem6893698 _92032 _92033)). Qed.
Lemma lem6893701 (y : int) (x : int) : (term711 x y) = (term703 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem6893702 (_92033 : int) (_92032 : int) : (term711 _92032 _92033) = (term703 _92033 _92032).
Proof. exact (@lem6893701 _92033 _92032). Qed.
Lemma lem6893704 (x : int) (y : int) : (int_le x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6893705 (_92033 : int) (_92032 : int) : (term703 _92033 _92032) = (term762 _92033 _92032).
Proof. exact (@lem6893704 (term36 _92033) _92032). Qed.
Lemma lem6893707 (x : int) (y : int) : (term37 x y) = (term38 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6893708 (_92033 : int) : (term39 _92033) = (term40 _92033).
Proof. exact (@lem6893707 _92033 term41). Qed.
Lemma lem6893710 (n : nat) : (term29 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6893711 : term42 = term43.
Proof. exact (@lem6893710 term8). Qed.
Lemma lem6893712 (_92033 : int) : (term44 _92033) = (term44 _92033).
Proof. exact (eq_refl (term44 _92033)). Qed.
Lemma lem6893713 (_92033 : int) : (term40 _92033) = (term45 _92033).
Proof. exact (MK_COMB (@lem6893712 _92033) (@lem6893711)). Qed.
Lemma lem6893714 (_92033 : int) : (term39 _92033) = (term45 _92033).
Proof. exact (TRANS (@lem6893708 _92033) (@lem6893713 _92033)). Qed.
Lemma lem6893715 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6893716 (_92033 : int) : (term46 _92033) = (term47 _92033).
Proof. exact (MK_COMB (@lem6893715) (@lem6893714 _92033)). Qed.
Lemma lem6893717 (_92032 : int) : (real_of_int _92032) = (real_of_int _92032).
Proof. exact (eq_refl (real_of_int _92032)). Qed.
Lemma lem6893718 (_92033 : int) (_92032 : int) : (term762 _92033 _92032) = (term763 _92033 _92032).
Proof. exact (MK_COMB (@lem6893716 _92033) (@lem6893717 _92032)). Qed.
Lemma lem6893719 (_92033 : int) (_92032 : int) : (term703 _92033 _92032) = (term763 _92033 _92032).
Proof. exact (TRANS (@lem6893705 _92033 _92032) (@lem6893718 _92033 _92032)). Qed.
Lemma lem6893720 (_92033 : int) (_92032 : int) : (term711 _92032 _92033) = (term763 _92033 _92032).
Proof. exact (TRANS (@lem6893702 _92033 _92032) (@lem6893719 _92033 _92032)). Qed.
Lemma lem6893721 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6893722 (_92032 : int) (_92033 : int) : (term770 _92033 _92032) = (term764 _92032 _92033).
Proof. exact (MK_COMB (@lem6893721) (@lem6893699 _92032 _92033)). Qed.
Lemma lem6893723 (_92033 : int) (_92032 : int) : (term713 _92032 _92033) = (term771 _92033 _92032).
Proof. exact (MK_COMB (@lem6893722 _92032 _92033) (@lem6893720 _92033 _92032)). Qed.
Lemma lem6893724 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6893725 (_92032 : int) (_92033 : int) : (term714 _92033 _92032) = (term772 _92032 _92033).
Proof. exact (MK_COMB (@lem6893724) (@lem6893678 _92032 _92033)). Qed.
Lemma lem6893726 (_92033 : int) (_92032 : int) : (term716 _92032 _92033) = (term773 _92033 _92032).
Proof. exact (MK_COMB (@lem6893725 _92032 _92033) (@lem6893723 _92033 _92032)). Qed.
Lemma lem6893727 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6893728 (_92033 : int) (_92032 : int) (_92034 : int) : (term720 _92033 _92032 _92034) = (term774 _92033 _92032 _92034).
Proof. exact (MK_COMB (@lem6893727) (@lem6893637 _92033 _92032 _92034)). Qed.
Lemma lem6893729 (_92034 : int) (_92033 : int) (_92032 : int) : (term722 _92034 _92032 _92033) = (term775 _92034 _92033 _92032).
Proof. exact (MK_COMB (@lem6893728 _92033 _92032 _92034) (@lem6893726 _92033 _92032)). Qed.
Lemma lem6893732 (x : int) (y : int) : (int_le x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6893734 (_92032 : int) (_92033 : int) : (int_le _92032 _92033) = (term26 _92032 _92033).
Proof. exact (@lem6893732 _92032 _92033). Qed.
Lemma lem6893737 (x : int) (y : int) : (int_le x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6893738 (_92033 : int) (_92032 : int) : (term703 _92033 _92032) = (term762 _92033 _92032).
Proof. exact (@lem6893737 (term36 _92033) _92032). Qed.
Lemma lem6893740 (x : int) (y : int) : (term37 x y) = (term38 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6893741 (_92033 : int) : (term39 _92033) = (term40 _92033).
Proof. exact (@lem6893740 _92033 term41). Qed.
Lemma lem6893743 (n : nat) : (term29 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6893744 : term42 = term43.
Proof. exact (@lem6893743 term8). Qed.
Lemma lem6893745 (_92033 : int) : (term44 _92033) = (term44 _92033).
Proof. exact (eq_refl (term44 _92033)). Qed.
Lemma lem6893746 (_92033 : int) : (term40 _92033) = (term45 _92033).
Proof. exact (MK_COMB (@lem6893745 _92033) (@lem6893744)). Qed.
Lemma lem6893747 (_92033 : int) : (term39 _92033) = (term45 _92033).
Proof. exact (TRANS (@lem6893741 _92033) (@lem6893746 _92033)). Qed.
Lemma lem6893748 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6893749 (_92033 : int) : (term46 _92033) = (term47 _92033).
Proof. exact (MK_COMB (@lem6893748) (@lem6893747 _92033)). Qed.
Lemma lem6893750 (_92032 : int) : (real_of_int _92032) = (real_of_int _92032).
Proof. exact (eq_refl (real_of_int _92032)). Qed.
Lemma lem6893751 (_92033 : int) (_92032 : int) : (term762 _92033 _92032) = (term763 _92033 _92032).
Proof. exact (MK_COMB (@lem6893749 _92033) (@lem6893750 _92032)). Qed.
Lemma lem6893753 (_92033 : int) (_92032 : int) : (term703 _92033 _92032) = (term763 _92033 _92032).
Proof. exact (TRANS (@lem6893738 _92033 _92032) (@lem6893751 _92033 _92032)). Qed.
Lemma lem6893756 (x : int) (y : int) : (int_le x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6893758 (_92032 : int) (_92034 : int) : (int_le _92032 _92034) = (term26 _92032 _92034).
Proof. exact (@lem6893756 _92032 _92034). Qed.
Lemma lem6893759 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6893760 (_92033 : int) (_92032 : int) : (term706 _92033 _92032) = (term764 _92033 _92032).
Proof. exact (MK_COMB (@lem6893759) (@lem6893753 _92033 _92032)). Qed.
Lemma lem6893761 (_92033 : int) (_92032 : int) (_92034 : int) : (term708 _92033 _92032 _92034) = (term765 _92033 _92032 _92034).
Proof. exact (MK_COMB (@lem6893760 _92033 _92032) (@lem6893758 _92032 _92034)). Qed.
Lemma lem6893764 {A : Type'} (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term563 A f j dom neut) = (term563 A f j dom neut).
Proof. exact (eq_refl (term563 A f j dom neut)). Qed.
Lemma lem6893765 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6893766 (_92033 : int) (_92032 : int) (_92034 : int) : (term720 _92033 _92032 _92034) = (term774 _92033 _92032 _92034).
Proof. exact (MK_COMB (@lem6893765) (@lem6893761 _92033 _92032 _92034)). Qed.
Lemma lem6893767 {A : Type'} (_92033 : int) (_92032 : int) (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term728 A _92033 _92032 _92034 f j dom neut) = (term776 A _92033 _92032 _92034 f j dom neut).
Proof. exact (MK_COMB (@lem6893766 _92033 _92032 _92034) (@lem6893764 A f j dom neut)). Qed.
Lemma lem6893768 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6893769 (_92032 : int) (_92033 : int) : (term731 _92032 _92033) = (term777 _92032 _92033).
Proof. exact (MK_COMB (@lem6893768) (@lem6893734 _92032 _92033)). Qed.
Lemma lem6893770 {A : Type'} (_92033 : int) (_92032 : int) (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term733 A _92033 _92032 _92034 f j dom neut) = (term778 A _92033 _92032 _92034 f j dom neut).
Proof. exact (MK_COMB (@lem6893769 _92032 _92033) (@lem6893767 A _92033 _92032 _92034 f j dom neut)). Qed.
Lemma lem6893772 (y : int) (x : int) : (term736 x y) = (term766 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem6893773 (_92033 : int) (_92032 : int) : (term736 _92032 _92033) = (term766 _92033 _92032).
Proof. exact (@lem6893772 _92033 _92032). Qed.
Lemma lem6893775 (x : int) (y : int) : (int_le x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6893776 (_92032 : int) (_92033 : int) : (term703 _92032 _92033) = (term762 _92032 _92033).
Proof. exact (@lem6893775 (term36 _92032) _92033). Qed.
Lemma lem6893778 (x : int) (y : int) : (term37 x y) = (term38 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6893779 (_92032 : int) : (term39 _92032) = (term40 _92032).
Proof. exact (@lem6893778 _92032 term41). Qed.
Lemma lem6893781 (n : nat) : (term29 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6893782 : term42 = term43.
Proof. exact (@lem6893781 term8). Qed.
Lemma lem6893783 (_92032 : int) : (term44 _92032) = (term44 _92032).
Proof. exact (eq_refl (term44 _92032)). Qed.
Lemma lem6893784 (_92032 : int) : (term40 _92032) = (term45 _92032).
Proof. exact (MK_COMB (@lem6893783 _92032) (@lem6893782)). Qed.
Lemma lem6893785 (_92032 : int) : (term39 _92032) = (term45 _92032).
Proof. exact (TRANS (@lem6893779 _92032) (@lem6893784 _92032)). Qed.
Lemma lem6893786 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6893787 (_92032 : int) : (term46 _92032) = (term47 _92032).
Proof. exact (MK_COMB (@lem6893786) (@lem6893785 _92032)). Qed.
Lemma lem6893788 (_92033 : int) : (real_of_int _92033) = (real_of_int _92033).
Proof. exact (eq_refl (real_of_int _92033)). Qed.
Lemma lem6893789 (_92032 : int) (_92033 : int) : (term762 _92032 _92033) = (term763 _92032 _92033).
Proof. exact (MK_COMB (@lem6893787 _92032) (@lem6893788 _92033)). Qed.
Lemma lem6893790 (_92032 : int) (_92033 : int) : (term703 _92032 _92033) = (term763 _92032 _92033).
Proof. exact (TRANS (@lem6893776 _92032 _92033) (@lem6893789 _92032 _92033)). Qed.
Lemma lem6893791 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6893792 (_92032 : int) (_92033 : int) : (term767 _92032 _92033) = (term768 _92032 _92033).
Proof. exact (MK_COMB (@lem6893791) (@lem6893790 _92032 _92033)). Qed.
Lemma lem6893794 (x : int) (y : int) : (int_le x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6893795 (_92033 : int) (_92032 : int) : (term703 _92033 _92032) = (term762 _92033 _92032).
Proof. exact (@lem6893794 (term36 _92033) _92032). Qed.
Lemma lem6893797 (x : int) (y : int) : (term37 x y) = (term38 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6893798 (_92033 : int) : (term39 _92033) = (term40 _92033).
Proof. exact (@lem6893797 _92033 term41). Qed.
Lemma lem6893800 (n : nat) : (term29 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6893801 : term42 = term43.
Proof. exact (@lem6893800 term8). Qed.
Lemma lem6893802 (_92033 : int) : (term44 _92033) = (term44 _92033).
Proof. exact (eq_refl (term44 _92033)). Qed.
Lemma lem6893803 (_92033 : int) : (term40 _92033) = (term45 _92033).
Proof. exact (MK_COMB (@lem6893802 _92033) (@lem6893801)). Qed.
Lemma lem6893804 (_92033 : int) : (term39 _92033) = (term45 _92033).
Proof. exact (TRANS (@lem6893798 _92033) (@lem6893803 _92033)). Qed.
Lemma lem6893805 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6893806 (_92033 : int) : (term46 _92033) = (term47 _92033).
Proof. exact (MK_COMB (@lem6893805) (@lem6893804 _92033)). Qed.
Lemma lem6893807 (_92032 : int) : (real_of_int _92032) = (real_of_int _92032).
Proof. exact (eq_refl (real_of_int _92032)). Qed.
Lemma lem6893808 (_92033 : int) (_92032 : int) : (term762 _92033 _92032) = (term763 _92033 _92032).
Proof. exact (MK_COMB (@lem6893806 _92033) (@lem6893807 _92032)). Qed.
Lemma lem6893809 (_92033 : int) (_92032 : int) : (term703 _92033 _92032) = (term763 _92033 _92032).
Proof. exact (TRANS (@lem6893795 _92033 _92032) (@lem6893808 _92033 _92032)). Qed.
Lemma lem6893810 (_92033 : int) (_92032 : int) : (term766 _92033 _92032) = (term769 _92033 _92032).
Proof. exact (MK_COMB (@lem6893792 _92032 _92033) (@lem6893809 _92033 _92032)). Qed.
Lemma lem6893811 (_92033 : int) (_92032 : int) : (term736 _92032 _92033) = (term769 _92033 _92032).
Proof. exact (TRANS (@lem6893773 _92033 _92032) (@lem6893810 _92033 _92032)). Qed.
Lemma lem6893812 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6893813 {A : Type'} (_92033 : int) (_92032 : int) (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term738 A _92033 _92032 _92034 f j dom neut) = (term779 A _92033 _92032 _92034 f j dom neut).
Proof. exact (MK_COMB (@lem6893812) (@lem6893770 A _92033 _92032 _92034 f j dom neut)). Qed.
Lemma lem6893814 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92033 : int) (_92032 : int) : (term740 A _92034 f j dom neut _92032 _92033) = (term780 A _92034 f j dom neut _92033 _92032).
Proof. exact (MK_COMB (@lem6893813 A _92033 _92032 _92034 f j dom neut) (@lem6893811 _92033 _92032)). Qed.
Lemma lem6893815 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6893816 (_92034 : int) (_92033 : int) (_92032 : int) : (term744 _92034 _92032 _92033) = (term781 _92034 _92033 _92032).
Proof. exact (MK_COMB (@lem6893815) (@lem6893729 _92034 _92033 _92032)). Qed.
Lemma lem6893817 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92033 : int) (_92032 : int) : (term746 A _92034 f j dom neut _92032 _92033) = (term782 A _92034 f j dom neut _92033 _92032).
Proof. exact (MK_COMB (@lem6893816 _92034 _92033 _92032) (@lem6893814 A _92034 f j dom neut _92033 _92032)). Qed.
Lemma lem6893818 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6893819 (_92034 : int) : (term20 _92034) = (term49 _92034).
Proof. exact (MK_COMB (@lem6893818) (@lem6893610 _92034)). Qed.
Lemma lem6893820 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92033 : int) (_92032 : int) : (term751 A _92034 f j dom neut _92032 _92033) = (term783 A _92034 f j dom neut _92033 _92032).
Proof. exact (MK_COMB (@lem6893819 _92034) (@lem6893817 A _92034 f j dom neut _92033 _92032)). Qed.
Lemma lem6893821 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6893822 (_92033 : int) : (term20 _92033) = (term49 _92033).
Proof. exact (MK_COMB (@lem6893821) (@lem6893597 _92033)). Qed.
Lemma lem6893823 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92033 : int) (_92032 : int) : (term755 A _92034 f j dom neut _92032 _92033) = (term784 A _92034 f j dom neut _92033 _92032).
Proof. exact (MK_COMB (@lem6893822 _92033) (@lem6893820 A _92034 f j dom neut _92033 _92032)). Qed.
Lemma lem6893824 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6893825 (_92032 : int) : (term20 _92032) = (term49 _92032).
Proof. exact (MK_COMB (@lem6893824) (@lem6893584 _92032)). Qed.
Lemma lem6893826 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92033 : int) (_92032 : int) : (term759 A _92034 f j dom neut _92032 _92033) = (term785 A _92034 f j dom neut _92033 _92032).
Proof. exact (MK_COMB (@lem6893825 _92032) (@lem6893823 A _92034 f j dom neut _92033 _92032)). Qed.
Lemma lem6893827 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92033 : int) (_92032 : int) : (term760 A _92034 f j dom neut _92032 _92033) = (term785 A _92034 f j dom neut _92033 _92032).
Proof. exact (TRANS (@lem6893571 A _92034 f j dom neut _92032 _92033) (@lem6893826 A _92034 f j dom neut _92033 _92032)). Qed.
Lemma lem6893831 (t : Prop) : (term51 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6893977 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92033 : int) (_92032 : int) : (term786 A _92034 f j dom neut _92033 _92032) = (term785 A _92034 f j dom neut _92033 _92032).
Proof. exact (@lem6893831 (term785 A _92034 f j dom neut _92033 _92032)). Qed.
Lemma lem6893978 (_92032 : int) : (term34 _92032) = (term53 _92032).
Proof. exact (@lem1988287 (real_of_int _92032) term31). Qed.
Lemma lem6893984 (_92032 : int) : (term54 _92032) = (term55 _92032).
Proof. exact (@lem1982792 (real_of_int _92032) term31). Qed.
Lemma lem6893986 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6893987 : term31 = term57.
Proof. exact (@lem6893986 (NUMERAL 0)). Qed.
Lemma lem6893989 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6893990 : term60 = term61.
Proof. exact (@lem6893989 term8). Qed.
Lemma lem6893991 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6893992 : term62 = term63.
Proof. exact (MK_COMB (@lem6893991) (@lem6893990)). Qed.
Lemma lem6893993 : term64 = term65.
Proof. exact (MK_COMB (@lem6893992) (@lem6893987)). Qed.
Lemma lem6893994 : term65 = term66.
Proof. exact (@lem1981613 term60 term31 term43 term43). Qed.
Lemma lem6893996 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6893997 : term69 = term70.
Proof. exact (@lem6893996 term8 term8). Qed.
Lemma lem6893998 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6893999 : term72 = term8.
Proof. exact (EQ_MP (@lem6893998) (@lem940073)). Qed.
Lemma lem6894000 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6894001 : term70 = term43.
Proof. exact (MK_COMB (@lem6894000) (@lem6893999)). Qed.
Lemma lem6894002 : term69 = term43.
Proof. exact (TRANS (@lem6893997) (@lem6894001)). Qed.
Lemma lem6894004 (x : nat) : (term73 x) = term31.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6894005 : term64 = term31.
Proof. exact (@lem6894004 term8). Qed.
Lemma lem6894006 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6894007 : term74 = term75.
Proof. exact (MK_COMB (@lem6894006) (@lem6894005)). Qed.
Lemma lem6894008 : term66 = term57.
Proof. exact (MK_COMB (@lem6894007) (@lem6894002)). Qed.
Lemma lem6894009 : term65 = term57.
Proof. exact (TRANS (@lem6893994) (@lem6894008)). Qed.
Lemma lem6894010 : term64 = term57.
Proof. exact (TRANS (@lem6893993) (@lem6894009)). Qed.
Lemma lem6894012 (x : real) : (term76 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6894013 : term57 = term31.
Proof. exact (@lem6894012 term31). Qed.
Lemma lem6894014 : term64 = term31.
Proof. exact (TRANS (@lem6894010) (@lem6894013)). Qed.
Lemma lem6894015 (_92032 : int) : (term44 _92032) = (term44 _92032).
Proof. exact (eq_refl (term44 _92032)). Qed.
Lemma lem6894016 (_92032 : int) : (term55 _92032) = (term77 _92032).
Proof. exact (MK_COMB (@lem6894015 _92032) (@lem6894014)). Qed.
Lemma lem6894017 (_92032 : int) : (term77 _92032) = (real_of_int _92032).
Proof. exact (@lem1982723 (real_of_int _92032)). Qed.
Lemma lem6894018 (_92032 : int) : (term55 _92032) = (real_of_int _92032).
Proof. exact (TRANS (@lem6894016 _92032) (@lem6894017 _92032)). Qed.
Lemma lem6894020 (_92032 : int) : (term54 _92032) = (real_of_int _92032).
Proof. exact (TRANS (@lem6893984 _92032) (@lem6894018 _92032)). Qed.
Lemma lem6894021 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6894022 (_92032 : int) : (term78 _92032) = (term79 _92032).
Proof. exact (MK_COMB (@lem6894021) (@lem6894020 _92032)). Qed.
Lemma lem6894023 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6894024 (_92032 : int) : (term53 _92032) = (term80 _92032).
Proof. exact (MK_COMB (@lem6894022 _92032) (@lem6894023)). Qed.
Lemma lem6894025 (_92032 : int) : (term34 _92032) = (term80 _92032).
Proof. exact (TRANS (@lem6893978 _92032) (@lem6894024 _92032)). Qed.
Lemma lem6894026 (_92033 : int) : (term34 _92033) = (term53 _92033).
Proof. exact (@lem1988287 (real_of_int _92033) term31). Qed.
Lemma lem6894032 (_92033 : int) : (term54 _92033) = (term55 _92033).
Proof. exact (@lem1982792 (real_of_int _92033) term31). Qed.
Lemma lem6894034 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6894035 : term31 = term57.
Proof. exact (@lem6894034 (NUMERAL 0)). Qed.
Lemma lem6894037 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6894038 : term60 = term61.
Proof. exact (@lem6894037 term8). Qed.
Lemma lem6894039 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6894040 : term62 = term63.
Proof. exact (MK_COMB (@lem6894039) (@lem6894038)). Qed.
Lemma lem6894041 : term64 = term65.
Proof. exact (MK_COMB (@lem6894040) (@lem6894035)). Qed.
Lemma lem6894042 : term65 = term66.
Proof. exact (@lem1981613 term60 term31 term43 term43). Qed.
Lemma lem6894044 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6894045 : term69 = term70.
Proof. exact (@lem6894044 term8 term8). Qed.
Lemma lem6894046 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6894047 : term72 = term8.
Proof. exact (EQ_MP (@lem6894046) (@lem940073)). Qed.
Lemma lem6894048 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6894049 : term70 = term43.
Proof. exact (MK_COMB (@lem6894048) (@lem6894047)). Qed.
Lemma lem6894050 : term69 = term43.
Proof. exact (TRANS (@lem6894045) (@lem6894049)). Qed.
Lemma lem6894052 (x : nat) : (term73 x) = term31.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6894053 : term64 = term31.
Proof. exact (@lem6894052 term8). Qed.
Lemma lem6894054 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6894055 : term74 = term75.
Proof. exact (MK_COMB (@lem6894054) (@lem6894053)). Qed.
Lemma lem6894056 : term66 = term57.
Proof. exact (MK_COMB (@lem6894055) (@lem6894050)). Qed.
Lemma lem6894057 : term65 = term57.
Proof. exact (TRANS (@lem6894042) (@lem6894056)). Qed.
Lemma lem6894058 : term64 = term57.
Proof. exact (TRANS (@lem6894041) (@lem6894057)). Qed.
Lemma lem6894060 (x : real) : (term76 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6894061 : term57 = term31.
Proof. exact (@lem6894060 term31). Qed.
Lemma lem6894062 : term64 = term31.
Proof. exact (TRANS (@lem6894058) (@lem6894061)). Qed.
Lemma lem6894063 (_92033 : int) : (term44 _92033) = (term44 _92033).
Proof. exact (eq_refl (term44 _92033)). Qed.
Lemma lem6894064 (_92033 : int) : (term55 _92033) = (term77 _92033).
Proof. exact (MK_COMB (@lem6894063 _92033) (@lem6894062)). Qed.
Lemma lem6894065 (_92033 : int) : (term77 _92033) = (real_of_int _92033).
Proof. exact (@lem1982723 (real_of_int _92033)). Qed.
Lemma lem6894066 (_92033 : int) : (term55 _92033) = (real_of_int _92033).
Proof. exact (TRANS (@lem6894064 _92033) (@lem6894065 _92033)). Qed.
Lemma lem6894068 (_92033 : int) : (term54 _92033) = (real_of_int _92033).
Proof. exact (TRANS (@lem6894032 _92033) (@lem6894066 _92033)). Qed.
Lemma lem6894069 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6894070 (_92033 : int) : (term78 _92033) = (term79 _92033).
Proof. exact (MK_COMB (@lem6894069) (@lem6894068 _92033)). Qed.
Lemma lem6894071 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6894072 (_92033 : int) : (term53 _92033) = (term80 _92033).
Proof. exact (MK_COMB (@lem6894070 _92033) (@lem6894071)). Qed.
Lemma lem6894073 (_92033 : int) : (term34 _92033) = (term80 _92033).
Proof. exact (TRANS (@lem6894026 _92033) (@lem6894072 _92033)). Qed.
Lemma lem6894074 (_92034 : int) : (term34 _92034) = (term53 _92034).
Proof. exact (@lem1988287 (real_of_int _92034) term31). Qed.
Lemma lem6894080 (_92034 : int) : (term54 _92034) = (term55 _92034).
Proof. exact (@lem1982792 (real_of_int _92034) term31). Qed.
Lemma lem6894082 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6894083 : term31 = term57.
Proof. exact (@lem6894082 (NUMERAL 0)). Qed.
Lemma lem6894085 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6894086 : term60 = term61.
Proof. exact (@lem6894085 term8). Qed.
Lemma lem6894087 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6894088 : term62 = term63.
Proof. exact (MK_COMB (@lem6894087) (@lem6894086)). Qed.
Lemma lem6894089 : term64 = term65.
Proof. exact (MK_COMB (@lem6894088) (@lem6894083)). Qed.
Lemma lem6894090 : term65 = term66.
Proof. exact (@lem1981613 term60 term31 term43 term43). Qed.
Lemma lem6894092 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6894093 : term69 = term70.
Proof. exact (@lem6894092 term8 term8). Qed.
Lemma lem6894094 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6894095 : term72 = term8.
Proof. exact (EQ_MP (@lem6894094) (@lem940073)). Qed.
Lemma lem6894096 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6894097 : term70 = term43.
Proof. exact (MK_COMB (@lem6894096) (@lem6894095)). Qed.
Lemma lem6894098 : term69 = term43.
Proof. exact (TRANS (@lem6894093) (@lem6894097)). Qed.
Lemma lem6894100 (x : nat) : (term73 x) = term31.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6894101 : term64 = term31.
Proof. exact (@lem6894100 term8). Qed.
Lemma lem6894102 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6894103 : term74 = term75.
Proof. exact (MK_COMB (@lem6894102) (@lem6894101)). Qed.
Lemma lem6894104 : term66 = term57.
Proof. exact (MK_COMB (@lem6894103) (@lem6894098)). Qed.
Lemma lem6894105 : term65 = term57.
Proof. exact (TRANS (@lem6894090) (@lem6894104)). Qed.
Lemma lem6894106 : term64 = term57.
Proof. exact (TRANS (@lem6894089) (@lem6894105)). Qed.
Lemma lem6894108 (x : real) : (term76 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6894109 : term57 = term31.
Proof. exact (@lem6894108 term31). Qed.
Lemma lem6894110 : term64 = term31.
Proof. exact (TRANS (@lem6894106) (@lem6894109)). Qed.
Lemma lem6894111 (_92034 : int) : (term44 _92034) = (term44 _92034).
Proof. exact (eq_refl (term44 _92034)). Qed.
Lemma lem6894112 (_92034 : int) : (term55 _92034) = (term77 _92034).
Proof. exact (MK_COMB (@lem6894111 _92034) (@lem6894110)). Qed.
Lemma lem6894113 (_92034 : int) : (term77 _92034) = (real_of_int _92034).
Proof. exact (@lem1982723 (real_of_int _92034)). Qed.
Lemma lem6894114 (_92034 : int) : (term55 _92034) = (real_of_int _92034).
Proof. exact (TRANS (@lem6894112 _92034) (@lem6894113 _92034)). Qed.
Lemma lem6894116 (_92034 : int) : (term54 _92034) = (real_of_int _92034).
Proof. exact (TRANS (@lem6894080 _92034) (@lem6894114 _92034)). Qed.
Lemma lem6894117 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6894118 (_92034 : int) : (term78 _92034) = (term79 _92034).
Proof. exact (MK_COMB (@lem6894117) (@lem6894116 _92034)). Qed.
Lemma lem6894119 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6894120 (_92034 : int) : (term53 _92034) = (term80 _92034).
Proof. exact (MK_COMB (@lem6894118 _92034) (@lem6894119)). Qed.
Lemma lem6894121 (_92034 : int) : (term34 _92034) = (term80 _92034).
Proof. exact (TRANS (@lem6894074 _92034) (@lem6894120 _92034)). Qed.
Lemma lem6894122 (_92032 : int) (_92033 : int) : (term763 _92033 _92032) = (term787 _92032 _92033).
Proof. exact (@lem1988287 (real_of_int _92032) (term45 _92033)). Qed.
Lemma lem6894134 (_92032 : int) (_92033 : int) : (term788 _92032 _92033) = (term789 _92032 _92033).
Proof. exact (@lem1982792 (real_of_int _92032) (term45 _92033)). Qed.
Lemma lem6894135 (_92033 : int) : (term84 _92033) = (term85 _92033).
Proof. exact (@lem1982781 (real_of_int _92033) term60 term43). Qed.
Lemma lem6894137 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6894138 : term43 = term86.
Proof. exact (@lem6894137 term8). Qed.
Lemma lem6894140 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6894141 : term60 = term61.
Proof. exact (@lem6894140 term8). Qed.
Lemma lem6894142 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6894143 : term62 = term63.
Proof. exact (MK_COMB (@lem6894142) (@lem6894141)). Qed.
Lemma lem6894144 : term87 = term88.
Proof. exact (MK_COMB (@lem6894143) (@lem6894138)). Qed.
Lemma lem6894145 : term88 = term89.
Proof. exact (@lem1981613 term60 term43 term43 term43). Qed.
Lemma lem6894147 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6894148 : term69 = term70.
Proof. exact (@lem6894147 term8 term8). Qed.
Lemma lem6894149 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6894150 : term72 = term8.
Proof. exact (EQ_MP (@lem6894149) (@lem940073)). Qed.
Lemma lem6894151 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6894152 : term70 = term43.
Proof. exact (MK_COMB (@lem6894151) (@lem6894150)). Qed.
Lemma lem6894153 : term69 = term43.
Proof. exact (TRANS (@lem6894148) (@lem6894152)). Qed.
Lemma lem6894155 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6894156 : term87 = term92.
Proof. exact (@lem6894155 term8 term8). Qed.
Lemma lem6894157 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6894158 : term72 = term8.
Proof. exact (EQ_MP (@lem6894157) (@lem940073)). Qed.
Lemma lem6894159 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6894160 : term70 = term43.
Proof. exact (MK_COMB (@lem6894159) (@lem6894158)). Qed.
Lemma lem6894161 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6894162 : term92 = term60.
Proof. exact (MK_COMB (@lem6894161) (@lem6894160)). Qed.
Lemma lem6894163 : term87 = term60.
Proof. exact (TRANS (@lem6894156) (@lem6894162)). Qed.
Lemma lem6894164 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6894165 : term93 = term94.
Proof. exact (MK_COMB (@lem6894164) (@lem6894163)). Qed.
Lemma lem6894166 : term89 = term61.
Proof. exact (MK_COMB (@lem6894165) (@lem6894153)). Qed.
Lemma lem6894167 : term88 = term61.
Proof. exact (TRANS (@lem6894145) (@lem6894166)). Qed.
Lemma lem6894168 : term87 = term61.
Proof. exact (TRANS (@lem6894144) (@lem6894167)). Qed.
Lemma lem6894170 (x : real) : (term76 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6894171 : term61 = term60.
Proof. exact (@lem6894170 term60). Qed.
Lemma lem6894172 : term87 = term60.
Proof. exact (TRANS (@lem6894168) (@lem6894171)). Qed.
Lemma lem6894175 (_92033 : int) : (term95 _92033) = (term95 _92033).
Proof. exact (eq_refl (term95 _92033)). Qed.
Lemma lem6894176 (_92033 : int) : (term85 _92033) = (term96 _92033).
Proof. exact (MK_COMB (@lem6894175 _92033) (@lem6894172)). Qed.
Lemma lem6894177 (_92033 : int) : (term84 _92033) = (term96 _92033).
Proof. exact (TRANS (@lem6894135 _92033) (@lem6894176 _92033)). Qed.
Lemma lem6894178 (_92032 : int) : (term44 _92032) = (term44 _92032).
Proof. exact (eq_refl (term44 _92032)). Qed.
Lemma lem6894181 (_92032 : int) (_92033 : int) : (term789 _92032 _92033) = (term790 _92032 _92033).
Proof. exact (MK_COMB (@lem6894178 _92032) (@lem6894177 _92033)). Qed.
Lemma lem6894183 (_92032 : int) (_92033 : int) : (term788 _92032 _92033) = (term790 _92032 _92033).
Proof. exact (TRANS (@lem6894134 _92032 _92033) (@lem6894181 _92032 _92033)). Qed.
Lemma lem6894184 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6894185 (_92032 : int) (_92033 : int) : (term791 _92032 _92033) = (term792 _92032 _92033).
Proof. exact (MK_COMB (@lem6894184) (@lem6894183 _92032 _92033)). Qed.
Lemma lem6894186 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6894187 (_92032 : int) (_92033 : int) : (term787 _92032 _92033) = (term793 _92032 _92033).
Proof. exact (MK_COMB (@lem6894185 _92032 _92033) (@lem6894186)). Qed.
Lemma lem6894188 (_92032 : int) (_92033 : int) : (term763 _92033 _92032) = (term793 _92032 _92033).
Proof. exact (TRANS (@lem6894122 _92032 _92033) (@lem6894187 _92032 _92033)). Qed.
Lemma lem6894189 (_92034 : int) (_92032 : int) : (term26 _92032 _92034) = (term794 _92034 _92032).
Proof. exact (@lem1988287 (real_of_int _92034) (real_of_int _92032)). Qed.
Lemma lem6894195 (_92034 : int) (_92032 : int) : (term795 _92034 _92032) = (term796 _92034 _92032).
Proof. exact (@lem1982792 (real_of_int _92034) (real_of_int _92032)). Qed.
Lemma lem6894200 (_92032 : int) (_92034 : int) : (term796 _92034 _92032) = (term797 _92032 _92034).
Proof. exact (@lem1982761 (term99 _92032) (real_of_int _92034)). Qed.
Lemma lem6894202 (_92032 : int) (_92034 : int) : (term795 _92034 _92032) = (term797 _92032 _92034).
Proof. exact (TRANS (@lem6894195 _92034 _92032) (@lem6894200 _92032 _92034)). Qed.
Lemma lem6894203 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6894204 (_92032 : int) (_92034 : int) : (term798 _92034 _92032) = (term799 _92032 _92034).
Proof. exact (MK_COMB (@lem6894203) (@lem6894202 _92032 _92034)). Qed.
Lemma lem6894205 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6894206 (_92032 : int) (_92034 : int) : (term794 _92034 _92032) = (term800 _92032 _92034).
Proof. exact (MK_COMB (@lem6894204 _92032 _92034) (@lem6894205)). Qed.
Lemma lem6894207 (_92032 : int) (_92034 : int) : (term26 _92032 _92034) = (term800 _92032 _92034).
Proof. exact (TRANS (@lem6894189 _92034 _92032) (@lem6894206 _92032 _92034)). Qed.
Lemma lem6894208 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6894209 (_92032 : int) (_92033 : int) : (term764 _92033 _92032) = (term801 _92032 _92033).
Proof. exact (MK_COMB (@lem6894208) (@lem6894188 _92032 _92033)). Qed.
Lemma lem6894210 (_92033 : int) (_92032 : int) (_92034 : int) : (term765 _92033 _92032 _92034) = (term802 _92033 _92032 _92034).
Proof. exact (MK_COMB (@lem6894209 _92032 _92033) (@lem6894207 _92032 _92034)). Qed.
Lemma lem6894211 (_92032 : int) (_92033 : int) : (term763 _92033 _92032) = (term787 _92032 _92033).
Proof. exact (@lem1988287 (real_of_int _92032) (term45 _92033)). Qed.
Lemma lem6894223 (_92032 : int) (_92033 : int) : (term788 _92032 _92033) = (term789 _92032 _92033).
Proof. exact (@lem1982792 (real_of_int _92032) (term45 _92033)). Qed.
Lemma lem6894224 (_92033 : int) : (term84 _92033) = (term85 _92033).
Proof. exact (@lem1982781 (real_of_int _92033) term60 term43). Qed.
Lemma lem6894226 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6894227 : term43 = term86.
Proof. exact (@lem6894226 term8). Qed.
Lemma lem6894229 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6894230 : term60 = term61.
Proof. exact (@lem6894229 term8). Qed.
Lemma lem6894231 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6894232 : term62 = term63.
Proof. exact (MK_COMB (@lem6894231) (@lem6894230)). Qed.
Lemma lem6894233 : term87 = term88.
Proof. exact (MK_COMB (@lem6894232) (@lem6894227)). Qed.
Lemma lem6894234 : term88 = term89.
Proof. exact (@lem1981613 term60 term43 term43 term43). Qed.
Lemma lem6894236 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6894237 : term69 = term70.
Proof. exact (@lem6894236 term8 term8). Qed.
Lemma lem6894238 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6894239 : term72 = term8.
Proof. exact (EQ_MP (@lem6894238) (@lem940073)). Qed.
Lemma lem6894240 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6894241 : term70 = term43.
Proof. exact (MK_COMB (@lem6894240) (@lem6894239)). Qed.
Lemma lem6894242 : term69 = term43.
Proof. exact (TRANS (@lem6894237) (@lem6894241)). Qed.
Lemma lem6894244 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6894245 : term87 = term92.
Proof. exact (@lem6894244 term8 term8). Qed.
Lemma lem6894246 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6894247 : term72 = term8.
Proof. exact (EQ_MP (@lem6894246) (@lem940073)). Qed.
Lemma lem6894248 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6894249 : term70 = term43.
Proof. exact (MK_COMB (@lem6894248) (@lem6894247)). Qed.
Lemma lem6894250 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6894251 : term92 = term60.
Proof. exact (MK_COMB (@lem6894250) (@lem6894249)). Qed.
Lemma lem6894252 : term87 = term60.
Proof. exact (TRANS (@lem6894245) (@lem6894251)). Qed.
Lemma lem6894253 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6894254 : term93 = term94.
Proof. exact (MK_COMB (@lem6894253) (@lem6894252)). Qed.
Lemma lem6894255 : term89 = term61.
Proof. exact (MK_COMB (@lem6894254) (@lem6894242)). Qed.
Lemma lem6894256 : term88 = term61.
Proof. exact (TRANS (@lem6894234) (@lem6894255)). Qed.
Lemma lem6894257 : term87 = term61.
Proof. exact (TRANS (@lem6894233) (@lem6894256)). Qed.
Lemma lem6894259 (x : real) : (term76 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6894260 : term61 = term60.
Proof. exact (@lem6894259 term60). Qed.
Lemma lem6894261 : term87 = term60.
Proof. exact (TRANS (@lem6894257) (@lem6894260)). Qed.
Lemma lem6894264 (_92033 : int) : (term95 _92033) = (term95 _92033).
Proof. exact (eq_refl (term95 _92033)). Qed.
Lemma lem6894265 (_92033 : int) : (term85 _92033) = (term96 _92033).
Proof. exact (MK_COMB (@lem6894264 _92033) (@lem6894261)). Qed.
Lemma lem6894266 (_92033 : int) : (term84 _92033) = (term96 _92033).
Proof. exact (TRANS (@lem6894224 _92033) (@lem6894265 _92033)). Qed.
Lemma lem6894267 (_92032 : int) : (term44 _92032) = (term44 _92032).
Proof. exact (eq_refl (term44 _92032)). Qed.
Lemma lem6894270 (_92032 : int) (_92033 : int) : (term789 _92032 _92033) = (term790 _92032 _92033).
Proof. exact (MK_COMB (@lem6894267 _92032) (@lem6894266 _92033)). Qed.
Lemma lem6894272 (_92032 : int) (_92033 : int) : (term788 _92032 _92033) = (term790 _92032 _92033).
Proof. exact (TRANS (@lem6894223 _92032 _92033) (@lem6894270 _92032 _92033)). Qed.
Lemma lem6894273 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6894274 (_92032 : int) (_92033 : int) : (term791 _92032 _92033) = (term792 _92032 _92033).
Proof. exact (MK_COMB (@lem6894273) (@lem6894272 _92032 _92033)). Qed.
Lemma lem6894275 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6894276 (_92032 : int) (_92033 : int) : (term787 _92032 _92033) = (term793 _92032 _92033).
Proof. exact (MK_COMB (@lem6894274 _92032 _92033) (@lem6894275)). Qed.
Lemma lem6894277 (_92032 : int) (_92033 : int) : (term763 _92033 _92032) = (term793 _92032 _92033).
Proof. exact (TRANS (@lem6894211 _92032 _92033) (@lem6894276 _92032 _92033)). Qed.
Lemma lem6894278 (_92033 : int) (_92032 : int) : (term763 _92032 _92033) = (term787 _92033 _92032).
Proof. exact (@lem1988287 (real_of_int _92033) (term45 _92032)). Qed.
Lemma lem6894290 (_92033 : int) (_92032 : int) : (term788 _92033 _92032) = (term789 _92033 _92032).
Proof. exact (@lem1982792 (real_of_int _92033) (term45 _92032)). Qed.
Lemma lem6894291 (_92032 : int) : (term84 _92032) = (term85 _92032).
Proof. exact (@lem1982781 (real_of_int _92032) term60 term43). Qed.
Lemma lem6894293 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6894294 : term43 = term86.
Proof. exact (@lem6894293 term8). Qed.
Lemma lem6894296 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6894297 : term60 = term61.
Proof. exact (@lem6894296 term8). Qed.
Lemma lem6894298 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6894299 : term62 = term63.
Proof. exact (MK_COMB (@lem6894298) (@lem6894297)). Qed.
Lemma lem6894300 : term87 = term88.
Proof. exact (MK_COMB (@lem6894299) (@lem6894294)). Qed.
Lemma lem6894301 : term88 = term89.
Proof. exact (@lem1981613 term60 term43 term43 term43). Qed.
Lemma lem6894303 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6894304 : term69 = term70.
Proof. exact (@lem6894303 term8 term8). Qed.
Lemma lem6894305 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6894306 : term72 = term8.
Proof. exact (EQ_MP (@lem6894305) (@lem940073)). Qed.
Lemma lem6894307 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6894308 : term70 = term43.
Proof. exact (MK_COMB (@lem6894307) (@lem6894306)). Qed.
Lemma lem6894309 : term69 = term43.
Proof. exact (TRANS (@lem6894304) (@lem6894308)). Qed.
Lemma lem6894311 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6894312 : term87 = term92.
Proof. exact (@lem6894311 term8 term8). Qed.
Lemma lem6894313 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6894314 : term72 = term8.
Proof. exact (EQ_MP (@lem6894313) (@lem940073)). Qed.
Lemma lem6894315 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6894316 : term70 = term43.
Proof. exact (MK_COMB (@lem6894315) (@lem6894314)). Qed.
Lemma lem6894317 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6894318 : term92 = term60.
Proof. exact (MK_COMB (@lem6894317) (@lem6894316)). Qed.
Lemma lem6894319 : term87 = term60.
Proof. exact (TRANS (@lem6894312) (@lem6894318)). Qed.
Lemma lem6894320 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6894321 : term93 = term94.
Proof. exact (MK_COMB (@lem6894320) (@lem6894319)). Qed.
Lemma lem6894322 : term89 = term61.
Proof. exact (MK_COMB (@lem6894321) (@lem6894309)). Qed.
Lemma lem6894323 : term88 = term61.
Proof. exact (TRANS (@lem6894301) (@lem6894322)). Qed.
Lemma lem6894324 : term87 = term61.
Proof. exact (TRANS (@lem6894300) (@lem6894323)). Qed.
Lemma lem6894326 (x : real) : (term76 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6894327 : term61 = term60.
Proof. exact (@lem6894326 term60). Qed.
Lemma lem6894328 : term87 = term60.
Proof. exact (TRANS (@lem6894324) (@lem6894327)). Qed.
Lemma lem6894331 (_92032 : int) : (term95 _92032) = (term95 _92032).
Proof. exact (eq_refl (term95 _92032)). Qed.
Lemma lem6894332 (_92032 : int) : (term85 _92032) = (term96 _92032).
Proof. exact (MK_COMB (@lem6894331 _92032) (@lem6894328)). Qed.
Lemma lem6894333 (_92032 : int) : (term84 _92032) = (term96 _92032).
Proof. exact (TRANS (@lem6894291 _92032) (@lem6894332 _92032)). Qed.
Lemma lem6894334 (_92033 : int) : (term44 _92033) = (term44 _92033).
Proof. exact (eq_refl (term44 _92033)). Qed.
Lemma lem6894335 (_92033 : int) (_92032 : int) : (term789 _92033 _92032) = (term790 _92033 _92032).
Proof. exact (MK_COMB (@lem6894334 _92033) (@lem6894333 _92032)). Qed.
Lemma lem6894340 (_92032 : int) (_92033 : int) : (term790 _92033 _92032) = (term803 _92032 _92033).
Proof. exact (@lem1982757 (term99 _92032) (real_of_int _92033) term60). Qed.
Lemma lem6894341 (_92032 : int) (_92033 : int) : (term789 _92033 _92032) = (term803 _92032 _92033).
Proof. exact (TRANS (@lem6894335 _92033 _92032) (@lem6894340 _92032 _92033)). Qed.
Lemma lem6894343 (_92032 : int) (_92033 : int) : (term788 _92033 _92032) = (term803 _92032 _92033).
Proof. exact (TRANS (@lem6894290 _92033 _92032) (@lem6894341 _92032 _92033)). Qed.
Lemma lem6894344 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6894345 (_92032 : int) (_92033 : int) : (term791 _92033 _92032) = (term804 _92032 _92033).
Proof. exact (MK_COMB (@lem6894344) (@lem6894343 _92032 _92033)). Qed.
Lemma lem6894346 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6894347 (_92032 : int) (_92033 : int) : (term787 _92033 _92032) = (term805 _92032 _92033).
Proof. exact (MK_COMB (@lem6894345 _92032 _92033) (@lem6894346)). Qed.
Lemma lem6894348 (_92032 : int) (_92033 : int) : (term763 _92032 _92033) = (term805 _92032 _92033).
Proof. exact (TRANS (@lem6894278 _92033 _92032) (@lem6894347 _92032 _92033)). Qed.
Lemma lem6894349 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6894350 (_92032 : int) (_92033 : int) : (term768 _92033 _92032) = (term806 _92032 _92033).
Proof. exact (MK_COMB (@lem6894349) (@lem6894277 _92032 _92033)). Qed.
Lemma lem6894351 (_92032 : int) (_92033 : int) : (term769 _92032 _92033) = (term807 _92032 _92033).
Proof. exact (MK_COMB (@lem6894350 _92032 _92033) (@lem6894348 _92032 _92033)). Qed.
Lemma lem6894352 (_92033 : int) (_92032 : int) : (term763 _92032 _92033) = (term787 _92033 _92032).
Proof. exact (@lem1988287 (real_of_int _92033) (term45 _92032)). Qed.
Lemma lem6894364 (_92033 : int) (_92032 : int) : (term788 _92033 _92032) = (term789 _92033 _92032).
Proof. exact (@lem1982792 (real_of_int _92033) (term45 _92032)). Qed.
Lemma lem6894365 (_92032 : int) : (term84 _92032) = (term85 _92032).
Proof. exact (@lem1982781 (real_of_int _92032) term60 term43). Qed.
Lemma lem6894367 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6894368 : term43 = term86.
Proof. exact (@lem6894367 term8). Qed.
Lemma lem6894370 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6894371 : term60 = term61.
Proof. exact (@lem6894370 term8). Qed.
Lemma lem6894372 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6894373 : term62 = term63.
Proof. exact (MK_COMB (@lem6894372) (@lem6894371)). Qed.
Lemma lem6894374 : term87 = term88.
Proof. exact (MK_COMB (@lem6894373) (@lem6894368)). Qed.
Lemma lem6894375 : term88 = term89.
Proof. exact (@lem1981613 term60 term43 term43 term43). Qed.
Lemma lem6894377 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6894378 : term69 = term70.
Proof. exact (@lem6894377 term8 term8). Qed.
Lemma lem6894379 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6894380 : term72 = term8.
Proof. exact (EQ_MP (@lem6894379) (@lem940073)). Qed.
Lemma lem6894381 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6894382 : term70 = term43.
Proof. exact (MK_COMB (@lem6894381) (@lem6894380)). Qed.
Lemma lem6894383 : term69 = term43.
Proof. exact (TRANS (@lem6894378) (@lem6894382)). Qed.
Lemma lem6894385 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6894386 : term87 = term92.
Proof. exact (@lem6894385 term8 term8). Qed.
Lemma lem6894387 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6894388 : term72 = term8.
Proof. exact (EQ_MP (@lem6894387) (@lem940073)). Qed.
Lemma lem6894389 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6894390 : term70 = term43.
Proof. exact (MK_COMB (@lem6894389) (@lem6894388)). Qed.
Lemma lem6894391 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6894392 : term92 = term60.
Proof. exact (MK_COMB (@lem6894391) (@lem6894390)). Qed.
Lemma lem6894393 : term87 = term60.
Proof. exact (TRANS (@lem6894386) (@lem6894392)). Qed.
Lemma lem6894394 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6894395 : term93 = term94.
Proof. exact (MK_COMB (@lem6894394) (@lem6894393)). Qed.
Lemma lem6894396 : term89 = term61.
Proof. exact (MK_COMB (@lem6894395) (@lem6894383)). Qed.
Lemma lem6894397 : term88 = term61.
Proof. exact (TRANS (@lem6894375) (@lem6894396)). Qed.
Lemma lem6894398 : term87 = term61.
Proof. exact (TRANS (@lem6894374) (@lem6894397)). Qed.
Lemma lem6894400 (x : real) : (term76 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6894401 : term61 = term60.
Proof. exact (@lem6894400 term60). Qed.
Lemma lem6894402 : term87 = term60.
Proof. exact (TRANS (@lem6894398) (@lem6894401)). Qed.
Lemma lem6894405 (_92032 : int) : (term95 _92032) = (term95 _92032).
Proof. exact (eq_refl (term95 _92032)). Qed.
Lemma lem6894406 (_92032 : int) : (term85 _92032) = (term96 _92032).
Proof. exact (MK_COMB (@lem6894405 _92032) (@lem6894402)). Qed.
Lemma lem6894407 (_92032 : int) : (term84 _92032) = (term96 _92032).
Proof. exact (TRANS (@lem6894365 _92032) (@lem6894406 _92032)). Qed.
Lemma lem6894408 (_92033 : int) : (term44 _92033) = (term44 _92033).
Proof. exact (eq_refl (term44 _92033)). Qed.
Lemma lem6894409 (_92033 : int) (_92032 : int) : (term789 _92033 _92032) = (term790 _92033 _92032).
Proof. exact (MK_COMB (@lem6894408 _92033) (@lem6894407 _92032)). Qed.
Lemma lem6894414 (_92032 : int) (_92033 : int) : (term790 _92033 _92032) = (term803 _92032 _92033).
Proof. exact (@lem1982757 (term99 _92032) (real_of_int _92033) term60). Qed.
Lemma lem6894415 (_92032 : int) (_92033 : int) : (term789 _92033 _92032) = (term803 _92032 _92033).
Proof. exact (TRANS (@lem6894409 _92033 _92032) (@lem6894414 _92032 _92033)). Qed.
Lemma lem6894417 (_92032 : int) (_92033 : int) : (term788 _92033 _92032) = (term803 _92032 _92033).
Proof. exact (TRANS (@lem6894364 _92033 _92032) (@lem6894415 _92032 _92033)). Qed.
Lemma lem6894418 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6894419 (_92032 : int) (_92033 : int) : (term791 _92033 _92032) = (term804 _92032 _92033).
Proof. exact (MK_COMB (@lem6894418) (@lem6894417 _92032 _92033)). Qed.
Lemma lem6894420 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6894421 (_92032 : int) (_92033 : int) : (term787 _92033 _92032) = (term805 _92032 _92033).
Proof. exact (MK_COMB (@lem6894419 _92032 _92033) (@lem6894420)). Qed.
Lemma lem6894422 (_92032 : int) (_92033 : int) : (term763 _92032 _92033) = (term805 _92032 _92033).
Proof. exact (TRANS (@lem6894352 _92033 _92032) (@lem6894421 _92032 _92033)). Qed.
Lemma lem6894423 (_92032 : int) (_92033 : int) : (term763 _92033 _92032) = (term787 _92032 _92033).
Proof. exact (@lem1988287 (real_of_int _92032) (term45 _92033)). Qed.
Lemma lem6894435 (_92032 : int) (_92033 : int) : (term788 _92032 _92033) = (term789 _92032 _92033).
Proof. exact (@lem1982792 (real_of_int _92032) (term45 _92033)). Qed.
Lemma lem6894436 (_92033 : int) : (term84 _92033) = (term85 _92033).
Proof. exact (@lem1982781 (real_of_int _92033) term60 term43). Qed.
Lemma lem6894438 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6894439 : term43 = term86.
Proof. exact (@lem6894438 term8). Qed.
Lemma lem6894441 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6894442 : term60 = term61.
Proof. exact (@lem6894441 term8). Qed.
Lemma lem6894443 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6894444 : term62 = term63.
Proof. exact (MK_COMB (@lem6894443) (@lem6894442)). Qed.
Lemma lem6894445 : term87 = term88.
Proof. exact (MK_COMB (@lem6894444) (@lem6894439)). Qed.
Lemma lem6894446 : term88 = term89.
Proof. exact (@lem1981613 term60 term43 term43 term43). Qed.
Lemma lem6894448 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6894449 : term69 = term70.
Proof. exact (@lem6894448 term8 term8). Qed.
Lemma lem6894450 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6894451 : term72 = term8.
Proof. exact (EQ_MP (@lem6894450) (@lem940073)). Qed.
Lemma lem6894452 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6894453 : term70 = term43.
Proof. exact (MK_COMB (@lem6894452) (@lem6894451)). Qed.
Lemma lem6894454 : term69 = term43.
Proof. exact (TRANS (@lem6894449) (@lem6894453)). Qed.
Lemma lem6894456 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6894457 : term87 = term92.
Proof. exact (@lem6894456 term8 term8). Qed.
Lemma lem6894458 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6894459 : term72 = term8.
Proof. exact (EQ_MP (@lem6894458) (@lem940073)). Qed.
Lemma lem6894460 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6894461 : term70 = term43.
Proof. exact (MK_COMB (@lem6894460) (@lem6894459)). Qed.
Lemma lem6894462 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6894463 : term92 = term60.
Proof. exact (MK_COMB (@lem6894462) (@lem6894461)). Qed.
Lemma lem6894464 : term87 = term60.
Proof. exact (TRANS (@lem6894457) (@lem6894463)). Qed.
Lemma lem6894465 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6894466 : term93 = term94.
Proof. exact (MK_COMB (@lem6894465) (@lem6894464)). Qed.
Lemma lem6894467 : term89 = term61.
Proof. exact (MK_COMB (@lem6894466) (@lem6894454)). Qed.
Lemma lem6894468 : term88 = term61.
Proof. exact (TRANS (@lem6894446) (@lem6894467)). Qed.
Lemma lem6894469 : term87 = term61.
Proof. exact (TRANS (@lem6894445) (@lem6894468)). Qed.
Lemma lem6894471 (x : real) : (term76 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6894472 : term61 = term60.
Proof. exact (@lem6894471 term60). Qed.
Lemma lem6894473 : term87 = term60.
Proof. exact (TRANS (@lem6894469) (@lem6894472)). Qed.
Lemma lem6894476 (_92033 : int) : (term95 _92033) = (term95 _92033).
Proof. exact (eq_refl (term95 _92033)). Qed.
Lemma lem6894477 (_92033 : int) : (term85 _92033) = (term96 _92033).
Proof. exact (MK_COMB (@lem6894476 _92033) (@lem6894473)). Qed.
Lemma lem6894478 (_92033 : int) : (term84 _92033) = (term96 _92033).
Proof. exact (TRANS (@lem6894436 _92033) (@lem6894477 _92033)). Qed.
Lemma lem6894479 (_92032 : int) : (term44 _92032) = (term44 _92032).
Proof. exact (eq_refl (term44 _92032)). Qed.
Lemma lem6894482 (_92032 : int) (_92033 : int) : (term789 _92032 _92033) = (term790 _92032 _92033).
Proof. exact (MK_COMB (@lem6894479 _92032) (@lem6894478 _92033)). Qed.
Lemma lem6894484 (_92032 : int) (_92033 : int) : (term788 _92032 _92033) = (term790 _92032 _92033).
Proof. exact (TRANS (@lem6894435 _92032 _92033) (@lem6894482 _92032 _92033)). Qed.
Lemma lem6894485 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6894486 (_92032 : int) (_92033 : int) : (term791 _92032 _92033) = (term792 _92032 _92033).
Proof. exact (MK_COMB (@lem6894485) (@lem6894484 _92032 _92033)). Qed.
Lemma lem6894487 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6894488 (_92032 : int) (_92033 : int) : (term787 _92032 _92033) = (term793 _92032 _92033).
Proof. exact (MK_COMB (@lem6894486 _92032 _92033) (@lem6894487)). Qed.
Lemma lem6894489 (_92032 : int) (_92033 : int) : (term763 _92033 _92032) = (term793 _92032 _92033).
Proof. exact (TRANS (@lem6894423 _92032 _92033) (@lem6894488 _92032 _92033)). Qed.
Lemma lem6894490 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6894491 (_92032 : int) (_92033 : int) : (term764 _92032 _92033) = (term808 _92032 _92033).
Proof. exact (MK_COMB (@lem6894490) (@lem6894422 _92032 _92033)). Qed.
Lemma lem6894492 (_92032 : int) (_92033 : int) : (term771 _92033 _92032) = (term809 _92032 _92033).
Proof. exact (MK_COMB (@lem6894491 _92032 _92033) (@lem6894489 _92032 _92033)). Qed.
Lemma lem6894493 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6894494 (_92032 : int) (_92033 : int) : (term772 _92032 _92033) = (term810 _92032 _92033).
Proof. exact (MK_COMB (@lem6894493) (@lem6894351 _92032 _92033)). Qed.
Lemma lem6894495 (_92032 : int) (_92033 : int) : (term773 _92033 _92032) = (term811 _92032 _92033).
Proof. exact (MK_COMB (@lem6894494 _92032 _92033) (@lem6894492 _92032 _92033)). Qed.
Lemma lem6894496 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6894497 (_92033 : int) (_92032 : int) (_92034 : int) : (term774 _92033 _92032 _92034) = (term812 _92033 _92032 _92034).
Proof. exact (MK_COMB (@lem6894496) (@lem6894210 _92033 _92032 _92034)). Qed.
Lemma lem6894498 (_92034 : int) (_92032 : int) (_92033 : int) : (term775 _92034 _92033 _92032) = (term813 _92034 _92032 _92033).
Proof. exact (MK_COMB (@lem6894497 _92033 _92032 _92034) (@lem6894495 _92032 _92033)). Qed.
Lemma lem6894499 (_92033 : int) (_92032 : int) : (term26 _92032 _92033) = (term794 _92033 _92032).
Proof. exact (@lem1988287 (real_of_int _92033) (real_of_int _92032)). Qed.
Lemma lem6894505 (_92033 : int) (_92032 : int) : (term795 _92033 _92032) = (term796 _92033 _92032).
Proof. exact (@lem1982792 (real_of_int _92033) (real_of_int _92032)). Qed.
Lemma lem6894510 (_92032 : int) (_92033 : int) : (term796 _92033 _92032) = (term797 _92032 _92033).
Proof. exact (@lem1982761 (term99 _92032) (real_of_int _92033)). Qed.
Lemma lem6894512 (_92032 : int) (_92033 : int) : (term795 _92033 _92032) = (term797 _92032 _92033).
Proof. exact (TRANS (@lem6894505 _92033 _92032) (@lem6894510 _92032 _92033)). Qed.
Lemma lem6894513 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6894514 (_92032 : int) (_92033 : int) : (term798 _92033 _92032) = (term799 _92032 _92033).
Proof. exact (MK_COMB (@lem6894513) (@lem6894512 _92032 _92033)). Qed.
Lemma lem6894515 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6894516 (_92032 : int) (_92033 : int) : (term794 _92033 _92032) = (term800 _92032 _92033).
Proof. exact (MK_COMB (@lem6894514 _92032 _92033) (@lem6894515)). Qed.
Lemma lem6894517 (_92032 : int) (_92033 : int) : (term26 _92032 _92033) = (term800 _92032 _92033).
Proof. exact (TRANS (@lem6894499 _92033 _92032) (@lem6894516 _92032 _92033)). Qed.
Lemma lem6894518 (_92032 : int) (_92033 : int) : (term763 _92033 _92032) = (term787 _92032 _92033).
Proof. exact (@lem1988287 (real_of_int _92032) (term45 _92033)). Qed.
Lemma lem6894530 (_92032 : int) (_92033 : int) : (term788 _92032 _92033) = (term789 _92032 _92033).
Proof. exact (@lem1982792 (real_of_int _92032) (term45 _92033)). Qed.
Lemma lem6894531 (_92033 : int) : (term84 _92033) = (term85 _92033).
Proof. exact (@lem1982781 (real_of_int _92033) term60 term43). Qed.
Lemma lem6894533 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6894534 : term43 = term86.
Proof. exact (@lem6894533 term8). Qed.
Lemma lem6894536 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6894537 : term60 = term61.
Proof. exact (@lem6894536 term8). Qed.
Lemma lem6894538 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6894539 : term62 = term63.
Proof. exact (MK_COMB (@lem6894538) (@lem6894537)). Qed.
Lemma lem6894540 : term87 = term88.
Proof. exact (MK_COMB (@lem6894539) (@lem6894534)). Qed.
Lemma lem6894541 : term88 = term89.
Proof. exact (@lem1981613 term60 term43 term43 term43). Qed.
Lemma lem6894543 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6894544 : term69 = term70.
Proof. exact (@lem6894543 term8 term8). Qed.
Lemma lem6894545 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6894546 : term72 = term8.
Proof. exact (EQ_MP (@lem6894545) (@lem940073)). Qed.
Lemma lem6894547 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6894548 : term70 = term43.
Proof. exact (MK_COMB (@lem6894547) (@lem6894546)). Qed.
Lemma lem6894549 : term69 = term43.
Proof. exact (TRANS (@lem6894544) (@lem6894548)). Qed.
Lemma lem6894551 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6894552 : term87 = term92.
Proof. exact (@lem6894551 term8 term8). Qed.
Lemma lem6894553 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6894554 : term72 = term8.
Proof. exact (EQ_MP (@lem6894553) (@lem940073)). Qed.
Lemma lem6894555 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6894556 : term70 = term43.
Proof. exact (MK_COMB (@lem6894555) (@lem6894554)). Qed.
Lemma lem6894557 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6894558 : term92 = term60.
Proof. exact (MK_COMB (@lem6894557) (@lem6894556)). Qed.
Lemma lem6894559 : term87 = term60.
Proof. exact (TRANS (@lem6894552) (@lem6894558)). Qed.
Lemma lem6894560 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6894561 : term93 = term94.
Proof. exact (MK_COMB (@lem6894560) (@lem6894559)). Qed.
Lemma lem6894562 : term89 = term61.
Proof. exact (MK_COMB (@lem6894561) (@lem6894549)). Qed.
Lemma lem6894563 : term88 = term61.
Proof. exact (TRANS (@lem6894541) (@lem6894562)). Qed.
Lemma lem6894564 : term87 = term61.
Proof. exact (TRANS (@lem6894540) (@lem6894563)). Qed.
Lemma lem6894566 (x : real) : (term76 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6894567 : term61 = term60.
Proof. exact (@lem6894566 term60). Qed.
Lemma lem6894568 : term87 = term60.
Proof. exact (TRANS (@lem6894564) (@lem6894567)). Qed.
Lemma lem6894571 (_92033 : int) : (term95 _92033) = (term95 _92033).
Proof. exact (eq_refl (term95 _92033)). Qed.
Lemma lem6894572 (_92033 : int) : (term85 _92033) = (term96 _92033).
Proof. exact (MK_COMB (@lem6894571 _92033) (@lem6894568)). Qed.
Lemma lem6894573 (_92033 : int) : (term84 _92033) = (term96 _92033).
Proof. exact (TRANS (@lem6894531 _92033) (@lem6894572 _92033)). Qed.
Lemma lem6894574 (_92032 : int) : (term44 _92032) = (term44 _92032).
Proof. exact (eq_refl (term44 _92032)). Qed.
Lemma lem6894577 (_92032 : int) (_92033 : int) : (term789 _92032 _92033) = (term790 _92032 _92033).
Proof. exact (MK_COMB (@lem6894574 _92032) (@lem6894573 _92033)). Qed.
Lemma lem6894579 (_92032 : int) (_92033 : int) : (term788 _92032 _92033) = (term790 _92032 _92033).
Proof. exact (TRANS (@lem6894530 _92032 _92033) (@lem6894577 _92032 _92033)). Qed.
Lemma lem6894580 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6894581 (_92032 : int) (_92033 : int) : (term791 _92032 _92033) = (term792 _92032 _92033).
Proof. exact (MK_COMB (@lem6894580) (@lem6894579 _92032 _92033)). Qed.
Lemma lem6894582 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6894583 (_92032 : int) (_92033 : int) : (term787 _92032 _92033) = (term793 _92032 _92033).
Proof. exact (MK_COMB (@lem6894581 _92032 _92033) (@lem6894582)). Qed.
Lemma lem6894584 (_92032 : int) (_92033 : int) : (term763 _92033 _92032) = (term793 _92032 _92033).
Proof. exact (TRANS (@lem6894518 _92032 _92033) (@lem6894583 _92032 _92033)). Qed.
Lemma lem6894585 (_92034 : int) (_92032 : int) : (term26 _92032 _92034) = (term794 _92034 _92032).
Proof. exact (@lem1988287 (real_of_int _92034) (real_of_int _92032)). Qed.
Lemma lem6894591 (_92034 : int) (_92032 : int) : (term795 _92034 _92032) = (term796 _92034 _92032).
Proof. exact (@lem1982792 (real_of_int _92034) (real_of_int _92032)). Qed.
Lemma lem6894596 (_92032 : int) (_92034 : int) : (term796 _92034 _92032) = (term797 _92032 _92034).
Proof. exact (@lem1982761 (term99 _92032) (real_of_int _92034)). Qed.
Lemma lem6894598 (_92032 : int) (_92034 : int) : (term795 _92034 _92032) = (term797 _92032 _92034).
Proof. exact (TRANS (@lem6894591 _92034 _92032) (@lem6894596 _92032 _92034)). Qed.
Lemma lem6894599 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6894600 (_92032 : int) (_92034 : int) : (term798 _92034 _92032) = (term799 _92032 _92034).
Proof. exact (MK_COMB (@lem6894599) (@lem6894598 _92032 _92034)). Qed.
Lemma lem6894601 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6894602 (_92032 : int) (_92034 : int) : (term794 _92034 _92032) = (term800 _92032 _92034).
Proof. exact (MK_COMB (@lem6894600 _92032 _92034) (@lem6894601)). Qed.
Lemma lem6894603 (_92032 : int) (_92034 : int) : (term26 _92032 _92034) = (term800 _92032 _92034).
Proof. exact (TRANS (@lem6894585 _92034 _92032) (@lem6894602 _92032 _92034)). Qed.
Lemma lem6894604 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6894605 (_92032 : int) (_92033 : int) : (term764 _92033 _92032) = (term801 _92032 _92033).
Proof. exact (MK_COMB (@lem6894604) (@lem6894584 _92032 _92033)). Qed.
Lemma lem6894606 (_92033 : int) (_92032 : int) (_92034 : int) : (term765 _92033 _92032 _92034) = (term802 _92033 _92032 _92034).
Proof. exact (MK_COMB (@lem6894605 _92032 _92033) (@lem6894603 _92032 _92034)). Qed.
Lemma lem6894607 {A : Type'} (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term563 A f j dom neut) = (term563 A f j dom neut).
Proof. exact (eq_refl (term563 A f j dom neut)). Qed.
Lemma lem6894608 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6894609 (_92033 : int) (_92032 : int) (_92034 : int) : (term774 _92033 _92032 _92034) = (term812 _92033 _92032 _92034).
Proof. exact (MK_COMB (@lem6894608) (@lem6894606 _92033 _92032 _92034)). Qed.
Lemma lem6894610 {A : Type'} (_92033 : int) (_92032 : int) (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term776 A _92033 _92032 _92034 f j dom neut) = (term814 A _92033 _92032 _92034 f j dom neut).
Proof. exact (MK_COMB (@lem6894609 _92033 _92032 _92034) (@lem6894607 A f j dom neut)). Qed.
Lemma lem6894611 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6894612 (_92032 : int) (_92033 : int) : (term777 _92032 _92033) = (term815 _92032 _92033).
Proof. exact (MK_COMB (@lem6894611) (@lem6894517 _92032 _92033)). Qed.
Lemma lem6894613 {A : Type'} (_92033 : int) (_92032 : int) (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term778 A _92033 _92032 _92034 f j dom neut) = (term816 A _92033 _92032 _92034 f j dom neut).
Proof. exact (MK_COMB (@lem6894612 _92032 _92033) (@lem6894610 A _92033 _92032 _92034 f j dom neut)). Qed.
Lemma lem6894614 (_92033 : int) (_92032 : int) : (term763 _92032 _92033) = (term787 _92033 _92032).
Proof. exact (@lem1988287 (real_of_int _92033) (term45 _92032)). Qed.
Lemma lem6894626 (_92033 : int) (_92032 : int) : (term788 _92033 _92032) = (term789 _92033 _92032).
Proof. exact (@lem1982792 (real_of_int _92033) (term45 _92032)). Qed.
Lemma lem6894627 (_92032 : int) : (term84 _92032) = (term85 _92032).
Proof. exact (@lem1982781 (real_of_int _92032) term60 term43). Qed.
Lemma lem6894629 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6894630 : term43 = term86.
Proof. exact (@lem6894629 term8). Qed.
Lemma lem6894632 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6894633 : term60 = term61.
Proof. exact (@lem6894632 term8). Qed.
Lemma lem6894634 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6894635 : term62 = term63.
Proof. exact (MK_COMB (@lem6894634) (@lem6894633)). Qed.
Lemma lem6894636 : term87 = term88.
Proof. exact (MK_COMB (@lem6894635) (@lem6894630)). Qed.
Lemma lem6894637 : term88 = term89.
Proof. exact (@lem1981613 term60 term43 term43 term43). Qed.
Lemma lem6894639 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6894640 : term69 = term70.
Proof. exact (@lem6894639 term8 term8). Qed.
Lemma lem6894641 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6894642 : term72 = term8.
Proof. exact (EQ_MP (@lem6894641) (@lem940073)). Qed.
Lemma lem6894643 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6894644 : term70 = term43.
Proof. exact (MK_COMB (@lem6894643) (@lem6894642)). Qed.
Lemma lem6894645 : term69 = term43.
Proof. exact (TRANS (@lem6894640) (@lem6894644)). Qed.
Lemma lem6894647 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6894648 : term87 = term92.
Proof. exact (@lem6894647 term8 term8). Qed.
Lemma lem6894649 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6894650 : term72 = term8.
Proof. exact (EQ_MP (@lem6894649) (@lem940073)). Qed.
Lemma lem6894651 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6894652 : term70 = term43.
Proof. exact (MK_COMB (@lem6894651) (@lem6894650)). Qed.
Lemma lem6894653 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6894654 : term92 = term60.
Proof. exact (MK_COMB (@lem6894653) (@lem6894652)). Qed.
Lemma lem6894655 : term87 = term60.
Proof. exact (TRANS (@lem6894648) (@lem6894654)). Qed.
Lemma lem6894656 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6894657 : term93 = term94.
Proof. exact (MK_COMB (@lem6894656) (@lem6894655)). Qed.
Lemma lem6894658 : term89 = term61.
Proof. exact (MK_COMB (@lem6894657) (@lem6894645)). Qed.
Lemma lem6894659 : term88 = term61.
Proof. exact (TRANS (@lem6894637) (@lem6894658)). Qed.
Lemma lem6894660 : term87 = term61.
Proof. exact (TRANS (@lem6894636) (@lem6894659)). Qed.
Lemma lem6894662 (x : real) : (term76 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6894663 : term61 = term60.
Proof. exact (@lem6894662 term60). Qed.
Lemma lem6894664 : term87 = term60.
Proof. exact (TRANS (@lem6894660) (@lem6894663)). Qed.
Lemma lem6894667 (_92032 : int) : (term95 _92032) = (term95 _92032).
Proof. exact (eq_refl (term95 _92032)). Qed.
Lemma lem6894668 (_92032 : int) : (term85 _92032) = (term96 _92032).
Proof. exact (MK_COMB (@lem6894667 _92032) (@lem6894664)). Qed.
Lemma lem6894669 (_92032 : int) : (term84 _92032) = (term96 _92032).
Proof. exact (TRANS (@lem6894627 _92032) (@lem6894668 _92032)). Qed.
Lemma lem6894670 (_92033 : int) : (term44 _92033) = (term44 _92033).
Proof. exact (eq_refl (term44 _92033)). Qed.
Lemma lem6894671 (_92033 : int) (_92032 : int) : (term789 _92033 _92032) = (term790 _92033 _92032).
Proof. exact (MK_COMB (@lem6894670 _92033) (@lem6894669 _92032)). Qed.
Lemma lem6894676 (_92032 : int) (_92033 : int) : (term790 _92033 _92032) = (term803 _92032 _92033).
Proof. exact (@lem1982757 (term99 _92032) (real_of_int _92033) term60). Qed.
Lemma lem6894677 (_92032 : int) (_92033 : int) : (term789 _92033 _92032) = (term803 _92032 _92033).
Proof. exact (TRANS (@lem6894671 _92033 _92032) (@lem6894676 _92032 _92033)). Qed.
Lemma lem6894679 (_92032 : int) (_92033 : int) : (term788 _92033 _92032) = (term803 _92032 _92033).
Proof. exact (TRANS (@lem6894626 _92033 _92032) (@lem6894677 _92032 _92033)). Qed.
Lemma lem6894680 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6894681 (_92032 : int) (_92033 : int) : (term791 _92033 _92032) = (term804 _92032 _92033).
Proof. exact (MK_COMB (@lem6894680) (@lem6894679 _92032 _92033)). Qed.
Lemma lem6894682 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6894683 (_92032 : int) (_92033 : int) : (term787 _92033 _92032) = (term805 _92032 _92033).
Proof. exact (MK_COMB (@lem6894681 _92032 _92033) (@lem6894682)). Qed.
Lemma lem6894684 (_92032 : int) (_92033 : int) : (term763 _92032 _92033) = (term805 _92032 _92033).
Proof. exact (TRANS (@lem6894614 _92033 _92032) (@lem6894683 _92032 _92033)). Qed.
Lemma lem6894685 (_92032 : int) (_92033 : int) : (term763 _92033 _92032) = (term787 _92032 _92033).
Proof. exact (@lem1988287 (real_of_int _92032) (term45 _92033)). Qed.
Lemma lem6894697 (_92032 : int) (_92033 : int) : (term788 _92032 _92033) = (term789 _92032 _92033).
Proof. exact (@lem1982792 (real_of_int _92032) (term45 _92033)). Qed.
Lemma lem6894698 (_92033 : int) : (term84 _92033) = (term85 _92033).
Proof. exact (@lem1982781 (real_of_int _92033) term60 term43). Qed.
Lemma lem6894700 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6894701 : term43 = term86.
Proof. exact (@lem6894700 term8). Qed.
Lemma lem6894703 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6894704 : term60 = term61.
Proof. exact (@lem6894703 term8). Qed.
Lemma lem6894705 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6894706 : term62 = term63.
Proof. exact (MK_COMB (@lem6894705) (@lem6894704)). Qed.
Lemma lem6894707 : term87 = term88.
Proof. exact (MK_COMB (@lem6894706) (@lem6894701)). Qed.
Lemma lem6894708 : term88 = term89.
Proof. exact (@lem1981613 term60 term43 term43 term43). Qed.
Lemma lem6894710 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6894711 : term69 = term70.
Proof. exact (@lem6894710 term8 term8). Qed.
Lemma lem6894712 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6894713 : term72 = term8.
Proof. exact (EQ_MP (@lem6894712) (@lem940073)). Qed.
Lemma lem6894714 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6894715 : term70 = term43.
Proof. exact (MK_COMB (@lem6894714) (@lem6894713)). Qed.
Lemma lem6894716 : term69 = term43.
Proof. exact (TRANS (@lem6894711) (@lem6894715)). Qed.
Lemma lem6894718 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6894719 : term87 = term92.
Proof. exact (@lem6894718 term8 term8). Qed.
Lemma lem6894720 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6894721 : term72 = term8.
Proof. exact (EQ_MP (@lem6894720) (@lem940073)). Qed.
Lemma lem6894722 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6894723 : term70 = term43.
Proof. exact (MK_COMB (@lem6894722) (@lem6894721)). Qed.
Lemma lem6894724 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6894725 : term92 = term60.
Proof. exact (MK_COMB (@lem6894724) (@lem6894723)). Qed.
Lemma lem6894726 : term87 = term60.
Proof. exact (TRANS (@lem6894719) (@lem6894725)). Qed.
Lemma lem6894727 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6894728 : term93 = term94.
Proof. exact (MK_COMB (@lem6894727) (@lem6894726)). Qed.
Lemma lem6894729 : term89 = term61.
Proof. exact (MK_COMB (@lem6894728) (@lem6894716)). Qed.
Lemma lem6894730 : term88 = term61.
Proof. exact (TRANS (@lem6894708) (@lem6894729)). Qed.
Lemma lem6894731 : term87 = term61.
Proof. exact (TRANS (@lem6894707) (@lem6894730)). Qed.
Lemma lem6894733 (x : real) : (term76 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6894734 : term61 = term60.
Proof. exact (@lem6894733 term60). Qed.
Lemma lem6894735 : term87 = term60.
Proof. exact (TRANS (@lem6894731) (@lem6894734)). Qed.
Lemma lem6894738 (_92033 : int) : (term95 _92033) = (term95 _92033).
Proof. exact (eq_refl (term95 _92033)). Qed.
Lemma lem6894739 (_92033 : int) : (term85 _92033) = (term96 _92033).
Proof. exact (MK_COMB (@lem6894738 _92033) (@lem6894735)). Qed.
Lemma lem6894740 (_92033 : int) : (term84 _92033) = (term96 _92033).
Proof. exact (TRANS (@lem6894698 _92033) (@lem6894739 _92033)). Qed.
Lemma lem6894741 (_92032 : int) : (term44 _92032) = (term44 _92032).
Proof. exact (eq_refl (term44 _92032)). Qed.
Lemma lem6894744 (_92032 : int) (_92033 : int) : (term789 _92032 _92033) = (term790 _92032 _92033).
Proof. exact (MK_COMB (@lem6894741 _92032) (@lem6894740 _92033)). Qed.
Lemma lem6894746 (_92032 : int) (_92033 : int) : (term788 _92032 _92033) = (term790 _92032 _92033).
Proof. exact (TRANS (@lem6894697 _92032 _92033) (@lem6894744 _92032 _92033)). Qed.
Lemma lem6894747 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6894748 (_92032 : int) (_92033 : int) : (term791 _92032 _92033) = (term792 _92032 _92033).
Proof. exact (MK_COMB (@lem6894747) (@lem6894746 _92032 _92033)). Qed.
Lemma lem6894749 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6894750 (_92032 : int) (_92033 : int) : (term787 _92032 _92033) = (term793 _92032 _92033).
Proof. exact (MK_COMB (@lem6894748 _92032 _92033) (@lem6894749)). Qed.
Lemma lem6894751 (_92032 : int) (_92033 : int) : (term763 _92033 _92032) = (term793 _92032 _92033).
Proof. exact (TRANS (@lem6894685 _92032 _92033) (@lem6894750 _92032 _92033)). Qed.
Lemma lem6894752 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6894753 (_92032 : int) (_92033 : int) : (term768 _92032 _92033) = (term817 _92032 _92033).
Proof. exact (MK_COMB (@lem6894752) (@lem6894684 _92032 _92033)). Qed.
Lemma lem6894754 (_92032 : int) (_92033 : int) : (term769 _92033 _92032) = (term818 _92032 _92033).
Proof. exact (MK_COMB (@lem6894753 _92032 _92033) (@lem6894751 _92032 _92033)). Qed.
Lemma lem6894755 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6894756 {A : Type'} (_92033 : int) (_92032 : int) (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) : (term779 A _92033 _92032 _92034 f j dom neut) = (term819 A _92033 _92032 _92034 f j dom neut).
Proof. exact (MK_COMB (@lem6894755) (@lem6894613 A _92033 _92032 _92034 f j dom neut)). Qed.
Lemma lem6894757 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term780 A _92034 f j dom neut _92033 _92032) = (term820 A _92034 f j dom neut _92032 _92033).
Proof. exact (MK_COMB (@lem6894756 A _92033 _92032 _92034 f j dom neut) (@lem6894754 _92032 _92033)). Qed.
Lemma lem6894758 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6894759 (_92034 : int) (_92032 : int) (_92033 : int) : (term781 _92034 _92033 _92032) = (term821 _92034 _92032 _92033).
Proof. exact (MK_COMB (@lem6894758) (@lem6894498 _92034 _92032 _92033)). Qed.
Lemma lem6894760 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term782 A _92034 f j dom neut _92033 _92032) = (term822 A _92034 f j dom neut _92032 _92033).
Proof. exact (MK_COMB (@lem6894759 _92034 _92032 _92033) (@lem6894757 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6894761 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6894762 (_92034 : int) : (term49 _92034) = (term131 _92034).
Proof. exact (MK_COMB (@lem6894761) (@lem6894121 _92034)). Qed.
Lemma lem6894763 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term783 A _92034 f j dom neut _92033 _92032) = (term823 A _92034 f j dom neut _92032 _92033).
Proof. exact (MK_COMB (@lem6894762 _92034) (@lem6894760 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6894764 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6894765 (_92033 : int) : (term49 _92033) = (term131 _92033).
Proof. exact (MK_COMB (@lem6894764) (@lem6894073 _92033)). Qed.
Lemma lem6894766 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term784 A _92034 f j dom neut _92033 _92032) = (term824 A _92034 f j dom neut _92032 _92033).
Proof. exact (MK_COMB (@lem6894765 _92033) (@lem6894763 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6894767 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6894768 (_92032 : int) : (term49 _92032) = (term131 _92032).
Proof. exact (MK_COMB (@lem6894767) (@lem6894025 _92032)). Qed.
Lemma lem6894769 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term785 A _92034 f j dom neut _92033 _92032) = (term825 A _92034 f j dom neut _92032 _92033).
Proof. exact (MK_COMB (@lem6894768 _92032) (@lem6894766 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6894776 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term786 A _92034 f j dom neut _92033 _92032) = (term825 A _92034 f j dom neut _92032 _92033).
Proof. exact (TRANS (@lem6893977 A _92034 f j dom neut _92033 _92032) (@lem6894769 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6894811 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term820 A _92034 f j dom neut _92032 _92033) = (term826 A _92034 f j dom neut _92032 _92033).
Proof. exact (@lem19158 (term805 _92032 _92033) (term816 A _92033 _92032 _92034 f j dom neut) (term793 _92032 _92033)). Qed.
Lemma lem6894834 (_92032 : int) (_92033 : int) : (term811 _92032 _92033) = (term827 _92032 _92033).
Proof. exact (@lem19367 (term793 _92032 _92033) (term805 _92032 _92033) (term809 _92032 _92033)). Qed.
Lemma lem6894843 (_92033 : int) (_92032 : int) (_92034 : int) : (term812 _92033 _92032 _92034) = (term812 _92033 _92032 _92034).
Proof. exact (eq_refl (term812 _92033 _92032 _92034)). Qed.
Lemma lem6894844 (_92034 : int) (_92032 : int) (_92033 : int) : (term813 _92034 _92032 _92033) = (term828 _92034 _92032 _92033).
Proof. exact (MK_COMB (@lem6894843 _92033 _92032 _92034) (@lem6894834 _92032 _92033)). Qed.
Lemma lem6894851 (_92034 : int) (_92032 : int) (_92033 : int) : (term828 _92034 _92032 _92033) = (term829 _92034 _92032 _92033).
Proof. exact (@lem19158 (term830 _92032 _92033) (term802 _92033 _92032 _92034) (term831 _92032 _92033)). Qed.
Lemma lem6894852 (_92034 : int) (_92032 : int) (_92033 : int) : (term813 _92034 _92032 _92033) = (term829 _92034 _92032 _92033).
Proof. exact (TRANS (@lem6894844 _92034 _92032 _92033) (@lem6894851 _92034 _92032 _92033)). Qed.
Lemma lem6894853 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6894854 (_92034 : int) (_92032 : int) (_92033 : int) : (term821 _92034 _92032 _92033) = (term832 _92034 _92032 _92033).
Proof. exact (MK_COMB (@lem6894853) (@lem6894852 _92034 _92032 _92033)). Qed.
Lemma lem6894855 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term822 A _92034 f j dom neut _92032 _92033) = (term833 A _92034 f j dom neut _92032 _92033).
Proof. exact (MK_COMB (@lem6894854 _92034 _92032 _92033) (@lem6894811 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6894858 (_92034 : int) : (term131 _92034) = (term131 _92034).
Proof. exact (eq_refl (term131 _92034)). Qed.
Lemma lem6894859 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term823 A _92034 f j dom neut _92032 _92033) = (term834 A _92034 f j dom neut _92032 _92033).
Proof. exact (MK_COMB (@lem6894858 _92034) (@lem6894855 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6894860 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term834 A _92034 f j dom neut _92032 _92033) = (term835 A _92034 f j dom neut _92032 _92033).
Proof. exact (@lem19158 (term829 _92034 _92032 _92033) (term80 _92034) (term826 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6894867 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term836 A _92034 f j dom neut _92032 _92033) = (term837 A _92034 f j dom neut _92032 _92033).
Proof. exact (@lem19158 (term838 A _92034 f j dom neut _92032 _92033) (term80 _92034) (term839 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6894874 (_92034 : int) (_92032 : int) (_92033 : int) : (term840 _92034 _92032 _92033) = (term841 _92034 _92032 _92033).
Proof. exact (@lem19158 (term842 _92034 _92032 _92033) (term80 _92034) (term843 _92034 _92032 _92033)). Qed.
Lemma lem6894875 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6894876 (_92034 : int) (_92032 : int) (_92033 : int) : (term844 _92034 _92032 _92033) = (term845 _92034 _92032 _92033).
Proof. exact (MK_COMB (@lem6894875) (@lem6894874 _92034 _92032 _92033)). Qed.
Lemma lem6894877 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term835 A _92034 f j dom neut _92032 _92033) = (term846 A _92034 f j dom neut _92032 _92033).
Proof. exact (MK_COMB (@lem6894876 _92034 _92032 _92033) (@lem6894867 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6894878 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term834 A _92034 f j dom neut _92032 _92033) = (term846 A _92034 f j dom neut _92032 _92033).
Proof. exact (TRANS (@lem6894860 A _92034 f j dom neut _92032 _92033) (@lem6894877 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6894879 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term823 A _92034 f j dom neut _92032 _92033) = (term846 A _92034 f j dom neut _92032 _92033).
Proof. exact (TRANS (@lem6894859 A _92034 f j dom neut _92032 _92033) (@lem6894878 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6894882 (_92033 : int) : (term131 _92033) = (term131 _92033).
Proof. exact (eq_refl (term131 _92033)). Qed.
Lemma lem6894883 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term824 A _92034 f j dom neut _92032 _92033) = (term847 A _92034 f j dom neut _92032 _92033).
Proof. exact (MK_COMB (@lem6894882 _92033) (@lem6894879 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6894884 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term847 A _92034 f j dom neut _92032 _92033) = (term848 A _92034 f j dom neut _92032 _92033).
Proof. exact (@lem19158 (term841 _92034 _92032 _92033) (term80 _92033) (term837 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6894891 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term849 A _92034 f j dom neut _92032 _92033) = (term850 A _92034 f j dom neut _92032 _92033).
Proof. exact (@lem19158 (term851 A _92034 f j dom neut _92032 _92033) (term80 _92033) (term852 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6894898 (_92034 : int) (_92032 : int) (_92033 : int) : (term853 _92034 _92032 _92033) = (term854 _92034 _92032 _92033).
Proof. exact (@lem19158 (term855 _92034 _92032 _92033) (term80 _92033) (term856 _92034 _92032 _92033)). Qed.
Lemma lem6894899 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6894900 (_92034 : int) (_92032 : int) (_92033 : int) : (term857 _92034 _92032 _92033) = (term858 _92034 _92032 _92033).
Proof. exact (MK_COMB (@lem6894899) (@lem6894898 _92034 _92032 _92033)). Qed.
Lemma lem6894901 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term848 A _92034 f j dom neut _92032 _92033) = (term859 A _92034 f j dom neut _92032 _92033).
Proof. exact (MK_COMB (@lem6894900 _92034 _92032 _92033) (@lem6894891 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6894902 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term847 A _92034 f j dom neut _92032 _92033) = (term859 A _92034 f j dom neut _92032 _92033).
Proof. exact (TRANS (@lem6894884 A _92034 f j dom neut _92032 _92033) (@lem6894901 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6894903 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term824 A _92034 f j dom neut _92032 _92033) = (term859 A _92034 f j dom neut _92032 _92033).
Proof. exact (TRANS (@lem6894883 A _92034 f j dom neut _92032 _92033) (@lem6894902 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6894906 (_92032 : int) : (term131 _92032) = (term131 _92032).
Proof. exact (eq_refl (term131 _92032)). Qed.
Lemma lem6894907 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term825 A _92034 f j dom neut _92032 _92033) = (term860 A _92034 f j dom neut _92032 _92033).
Proof. exact (MK_COMB (@lem6894906 _92032) (@lem6894903 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6894908 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term860 A _92034 f j dom neut _92032 _92033) = (term861 A _92034 f j dom neut _92032 _92033).
Proof. exact (@lem19158 (term854 _92034 _92032 _92033) (term80 _92032) (term850 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6894915 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term862 A _92034 f j dom neut _92032 _92033) = (term863 A _92034 f j dom neut _92032 _92033).
Proof. exact (@lem19158 (term864 A _92034 f j dom neut _92032 _92033) (term80 _92032) (term865 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6894922 (_92034 : int) (_92032 : int) (_92033 : int) : (term866 _92034 _92032 _92033) = (term867 _92034 _92032 _92033).
Proof. exact (@lem19158 (term868 _92034 _92032 _92033) (term80 _92032) (term869 _92034 _92032 _92033)). Qed.
Lemma lem6894923 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6894924 (_92034 : int) (_92032 : int) (_92033 : int) : (term870 _92034 _92032 _92033) = (term871 _92034 _92032 _92033).
Proof. exact (MK_COMB (@lem6894923) (@lem6894922 _92034 _92032 _92033)). Qed.
Lemma lem6894925 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term861 A _92034 f j dom neut _92032 _92033) = (term872 A _92034 f j dom neut _92032 _92033).
Proof. exact (MK_COMB (@lem6894924 _92034 _92032 _92033) (@lem6894915 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6894926 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term860 A _92034 f j dom neut _92032 _92033) = (term872 A _92034 f j dom neut _92032 _92033).
Proof. exact (TRANS (@lem6894908 A _92034 f j dom neut _92032 _92033) (@lem6894925 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6894927 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term825 A _92034 f j dom neut _92032 _92033) = (term872 A _92034 f j dom neut _92032 _92033).
Proof. exact (TRANS (@lem6894907 A _92034 f j dom neut _92032 _92033) (@lem6894926 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6894928 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term786 A _92034 f j dom neut _92033 _92032) = (term872 A _92034 f j dom neut _92032 _92033).
Proof. exact (TRANS (@lem6894776 A _92034 f j dom neut _92032 _92033) (@lem6894927 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6894950 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term872 A _92034 f j dom neut _92032 _92033) : term872 A _92034 f j dom neut _92032 _92033.
Proof. exact (h1). Qed.
Lemma lem6894951 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term867 _92034 _92032 _92033) : term867 _92034 _92032 _92033.
Proof. exact (h1). Qed.
Lemma lem6894952 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term873 _92034 _92032 _92033) : term873 _92034 _92032 _92033.
Proof. exact (h1). Qed.
Lemma lem6894953 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term873 _92034 _92032 _92033) : term868 _92034 _92032 _92033.
Proof. exact (proj2 (@lem6894952 _92034 _92032 _92033 h1)). Qed.
Lemma lem6894955 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term873 _92034 _92032 _92033) : term855 _92034 _92032 _92033.
Proof. exact (proj2 (@lem6894953 _92034 _92032 _92033 h1)). Qed.
Lemma lem6894957 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term873 _92034 _92032 _92033) : term842 _92034 _92032 _92033.
Proof. exact (proj2 (@lem6894955 _92034 _92032 _92033 h1)). Qed.
Lemma lem6894959 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term873 _92034 _92032 _92033) : term830 _92032 _92033.
Proof. exact (proj2 (@lem6894957 _92034 _92032 _92033 h1)). Qed.
Lemma lem6894963 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term873 _92034 _92032 _92033) : term809 _92032 _92033.
Proof. exact (proj2 (@lem6894959 _92034 _92032 _92033 h1)). Qed.
Lemma lem6894965 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term873 _92034 _92032 _92033) : term793 _92032 _92033.
Proof. exact (proj2 (@lem6894963 _92034 _92032 _92033 h1)). Qed.
Lemma lem6894966 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term873 _92034 _92032 _92033) : term805 _92032 _92033.
Proof. exact (proj1 (@lem6894963 _92034 _92032 _92033 h1)). Qed.
Lemma lem6894968 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6894969 : term874 = term108.
Proof. exact (@lem6894968 term31 term43). Qed.
Lemma lem6894971 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6894972 : term43 = term86.
Proof. exact (@lem6894971 term8). Qed.
Lemma lem6894974 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6894975 : term31 = term57.
Proof. exact (@lem6894974 (NUMERAL 0)). Qed.
Lemma lem6894976 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6894977 : term875 = term876.
Proof. exact (MK_COMB (@lem6894976) (@lem6894975)). Qed.
Lemma lem6894978 : term108 = term877.
Proof. exact (MK_COMB (@lem6894977) (@lem6894972)). Qed.
Lemma lem6894979 : term878.
Proof. exact (@lem1980255 term31 term43 term43 term43). Qed.
Lemma lem6894981 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6894982 : term108 = term109.
Proof. exact (@lem6894981 (NUMERAL 0) term8). Qed.
Lemma lem6894983 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6894984 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6894985 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6894984 h1) (fun h1 : term109 = True => @lem6894983)). Qed.
Lemma lem6894986 : term109 = True.
Proof. exact (EQ_MP (@lem6894985) (@lem6894983)). Qed.
Lemma lem6894987 : term108 = True.
Proof. exact (TRANS (@lem6894982) (@lem6894986)). Qed.
Lemma lem6894988 : True = term108.
Proof. exact (SYM (@lem6894987)). Qed.
Lemma lem6894989 : term108.
Proof. exact (EQ_MP (@lem6894988) (@lem0)). Qed.
Lemma lem6894990 : term879.
Proof. exact (@lem6894979 (@lem6894989)). Qed.
Lemma lem6894992 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6894993 : term108 = term109.
Proof. exact (@lem6894992 (NUMERAL 0) term8). Qed.
Lemma lem6894994 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6894995 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6894996 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6894995 h1) (fun h1 : term109 = True => @lem6894994)). Qed.
Lemma lem6894997 : term109 = True.
Proof. exact (EQ_MP (@lem6894996) (@lem6894994)). Qed.
Lemma lem6894998 : term108 = True.
Proof. exact (TRANS (@lem6894993) (@lem6894997)). Qed.
Lemma lem6894999 : True = term108.
Proof. exact (SYM (@lem6894998)). Qed.
Lemma lem6895000 : term108.
Proof. exact (EQ_MP (@lem6894999) (@lem0)). Qed.
Lemma lem6895001 : term877 = term880.
Proof. exact (@lem6894990 (@lem6895000)). Qed.
Lemma lem6895003 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6895004 : term69 = term70.
Proof. exact (@lem6895003 term8 term8). Qed.
Lemma lem6895005 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6895006 : term72 = term8.
Proof. exact (EQ_MP (@lem6895005) (@lem940073)). Qed.
Lemma lem6895007 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6895008 : term70 = term43.
Proof. exact (MK_COMB (@lem6895007) (@lem6895006)). Qed.
Lemma lem6895009 : term69 = term43.
Proof. exact (TRANS (@lem6895004) (@lem6895008)). Qed.
Lemma lem6895011 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6895012 : term120 = term31.
Proof. exact (@lem6895011 term8). Qed.
Lemma lem6895013 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6895014 : term881 = term875.
Proof. exact (MK_COMB (@lem6895013) (@lem6895012)). Qed.
Lemma lem6895015 : term880 = term108.
Proof. exact (MK_COMB (@lem6895014) (@lem6895009)). Qed.
Lemma lem6895017 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895018 : term108 = term109.
Proof. exact (@lem6895017 (NUMERAL 0) term8). Qed.
Lemma lem6895019 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895020 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895021 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895020 h1) (fun h1 : term109 = True => @lem6895019)). Qed.
Lemma lem6895022 : term109 = True.
Proof. exact (EQ_MP (@lem6895021) (@lem6895019)). Qed.
Lemma lem6895023 : term108 = True.
Proof. exact (TRANS (@lem6895018) (@lem6895022)). Qed.
Lemma lem6895024 : term880 = True.
Proof. exact (TRANS (@lem6895015) (@lem6895023)). Qed.
Lemma lem6895025 : term877 = True.
Proof. exact (TRANS (@lem6895001) (@lem6895024)). Qed.
Lemma lem6895026 : term108 = True.
Proof. exact (TRANS (@lem6894978) (@lem6895025)). Qed.
Lemma lem6895027 : term874 = True.
Proof. exact (TRANS (@lem6894969) (@lem6895026)). Qed.
Lemma lem6895028 : True = term874.
Proof. exact (SYM (@lem6895027)). Qed.
Lemma lem6895029 : term874.
Proof. exact (EQ_MP (@lem6895028) (@lem0)). Qed.
Lemma lem6895030 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term873 _92034 _92032 _92033) : term882 _92032 _92033.
Proof. exact (conj (@lem6895029) (@lem6894965 _92034 _92032 _92033 h1)). Qed.
Lemma lem6895032 (x : real) (y : real) : term883 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6895033 (_92032 : int) (_92033 : int) : term884 _92032 _92033.
Proof. exact (@lem6895032 term43 (term790 _92032 _92033)). Qed.
Lemma lem6895034 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term873 _92034 _92032 _92033) : term885 _92032 _92033.
Proof. exact (@lem6895033 _92032 _92033 (@lem6895030 _92034 _92032 _92033 h1)). Qed.
Lemma lem6895035 (_92032 : int) (_92033 : int) : (term886 _92032 _92033) = (term790 _92032 _92033).
Proof. exact (@lem1982733 (term790 _92032 _92033)). Qed.
Lemma lem6895036 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6895037 (_92032 : int) (_92033 : int) : (term887 _92032 _92033) = (term792 _92032 _92033).
Proof. exact (MK_COMB (@lem6895036) (@lem6895035 _92032 _92033)). Qed.
Lemma lem6895038 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6895039 (_92032 : int) (_92033 : int) : (term885 _92032 _92033) = (term793 _92032 _92033).
Proof. exact (MK_COMB (@lem6895037 _92032 _92033) (@lem6895038)). Qed.
Lemma lem6895040 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term873 _92034 _92032 _92033) : term793 _92032 _92033.
Proof. exact (EQ_MP (@lem6895039 _92032 _92033) (@lem6895034 _92034 _92032 _92033 h1)). Qed.
Lemma lem6895042 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6895043 : term874 = term108.
Proof. exact (@lem6895042 term31 term43). Qed.
Lemma lem6895045 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6895046 : term43 = term86.
Proof. exact (@lem6895045 term8). Qed.
Lemma lem6895048 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6895049 : term31 = term57.
Proof. exact (@lem6895048 (NUMERAL 0)). Qed.
Lemma lem6895050 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6895051 : term875 = term876.
Proof. exact (MK_COMB (@lem6895050) (@lem6895049)). Qed.
Lemma lem6895052 : term108 = term877.
Proof. exact (MK_COMB (@lem6895051) (@lem6895046)). Qed.
Lemma lem6895053 : term878.
Proof. exact (@lem1980255 term31 term43 term43 term43). Qed.
Lemma lem6895055 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895056 : term108 = term109.
Proof. exact (@lem6895055 (NUMERAL 0) term8). Qed.
Lemma lem6895057 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895058 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895059 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895058 h1) (fun h1 : term109 = True => @lem6895057)). Qed.
Lemma lem6895060 : term109 = True.
Proof. exact (EQ_MP (@lem6895059) (@lem6895057)). Qed.
Lemma lem6895061 : term108 = True.
Proof. exact (TRANS (@lem6895056) (@lem6895060)). Qed.
Lemma lem6895062 : True = term108.
Proof. exact (SYM (@lem6895061)). Qed.
Lemma lem6895063 : term108.
Proof. exact (EQ_MP (@lem6895062) (@lem0)). Qed.
Lemma lem6895064 : term879.
Proof. exact (@lem6895053 (@lem6895063)). Qed.
Lemma lem6895066 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895067 : term108 = term109.
Proof. exact (@lem6895066 (NUMERAL 0) term8). Qed.
Lemma lem6895068 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895069 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895070 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895069 h1) (fun h1 : term109 = True => @lem6895068)). Qed.
Lemma lem6895071 : term109 = True.
Proof. exact (EQ_MP (@lem6895070) (@lem6895068)). Qed.
Lemma lem6895072 : term108 = True.
Proof. exact (TRANS (@lem6895067) (@lem6895071)). Qed.
Lemma lem6895073 : True = term108.
Proof. exact (SYM (@lem6895072)). Qed.
Lemma lem6895074 : term108.
Proof. exact (EQ_MP (@lem6895073) (@lem0)). Qed.
Lemma lem6895075 : term877 = term880.
Proof. exact (@lem6895064 (@lem6895074)). Qed.
Lemma lem6895077 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6895078 : term69 = term70.
Proof. exact (@lem6895077 term8 term8). Qed.
Lemma lem6895079 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6895080 : term72 = term8.
Proof. exact (EQ_MP (@lem6895079) (@lem940073)). Qed.
Lemma lem6895081 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6895082 : term70 = term43.
Proof. exact (MK_COMB (@lem6895081) (@lem6895080)). Qed.
Lemma lem6895083 : term69 = term43.
Proof. exact (TRANS (@lem6895078) (@lem6895082)). Qed.
Lemma lem6895085 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6895086 : term120 = term31.
Proof. exact (@lem6895085 term8). Qed.
Lemma lem6895087 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6895088 : term881 = term875.
Proof. exact (MK_COMB (@lem6895087) (@lem6895086)). Qed.
Lemma lem6895089 : term880 = term108.
Proof. exact (MK_COMB (@lem6895088) (@lem6895083)). Qed.
Lemma lem6895091 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895092 : term108 = term109.
Proof. exact (@lem6895091 (NUMERAL 0) term8). Qed.
Lemma lem6895093 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895094 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895095 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895094 h1) (fun h1 : term109 = True => @lem6895093)). Qed.
Lemma lem6895096 : term109 = True.
Proof. exact (EQ_MP (@lem6895095) (@lem6895093)). Qed.
Lemma lem6895097 : term108 = True.
Proof. exact (TRANS (@lem6895092) (@lem6895096)). Qed.
Lemma lem6895098 : term880 = True.
Proof. exact (TRANS (@lem6895089) (@lem6895097)). Qed.
Lemma lem6895099 : term877 = True.
Proof. exact (TRANS (@lem6895075) (@lem6895098)). Qed.
Lemma lem6895100 : term108 = True.
Proof. exact (TRANS (@lem6895052) (@lem6895099)). Qed.
Lemma lem6895101 : term874 = True.
Proof. exact (TRANS (@lem6895043) (@lem6895100)). Qed.
Lemma lem6895102 : True = term874.
Proof. exact (SYM (@lem6895101)). Qed.
Lemma lem6895103 : term874.
Proof. exact (EQ_MP (@lem6895102) (@lem0)). Qed.
Lemma lem6895104 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term873 _92034 _92032 _92033) : term888 _92032 _92033.
Proof. exact (conj (@lem6895103) (@lem6894966 _92034 _92032 _92033 h1)). Qed.
Lemma lem6895106 (x : real) (y : real) : term883 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6895107 (_92032 : int) (_92033 : int) : term889 _92032 _92033.
Proof. exact (@lem6895106 term43 (term803 _92032 _92033)). Qed.
Lemma lem6895108 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term873 _92034 _92032 _92033) : term890 _92032 _92033.
Proof. exact (@lem6895107 _92032 _92033 (@lem6895104 _92034 _92032 _92033 h1)). Qed.
Lemma lem6895109 (_92032 : int) (_92033 : int) : (term891 _92032 _92033) = (term803 _92032 _92033).
Proof. exact (@lem1982733 (term803 _92032 _92033)). Qed.
Lemma lem6895110 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6895111 (_92032 : int) (_92033 : int) : (term892 _92032 _92033) = (term804 _92032 _92033).
Proof. exact (MK_COMB (@lem6895110) (@lem6895109 _92032 _92033)). Qed.
Lemma lem6895112 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6895113 (_92032 : int) (_92033 : int) : (term890 _92032 _92033) = (term805 _92032 _92033).
Proof. exact (MK_COMB (@lem6895111 _92032 _92033) (@lem6895112)). Qed.
Lemma lem6895114 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term873 _92034 _92032 _92033) : term805 _92032 _92033.
Proof. exact (EQ_MP (@lem6895113 _92032 _92033) (@lem6895108 _92034 _92032 _92033 h1)). Qed.
Lemma lem6895115 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term873 _92034 _92032 _92033) : term809 _92032 _92033.
Proof. exact (conj (@lem6895114 _92034 _92032 _92033 h1) (@lem6895040 _92034 _92032 _92033 h1)). Qed.
Lemma lem6895117 (x : real) (y : real) : term893 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem6895118 (_92032 : int) (_92033 : int) : term894 _92032 _92033.
Proof. exact (@lem6895117 (term803 _92032 _92033) (term790 _92032 _92033)). Qed.
Lemma lem6895119 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term873 _92034 _92032 _92033) : term895 _92032 _92033.
Proof. exact (@lem6895118 _92032 _92033 (@lem6895115 _92034 _92032 _92033 h1)). Qed.
Lemma lem6895120 (_92032 : int) (_92033 : int) : (term896 _92032 _92033) = (term897 _92032 _92033).
Proof. exact (@lem1982753 (term99 _92032) (real_of_int _92032) (term898 _92033) (term96 _92033)). Qed.
Lemma lem6895121 (_92032 : int) : (term899 _92032) = (term101 _92032).
Proof. exact (@lem1982713 term60 (real_of_int _92032)). Qed.
Lemma lem6895123 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6895124 : term43 = term86.
Proof. exact (@lem6895123 term8). Qed.
Lemma lem6895126 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6895127 : term60 = term61.
Proof. exact (@lem6895126 term8). Qed.
Lemma lem6895128 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6895129 : term102 = term103.
Proof. exact (MK_COMB (@lem6895128) (@lem6895127)). Qed.
Lemma lem6895130 : term104 = term105.
Proof. exact (MK_COMB (@lem6895129) (@lem6895124)). Qed.
Lemma lem6895131 : term106.
Proof. exact (@lem1981473 term60 term43 term43 term43 term31 term43). Qed.
Lemma lem6895133 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895134 : term108 = term109.
Proof. exact (@lem6895133 (NUMERAL 0) term8). Qed.
Lemma lem6895135 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895136 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895137 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895136 h1) (fun h1 : term109 = True => @lem6895135)). Qed.
Lemma lem6895138 : term109 = True.
Proof. exact (EQ_MP (@lem6895137) (@lem6895135)). Qed.
Lemma lem6895139 : term108 = True.
Proof. exact (TRANS (@lem6895134) (@lem6895138)). Qed.
Lemma lem6895140 : True = term108.
Proof. exact (SYM (@lem6895139)). Qed.
Lemma lem6895141 : term108.
Proof. exact (EQ_MP (@lem6895140) (@lem0)). Qed.
Lemma lem6895142 : term111.
Proof. exact (@lem6895131 (@lem6895141)). Qed.
Lemma lem6895144 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895145 : term108 = term109.
Proof. exact (@lem6895144 (NUMERAL 0) term8). Qed.
Lemma lem6895146 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895147 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895148 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895147 h1) (fun h1 : term109 = True => @lem6895146)). Qed.
Lemma lem6895149 : term109 = True.
Proof. exact (EQ_MP (@lem6895148) (@lem6895146)). Qed.
Lemma lem6895150 : term108 = True.
Proof. exact (TRANS (@lem6895145) (@lem6895149)). Qed.
Lemma lem6895151 : True = term108.
Proof. exact (SYM (@lem6895150)). Qed.
Lemma lem6895152 : term108.
Proof. exact (EQ_MP (@lem6895151) (@lem0)). Qed.
Lemma lem6895153 : term112.
Proof. exact (@lem6895142 (@lem6895152)). Qed.
Lemma lem6895155 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895156 : term108 = term109.
Proof. exact (@lem6895155 (NUMERAL 0) term8). Qed.
Lemma lem6895157 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895158 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895159 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895158 h1) (fun h1 : term109 = True => @lem6895157)). Qed.
Lemma lem6895160 : term109 = True.
Proof. exact (EQ_MP (@lem6895159) (@lem6895157)). Qed.
Lemma lem6895161 : term108 = True.
Proof. exact (TRANS (@lem6895156) (@lem6895160)). Qed.
Lemma lem6895162 : True = term108.
Proof. exact (SYM (@lem6895161)). Qed.
Lemma lem6895163 : term108.
Proof. exact (EQ_MP (@lem6895162) (@lem0)). Qed.
Lemma lem6895164 : term113.
Proof. exact (@lem6895153 (@lem6895163)). Qed.
Lemma lem6895166 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6895167 : term69 = term70.
Proof. exact (@lem6895166 term8 term8). Qed.
Lemma lem6895168 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6895169 : term72 = term8.
Proof. exact (EQ_MP (@lem6895168) (@lem940073)). Qed.
Lemma lem6895170 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6895171 : term70 = term43.
Proof. exact (MK_COMB (@lem6895170) (@lem6895169)). Qed.
Lemma lem6895172 : term69 = term43.
Proof. exact (TRANS (@lem6895167) (@lem6895171)). Qed.
Lemma lem6895174 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6895175 : term87 = term92.
Proof. exact (@lem6895174 term8 term8). Qed.
Lemma lem6895176 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6895177 : term72 = term8.
Proof. exact (EQ_MP (@lem6895176) (@lem940073)). Qed.
Lemma lem6895178 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6895179 : term70 = term43.
Proof. exact (MK_COMB (@lem6895178) (@lem6895177)). Qed.
Lemma lem6895180 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6895181 : term92 = term60.
Proof. exact (MK_COMB (@lem6895180) (@lem6895179)). Qed.
Lemma lem6895182 : term87 = term60.
Proof. exact (TRANS (@lem6895175) (@lem6895181)). Qed.
Lemma lem6895183 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6895184 : term114 = term102.
Proof. exact (MK_COMB (@lem6895183) (@lem6895182)). Qed.
Lemma lem6895185 : term115 = term104.
Proof. exact (MK_COMB (@lem6895184) (@lem6895172)). Qed.
Lemma lem6895187 (m : nat) : (term116 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6895188 : term104 = term31.
Proof. exact (@lem6895187 term8). Qed.
Lemma lem6895189 : term115 = term31.
Proof. exact (TRANS (@lem6895185) (@lem6895188)). Qed.
Lemma lem6895190 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6895191 : term117 = term118.
Proof. exact (MK_COMB (@lem6895190) (@lem6895189)). Qed.
Lemma lem6895192 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem6895193 : term119 = term120.
Proof. exact (MK_COMB (@lem6895191) (@lem6895192)). Qed.
Lemma lem6895195 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6895196 : term120 = term31.
Proof. exact (@lem6895195 term8). Qed.
Lemma lem6895197 : term119 = term31.
Proof. exact (TRANS (@lem6895193) (@lem6895196)). Qed.
Lemma lem6895199 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6895200 : term69 = term70.
Proof. exact (@lem6895199 term8 term8). Qed.
Lemma lem6895201 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6895202 : term72 = term8.
Proof. exact (EQ_MP (@lem6895201) (@lem940073)). Qed.
Lemma lem6895203 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6895204 : term70 = term43.
Proof. exact (MK_COMB (@lem6895203) (@lem6895202)). Qed.
Lemma lem6895205 : term69 = term43.
Proof. exact (TRANS (@lem6895200) (@lem6895204)). Qed.
Lemma lem6895206 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem6895207 : term122 = term120.
Proof. exact (MK_COMB (@lem6895206) (@lem6895205)). Qed.
Lemma lem6895209 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6895210 : term120 = term31.
Proof. exact (@lem6895209 term8). Qed.
Lemma lem6895211 : term122 = term31.
Proof. exact (TRANS (@lem6895207) (@lem6895210)). Qed.
Lemma lem6895212 : term31 = term122.
Proof. exact (SYM (@lem6895211)). Qed.
Lemma lem6895213 : term119 = term122.
Proof. exact (TRANS (@lem6895197) (@lem6895212)). Qed.
Lemma lem6895214 : term105 = term57.
Proof. exact (@lem6895164 (@lem6895213)). Qed.
Lemma lem6895215 : term104 = term57.
Proof. exact (TRANS (@lem6895130) (@lem6895214)). Qed.
Lemma lem6895217 (x : real) : (term76 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6895218 : term57 = term31.
Proof. exact (@lem6895217 term31). Qed.
Lemma lem6895219 : term104 = term31.
Proof. exact (TRANS (@lem6895215) (@lem6895218)). Qed.
Lemma lem6895220 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6895221 : term123 = term118.
Proof. exact (MK_COMB (@lem6895220) (@lem6895219)). Qed.
Lemma lem6895222 (_92032 : int) : (real_of_int _92032) = (real_of_int _92032).
Proof. exact (eq_refl (real_of_int _92032)). Qed.
Lemma lem6895223 (_92032 : int) : (term101 _92032) = (term124 _92032).
Proof. exact (MK_COMB (@lem6895221) (@lem6895222 _92032)). Qed.
Lemma lem6895224 (_92032 : int) : (term899 _92032) = (term124 _92032).
Proof. exact (TRANS (@lem6895121 _92032) (@lem6895223 _92032)). Qed.
Lemma lem6895225 (_92032 : int) : (term124 _92032) = term31.
Proof. exact (@lem1982719 (real_of_int _92032)). Qed.
Lemma lem6895226 (_92032 : int) : (term899 _92032) = term31.
Proof. exact (TRANS (@lem6895224 _92032) (@lem6895225 _92032)). Qed.
Lemma lem6895227 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6895228 (_92032 : int) : (term900 _92032) = term126.
Proof. exact (MK_COMB (@lem6895227) (@lem6895226 _92032)). Qed.
Lemma lem6895229 (_92033 : int) : (term901 _92033) = (term902 _92033).
Proof. exact (@lem1982753 (real_of_int _92033) (term99 _92033) term60 term60). Qed.
Lemma lem6895230 (_92033 : int) : (term100 _92033) = (term101 _92033).
Proof. exact (@lem1982715 term60 (real_of_int _92033)). Qed.
Lemma lem6895232 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6895233 : term43 = term86.
Proof. exact (@lem6895232 term8). Qed.
Lemma lem6895235 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6895236 : term60 = term61.
Proof. exact (@lem6895235 term8). Qed.
Lemma lem6895237 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6895238 : term102 = term103.
Proof. exact (MK_COMB (@lem6895237) (@lem6895236)). Qed.
Lemma lem6895239 : term104 = term105.
Proof. exact (MK_COMB (@lem6895238) (@lem6895233)). Qed.
Lemma lem6895240 : term106.
Proof. exact (@lem1981473 term60 term43 term43 term43 term31 term43). Qed.
Lemma lem6895242 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895243 : term108 = term109.
Proof. exact (@lem6895242 (NUMERAL 0) term8). Qed.
Lemma lem6895244 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895245 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895246 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895245 h1) (fun h1 : term109 = True => @lem6895244)). Qed.
Lemma lem6895247 : term109 = True.
Proof. exact (EQ_MP (@lem6895246) (@lem6895244)). Qed.
Lemma lem6895248 : term108 = True.
Proof. exact (TRANS (@lem6895243) (@lem6895247)). Qed.
Lemma lem6895249 : True = term108.
Proof. exact (SYM (@lem6895248)). Qed.
Lemma lem6895250 : term108.
Proof. exact (EQ_MP (@lem6895249) (@lem0)). Qed.
Lemma lem6895251 : term111.
Proof. exact (@lem6895240 (@lem6895250)). Qed.
Lemma lem6895253 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895254 : term108 = term109.
Proof. exact (@lem6895253 (NUMERAL 0) term8). Qed.
Lemma lem6895255 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895256 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895257 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895256 h1) (fun h1 : term109 = True => @lem6895255)). Qed.
Lemma lem6895258 : term109 = True.
Proof. exact (EQ_MP (@lem6895257) (@lem6895255)). Qed.
Lemma lem6895259 : term108 = True.
Proof. exact (TRANS (@lem6895254) (@lem6895258)). Qed.
Lemma lem6895260 : True = term108.
Proof. exact (SYM (@lem6895259)). Qed.
Lemma lem6895261 : term108.
Proof. exact (EQ_MP (@lem6895260) (@lem0)). Qed.
Lemma lem6895262 : term112.
Proof. exact (@lem6895251 (@lem6895261)). Qed.
Lemma lem6895264 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895265 : term108 = term109.
Proof. exact (@lem6895264 (NUMERAL 0) term8). Qed.
Lemma lem6895266 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895267 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895268 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895267 h1) (fun h1 : term109 = True => @lem6895266)). Qed.
Lemma lem6895269 : term109 = True.
Proof. exact (EQ_MP (@lem6895268) (@lem6895266)). Qed.
Lemma lem6895270 : term108 = True.
Proof. exact (TRANS (@lem6895265) (@lem6895269)). Qed.
Lemma lem6895271 : True = term108.
Proof. exact (SYM (@lem6895270)). Qed.
Lemma lem6895272 : term108.
Proof. exact (EQ_MP (@lem6895271) (@lem0)). Qed.
Lemma lem6895273 : term113.
Proof. exact (@lem6895262 (@lem6895272)). Qed.
Lemma lem6895275 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6895276 : term69 = term70.
Proof. exact (@lem6895275 term8 term8). Qed.
Lemma lem6895277 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6895278 : term72 = term8.
Proof. exact (EQ_MP (@lem6895277) (@lem940073)). Qed.
Lemma lem6895279 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6895280 : term70 = term43.
Proof. exact (MK_COMB (@lem6895279) (@lem6895278)). Qed.
Lemma lem6895281 : term69 = term43.
Proof. exact (TRANS (@lem6895276) (@lem6895280)). Qed.
Lemma lem6895283 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6895284 : term87 = term92.
Proof. exact (@lem6895283 term8 term8). Qed.
Lemma lem6895285 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6895286 : term72 = term8.
Proof. exact (EQ_MP (@lem6895285) (@lem940073)). Qed.
Lemma lem6895287 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6895288 : term70 = term43.
Proof. exact (MK_COMB (@lem6895287) (@lem6895286)). Qed.
Lemma lem6895289 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6895290 : term92 = term60.
Proof. exact (MK_COMB (@lem6895289) (@lem6895288)). Qed.
Lemma lem6895291 : term87 = term60.
Proof. exact (TRANS (@lem6895284) (@lem6895290)). Qed.
Lemma lem6895292 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6895293 : term114 = term102.
Proof. exact (MK_COMB (@lem6895292) (@lem6895291)). Qed.
Lemma lem6895294 : term115 = term104.
Proof. exact (MK_COMB (@lem6895293) (@lem6895281)). Qed.
Lemma lem6895296 (m : nat) : (term116 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6895297 : term104 = term31.
Proof. exact (@lem6895296 term8). Qed.
Lemma lem6895298 : term115 = term31.
Proof. exact (TRANS (@lem6895294) (@lem6895297)). Qed.
Lemma lem6895299 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6895300 : term117 = term118.
Proof. exact (MK_COMB (@lem6895299) (@lem6895298)). Qed.
Lemma lem6895301 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem6895302 : term119 = term120.
Proof. exact (MK_COMB (@lem6895300) (@lem6895301)). Qed.
Lemma lem6895304 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6895305 : term120 = term31.
Proof. exact (@lem6895304 term8). Qed.
Lemma lem6895306 : term119 = term31.
Proof. exact (TRANS (@lem6895302) (@lem6895305)). Qed.
Lemma lem6895308 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6895309 : term69 = term70.
Proof. exact (@lem6895308 term8 term8). Qed.
Lemma lem6895310 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6895311 : term72 = term8.
Proof. exact (EQ_MP (@lem6895310) (@lem940073)). Qed.
Lemma lem6895312 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6895313 : term70 = term43.
Proof. exact (MK_COMB (@lem6895312) (@lem6895311)). Qed.
Lemma lem6895314 : term69 = term43.
Proof. exact (TRANS (@lem6895309) (@lem6895313)). Qed.
Lemma lem6895315 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem6895316 : term122 = term120.
Proof. exact (MK_COMB (@lem6895315) (@lem6895314)). Qed.
Lemma lem6895318 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6895319 : term120 = term31.
Proof. exact (@lem6895318 term8). Qed.
Lemma lem6895320 : term122 = term31.
Proof. exact (TRANS (@lem6895316) (@lem6895319)). Qed.
Lemma lem6895321 : term31 = term122.
Proof. exact (SYM (@lem6895320)). Qed.
Lemma lem6895322 : term119 = term122.
Proof. exact (TRANS (@lem6895306) (@lem6895321)). Qed.
Lemma lem6895323 : term105 = term57.
Proof. exact (@lem6895273 (@lem6895322)). Qed.
Lemma lem6895324 : term104 = term57.
Proof. exact (TRANS (@lem6895239) (@lem6895323)). Qed.
Lemma lem6895326 (x : real) : (term76 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6895327 : term57 = term31.
Proof. exact (@lem6895326 term31). Qed.
Lemma lem6895328 : term104 = term31.
Proof. exact (TRANS (@lem6895324) (@lem6895327)). Qed.
Lemma lem6895329 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6895330 : term123 = term118.
Proof. exact (MK_COMB (@lem6895329) (@lem6895328)). Qed.
Lemma lem6895331 (_92033 : int) : (real_of_int _92033) = (real_of_int _92033).
Proof. exact (eq_refl (real_of_int _92033)). Qed.
Lemma lem6895332 (_92033 : int) : (term101 _92033) = (term124 _92033).
Proof. exact (MK_COMB (@lem6895330) (@lem6895331 _92033)). Qed.
Lemma lem6895333 (_92033 : int) : (term100 _92033) = (term124 _92033).
Proof. exact (TRANS (@lem6895230 _92033) (@lem6895332 _92033)). Qed.
Lemma lem6895334 (_92033 : int) : (term124 _92033) = term31.
Proof. exact (@lem1982719 (real_of_int _92033)). Qed.
Lemma lem6895335 (_92033 : int) : (term100 _92033) = term31.
Proof. exact (TRANS (@lem6895333 _92033) (@lem6895334 _92033)). Qed.
Lemma lem6895336 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6895337 (_92033 : int) : (term125 _92033) = term126.
Proof. exact (MK_COMB (@lem6895336) (@lem6895335 _92033)). Qed.
Lemma lem6895339 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6895340 : term60 = term61.
Proof. exact (@lem6895339 term8). Qed.
Lemma lem6895342 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6895343 : term60 = term61.
Proof. exact (@lem6895342 term8). Qed.
Lemma lem6895344 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6895345 : term102 = term103.
Proof. exact (MK_COMB (@lem6895344) (@lem6895343)). Qed.
Lemma lem6895346 : term903 = term904.
Proof. exact (MK_COMB (@lem6895345) (@lem6895340)). Qed.
Lemma lem6895347 : term905.
Proof. exact (@lem1981473 term60 term43 term60 term43 term906 term43). Qed.
Lemma lem6895349 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895350 : term108 = term109.
Proof. exact (@lem6895349 (NUMERAL 0) term8). Qed.
Lemma lem6895351 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895352 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895353 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895352 h1) (fun h1 : term109 = True => @lem6895351)). Qed.
Lemma lem6895354 : term109 = True.
Proof. exact (EQ_MP (@lem6895353) (@lem6895351)). Qed.
Lemma lem6895355 : term108 = True.
Proof. exact (TRANS (@lem6895350) (@lem6895354)). Qed.
Lemma lem6895356 : True = term108.
Proof. exact (SYM (@lem6895355)). Qed.
Lemma lem6895357 : term108.
Proof. exact (EQ_MP (@lem6895356) (@lem0)). Qed.
Lemma lem6895358 : term907.
Proof. exact (@lem6895347 (@lem6895357)). Qed.
Lemma lem6895360 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895361 : term108 = term109.
Proof. exact (@lem6895360 (NUMERAL 0) term8). Qed.
Lemma lem6895362 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895363 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895364 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895363 h1) (fun h1 : term109 = True => @lem6895362)). Qed.
Lemma lem6895365 : term109 = True.
Proof. exact (EQ_MP (@lem6895364) (@lem6895362)). Qed.
Lemma lem6895366 : term108 = True.
Proof. exact (TRANS (@lem6895361) (@lem6895365)). Qed.
Lemma lem6895367 : True = term108.
Proof. exact (SYM (@lem6895366)). Qed.
Lemma lem6895368 : term108.
Proof. exact (EQ_MP (@lem6895367) (@lem0)). Qed.
Lemma lem6895369 : term908.
Proof. exact (@lem6895358 (@lem6895368)). Qed.
Lemma lem6895371 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895372 : term108 = term109.
Proof. exact (@lem6895371 (NUMERAL 0) term8). Qed.
Lemma lem6895373 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895374 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895375 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895374 h1) (fun h1 : term109 = True => @lem6895373)). Qed.
Lemma lem6895376 : term109 = True.
Proof. exact (EQ_MP (@lem6895375) (@lem6895373)). Qed.
Lemma lem6895377 : term108 = True.
Proof. exact (TRANS (@lem6895372) (@lem6895376)). Qed.
Lemma lem6895378 : True = term108.
Proof. exact (SYM (@lem6895377)). Qed.
Lemma lem6895379 : term108.
Proof. exact (EQ_MP (@lem6895378) (@lem0)). Qed.
Lemma lem6895380 : term909.
Proof. exact (@lem6895369 (@lem6895379)). Qed.
Lemma lem6895382 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6895383 : term87 = term92.
Proof. exact (@lem6895382 term8 term8). Qed.
Lemma lem6895384 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6895385 : term72 = term8.
Proof. exact (EQ_MP (@lem6895384) (@lem940073)). Qed.
Lemma lem6895386 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6895387 : term70 = term43.
Proof. exact (MK_COMB (@lem6895386) (@lem6895385)). Qed.
Lemma lem6895388 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6895389 : term92 = term60.
Proof. exact (MK_COMB (@lem6895388) (@lem6895387)). Qed.
Lemma lem6895390 : term87 = term60.
Proof. exact (TRANS (@lem6895383) (@lem6895389)). Qed.
Lemma lem6895392 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6895393 : term87 = term92.
Proof. exact (@lem6895392 term8 term8). Qed.
Lemma lem6895394 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6895395 : term72 = term8.
Proof. exact (EQ_MP (@lem6895394) (@lem940073)). Qed.
Lemma lem6895396 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6895397 : term70 = term43.
Proof. exact (MK_COMB (@lem6895396) (@lem6895395)). Qed.
Lemma lem6895398 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6895399 : term92 = term60.
Proof. exact (MK_COMB (@lem6895398) (@lem6895397)). Qed.
Lemma lem6895400 : term87 = term60.
Proof. exact (TRANS (@lem6895393) (@lem6895399)). Qed.
Lemma lem6895401 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6895402 : term114 = term102.
Proof. exact (MK_COMB (@lem6895401) (@lem6895400)). Qed.
Lemma lem6895403 : term910 = term903.
Proof. exact (MK_COMB (@lem6895402) (@lem6895390)). Qed.
Lemma lem6895404 : term903 = term911.
Proof. exact (@lem1367763 term8 term8). Qed.
Lemma lem6895405 : term912 = term913.
Proof. exact (@lem706885). Qed.
Lemma lem6895406 : (term912 = term913) = (term914 = term915).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term913). Qed.
Lemma lem6895407 : term914 = term915.
Proof. exact (EQ_MP (@lem6895406) (@lem6895405)). Qed.
Lemma lem6895408 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6895409 : term916 = term917.
Proof. exact (MK_COMB (@lem6895408) (@lem6895407)). Qed.
Lemma lem6895410 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6895411 : term911 = term906.
Proof. exact (MK_COMB (@lem6895410) (@lem6895409)). Qed.
Lemma lem6895412 : term903 = term906.
Proof. exact (TRANS (@lem6895404) (@lem6895411)). Qed.
Lemma lem6895413 : term910 = term906.
Proof. exact (TRANS (@lem6895403) (@lem6895412)). Qed.
Lemma lem6895414 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6895415 : term918 = term919.
Proof. exact (MK_COMB (@lem6895414) (@lem6895413)). Qed.
Lemma lem6895416 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem6895417 : term920 = term921.
Proof. exact (MK_COMB (@lem6895415) (@lem6895416)). Qed.
Lemma lem6895419 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6895420 : term921 = term922.
Proof. exact (@lem6895419 term915 term8). Qed.
Lemma lem6895421 : term923 = term913.
Proof. exact (@lem996237 term913). Qed.
Lemma lem6895422 : (term923 = term913) = (term924 = term915).
Proof. exact (@lem1007663 term913 (BIT1 0) term913). Qed.
Lemma lem6895423 : term924 = term915.
Proof. exact (EQ_MP (@lem6895422) (@lem6895421)). Qed.
Lemma lem6895424 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6895425 : term925 = term917.
Proof. exact (MK_COMB (@lem6895424) (@lem6895423)). Qed.
Lemma lem6895426 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6895427 : term922 = term906.
Proof. exact (MK_COMB (@lem6895426) (@lem6895425)). Qed.
Lemma lem6895428 : term921 = term906.
Proof. exact (TRANS (@lem6895420) (@lem6895427)). Qed.
Lemma lem6895429 : term920 = term906.
Proof. exact (TRANS (@lem6895417) (@lem6895428)). Qed.
Lemma lem6895431 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6895432 : term69 = term70.
Proof. exact (@lem6895431 term8 term8). Qed.
Lemma lem6895433 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6895434 : term72 = term8.
Proof. exact (EQ_MP (@lem6895433) (@lem940073)). Qed.
Lemma lem6895435 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6895436 : term70 = term43.
Proof. exact (MK_COMB (@lem6895435) (@lem6895434)). Qed.
Lemma lem6895437 : term69 = term43.
Proof. exact (TRANS (@lem6895432) (@lem6895436)). Qed.
Lemma lem6895438 : term919 = term919.
Proof. exact (eq_refl term919). Qed.
Lemma lem6895439 : term926 = term921.
Proof. exact (MK_COMB (@lem6895438) (@lem6895437)). Qed.
Lemma lem6895441 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6895442 : term921 = term922.
Proof. exact (@lem6895441 term915 term8). Qed.
Lemma lem6895443 : term923 = term913.
Proof. exact (@lem996237 term913). Qed.
Lemma lem6895444 : (term923 = term913) = (term924 = term915).
Proof. exact (@lem1007663 term913 (BIT1 0) term913). Qed.
Lemma lem6895445 : term924 = term915.
Proof. exact (EQ_MP (@lem6895444) (@lem6895443)). Qed.
Lemma lem6895446 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6895447 : term925 = term917.
Proof. exact (MK_COMB (@lem6895446) (@lem6895445)). Qed.
Lemma lem6895448 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6895449 : term922 = term906.
Proof. exact (MK_COMB (@lem6895448) (@lem6895447)). Qed.
Lemma lem6895450 : term921 = term906.
Proof. exact (TRANS (@lem6895442) (@lem6895449)). Qed.
Lemma lem6895451 : term926 = term906.
Proof. exact (TRANS (@lem6895439) (@lem6895450)). Qed.
Lemma lem6895452 : term906 = term926.
Proof. exact (SYM (@lem6895451)). Qed.
Lemma lem6895453 : term920 = term926.
Proof. exact (TRANS (@lem6895429) (@lem6895452)). Qed.
Lemma lem6895454 : term904 = term927.
Proof. exact (@lem6895380 (@lem6895453)). Qed.
Lemma lem6895455 : term903 = term927.
Proof. exact (TRANS (@lem6895346) (@lem6895454)). Qed.
Lemma lem6895457 (x : real) : (term76 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6895458 : term927 = term906.
Proof. exact (@lem6895457 term906). Qed.
Lemma lem6895459 : term903 = term906.
Proof. exact (TRANS (@lem6895455) (@lem6895458)). Qed.
Lemma lem6895460 (_92033 : int) : (term902 _92033) = term928.
Proof. exact (MK_COMB (@lem6895337 _92033) (@lem6895459)). Qed.
Lemma lem6895461 (_92033 : int) : (term901 _92033) = term928.
Proof. exact (TRANS (@lem6895229 _92033) (@lem6895460 _92033)). Qed.
Lemma lem6895462 : term928 = term906.
Proof. exact (@lem1982721 term906). Qed.
Lemma lem6895463 (_92033 : int) : (term901 _92033) = term906.
Proof. exact (TRANS (@lem6895461 _92033) (@lem6895462)). Qed.
Lemma lem6895464 (_92032 : int) (_92033 : int) : (term897 _92032 _92033) = term928.
Proof. exact (MK_COMB (@lem6895228 _92032) (@lem6895463 _92033)). Qed.
Lemma lem6895465 (_92032 : int) (_92033 : int) : (term896 _92032 _92033) = term928.
Proof. exact (TRANS (@lem6895120 _92032 _92033) (@lem6895464 _92032 _92033)). Qed.
Lemma lem6895466 : term928 = term906.
Proof. exact (@lem1982721 term906). Qed.
Lemma lem6895467 (_92032 : int) (_92033 : int) : (term896 _92032 _92033) = term906.
Proof. exact (TRANS (@lem6895465 _92032 _92033) (@lem6895466)). Qed.
Lemma lem6895468 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6895469 (_92032 : int) (_92033 : int) : (term929 _92032 _92033) = term930.
Proof. exact (MK_COMB (@lem6895468) (@lem6895467 _92032 _92033)). Qed.
Lemma lem6895470 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6895471 (_92032 : int) (_92033 : int) : (term895 _92032 _92033) = term931.
Proof. exact (MK_COMB (@lem6895469 _92032 _92033) (@lem6895470)). Qed.
Lemma lem6895472 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term873 _92034 _92032 _92033) : term931.
Proof. exact (EQ_MP (@lem6895471 _92032 _92033) (@lem6895119 _92034 _92032 _92033 h1)). Qed.
Lemma lem6895474 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6895475 : term931 = term932.
Proof. exact (@lem6895474 term31 term906). Qed.
Lemma lem6895477 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6895478 : term906 = term927.
Proof. exact (@lem6895477 term915). Qed.
Lemma lem6895480 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6895481 : term31 = term57.
Proof. exact (@lem6895480 (NUMERAL 0)). Qed.
Lemma lem6895482 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6895483 : term33 = term134.
Proof. exact (MK_COMB (@lem6895482) (@lem6895481)). Qed.
Lemma lem6895484 : term932 = term933.
Proof. exact (MK_COMB (@lem6895483) (@lem6895478)). Qed.
Lemma lem6895485 : term934.
Proof. exact (@lem1980026 term31 term43 term906 term43). Qed.
Lemma lem6895487 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895488 : term108 = term109.
Proof. exact (@lem6895487 (NUMERAL 0) term8). Qed.
Lemma lem6895489 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895490 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895491 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895490 h1) (fun h1 : term109 = True => @lem6895489)). Qed.
Lemma lem6895492 : term109 = True.
Proof. exact (EQ_MP (@lem6895491) (@lem6895489)). Qed.
Lemma lem6895493 : term108 = True.
Proof. exact (TRANS (@lem6895488) (@lem6895492)). Qed.
Lemma lem6895494 : True = term108.
Proof. exact (SYM (@lem6895493)). Qed.
Lemma lem6895495 : term108.
Proof. exact (EQ_MP (@lem6895494) (@lem0)). Qed.
Lemma lem6895496 : term935.
Proof. exact (@lem6895485 (@lem6895495)). Qed.
Lemma lem6895498 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895499 : term108 = term109.
Proof. exact (@lem6895498 (NUMERAL 0) term8). Qed.
Lemma lem6895500 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895501 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895502 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895501 h1) (fun h1 : term109 = True => @lem6895500)). Qed.
Lemma lem6895503 : term109 = True.
Proof. exact (EQ_MP (@lem6895502) (@lem6895500)). Qed.
Lemma lem6895504 : term108 = True.
Proof. exact (TRANS (@lem6895499) (@lem6895503)). Qed.
Lemma lem6895505 : True = term108.
Proof. exact (SYM (@lem6895504)). Qed.
Lemma lem6895506 : term108.
Proof. exact (EQ_MP (@lem6895505) (@lem0)). Qed.
Lemma lem6895507 : term933 = term936.
Proof. exact (@lem6895496 (@lem6895506)). Qed.
Lemma lem6895509 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6895510 : term921 = term922.
Proof. exact (@lem6895509 term915 term8). Qed.
Lemma lem6895511 : term923 = term913.
Proof. exact (@lem996237 term913). Qed.
Lemma lem6895512 : (term923 = term913) = (term924 = term915).
Proof. exact (@lem1007663 term913 (BIT1 0) term913). Qed.
Lemma lem6895513 : term924 = term915.
Proof. exact (EQ_MP (@lem6895512) (@lem6895511)). Qed.
Lemma lem6895514 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6895515 : term925 = term917.
Proof. exact (MK_COMB (@lem6895514) (@lem6895513)). Qed.
Lemma lem6895516 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6895517 : term922 = term906.
Proof. exact (MK_COMB (@lem6895516) (@lem6895515)). Qed.
Lemma lem6895518 : term921 = term906.
Proof. exact (TRANS (@lem6895510) (@lem6895517)). Qed.
Lemma lem6895520 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6895521 : term120 = term31.
Proof. exact (@lem6895520 term8). Qed.
Lemma lem6895522 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6895523 : term139 = term33.
Proof. exact (MK_COMB (@lem6895522) (@lem6895521)). Qed.
Lemma lem6895524 : term936 = term932.
Proof. exact (MK_COMB (@lem6895523) (@lem6895518)). Qed.
Lemma lem6895526 (m : nat) (n : nat) : (term140 m n) = (term141 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6895527 : term932 = term937.
Proof. exact (@lem6895526 (NUMERAL 0) term915). Qed.
Lemma lem6895528 : term938 = term913.
Proof. exact (@lem912803). Qed.
Lemma lem6895529 (h1 : term938 = term913) : (term915 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term913 h1). Qed.
Lemma lem6895530 : (term938 = term913) = ((term915 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term938 = term913 => @lem6895529 h1) (fun h1 : (term915 = (NUMERAL 0)) = False => @lem6895528)). Qed.
Lemma lem6895531 : (term915 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6895530) (@lem6895528)). Qed.
Lemma lem6895532 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6895533 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6895534 : term143 = (and True).
Proof. exact (MK_COMB (@lem6895533) (@lem6895532)). Qed.
Lemma lem6895535 : term937 = (True /\ False).
Proof. exact (MK_COMB (@lem6895534) (@lem6895531)). Qed.
Lemma lem6895537 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6895538 : term937 = False.
Proof. exact (TRANS (@lem6895535) (@lem6895537)). Qed.
Lemma lem6895539 : term932 = False.
Proof. exact (TRANS (@lem6895527) (@lem6895538)). Qed.
Lemma lem6895540 : term936 = False.
Proof. exact (TRANS (@lem6895524) (@lem6895539)). Qed.
Lemma lem6895541 : term933 = False.
Proof. exact (TRANS (@lem6895507) (@lem6895540)). Qed.
Lemma lem6895542 : term932 = False.
Proof. exact (TRANS (@lem6895484) (@lem6895541)). Qed.
Lemma lem6895543 : term931 = False.
Proof. exact (TRANS (@lem6895475) (@lem6895542)). Qed.
Lemma lem6895544 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term873 _92034 _92032 _92033) : False.
Proof. exact (EQ_MP (@lem6895543) (@lem6895472 _92034 _92032 _92033 h1)). Qed.
Lemma lem6895545 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term939 _92034 _92032 _92033) : term939 _92034 _92032 _92033.
Proof. exact (h1). Qed.
Lemma lem6895546 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term939 _92034 _92032 _92033) : term869 _92034 _92032 _92033.
Proof. exact (proj2 (@lem6895545 _92034 _92032 _92033 h1)). Qed.
Lemma lem6895548 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term939 _92034 _92032 _92033) : term856 _92034 _92032 _92033.
Proof. exact (proj2 (@lem6895546 _92034 _92032 _92033 h1)). Qed.
Lemma lem6895550 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term939 _92034 _92032 _92033) : term843 _92034 _92032 _92033.
Proof. exact (proj2 (@lem6895548 _92034 _92032 _92033 h1)). Qed.
Lemma lem6895552 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term939 _92034 _92032 _92033) : term831 _92032 _92033.
Proof. exact (proj2 (@lem6895550 _92034 _92032 _92033 h1)). Qed.
Lemma lem6895556 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term939 _92034 _92032 _92033) : term809 _92032 _92033.
Proof. exact (proj2 (@lem6895552 _92034 _92032 _92033 h1)). Qed.
Lemma lem6895558 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term939 _92034 _92032 _92033) : term793 _92032 _92033.
Proof. exact (proj2 (@lem6895556 _92034 _92032 _92033 h1)). Qed.
Lemma lem6895559 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term939 _92034 _92032 _92033) : term805 _92032 _92033.
Proof. exact (proj1 (@lem6895556 _92034 _92032 _92033 h1)). Qed.
Lemma lem6895561 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6895562 : term874 = term108.
Proof. exact (@lem6895561 term31 term43). Qed.
Lemma lem6895564 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6895565 : term43 = term86.
Proof. exact (@lem6895564 term8). Qed.
Lemma lem6895567 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6895568 : term31 = term57.
Proof. exact (@lem6895567 (NUMERAL 0)). Qed.
Lemma lem6895569 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6895570 : term875 = term876.
Proof. exact (MK_COMB (@lem6895569) (@lem6895568)). Qed.
Lemma lem6895571 : term108 = term877.
Proof. exact (MK_COMB (@lem6895570) (@lem6895565)). Qed.
Lemma lem6895572 : term878.
Proof. exact (@lem1980255 term31 term43 term43 term43). Qed.
Lemma lem6895574 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895575 : term108 = term109.
Proof. exact (@lem6895574 (NUMERAL 0) term8). Qed.
Lemma lem6895576 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895577 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895578 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895577 h1) (fun h1 : term109 = True => @lem6895576)). Qed.
Lemma lem6895579 : term109 = True.
Proof. exact (EQ_MP (@lem6895578) (@lem6895576)). Qed.
Lemma lem6895580 : term108 = True.
Proof. exact (TRANS (@lem6895575) (@lem6895579)). Qed.
Lemma lem6895581 : True = term108.
Proof. exact (SYM (@lem6895580)). Qed.
Lemma lem6895582 : term108.
Proof. exact (EQ_MP (@lem6895581) (@lem0)). Qed.
Lemma lem6895583 : term879.
Proof. exact (@lem6895572 (@lem6895582)). Qed.
Lemma lem6895585 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895586 : term108 = term109.
Proof. exact (@lem6895585 (NUMERAL 0) term8). Qed.
Lemma lem6895587 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895588 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895589 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895588 h1) (fun h1 : term109 = True => @lem6895587)). Qed.
Lemma lem6895590 : term109 = True.
Proof. exact (EQ_MP (@lem6895589) (@lem6895587)). Qed.
Lemma lem6895591 : term108 = True.
Proof. exact (TRANS (@lem6895586) (@lem6895590)). Qed.
Lemma lem6895592 : True = term108.
Proof. exact (SYM (@lem6895591)). Qed.
Lemma lem6895593 : term108.
Proof. exact (EQ_MP (@lem6895592) (@lem0)). Qed.
Lemma lem6895594 : term877 = term880.
Proof. exact (@lem6895583 (@lem6895593)). Qed.
Lemma lem6895596 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6895597 : term69 = term70.
Proof. exact (@lem6895596 term8 term8). Qed.
Lemma lem6895598 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6895599 : term72 = term8.
Proof. exact (EQ_MP (@lem6895598) (@lem940073)). Qed.
Lemma lem6895600 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6895601 : term70 = term43.
Proof. exact (MK_COMB (@lem6895600) (@lem6895599)). Qed.
Lemma lem6895602 : term69 = term43.
Proof. exact (TRANS (@lem6895597) (@lem6895601)). Qed.
Lemma lem6895604 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6895605 : term120 = term31.
Proof. exact (@lem6895604 term8). Qed.
Lemma lem6895606 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6895607 : term881 = term875.
Proof. exact (MK_COMB (@lem6895606) (@lem6895605)). Qed.
Lemma lem6895608 : term880 = term108.
Proof. exact (MK_COMB (@lem6895607) (@lem6895602)). Qed.
Lemma lem6895610 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895611 : term108 = term109.
Proof. exact (@lem6895610 (NUMERAL 0) term8). Qed.
Lemma lem6895612 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895613 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895614 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895613 h1) (fun h1 : term109 = True => @lem6895612)). Qed.
Lemma lem6895615 : term109 = True.
Proof. exact (EQ_MP (@lem6895614) (@lem6895612)). Qed.
Lemma lem6895616 : term108 = True.
Proof. exact (TRANS (@lem6895611) (@lem6895615)). Qed.
Lemma lem6895617 : term880 = True.
Proof. exact (TRANS (@lem6895608) (@lem6895616)). Qed.
Lemma lem6895618 : term877 = True.
Proof. exact (TRANS (@lem6895594) (@lem6895617)). Qed.
Lemma lem6895619 : term108 = True.
Proof. exact (TRANS (@lem6895571) (@lem6895618)). Qed.
Lemma lem6895620 : term874 = True.
Proof. exact (TRANS (@lem6895562) (@lem6895619)). Qed.
Lemma lem6895621 : True = term874.
Proof. exact (SYM (@lem6895620)). Qed.
Lemma lem6895622 : term874.
Proof. exact (EQ_MP (@lem6895621) (@lem0)). Qed.
Lemma lem6895623 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term939 _92034 _92032 _92033) : term882 _92032 _92033.
Proof. exact (conj (@lem6895622) (@lem6895558 _92034 _92032 _92033 h1)). Qed.
Lemma lem6895625 (x : real) (y : real) : term883 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6895626 (_92032 : int) (_92033 : int) : term884 _92032 _92033.
Proof. exact (@lem6895625 term43 (term790 _92032 _92033)). Qed.
Lemma lem6895627 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term939 _92034 _92032 _92033) : term885 _92032 _92033.
Proof. exact (@lem6895626 _92032 _92033 (@lem6895623 _92034 _92032 _92033 h1)). Qed.
Lemma lem6895628 (_92032 : int) (_92033 : int) : (term886 _92032 _92033) = (term790 _92032 _92033).
Proof. exact (@lem1982733 (term790 _92032 _92033)). Qed.
Lemma lem6895629 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6895630 (_92032 : int) (_92033 : int) : (term887 _92032 _92033) = (term792 _92032 _92033).
Proof. exact (MK_COMB (@lem6895629) (@lem6895628 _92032 _92033)). Qed.
Lemma lem6895631 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6895632 (_92032 : int) (_92033 : int) : (term885 _92032 _92033) = (term793 _92032 _92033).
Proof. exact (MK_COMB (@lem6895630 _92032 _92033) (@lem6895631)). Qed.
Lemma lem6895633 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term939 _92034 _92032 _92033) : term793 _92032 _92033.
Proof. exact (EQ_MP (@lem6895632 _92032 _92033) (@lem6895627 _92034 _92032 _92033 h1)). Qed.
Lemma lem6895635 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6895636 : term874 = term108.
Proof. exact (@lem6895635 term31 term43). Qed.
Lemma lem6895638 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6895639 : term43 = term86.
Proof. exact (@lem6895638 term8). Qed.
Lemma lem6895641 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6895642 : term31 = term57.
Proof. exact (@lem6895641 (NUMERAL 0)). Qed.
Lemma lem6895643 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6895644 : term875 = term876.
Proof. exact (MK_COMB (@lem6895643) (@lem6895642)). Qed.
Lemma lem6895645 : term108 = term877.
Proof. exact (MK_COMB (@lem6895644) (@lem6895639)). Qed.
Lemma lem6895646 : term878.
Proof. exact (@lem1980255 term31 term43 term43 term43). Qed.
Lemma lem6895648 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895649 : term108 = term109.
Proof. exact (@lem6895648 (NUMERAL 0) term8). Qed.
Lemma lem6895650 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895651 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895652 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895651 h1) (fun h1 : term109 = True => @lem6895650)). Qed.
Lemma lem6895653 : term109 = True.
Proof. exact (EQ_MP (@lem6895652) (@lem6895650)). Qed.
Lemma lem6895654 : term108 = True.
Proof. exact (TRANS (@lem6895649) (@lem6895653)). Qed.
Lemma lem6895655 : True = term108.
Proof. exact (SYM (@lem6895654)). Qed.
Lemma lem6895656 : term108.
Proof. exact (EQ_MP (@lem6895655) (@lem0)). Qed.
Lemma lem6895657 : term879.
Proof. exact (@lem6895646 (@lem6895656)). Qed.
Lemma lem6895659 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895660 : term108 = term109.
Proof. exact (@lem6895659 (NUMERAL 0) term8). Qed.
Lemma lem6895661 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895662 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895663 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895662 h1) (fun h1 : term109 = True => @lem6895661)). Qed.
Lemma lem6895664 : term109 = True.
Proof. exact (EQ_MP (@lem6895663) (@lem6895661)). Qed.
Lemma lem6895665 : term108 = True.
Proof. exact (TRANS (@lem6895660) (@lem6895664)). Qed.
Lemma lem6895666 : True = term108.
Proof. exact (SYM (@lem6895665)). Qed.
Lemma lem6895667 : term108.
Proof. exact (EQ_MP (@lem6895666) (@lem0)). Qed.
Lemma lem6895668 : term877 = term880.
Proof. exact (@lem6895657 (@lem6895667)). Qed.
Lemma lem6895670 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6895671 : term69 = term70.
Proof. exact (@lem6895670 term8 term8). Qed.
Lemma lem6895672 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6895673 : term72 = term8.
Proof. exact (EQ_MP (@lem6895672) (@lem940073)). Qed.
Lemma lem6895674 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6895675 : term70 = term43.
Proof. exact (MK_COMB (@lem6895674) (@lem6895673)). Qed.
Lemma lem6895676 : term69 = term43.
Proof. exact (TRANS (@lem6895671) (@lem6895675)). Qed.
Lemma lem6895678 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6895679 : term120 = term31.
Proof. exact (@lem6895678 term8). Qed.
Lemma lem6895680 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6895681 : term881 = term875.
Proof. exact (MK_COMB (@lem6895680) (@lem6895679)). Qed.
Lemma lem6895682 : term880 = term108.
Proof. exact (MK_COMB (@lem6895681) (@lem6895676)). Qed.
Lemma lem6895684 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895685 : term108 = term109.
Proof. exact (@lem6895684 (NUMERAL 0) term8). Qed.
Lemma lem6895686 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895687 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895688 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895687 h1) (fun h1 : term109 = True => @lem6895686)). Qed.
Lemma lem6895689 : term109 = True.
Proof. exact (EQ_MP (@lem6895688) (@lem6895686)). Qed.
Lemma lem6895690 : term108 = True.
Proof. exact (TRANS (@lem6895685) (@lem6895689)). Qed.
Lemma lem6895691 : term880 = True.
Proof. exact (TRANS (@lem6895682) (@lem6895690)). Qed.
Lemma lem6895692 : term877 = True.
Proof. exact (TRANS (@lem6895668) (@lem6895691)). Qed.
Lemma lem6895693 : term108 = True.
Proof. exact (TRANS (@lem6895645) (@lem6895692)). Qed.
Lemma lem6895694 : term874 = True.
Proof. exact (TRANS (@lem6895636) (@lem6895693)). Qed.
Lemma lem6895695 : True = term874.
Proof. exact (SYM (@lem6895694)). Qed.
Lemma lem6895696 : term874.
Proof. exact (EQ_MP (@lem6895695) (@lem0)). Qed.
Lemma lem6895697 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term939 _92034 _92032 _92033) : term888 _92032 _92033.
Proof. exact (conj (@lem6895696) (@lem6895559 _92034 _92032 _92033 h1)). Qed.
Lemma lem6895699 (x : real) (y : real) : term883 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6895700 (_92032 : int) (_92033 : int) : term889 _92032 _92033.
Proof. exact (@lem6895699 term43 (term803 _92032 _92033)). Qed.
Lemma lem6895701 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term939 _92034 _92032 _92033) : term890 _92032 _92033.
Proof. exact (@lem6895700 _92032 _92033 (@lem6895697 _92034 _92032 _92033 h1)). Qed.
Lemma lem6895702 (_92032 : int) (_92033 : int) : (term891 _92032 _92033) = (term803 _92032 _92033).
Proof. exact (@lem1982733 (term803 _92032 _92033)). Qed.
Lemma lem6895703 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6895704 (_92032 : int) (_92033 : int) : (term892 _92032 _92033) = (term804 _92032 _92033).
Proof. exact (MK_COMB (@lem6895703) (@lem6895702 _92032 _92033)). Qed.
Lemma lem6895705 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6895706 (_92032 : int) (_92033 : int) : (term890 _92032 _92033) = (term805 _92032 _92033).
Proof. exact (MK_COMB (@lem6895704 _92032 _92033) (@lem6895705)). Qed.
Lemma lem6895707 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term939 _92034 _92032 _92033) : term805 _92032 _92033.
Proof. exact (EQ_MP (@lem6895706 _92032 _92033) (@lem6895701 _92034 _92032 _92033 h1)). Qed.
Lemma lem6895708 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term939 _92034 _92032 _92033) : term809 _92032 _92033.
Proof. exact (conj (@lem6895707 _92034 _92032 _92033 h1) (@lem6895633 _92034 _92032 _92033 h1)). Qed.
Lemma lem6895710 (x : real) (y : real) : term893 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem6895711 (_92032 : int) (_92033 : int) : term894 _92032 _92033.
Proof. exact (@lem6895710 (term803 _92032 _92033) (term790 _92032 _92033)). Qed.
Lemma lem6895712 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term939 _92034 _92032 _92033) : term895 _92032 _92033.
Proof. exact (@lem6895711 _92032 _92033 (@lem6895708 _92034 _92032 _92033 h1)). Qed.
Lemma lem6895713 (_92032 : int) (_92033 : int) : (term896 _92032 _92033) = (term897 _92032 _92033).
Proof. exact (@lem1982753 (term99 _92032) (real_of_int _92032) (term898 _92033) (term96 _92033)). Qed.
Lemma lem6895714 (_92032 : int) : (term899 _92032) = (term101 _92032).
Proof. exact (@lem1982713 term60 (real_of_int _92032)). Qed.
Lemma lem6895716 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6895717 : term43 = term86.
Proof. exact (@lem6895716 term8). Qed.
Lemma lem6895719 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6895720 : term60 = term61.
Proof. exact (@lem6895719 term8). Qed.
Lemma lem6895721 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6895722 : term102 = term103.
Proof. exact (MK_COMB (@lem6895721) (@lem6895720)). Qed.
Lemma lem6895723 : term104 = term105.
Proof. exact (MK_COMB (@lem6895722) (@lem6895717)). Qed.
Lemma lem6895724 : term106.
Proof. exact (@lem1981473 term60 term43 term43 term43 term31 term43). Qed.
Lemma lem6895726 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895727 : term108 = term109.
Proof. exact (@lem6895726 (NUMERAL 0) term8). Qed.
Lemma lem6895728 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895729 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895730 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895729 h1) (fun h1 : term109 = True => @lem6895728)). Qed.
Lemma lem6895731 : term109 = True.
Proof. exact (EQ_MP (@lem6895730) (@lem6895728)). Qed.
Lemma lem6895732 : term108 = True.
Proof. exact (TRANS (@lem6895727) (@lem6895731)). Qed.
Lemma lem6895733 : True = term108.
Proof. exact (SYM (@lem6895732)). Qed.
Lemma lem6895734 : term108.
Proof. exact (EQ_MP (@lem6895733) (@lem0)). Qed.
Lemma lem6895735 : term111.
Proof. exact (@lem6895724 (@lem6895734)). Qed.
Lemma lem6895737 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895738 : term108 = term109.
Proof. exact (@lem6895737 (NUMERAL 0) term8). Qed.
Lemma lem6895739 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895740 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895741 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895740 h1) (fun h1 : term109 = True => @lem6895739)). Qed.
Lemma lem6895742 : term109 = True.
Proof. exact (EQ_MP (@lem6895741) (@lem6895739)). Qed.
Lemma lem6895743 : term108 = True.
Proof. exact (TRANS (@lem6895738) (@lem6895742)). Qed.
Lemma lem6895744 : True = term108.
Proof. exact (SYM (@lem6895743)). Qed.
Lemma lem6895745 : term108.
Proof. exact (EQ_MP (@lem6895744) (@lem0)). Qed.
Lemma lem6895746 : term112.
Proof. exact (@lem6895735 (@lem6895745)). Qed.
Lemma lem6895748 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895749 : term108 = term109.
Proof. exact (@lem6895748 (NUMERAL 0) term8). Qed.
Lemma lem6895750 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895751 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895752 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895751 h1) (fun h1 : term109 = True => @lem6895750)). Qed.
Lemma lem6895753 : term109 = True.
Proof. exact (EQ_MP (@lem6895752) (@lem6895750)). Qed.
Lemma lem6895754 : term108 = True.
Proof. exact (TRANS (@lem6895749) (@lem6895753)). Qed.
Lemma lem6895755 : True = term108.
Proof. exact (SYM (@lem6895754)). Qed.
Lemma lem6895756 : term108.
Proof. exact (EQ_MP (@lem6895755) (@lem0)). Qed.
Lemma lem6895757 : term113.
Proof. exact (@lem6895746 (@lem6895756)). Qed.
Lemma lem6895759 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6895760 : term69 = term70.
Proof. exact (@lem6895759 term8 term8). Qed.
Lemma lem6895761 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6895762 : term72 = term8.
Proof. exact (EQ_MP (@lem6895761) (@lem940073)). Qed.
Lemma lem6895763 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6895764 : term70 = term43.
Proof. exact (MK_COMB (@lem6895763) (@lem6895762)). Qed.
Lemma lem6895765 : term69 = term43.
Proof. exact (TRANS (@lem6895760) (@lem6895764)). Qed.
Lemma lem6895767 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6895768 : term87 = term92.
Proof. exact (@lem6895767 term8 term8). Qed.
Lemma lem6895769 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6895770 : term72 = term8.
Proof. exact (EQ_MP (@lem6895769) (@lem940073)). Qed.
Lemma lem6895771 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6895772 : term70 = term43.
Proof. exact (MK_COMB (@lem6895771) (@lem6895770)). Qed.
Lemma lem6895773 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6895774 : term92 = term60.
Proof. exact (MK_COMB (@lem6895773) (@lem6895772)). Qed.
Lemma lem6895775 : term87 = term60.
Proof. exact (TRANS (@lem6895768) (@lem6895774)). Qed.
Lemma lem6895776 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6895777 : term114 = term102.
Proof. exact (MK_COMB (@lem6895776) (@lem6895775)). Qed.
Lemma lem6895778 : term115 = term104.
Proof. exact (MK_COMB (@lem6895777) (@lem6895765)). Qed.
Lemma lem6895780 (m : nat) : (term116 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6895781 : term104 = term31.
Proof. exact (@lem6895780 term8). Qed.
Lemma lem6895782 : term115 = term31.
Proof. exact (TRANS (@lem6895778) (@lem6895781)). Qed.
Lemma lem6895783 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6895784 : term117 = term118.
Proof. exact (MK_COMB (@lem6895783) (@lem6895782)). Qed.
Lemma lem6895785 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem6895786 : term119 = term120.
Proof. exact (MK_COMB (@lem6895784) (@lem6895785)). Qed.
Lemma lem6895788 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6895789 : term120 = term31.
Proof. exact (@lem6895788 term8). Qed.
Lemma lem6895790 : term119 = term31.
Proof. exact (TRANS (@lem6895786) (@lem6895789)). Qed.
Lemma lem6895792 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6895793 : term69 = term70.
Proof. exact (@lem6895792 term8 term8). Qed.
Lemma lem6895794 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6895795 : term72 = term8.
Proof. exact (EQ_MP (@lem6895794) (@lem940073)). Qed.
Lemma lem6895796 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6895797 : term70 = term43.
Proof. exact (MK_COMB (@lem6895796) (@lem6895795)). Qed.
Lemma lem6895798 : term69 = term43.
Proof. exact (TRANS (@lem6895793) (@lem6895797)). Qed.
Lemma lem6895799 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem6895800 : term122 = term120.
Proof. exact (MK_COMB (@lem6895799) (@lem6895798)). Qed.
Lemma lem6895802 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6895803 : term120 = term31.
Proof. exact (@lem6895802 term8). Qed.
Lemma lem6895804 : term122 = term31.
Proof. exact (TRANS (@lem6895800) (@lem6895803)). Qed.
Lemma lem6895805 : term31 = term122.
Proof. exact (SYM (@lem6895804)). Qed.
Lemma lem6895806 : term119 = term122.
Proof. exact (TRANS (@lem6895790) (@lem6895805)). Qed.
Lemma lem6895807 : term105 = term57.
Proof. exact (@lem6895757 (@lem6895806)). Qed.
Lemma lem6895808 : term104 = term57.
Proof. exact (TRANS (@lem6895723) (@lem6895807)). Qed.
Lemma lem6895810 (x : real) : (term76 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6895811 : term57 = term31.
Proof. exact (@lem6895810 term31). Qed.
Lemma lem6895812 : term104 = term31.
Proof. exact (TRANS (@lem6895808) (@lem6895811)). Qed.
Lemma lem6895813 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6895814 : term123 = term118.
Proof. exact (MK_COMB (@lem6895813) (@lem6895812)). Qed.
Lemma lem6895815 (_92032 : int) : (real_of_int _92032) = (real_of_int _92032).
Proof. exact (eq_refl (real_of_int _92032)). Qed.
Lemma lem6895816 (_92032 : int) : (term101 _92032) = (term124 _92032).
Proof. exact (MK_COMB (@lem6895814) (@lem6895815 _92032)). Qed.
Lemma lem6895817 (_92032 : int) : (term899 _92032) = (term124 _92032).
Proof. exact (TRANS (@lem6895714 _92032) (@lem6895816 _92032)). Qed.
Lemma lem6895818 (_92032 : int) : (term124 _92032) = term31.
Proof. exact (@lem1982719 (real_of_int _92032)). Qed.
Lemma lem6895819 (_92032 : int) : (term899 _92032) = term31.
Proof. exact (TRANS (@lem6895817 _92032) (@lem6895818 _92032)). Qed.
Lemma lem6895820 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6895821 (_92032 : int) : (term900 _92032) = term126.
Proof. exact (MK_COMB (@lem6895820) (@lem6895819 _92032)). Qed.
Lemma lem6895822 (_92033 : int) : (term901 _92033) = (term902 _92033).
Proof. exact (@lem1982753 (real_of_int _92033) (term99 _92033) term60 term60). Qed.
Lemma lem6895823 (_92033 : int) : (term100 _92033) = (term101 _92033).
Proof. exact (@lem1982715 term60 (real_of_int _92033)). Qed.
Lemma lem6895825 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6895826 : term43 = term86.
Proof. exact (@lem6895825 term8). Qed.
Lemma lem6895828 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6895829 : term60 = term61.
Proof. exact (@lem6895828 term8). Qed.
Lemma lem6895830 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6895831 : term102 = term103.
Proof. exact (MK_COMB (@lem6895830) (@lem6895829)). Qed.
Lemma lem6895832 : term104 = term105.
Proof. exact (MK_COMB (@lem6895831) (@lem6895826)). Qed.
Lemma lem6895833 : term106.
Proof. exact (@lem1981473 term60 term43 term43 term43 term31 term43). Qed.
Lemma lem6895835 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895836 : term108 = term109.
Proof. exact (@lem6895835 (NUMERAL 0) term8). Qed.
Lemma lem6895837 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895838 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895839 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895838 h1) (fun h1 : term109 = True => @lem6895837)). Qed.
Lemma lem6895840 : term109 = True.
Proof. exact (EQ_MP (@lem6895839) (@lem6895837)). Qed.
Lemma lem6895841 : term108 = True.
Proof. exact (TRANS (@lem6895836) (@lem6895840)). Qed.
Lemma lem6895842 : True = term108.
Proof. exact (SYM (@lem6895841)). Qed.
Lemma lem6895843 : term108.
Proof. exact (EQ_MP (@lem6895842) (@lem0)). Qed.
Lemma lem6895844 : term111.
Proof. exact (@lem6895833 (@lem6895843)). Qed.
Lemma lem6895846 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895847 : term108 = term109.
Proof. exact (@lem6895846 (NUMERAL 0) term8). Qed.
Lemma lem6895848 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895849 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895850 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895849 h1) (fun h1 : term109 = True => @lem6895848)). Qed.
Lemma lem6895851 : term109 = True.
Proof. exact (EQ_MP (@lem6895850) (@lem6895848)). Qed.
Lemma lem6895852 : term108 = True.
Proof. exact (TRANS (@lem6895847) (@lem6895851)). Qed.
Lemma lem6895853 : True = term108.
Proof. exact (SYM (@lem6895852)). Qed.
Lemma lem6895854 : term108.
Proof. exact (EQ_MP (@lem6895853) (@lem0)). Qed.
Lemma lem6895855 : term112.
Proof. exact (@lem6895844 (@lem6895854)). Qed.
Lemma lem6895857 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895858 : term108 = term109.
Proof. exact (@lem6895857 (NUMERAL 0) term8). Qed.
Lemma lem6895859 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895860 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895861 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895860 h1) (fun h1 : term109 = True => @lem6895859)). Qed.
Lemma lem6895862 : term109 = True.
Proof. exact (EQ_MP (@lem6895861) (@lem6895859)). Qed.
Lemma lem6895863 : term108 = True.
Proof. exact (TRANS (@lem6895858) (@lem6895862)). Qed.
Lemma lem6895864 : True = term108.
Proof. exact (SYM (@lem6895863)). Qed.
Lemma lem6895865 : term108.
Proof. exact (EQ_MP (@lem6895864) (@lem0)). Qed.
Lemma lem6895866 : term113.
Proof. exact (@lem6895855 (@lem6895865)). Qed.
Lemma lem6895868 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6895869 : term69 = term70.
Proof. exact (@lem6895868 term8 term8). Qed.
Lemma lem6895870 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6895871 : term72 = term8.
Proof. exact (EQ_MP (@lem6895870) (@lem940073)). Qed.
Lemma lem6895872 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6895873 : term70 = term43.
Proof. exact (MK_COMB (@lem6895872) (@lem6895871)). Qed.
Lemma lem6895874 : term69 = term43.
Proof. exact (TRANS (@lem6895869) (@lem6895873)). Qed.
Lemma lem6895876 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6895877 : term87 = term92.
Proof. exact (@lem6895876 term8 term8). Qed.
Lemma lem6895878 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6895879 : term72 = term8.
Proof. exact (EQ_MP (@lem6895878) (@lem940073)). Qed.
Lemma lem6895880 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6895881 : term70 = term43.
Proof. exact (MK_COMB (@lem6895880) (@lem6895879)). Qed.
Lemma lem6895882 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6895883 : term92 = term60.
Proof. exact (MK_COMB (@lem6895882) (@lem6895881)). Qed.
Lemma lem6895884 : term87 = term60.
Proof. exact (TRANS (@lem6895877) (@lem6895883)). Qed.
Lemma lem6895885 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6895886 : term114 = term102.
Proof. exact (MK_COMB (@lem6895885) (@lem6895884)). Qed.
Lemma lem6895887 : term115 = term104.
Proof. exact (MK_COMB (@lem6895886) (@lem6895874)). Qed.
Lemma lem6895889 (m : nat) : (term116 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6895890 : term104 = term31.
Proof. exact (@lem6895889 term8). Qed.
Lemma lem6895891 : term115 = term31.
Proof. exact (TRANS (@lem6895887) (@lem6895890)). Qed.
Lemma lem6895892 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6895893 : term117 = term118.
Proof. exact (MK_COMB (@lem6895892) (@lem6895891)). Qed.
Lemma lem6895894 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem6895895 : term119 = term120.
Proof. exact (MK_COMB (@lem6895893) (@lem6895894)). Qed.
Lemma lem6895897 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6895898 : term120 = term31.
Proof. exact (@lem6895897 term8). Qed.
Lemma lem6895899 : term119 = term31.
Proof. exact (TRANS (@lem6895895) (@lem6895898)). Qed.
Lemma lem6895901 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6895902 : term69 = term70.
Proof. exact (@lem6895901 term8 term8). Qed.
Lemma lem6895903 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6895904 : term72 = term8.
Proof. exact (EQ_MP (@lem6895903) (@lem940073)). Qed.
Lemma lem6895905 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6895906 : term70 = term43.
Proof. exact (MK_COMB (@lem6895905) (@lem6895904)). Qed.
Lemma lem6895907 : term69 = term43.
Proof. exact (TRANS (@lem6895902) (@lem6895906)). Qed.
Lemma lem6895908 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem6895909 : term122 = term120.
Proof. exact (MK_COMB (@lem6895908) (@lem6895907)). Qed.
Lemma lem6895911 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6895912 : term120 = term31.
Proof. exact (@lem6895911 term8). Qed.
Lemma lem6895913 : term122 = term31.
Proof. exact (TRANS (@lem6895909) (@lem6895912)). Qed.
Lemma lem6895914 : term31 = term122.
Proof. exact (SYM (@lem6895913)). Qed.
Lemma lem6895915 : term119 = term122.
Proof. exact (TRANS (@lem6895899) (@lem6895914)). Qed.
Lemma lem6895916 : term105 = term57.
Proof. exact (@lem6895866 (@lem6895915)). Qed.
Lemma lem6895917 : term104 = term57.
Proof. exact (TRANS (@lem6895832) (@lem6895916)). Qed.
Lemma lem6895919 (x : real) : (term76 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6895920 : term57 = term31.
Proof. exact (@lem6895919 term31). Qed.
Lemma lem6895921 : term104 = term31.
Proof. exact (TRANS (@lem6895917) (@lem6895920)). Qed.
Lemma lem6895922 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6895923 : term123 = term118.
Proof. exact (MK_COMB (@lem6895922) (@lem6895921)). Qed.
Lemma lem6895924 (_92033 : int) : (real_of_int _92033) = (real_of_int _92033).
Proof. exact (eq_refl (real_of_int _92033)). Qed.
Lemma lem6895925 (_92033 : int) : (term101 _92033) = (term124 _92033).
Proof. exact (MK_COMB (@lem6895923) (@lem6895924 _92033)). Qed.
Lemma lem6895926 (_92033 : int) : (term100 _92033) = (term124 _92033).
Proof. exact (TRANS (@lem6895823 _92033) (@lem6895925 _92033)). Qed.
Lemma lem6895927 (_92033 : int) : (term124 _92033) = term31.
Proof. exact (@lem1982719 (real_of_int _92033)). Qed.
Lemma lem6895928 (_92033 : int) : (term100 _92033) = term31.
Proof. exact (TRANS (@lem6895926 _92033) (@lem6895927 _92033)). Qed.
Lemma lem6895929 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6895930 (_92033 : int) : (term125 _92033) = term126.
Proof. exact (MK_COMB (@lem6895929) (@lem6895928 _92033)). Qed.
Lemma lem6895932 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6895933 : term60 = term61.
Proof. exact (@lem6895932 term8). Qed.
Lemma lem6895935 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6895936 : term60 = term61.
Proof. exact (@lem6895935 term8). Qed.
Lemma lem6895937 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6895938 : term102 = term103.
Proof. exact (MK_COMB (@lem6895937) (@lem6895936)). Qed.
Lemma lem6895939 : term903 = term904.
Proof. exact (MK_COMB (@lem6895938) (@lem6895933)). Qed.
Lemma lem6895940 : term905.
Proof. exact (@lem1981473 term60 term43 term60 term43 term906 term43). Qed.
Lemma lem6895942 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895943 : term108 = term109.
Proof. exact (@lem6895942 (NUMERAL 0) term8). Qed.
Lemma lem6895944 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895945 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895946 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895945 h1) (fun h1 : term109 = True => @lem6895944)). Qed.
Lemma lem6895947 : term109 = True.
Proof. exact (EQ_MP (@lem6895946) (@lem6895944)). Qed.
Lemma lem6895948 : term108 = True.
Proof. exact (TRANS (@lem6895943) (@lem6895947)). Qed.
Lemma lem6895949 : True = term108.
Proof. exact (SYM (@lem6895948)). Qed.
Lemma lem6895950 : term108.
Proof. exact (EQ_MP (@lem6895949) (@lem0)). Qed.
Lemma lem6895951 : term907.
Proof. exact (@lem6895940 (@lem6895950)). Qed.
Lemma lem6895953 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895954 : term108 = term109.
Proof. exact (@lem6895953 (NUMERAL 0) term8). Qed.
Lemma lem6895955 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895956 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895957 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895956 h1) (fun h1 : term109 = True => @lem6895955)). Qed.
Lemma lem6895958 : term109 = True.
Proof. exact (EQ_MP (@lem6895957) (@lem6895955)). Qed.
Lemma lem6895959 : term108 = True.
Proof. exact (TRANS (@lem6895954) (@lem6895958)). Qed.
Lemma lem6895960 : True = term108.
Proof. exact (SYM (@lem6895959)). Qed.
Lemma lem6895961 : term108.
Proof. exact (EQ_MP (@lem6895960) (@lem0)). Qed.
Lemma lem6895962 : term908.
Proof. exact (@lem6895951 (@lem6895961)). Qed.
Lemma lem6895964 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6895965 : term108 = term109.
Proof. exact (@lem6895964 (NUMERAL 0) term8). Qed.
Lemma lem6895966 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6895967 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6895968 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6895967 h1) (fun h1 : term109 = True => @lem6895966)). Qed.
Lemma lem6895969 : term109 = True.
Proof. exact (EQ_MP (@lem6895968) (@lem6895966)). Qed.
Lemma lem6895970 : term108 = True.
Proof. exact (TRANS (@lem6895965) (@lem6895969)). Qed.
Lemma lem6895971 : True = term108.
Proof. exact (SYM (@lem6895970)). Qed.
Lemma lem6895972 : term108.
Proof. exact (EQ_MP (@lem6895971) (@lem0)). Qed.
Lemma lem6895973 : term909.
Proof. exact (@lem6895962 (@lem6895972)). Qed.
Lemma lem6895975 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6895976 : term87 = term92.
Proof. exact (@lem6895975 term8 term8). Qed.
Lemma lem6895977 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6895978 : term72 = term8.
Proof. exact (EQ_MP (@lem6895977) (@lem940073)). Qed.
Lemma lem6895979 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6895980 : term70 = term43.
Proof. exact (MK_COMB (@lem6895979) (@lem6895978)). Qed.
Lemma lem6895981 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6895982 : term92 = term60.
Proof. exact (MK_COMB (@lem6895981) (@lem6895980)). Qed.
Lemma lem6895983 : term87 = term60.
Proof. exact (TRANS (@lem6895976) (@lem6895982)). Qed.
Lemma lem6895985 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6895986 : term87 = term92.
Proof. exact (@lem6895985 term8 term8). Qed.
Lemma lem6895987 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6895988 : term72 = term8.
Proof. exact (EQ_MP (@lem6895987) (@lem940073)). Qed.
Lemma lem6895989 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6895990 : term70 = term43.
Proof. exact (MK_COMB (@lem6895989) (@lem6895988)). Qed.
Lemma lem6895991 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6895992 : term92 = term60.
Proof. exact (MK_COMB (@lem6895991) (@lem6895990)). Qed.
Lemma lem6895993 : term87 = term60.
Proof. exact (TRANS (@lem6895986) (@lem6895992)). Qed.
Lemma lem6895994 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6895995 : term114 = term102.
Proof. exact (MK_COMB (@lem6895994) (@lem6895993)). Qed.
Lemma lem6895996 : term910 = term903.
Proof. exact (MK_COMB (@lem6895995) (@lem6895983)). Qed.
Lemma lem6895997 : term903 = term911.
Proof. exact (@lem1367763 term8 term8). Qed.
Lemma lem6895998 : term912 = term913.
Proof. exact (@lem706885). Qed.
Lemma lem6895999 : (term912 = term913) = (term914 = term915).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term913). Qed.
Lemma lem6896000 : term914 = term915.
Proof. exact (EQ_MP (@lem6895999) (@lem6895998)). Qed.
Lemma lem6896001 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6896002 : term916 = term917.
Proof. exact (MK_COMB (@lem6896001) (@lem6896000)). Qed.
Lemma lem6896003 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6896004 : term911 = term906.
Proof. exact (MK_COMB (@lem6896003) (@lem6896002)). Qed.
Lemma lem6896005 : term903 = term906.
Proof. exact (TRANS (@lem6895997) (@lem6896004)). Qed.
Lemma lem6896006 : term910 = term906.
Proof. exact (TRANS (@lem6895996) (@lem6896005)). Qed.
Lemma lem6896007 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6896008 : term918 = term919.
Proof. exact (MK_COMB (@lem6896007) (@lem6896006)). Qed.
Lemma lem6896009 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem6896010 : term920 = term921.
Proof. exact (MK_COMB (@lem6896008) (@lem6896009)). Qed.
Lemma lem6896012 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6896013 : term921 = term922.
Proof. exact (@lem6896012 term915 term8). Qed.
Lemma lem6896014 : term923 = term913.
Proof. exact (@lem996237 term913). Qed.
Lemma lem6896015 : (term923 = term913) = (term924 = term915).
Proof. exact (@lem1007663 term913 (BIT1 0) term913). Qed.
Lemma lem6896016 : term924 = term915.
Proof. exact (EQ_MP (@lem6896015) (@lem6896014)). Qed.
Lemma lem6896017 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6896018 : term925 = term917.
Proof. exact (MK_COMB (@lem6896017) (@lem6896016)). Qed.
Lemma lem6896019 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6896020 : term922 = term906.
Proof. exact (MK_COMB (@lem6896019) (@lem6896018)). Qed.
Lemma lem6896021 : term921 = term906.
Proof. exact (TRANS (@lem6896013) (@lem6896020)). Qed.
Lemma lem6896022 : term920 = term906.
Proof. exact (TRANS (@lem6896010) (@lem6896021)). Qed.
Lemma lem6896024 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6896025 : term69 = term70.
Proof. exact (@lem6896024 term8 term8). Qed.
Lemma lem6896026 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6896027 : term72 = term8.
Proof. exact (EQ_MP (@lem6896026) (@lem940073)). Qed.
Lemma lem6896028 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6896029 : term70 = term43.
Proof. exact (MK_COMB (@lem6896028) (@lem6896027)). Qed.
Lemma lem6896030 : term69 = term43.
Proof. exact (TRANS (@lem6896025) (@lem6896029)). Qed.
Lemma lem6896031 : term919 = term919.
Proof. exact (eq_refl term919). Qed.
Lemma lem6896032 : term926 = term921.
Proof. exact (MK_COMB (@lem6896031) (@lem6896030)). Qed.
Lemma lem6896034 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6896035 : term921 = term922.
Proof. exact (@lem6896034 term915 term8). Qed.
Lemma lem6896036 : term923 = term913.
Proof. exact (@lem996237 term913). Qed.
Lemma lem6896037 : (term923 = term913) = (term924 = term915).
Proof. exact (@lem1007663 term913 (BIT1 0) term913). Qed.
Lemma lem6896038 : term924 = term915.
Proof. exact (EQ_MP (@lem6896037) (@lem6896036)). Qed.
Lemma lem6896039 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6896040 : term925 = term917.
Proof. exact (MK_COMB (@lem6896039) (@lem6896038)). Qed.
Lemma lem6896041 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6896042 : term922 = term906.
Proof. exact (MK_COMB (@lem6896041) (@lem6896040)). Qed.
Lemma lem6896043 : term921 = term906.
Proof. exact (TRANS (@lem6896035) (@lem6896042)). Qed.
Lemma lem6896044 : term926 = term906.
Proof. exact (TRANS (@lem6896032) (@lem6896043)). Qed.
Lemma lem6896045 : term906 = term926.
Proof. exact (SYM (@lem6896044)). Qed.
Lemma lem6896046 : term920 = term926.
Proof. exact (TRANS (@lem6896022) (@lem6896045)). Qed.
Lemma lem6896047 : term904 = term927.
Proof. exact (@lem6895973 (@lem6896046)). Qed.
Lemma lem6896048 : term903 = term927.
Proof. exact (TRANS (@lem6895939) (@lem6896047)). Qed.
Lemma lem6896050 (x : real) : (term76 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6896051 : term927 = term906.
Proof. exact (@lem6896050 term906). Qed.
Lemma lem6896052 : term903 = term906.
Proof. exact (TRANS (@lem6896048) (@lem6896051)). Qed.
Lemma lem6896053 (_92033 : int) : (term902 _92033) = term928.
Proof. exact (MK_COMB (@lem6895930 _92033) (@lem6896052)). Qed.
Lemma lem6896054 (_92033 : int) : (term901 _92033) = term928.
Proof. exact (TRANS (@lem6895822 _92033) (@lem6896053 _92033)). Qed.
Lemma lem6896055 : term928 = term906.
Proof. exact (@lem1982721 term906). Qed.
Lemma lem6896056 (_92033 : int) : (term901 _92033) = term906.
Proof. exact (TRANS (@lem6896054 _92033) (@lem6896055)). Qed.
Lemma lem6896057 (_92032 : int) (_92033 : int) : (term897 _92032 _92033) = term928.
Proof. exact (MK_COMB (@lem6895821 _92032) (@lem6896056 _92033)). Qed.
Lemma lem6896058 (_92032 : int) (_92033 : int) : (term896 _92032 _92033) = term928.
Proof. exact (TRANS (@lem6895713 _92032 _92033) (@lem6896057 _92032 _92033)). Qed.
Lemma lem6896059 : term928 = term906.
Proof. exact (@lem1982721 term906). Qed.
Lemma lem6896060 (_92032 : int) (_92033 : int) : (term896 _92032 _92033) = term906.
Proof. exact (TRANS (@lem6896058 _92032 _92033) (@lem6896059)). Qed.
Lemma lem6896061 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6896062 (_92032 : int) (_92033 : int) : (term929 _92032 _92033) = term930.
Proof. exact (MK_COMB (@lem6896061) (@lem6896060 _92032 _92033)). Qed.
Lemma lem6896063 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6896064 (_92032 : int) (_92033 : int) : (term895 _92032 _92033) = term931.
Proof. exact (MK_COMB (@lem6896062 _92032 _92033) (@lem6896063)). Qed.
Lemma lem6896065 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term939 _92034 _92032 _92033) : term931.
Proof. exact (EQ_MP (@lem6896064 _92032 _92033) (@lem6895712 _92034 _92032 _92033 h1)). Qed.
Lemma lem6896067 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6896068 : term931 = term932.
Proof. exact (@lem6896067 term31 term906). Qed.
Lemma lem6896070 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6896071 : term906 = term927.
Proof. exact (@lem6896070 term915). Qed.
Lemma lem6896073 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6896074 : term31 = term57.
Proof. exact (@lem6896073 (NUMERAL 0)). Qed.
Lemma lem6896075 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6896076 : term33 = term134.
Proof. exact (MK_COMB (@lem6896075) (@lem6896074)). Qed.
Lemma lem6896077 : term932 = term933.
Proof. exact (MK_COMB (@lem6896076) (@lem6896071)). Qed.
Lemma lem6896078 : term934.
Proof. exact (@lem1980026 term31 term43 term906 term43). Qed.
Lemma lem6896080 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896081 : term108 = term109.
Proof. exact (@lem6896080 (NUMERAL 0) term8). Qed.
Lemma lem6896082 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896083 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896084 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896083 h1) (fun h1 : term109 = True => @lem6896082)). Qed.
Lemma lem6896085 : term109 = True.
Proof. exact (EQ_MP (@lem6896084) (@lem6896082)). Qed.
Lemma lem6896086 : term108 = True.
Proof. exact (TRANS (@lem6896081) (@lem6896085)). Qed.
Lemma lem6896087 : True = term108.
Proof. exact (SYM (@lem6896086)). Qed.
Lemma lem6896088 : term108.
Proof. exact (EQ_MP (@lem6896087) (@lem0)). Qed.
Lemma lem6896089 : term935.
Proof. exact (@lem6896078 (@lem6896088)). Qed.
Lemma lem6896091 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896092 : term108 = term109.
Proof. exact (@lem6896091 (NUMERAL 0) term8). Qed.
Lemma lem6896093 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896094 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896095 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896094 h1) (fun h1 : term109 = True => @lem6896093)). Qed.
Lemma lem6896096 : term109 = True.
Proof. exact (EQ_MP (@lem6896095) (@lem6896093)). Qed.
Lemma lem6896097 : term108 = True.
Proof. exact (TRANS (@lem6896092) (@lem6896096)). Qed.
Lemma lem6896098 : True = term108.
Proof. exact (SYM (@lem6896097)). Qed.
Lemma lem6896099 : term108.
Proof. exact (EQ_MP (@lem6896098) (@lem0)). Qed.
Lemma lem6896100 : term933 = term936.
Proof. exact (@lem6896089 (@lem6896099)). Qed.
Lemma lem6896102 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6896103 : term921 = term922.
Proof. exact (@lem6896102 term915 term8). Qed.
Lemma lem6896104 : term923 = term913.
Proof. exact (@lem996237 term913). Qed.
Lemma lem6896105 : (term923 = term913) = (term924 = term915).
Proof. exact (@lem1007663 term913 (BIT1 0) term913). Qed.
Lemma lem6896106 : term924 = term915.
Proof. exact (EQ_MP (@lem6896105) (@lem6896104)). Qed.
Lemma lem6896107 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6896108 : term925 = term917.
Proof. exact (MK_COMB (@lem6896107) (@lem6896106)). Qed.
Lemma lem6896109 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6896110 : term922 = term906.
Proof. exact (MK_COMB (@lem6896109) (@lem6896108)). Qed.
Lemma lem6896111 : term921 = term906.
Proof. exact (TRANS (@lem6896103) (@lem6896110)). Qed.
Lemma lem6896113 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6896114 : term120 = term31.
Proof. exact (@lem6896113 term8). Qed.
Lemma lem6896115 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6896116 : term139 = term33.
Proof. exact (MK_COMB (@lem6896115) (@lem6896114)). Qed.
Lemma lem6896117 : term936 = term932.
Proof. exact (MK_COMB (@lem6896116) (@lem6896111)). Qed.
Lemma lem6896119 (m : nat) (n : nat) : (term140 m n) = (term141 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6896120 : term932 = term937.
Proof. exact (@lem6896119 (NUMERAL 0) term915). Qed.
Lemma lem6896121 : term938 = term913.
Proof. exact (@lem912803). Qed.
Lemma lem6896122 (h1 : term938 = term913) : (term915 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term913 h1). Qed.
Lemma lem6896123 : (term938 = term913) = ((term915 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term938 = term913 => @lem6896122 h1) (fun h1 : (term915 = (NUMERAL 0)) = False => @lem6896121)). Qed.
Lemma lem6896124 : (term915 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6896123) (@lem6896121)). Qed.
Lemma lem6896125 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6896126 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6896127 : term143 = (and True).
Proof. exact (MK_COMB (@lem6896126) (@lem6896125)). Qed.
Lemma lem6896128 : term937 = (True /\ False).
Proof. exact (MK_COMB (@lem6896127) (@lem6896124)). Qed.
Lemma lem6896130 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6896131 : term937 = False.
Proof. exact (TRANS (@lem6896128) (@lem6896130)). Qed.
Lemma lem6896132 : term932 = False.
Proof. exact (TRANS (@lem6896120) (@lem6896131)). Qed.
Lemma lem6896133 : term936 = False.
Proof. exact (TRANS (@lem6896117) (@lem6896132)). Qed.
Lemma lem6896134 : term933 = False.
Proof. exact (TRANS (@lem6896100) (@lem6896133)). Qed.
Lemma lem6896135 : term932 = False.
Proof. exact (TRANS (@lem6896077) (@lem6896134)). Qed.
Lemma lem6896136 : term931 = False.
Proof. exact (TRANS (@lem6896068) (@lem6896135)). Qed.
Lemma lem6896137 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term939 _92034 _92032 _92033) : False.
Proof. exact (EQ_MP (@lem6896136) (@lem6896065 _92034 _92032 _92033 h1)). Qed.
Lemma lem6896138 (_92034 : int) (_92032 : int) (_92033 : int) (h1 : term867 _92034 _92032 _92033) : False.
Proof. exact (or_elim (@lem6894951 _92034 _92032 _92033 h1) (fun h0 : term873 _92034 _92032 _92033 => @lem6895544 _92034 _92032 _92033 h0) (fun h0 : term939 _92034 _92032 _92033 => @lem6896137 _92034 _92032 _92033 h0)). Qed.
Lemma lem6896139 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term863 A _92034 f j dom neut _92032 _92033) : term863 A _92034 f j dom neut _92032 _92033.
Proof. exact (h1). Qed.
Lemma lem6896140 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term940 A _92034 f j dom neut _92032 _92033) : term940 A _92034 f j dom neut _92032 _92033.
Proof. exact (h1). Qed.
Lemma lem6896141 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term940 A _92034 f j dom neut _92032 _92033) : term864 A _92034 f j dom neut _92032 _92033.
Proof. exact (proj2 (@lem6896140 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896143 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term940 A _92034 f j dom neut _92032 _92033) : term851 A _92034 f j dom neut _92032 _92033.
Proof. exact (proj2 (@lem6896141 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896145 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term940 A _92034 f j dom neut _92032 _92033) : term838 A _92034 f j dom neut _92032 _92033.
Proof. exact (proj2 (@lem6896143 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896147 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term940 A _92034 f j dom neut _92032 _92033) : term805 _92032 _92033.
Proof. exact (proj2 (@lem6896145 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896148 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term940 A _92034 f j dom neut _92032 _92033) : term816 A _92033 _92032 _92034 f j dom neut.
Proof. exact (proj1 (@lem6896145 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896149 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term940 A _92034 f j dom neut _92032 _92033) : term814 A _92033 _92032 _92034 f j dom neut.
Proof. exact (proj2 (@lem6896148 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896152 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term940 A _92034 f j dom neut _92032 _92033) : term802 _92033 _92032 _92034.
Proof. exact (proj1 (@lem6896149 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896154 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term940 A _92034 f j dom neut _92032 _92033) : term793 _92032 _92033.
Proof. exact (proj1 (@lem6896152 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896156 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6896157 : term874 = term108.
Proof. exact (@lem6896156 term31 term43). Qed.
Lemma lem6896159 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6896160 : term43 = term86.
Proof. exact (@lem6896159 term8). Qed.
Lemma lem6896162 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6896163 : term31 = term57.
Proof. exact (@lem6896162 (NUMERAL 0)). Qed.
Lemma lem6896164 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6896165 : term875 = term876.
Proof. exact (MK_COMB (@lem6896164) (@lem6896163)). Qed.
Lemma lem6896166 : term108 = term877.
Proof. exact (MK_COMB (@lem6896165) (@lem6896160)). Qed.
Lemma lem6896167 : term878.
Proof. exact (@lem1980255 term31 term43 term43 term43). Qed.
Lemma lem6896169 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896170 : term108 = term109.
Proof. exact (@lem6896169 (NUMERAL 0) term8). Qed.
Lemma lem6896171 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896172 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896173 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896172 h1) (fun h1 : term109 = True => @lem6896171)). Qed.
Lemma lem6896174 : term109 = True.
Proof. exact (EQ_MP (@lem6896173) (@lem6896171)). Qed.
Lemma lem6896175 : term108 = True.
Proof. exact (TRANS (@lem6896170) (@lem6896174)). Qed.
Lemma lem6896176 : True = term108.
Proof. exact (SYM (@lem6896175)). Qed.
Lemma lem6896177 : term108.
Proof. exact (EQ_MP (@lem6896176) (@lem0)). Qed.
Lemma lem6896178 : term879.
Proof. exact (@lem6896167 (@lem6896177)). Qed.
Lemma lem6896180 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896181 : term108 = term109.
Proof. exact (@lem6896180 (NUMERAL 0) term8). Qed.
Lemma lem6896182 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896183 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896184 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896183 h1) (fun h1 : term109 = True => @lem6896182)). Qed.
Lemma lem6896185 : term109 = True.
Proof. exact (EQ_MP (@lem6896184) (@lem6896182)). Qed.
Lemma lem6896186 : term108 = True.
Proof. exact (TRANS (@lem6896181) (@lem6896185)). Qed.
Lemma lem6896187 : True = term108.
Proof. exact (SYM (@lem6896186)). Qed.
Lemma lem6896188 : term108.
Proof. exact (EQ_MP (@lem6896187) (@lem0)). Qed.
Lemma lem6896189 : term877 = term880.
Proof. exact (@lem6896178 (@lem6896188)). Qed.
Lemma lem6896191 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6896192 : term69 = term70.
Proof. exact (@lem6896191 term8 term8). Qed.
Lemma lem6896193 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6896194 : term72 = term8.
Proof. exact (EQ_MP (@lem6896193) (@lem940073)). Qed.
Lemma lem6896195 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6896196 : term70 = term43.
Proof. exact (MK_COMB (@lem6896195) (@lem6896194)). Qed.
Lemma lem6896197 : term69 = term43.
Proof. exact (TRANS (@lem6896192) (@lem6896196)). Qed.
Lemma lem6896199 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6896200 : term120 = term31.
Proof. exact (@lem6896199 term8). Qed.
Lemma lem6896201 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6896202 : term881 = term875.
Proof. exact (MK_COMB (@lem6896201) (@lem6896200)). Qed.
Lemma lem6896203 : term880 = term108.
Proof. exact (MK_COMB (@lem6896202) (@lem6896197)). Qed.
Lemma lem6896205 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896206 : term108 = term109.
Proof. exact (@lem6896205 (NUMERAL 0) term8). Qed.
Lemma lem6896207 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896208 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896209 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896208 h1) (fun h1 : term109 = True => @lem6896207)). Qed.
Lemma lem6896210 : term109 = True.
Proof. exact (EQ_MP (@lem6896209) (@lem6896207)). Qed.
Lemma lem6896211 : term108 = True.
Proof. exact (TRANS (@lem6896206) (@lem6896210)). Qed.
Lemma lem6896212 : term880 = True.
Proof. exact (TRANS (@lem6896203) (@lem6896211)). Qed.
Lemma lem6896213 : term877 = True.
Proof. exact (TRANS (@lem6896189) (@lem6896212)). Qed.
Lemma lem6896214 : term108 = True.
Proof. exact (TRANS (@lem6896166) (@lem6896213)). Qed.
Lemma lem6896215 : term874 = True.
Proof. exact (TRANS (@lem6896157) (@lem6896214)). Qed.
Lemma lem6896216 : True = term874.
Proof. exact (SYM (@lem6896215)). Qed.
Lemma lem6896217 : term874.
Proof. exact (EQ_MP (@lem6896216) (@lem0)). Qed.
Lemma lem6896218 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term940 A _92034 f j dom neut _92032 _92033) : term888 _92032 _92033.
Proof. exact (conj (@lem6896217) (@lem6896147 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896220 (x : real) (y : real) : term883 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6896221 (_92032 : int) (_92033 : int) : term889 _92032 _92033.
Proof. exact (@lem6896220 term43 (term803 _92032 _92033)). Qed.
Lemma lem6896222 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term940 A _92034 f j dom neut _92032 _92033) : term890 _92032 _92033.
Proof. exact (@lem6896221 _92032 _92033 (@lem6896218 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896223 (_92032 : int) (_92033 : int) : (term891 _92032 _92033) = (term803 _92032 _92033).
Proof. exact (@lem1982733 (term803 _92032 _92033)). Qed.
Lemma lem6896224 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6896225 (_92032 : int) (_92033 : int) : (term892 _92032 _92033) = (term804 _92032 _92033).
Proof. exact (MK_COMB (@lem6896224) (@lem6896223 _92032 _92033)). Qed.
Lemma lem6896226 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6896227 (_92032 : int) (_92033 : int) : (term890 _92032 _92033) = (term805 _92032 _92033).
Proof. exact (MK_COMB (@lem6896225 _92032 _92033) (@lem6896226)). Qed.
Lemma lem6896228 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term940 A _92034 f j dom neut _92032 _92033) : term805 _92032 _92033.
Proof. exact (EQ_MP (@lem6896227 _92032 _92033) (@lem6896222 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896230 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6896231 : term874 = term108.
Proof. exact (@lem6896230 term31 term43). Qed.
Lemma lem6896233 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6896234 : term43 = term86.
Proof. exact (@lem6896233 term8). Qed.
Lemma lem6896236 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6896237 : term31 = term57.
Proof. exact (@lem6896236 (NUMERAL 0)). Qed.
Lemma lem6896238 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6896239 : term875 = term876.
Proof. exact (MK_COMB (@lem6896238) (@lem6896237)). Qed.
Lemma lem6896240 : term108 = term877.
Proof. exact (MK_COMB (@lem6896239) (@lem6896234)). Qed.
Lemma lem6896241 : term878.
Proof. exact (@lem1980255 term31 term43 term43 term43). Qed.
Lemma lem6896243 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896244 : term108 = term109.
Proof. exact (@lem6896243 (NUMERAL 0) term8). Qed.
Lemma lem6896245 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896246 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896247 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896246 h1) (fun h1 : term109 = True => @lem6896245)). Qed.
Lemma lem6896248 : term109 = True.
Proof. exact (EQ_MP (@lem6896247) (@lem6896245)). Qed.
Lemma lem6896249 : term108 = True.
Proof. exact (TRANS (@lem6896244) (@lem6896248)). Qed.
Lemma lem6896250 : True = term108.
Proof. exact (SYM (@lem6896249)). Qed.
Lemma lem6896251 : term108.
Proof. exact (EQ_MP (@lem6896250) (@lem0)). Qed.
Lemma lem6896252 : term879.
Proof. exact (@lem6896241 (@lem6896251)). Qed.
Lemma lem6896254 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896255 : term108 = term109.
Proof. exact (@lem6896254 (NUMERAL 0) term8). Qed.
Lemma lem6896256 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896257 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896258 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896257 h1) (fun h1 : term109 = True => @lem6896256)). Qed.
Lemma lem6896259 : term109 = True.
Proof. exact (EQ_MP (@lem6896258) (@lem6896256)). Qed.
Lemma lem6896260 : term108 = True.
Proof. exact (TRANS (@lem6896255) (@lem6896259)). Qed.
Lemma lem6896261 : True = term108.
Proof. exact (SYM (@lem6896260)). Qed.
Lemma lem6896262 : term108.
Proof. exact (EQ_MP (@lem6896261) (@lem0)). Qed.
Lemma lem6896263 : term877 = term880.
Proof. exact (@lem6896252 (@lem6896262)). Qed.
Lemma lem6896265 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6896266 : term69 = term70.
Proof. exact (@lem6896265 term8 term8). Qed.
Lemma lem6896267 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6896268 : term72 = term8.
Proof. exact (EQ_MP (@lem6896267) (@lem940073)). Qed.
Lemma lem6896269 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6896270 : term70 = term43.
Proof. exact (MK_COMB (@lem6896269) (@lem6896268)). Qed.
Lemma lem6896271 : term69 = term43.
Proof. exact (TRANS (@lem6896266) (@lem6896270)). Qed.
Lemma lem6896273 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6896274 : term120 = term31.
Proof. exact (@lem6896273 term8). Qed.
Lemma lem6896275 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6896276 : term881 = term875.
Proof. exact (MK_COMB (@lem6896275) (@lem6896274)). Qed.
Lemma lem6896277 : term880 = term108.
Proof. exact (MK_COMB (@lem6896276) (@lem6896271)). Qed.
Lemma lem6896279 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896280 : term108 = term109.
Proof. exact (@lem6896279 (NUMERAL 0) term8). Qed.
Lemma lem6896281 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896282 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896283 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896282 h1) (fun h1 : term109 = True => @lem6896281)). Qed.
Lemma lem6896284 : term109 = True.
Proof. exact (EQ_MP (@lem6896283) (@lem6896281)). Qed.
Lemma lem6896285 : term108 = True.
Proof. exact (TRANS (@lem6896280) (@lem6896284)). Qed.
Lemma lem6896286 : term880 = True.
Proof. exact (TRANS (@lem6896277) (@lem6896285)). Qed.
Lemma lem6896287 : term877 = True.
Proof. exact (TRANS (@lem6896263) (@lem6896286)). Qed.
Lemma lem6896288 : term108 = True.
Proof. exact (TRANS (@lem6896240) (@lem6896287)). Qed.
Lemma lem6896289 : term874 = True.
Proof. exact (TRANS (@lem6896231) (@lem6896288)). Qed.
Lemma lem6896290 : True = term874.
Proof. exact (SYM (@lem6896289)). Qed.
Lemma lem6896291 : term874.
Proof. exact (EQ_MP (@lem6896290) (@lem0)). Qed.
Lemma lem6896292 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term940 A _92034 f j dom neut _92032 _92033) : term882 _92032 _92033.
Proof. exact (conj (@lem6896291) (@lem6896154 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896294 (x : real) (y : real) : term883 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6896295 (_92032 : int) (_92033 : int) : term884 _92032 _92033.
Proof. exact (@lem6896294 term43 (term790 _92032 _92033)). Qed.
Lemma lem6896296 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term940 A _92034 f j dom neut _92032 _92033) : term885 _92032 _92033.
Proof. exact (@lem6896295 _92032 _92033 (@lem6896292 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896297 (_92032 : int) (_92033 : int) : (term886 _92032 _92033) = (term790 _92032 _92033).
Proof. exact (@lem1982733 (term790 _92032 _92033)). Qed.
Lemma lem6896298 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6896299 (_92032 : int) (_92033 : int) : (term887 _92032 _92033) = (term792 _92032 _92033).
Proof. exact (MK_COMB (@lem6896298) (@lem6896297 _92032 _92033)). Qed.
Lemma lem6896300 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6896301 (_92032 : int) (_92033 : int) : (term885 _92032 _92033) = (term793 _92032 _92033).
Proof. exact (MK_COMB (@lem6896299 _92032 _92033) (@lem6896300)). Qed.
Lemma lem6896302 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term940 A _92034 f j dom neut _92032 _92033) : term793 _92032 _92033.
Proof. exact (EQ_MP (@lem6896301 _92032 _92033) (@lem6896296 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896303 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term940 A _92034 f j dom neut _92032 _92033) : term941 _92032 _92033.
Proof. exact (conj (@lem6896302 A _92034 f j dom neut _92032 _92033 h1) (@lem6896228 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896305 (x : real) (y : real) : term893 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem6896306 (_92032 : int) (_92033 : int) : term942 _92032 _92033.
Proof. exact (@lem6896305 (term790 _92032 _92033) (term803 _92032 _92033)). Qed.
Lemma lem6896307 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term940 A _92034 f j dom neut _92032 _92033) : term943 _92032 _92033.
Proof. exact (@lem6896306 _92032 _92033 (@lem6896303 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896308 (_92032 : int) (_92033 : int) : (term944 _92032 _92033) = (term945 _92032 _92033).
Proof. exact (@lem1982753 (real_of_int _92032) (term99 _92032) (term96 _92033) (term898 _92033)). Qed.
Lemma lem6896309 (_92032 : int) : (term100 _92032) = (term101 _92032).
Proof. exact (@lem1982715 term60 (real_of_int _92032)). Qed.
Lemma lem6896311 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6896312 : term43 = term86.
Proof. exact (@lem6896311 term8). Qed.
Lemma lem6896314 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6896315 : term60 = term61.
Proof. exact (@lem6896314 term8). Qed.
Lemma lem6896316 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6896317 : term102 = term103.
Proof. exact (MK_COMB (@lem6896316) (@lem6896315)). Qed.
Lemma lem6896318 : term104 = term105.
Proof. exact (MK_COMB (@lem6896317) (@lem6896312)). Qed.
Lemma lem6896319 : term106.
Proof. exact (@lem1981473 term60 term43 term43 term43 term31 term43). Qed.
Lemma lem6896321 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896322 : term108 = term109.
Proof. exact (@lem6896321 (NUMERAL 0) term8). Qed.
Lemma lem6896323 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896324 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896325 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896324 h1) (fun h1 : term109 = True => @lem6896323)). Qed.
Lemma lem6896326 : term109 = True.
Proof. exact (EQ_MP (@lem6896325) (@lem6896323)). Qed.
Lemma lem6896327 : term108 = True.
Proof. exact (TRANS (@lem6896322) (@lem6896326)). Qed.
Lemma lem6896328 : True = term108.
Proof. exact (SYM (@lem6896327)). Qed.
Lemma lem6896329 : term108.
Proof. exact (EQ_MP (@lem6896328) (@lem0)). Qed.
Lemma lem6896330 : term111.
Proof. exact (@lem6896319 (@lem6896329)). Qed.
Lemma lem6896332 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896333 : term108 = term109.
Proof. exact (@lem6896332 (NUMERAL 0) term8). Qed.
Lemma lem6896334 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896335 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896336 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896335 h1) (fun h1 : term109 = True => @lem6896334)). Qed.
Lemma lem6896337 : term109 = True.
Proof. exact (EQ_MP (@lem6896336) (@lem6896334)). Qed.
Lemma lem6896338 : term108 = True.
Proof. exact (TRANS (@lem6896333) (@lem6896337)). Qed.
Lemma lem6896339 : True = term108.
Proof. exact (SYM (@lem6896338)). Qed.
Lemma lem6896340 : term108.
Proof. exact (EQ_MP (@lem6896339) (@lem0)). Qed.
Lemma lem6896341 : term112.
Proof. exact (@lem6896330 (@lem6896340)). Qed.
Lemma lem6896343 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896344 : term108 = term109.
Proof. exact (@lem6896343 (NUMERAL 0) term8). Qed.
Lemma lem6896345 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896346 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896347 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896346 h1) (fun h1 : term109 = True => @lem6896345)). Qed.
Lemma lem6896348 : term109 = True.
Proof. exact (EQ_MP (@lem6896347) (@lem6896345)). Qed.
Lemma lem6896349 : term108 = True.
Proof. exact (TRANS (@lem6896344) (@lem6896348)). Qed.
Lemma lem6896350 : True = term108.
Proof. exact (SYM (@lem6896349)). Qed.
Lemma lem6896351 : term108.
Proof. exact (EQ_MP (@lem6896350) (@lem0)). Qed.
Lemma lem6896352 : term113.
Proof. exact (@lem6896341 (@lem6896351)). Qed.
Lemma lem6896354 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6896355 : term69 = term70.
Proof. exact (@lem6896354 term8 term8). Qed.
Lemma lem6896356 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6896357 : term72 = term8.
Proof. exact (EQ_MP (@lem6896356) (@lem940073)). Qed.
Lemma lem6896358 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6896359 : term70 = term43.
Proof. exact (MK_COMB (@lem6896358) (@lem6896357)). Qed.
Lemma lem6896360 : term69 = term43.
Proof. exact (TRANS (@lem6896355) (@lem6896359)). Qed.
Lemma lem6896362 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6896363 : term87 = term92.
Proof. exact (@lem6896362 term8 term8). Qed.
Lemma lem6896364 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6896365 : term72 = term8.
Proof. exact (EQ_MP (@lem6896364) (@lem940073)). Qed.
Lemma lem6896366 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6896367 : term70 = term43.
Proof. exact (MK_COMB (@lem6896366) (@lem6896365)). Qed.
Lemma lem6896368 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6896369 : term92 = term60.
Proof. exact (MK_COMB (@lem6896368) (@lem6896367)). Qed.
Lemma lem6896370 : term87 = term60.
Proof. exact (TRANS (@lem6896363) (@lem6896369)). Qed.
Lemma lem6896371 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6896372 : term114 = term102.
Proof. exact (MK_COMB (@lem6896371) (@lem6896370)). Qed.
Lemma lem6896373 : term115 = term104.
Proof. exact (MK_COMB (@lem6896372) (@lem6896360)). Qed.
Lemma lem6896375 (m : nat) : (term116 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6896376 : term104 = term31.
Proof. exact (@lem6896375 term8). Qed.
Lemma lem6896377 : term115 = term31.
Proof. exact (TRANS (@lem6896373) (@lem6896376)). Qed.
Lemma lem6896378 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6896379 : term117 = term118.
Proof. exact (MK_COMB (@lem6896378) (@lem6896377)). Qed.
Lemma lem6896380 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem6896381 : term119 = term120.
Proof. exact (MK_COMB (@lem6896379) (@lem6896380)). Qed.
Lemma lem6896383 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6896384 : term120 = term31.
Proof. exact (@lem6896383 term8). Qed.
Lemma lem6896385 : term119 = term31.
Proof. exact (TRANS (@lem6896381) (@lem6896384)). Qed.
Lemma lem6896387 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6896388 : term69 = term70.
Proof. exact (@lem6896387 term8 term8). Qed.
Lemma lem6896389 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6896390 : term72 = term8.
Proof. exact (EQ_MP (@lem6896389) (@lem940073)). Qed.
Lemma lem6896391 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6896392 : term70 = term43.
Proof. exact (MK_COMB (@lem6896391) (@lem6896390)). Qed.
Lemma lem6896393 : term69 = term43.
Proof. exact (TRANS (@lem6896388) (@lem6896392)). Qed.
Lemma lem6896394 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem6896395 : term122 = term120.
Proof. exact (MK_COMB (@lem6896394) (@lem6896393)). Qed.
Lemma lem6896397 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6896398 : term120 = term31.
Proof. exact (@lem6896397 term8). Qed.
Lemma lem6896399 : term122 = term31.
Proof. exact (TRANS (@lem6896395) (@lem6896398)). Qed.
Lemma lem6896400 : term31 = term122.
Proof. exact (SYM (@lem6896399)). Qed.
Lemma lem6896401 : term119 = term122.
Proof. exact (TRANS (@lem6896385) (@lem6896400)). Qed.
Lemma lem6896402 : term105 = term57.
Proof. exact (@lem6896352 (@lem6896401)). Qed.
Lemma lem6896403 : term104 = term57.
Proof. exact (TRANS (@lem6896318) (@lem6896402)). Qed.
Lemma lem6896405 (x : real) : (term76 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6896406 : term57 = term31.
Proof. exact (@lem6896405 term31). Qed.
Lemma lem6896407 : term104 = term31.
Proof. exact (TRANS (@lem6896403) (@lem6896406)). Qed.
Lemma lem6896408 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6896409 : term123 = term118.
Proof. exact (MK_COMB (@lem6896408) (@lem6896407)). Qed.
Lemma lem6896410 (_92032 : int) : (real_of_int _92032) = (real_of_int _92032).
Proof. exact (eq_refl (real_of_int _92032)). Qed.
Lemma lem6896411 (_92032 : int) : (term101 _92032) = (term124 _92032).
Proof. exact (MK_COMB (@lem6896409) (@lem6896410 _92032)). Qed.
Lemma lem6896412 (_92032 : int) : (term100 _92032) = (term124 _92032).
Proof. exact (TRANS (@lem6896309 _92032) (@lem6896411 _92032)). Qed.
Lemma lem6896413 (_92032 : int) : (term124 _92032) = term31.
Proof. exact (@lem1982719 (real_of_int _92032)). Qed.
Lemma lem6896414 (_92032 : int) : (term100 _92032) = term31.
Proof. exact (TRANS (@lem6896412 _92032) (@lem6896413 _92032)). Qed.
Lemma lem6896415 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6896416 (_92032 : int) : (term125 _92032) = term126.
Proof. exact (MK_COMB (@lem6896415) (@lem6896414 _92032)). Qed.
Lemma lem6896417 (_92033 : int) : (term946 _92033) = (term947 _92033).
Proof. exact (@lem1982753 (term99 _92033) (real_of_int _92033) term60 term60). Qed.
Lemma lem6896418 (_92033 : int) : (term899 _92033) = (term101 _92033).
Proof. exact (@lem1982713 term60 (real_of_int _92033)). Qed.
Lemma lem6896420 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6896421 : term43 = term86.
Proof. exact (@lem6896420 term8). Qed.
Lemma lem6896423 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6896424 : term60 = term61.
Proof. exact (@lem6896423 term8). Qed.
Lemma lem6896425 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6896426 : term102 = term103.
Proof. exact (MK_COMB (@lem6896425) (@lem6896424)). Qed.
Lemma lem6896427 : term104 = term105.
Proof. exact (MK_COMB (@lem6896426) (@lem6896421)). Qed.
Lemma lem6896428 : term106.
Proof. exact (@lem1981473 term60 term43 term43 term43 term31 term43). Qed.
Lemma lem6896430 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896431 : term108 = term109.
Proof. exact (@lem6896430 (NUMERAL 0) term8). Qed.
Lemma lem6896432 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896433 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896434 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896433 h1) (fun h1 : term109 = True => @lem6896432)). Qed.
Lemma lem6896435 : term109 = True.
Proof. exact (EQ_MP (@lem6896434) (@lem6896432)). Qed.
Lemma lem6896436 : term108 = True.
Proof. exact (TRANS (@lem6896431) (@lem6896435)). Qed.
Lemma lem6896437 : True = term108.
Proof. exact (SYM (@lem6896436)). Qed.
Lemma lem6896438 : term108.
Proof. exact (EQ_MP (@lem6896437) (@lem0)). Qed.
Lemma lem6896439 : term111.
Proof. exact (@lem6896428 (@lem6896438)). Qed.
Lemma lem6896441 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896442 : term108 = term109.
Proof. exact (@lem6896441 (NUMERAL 0) term8). Qed.
Lemma lem6896443 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896444 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896445 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896444 h1) (fun h1 : term109 = True => @lem6896443)). Qed.
Lemma lem6896446 : term109 = True.
Proof. exact (EQ_MP (@lem6896445) (@lem6896443)). Qed.
Lemma lem6896447 : term108 = True.
Proof. exact (TRANS (@lem6896442) (@lem6896446)). Qed.
Lemma lem6896448 : True = term108.
Proof. exact (SYM (@lem6896447)). Qed.
Lemma lem6896449 : term108.
Proof. exact (EQ_MP (@lem6896448) (@lem0)). Qed.
Lemma lem6896450 : term112.
Proof. exact (@lem6896439 (@lem6896449)). Qed.
Lemma lem6896452 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896453 : term108 = term109.
Proof. exact (@lem6896452 (NUMERAL 0) term8). Qed.
Lemma lem6896454 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896455 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896456 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896455 h1) (fun h1 : term109 = True => @lem6896454)). Qed.
Lemma lem6896457 : term109 = True.
Proof. exact (EQ_MP (@lem6896456) (@lem6896454)). Qed.
Lemma lem6896458 : term108 = True.
Proof. exact (TRANS (@lem6896453) (@lem6896457)). Qed.
Lemma lem6896459 : True = term108.
Proof. exact (SYM (@lem6896458)). Qed.
Lemma lem6896460 : term108.
Proof. exact (EQ_MP (@lem6896459) (@lem0)). Qed.
Lemma lem6896461 : term113.
Proof. exact (@lem6896450 (@lem6896460)). Qed.
Lemma lem6896463 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6896464 : term69 = term70.
Proof. exact (@lem6896463 term8 term8). Qed.
Lemma lem6896465 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6896466 : term72 = term8.
Proof. exact (EQ_MP (@lem6896465) (@lem940073)). Qed.
Lemma lem6896467 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6896468 : term70 = term43.
Proof. exact (MK_COMB (@lem6896467) (@lem6896466)). Qed.
Lemma lem6896469 : term69 = term43.
Proof. exact (TRANS (@lem6896464) (@lem6896468)). Qed.
Lemma lem6896471 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6896472 : term87 = term92.
Proof. exact (@lem6896471 term8 term8). Qed.
Lemma lem6896473 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6896474 : term72 = term8.
Proof. exact (EQ_MP (@lem6896473) (@lem940073)). Qed.
Lemma lem6896475 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6896476 : term70 = term43.
Proof. exact (MK_COMB (@lem6896475) (@lem6896474)). Qed.
Lemma lem6896477 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6896478 : term92 = term60.
Proof. exact (MK_COMB (@lem6896477) (@lem6896476)). Qed.
Lemma lem6896479 : term87 = term60.
Proof. exact (TRANS (@lem6896472) (@lem6896478)). Qed.
Lemma lem6896480 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6896481 : term114 = term102.
Proof. exact (MK_COMB (@lem6896480) (@lem6896479)). Qed.
Lemma lem6896482 : term115 = term104.
Proof. exact (MK_COMB (@lem6896481) (@lem6896469)). Qed.
Lemma lem6896484 (m : nat) : (term116 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6896485 : term104 = term31.
Proof. exact (@lem6896484 term8). Qed.
Lemma lem6896486 : term115 = term31.
Proof. exact (TRANS (@lem6896482) (@lem6896485)). Qed.
Lemma lem6896487 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6896488 : term117 = term118.
Proof. exact (MK_COMB (@lem6896487) (@lem6896486)). Qed.
Lemma lem6896489 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem6896490 : term119 = term120.
Proof. exact (MK_COMB (@lem6896488) (@lem6896489)). Qed.
Lemma lem6896492 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6896493 : term120 = term31.
Proof. exact (@lem6896492 term8). Qed.
Lemma lem6896494 : term119 = term31.
Proof. exact (TRANS (@lem6896490) (@lem6896493)). Qed.
Lemma lem6896496 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6896497 : term69 = term70.
Proof. exact (@lem6896496 term8 term8). Qed.
Lemma lem6896498 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6896499 : term72 = term8.
Proof. exact (EQ_MP (@lem6896498) (@lem940073)). Qed.
Lemma lem6896500 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6896501 : term70 = term43.
Proof. exact (MK_COMB (@lem6896500) (@lem6896499)). Qed.
Lemma lem6896502 : term69 = term43.
Proof. exact (TRANS (@lem6896497) (@lem6896501)). Qed.
Lemma lem6896503 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem6896504 : term122 = term120.
Proof. exact (MK_COMB (@lem6896503) (@lem6896502)). Qed.
Lemma lem6896506 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6896507 : term120 = term31.
Proof. exact (@lem6896506 term8). Qed.
Lemma lem6896508 : term122 = term31.
Proof. exact (TRANS (@lem6896504) (@lem6896507)). Qed.
Lemma lem6896509 : term31 = term122.
Proof. exact (SYM (@lem6896508)). Qed.
Lemma lem6896510 : term119 = term122.
Proof. exact (TRANS (@lem6896494) (@lem6896509)). Qed.
Lemma lem6896511 : term105 = term57.
Proof. exact (@lem6896461 (@lem6896510)). Qed.
Lemma lem6896512 : term104 = term57.
Proof. exact (TRANS (@lem6896427) (@lem6896511)). Qed.
Lemma lem6896514 (x : real) : (term76 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6896515 : term57 = term31.
Proof. exact (@lem6896514 term31). Qed.
Lemma lem6896516 : term104 = term31.
Proof. exact (TRANS (@lem6896512) (@lem6896515)). Qed.
Lemma lem6896517 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6896518 : term123 = term118.
Proof. exact (MK_COMB (@lem6896517) (@lem6896516)). Qed.
Lemma lem6896519 (_92033 : int) : (real_of_int _92033) = (real_of_int _92033).
Proof. exact (eq_refl (real_of_int _92033)). Qed.
Lemma lem6896520 (_92033 : int) : (term101 _92033) = (term124 _92033).
Proof. exact (MK_COMB (@lem6896518) (@lem6896519 _92033)). Qed.
Lemma lem6896521 (_92033 : int) : (term899 _92033) = (term124 _92033).
Proof. exact (TRANS (@lem6896418 _92033) (@lem6896520 _92033)). Qed.
Lemma lem6896522 (_92033 : int) : (term124 _92033) = term31.
Proof. exact (@lem1982719 (real_of_int _92033)). Qed.
Lemma lem6896523 (_92033 : int) : (term899 _92033) = term31.
Proof. exact (TRANS (@lem6896521 _92033) (@lem6896522 _92033)). Qed.
Lemma lem6896524 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6896525 (_92033 : int) : (term900 _92033) = term126.
Proof. exact (MK_COMB (@lem6896524) (@lem6896523 _92033)). Qed.
Lemma lem6896527 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6896528 : term60 = term61.
Proof. exact (@lem6896527 term8). Qed.
Lemma lem6896530 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6896531 : term60 = term61.
Proof. exact (@lem6896530 term8). Qed.
Lemma lem6896532 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6896533 : term102 = term103.
Proof. exact (MK_COMB (@lem6896532) (@lem6896531)). Qed.
Lemma lem6896534 : term903 = term904.
Proof. exact (MK_COMB (@lem6896533) (@lem6896528)). Qed.
Lemma lem6896535 : term905.
Proof. exact (@lem1981473 term60 term43 term60 term43 term906 term43). Qed.
Lemma lem6896537 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896538 : term108 = term109.
Proof. exact (@lem6896537 (NUMERAL 0) term8). Qed.
Lemma lem6896539 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896540 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896541 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896540 h1) (fun h1 : term109 = True => @lem6896539)). Qed.
Lemma lem6896542 : term109 = True.
Proof. exact (EQ_MP (@lem6896541) (@lem6896539)). Qed.
Lemma lem6896543 : term108 = True.
Proof. exact (TRANS (@lem6896538) (@lem6896542)). Qed.
Lemma lem6896544 : True = term108.
Proof. exact (SYM (@lem6896543)). Qed.
Lemma lem6896545 : term108.
Proof. exact (EQ_MP (@lem6896544) (@lem0)). Qed.
Lemma lem6896546 : term907.
Proof. exact (@lem6896535 (@lem6896545)). Qed.
Lemma lem6896548 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896549 : term108 = term109.
Proof. exact (@lem6896548 (NUMERAL 0) term8). Qed.
Lemma lem6896550 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896551 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896552 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896551 h1) (fun h1 : term109 = True => @lem6896550)). Qed.
Lemma lem6896553 : term109 = True.
Proof. exact (EQ_MP (@lem6896552) (@lem6896550)). Qed.
Lemma lem6896554 : term108 = True.
Proof. exact (TRANS (@lem6896549) (@lem6896553)). Qed.
Lemma lem6896555 : True = term108.
Proof. exact (SYM (@lem6896554)). Qed.
Lemma lem6896556 : term108.
Proof. exact (EQ_MP (@lem6896555) (@lem0)). Qed.
Lemma lem6896557 : term908.
Proof. exact (@lem6896546 (@lem6896556)). Qed.
Lemma lem6896559 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896560 : term108 = term109.
Proof. exact (@lem6896559 (NUMERAL 0) term8). Qed.
Lemma lem6896561 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896562 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896563 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896562 h1) (fun h1 : term109 = True => @lem6896561)). Qed.
Lemma lem6896564 : term109 = True.
Proof. exact (EQ_MP (@lem6896563) (@lem6896561)). Qed.
Lemma lem6896565 : term108 = True.
Proof. exact (TRANS (@lem6896560) (@lem6896564)). Qed.
Lemma lem6896566 : True = term108.
Proof. exact (SYM (@lem6896565)). Qed.
Lemma lem6896567 : term108.
Proof. exact (EQ_MP (@lem6896566) (@lem0)). Qed.
Lemma lem6896568 : term909.
Proof. exact (@lem6896557 (@lem6896567)). Qed.
Lemma lem6896570 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6896571 : term87 = term92.
Proof. exact (@lem6896570 term8 term8). Qed.
Lemma lem6896572 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6896573 : term72 = term8.
Proof. exact (EQ_MP (@lem6896572) (@lem940073)). Qed.
Lemma lem6896574 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6896575 : term70 = term43.
Proof. exact (MK_COMB (@lem6896574) (@lem6896573)). Qed.
Lemma lem6896576 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6896577 : term92 = term60.
Proof. exact (MK_COMB (@lem6896576) (@lem6896575)). Qed.
Lemma lem6896578 : term87 = term60.
Proof. exact (TRANS (@lem6896571) (@lem6896577)). Qed.
Lemma lem6896580 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6896581 : term87 = term92.
Proof. exact (@lem6896580 term8 term8). Qed.
Lemma lem6896582 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6896583 : term72 = term8.
Proof. exact (EQ_MP (@lem6896582) (@lem940073)). Qed.
Lemma lem6896584 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6896585 : term70 = term43.
Proof. exact (MK_COMB (@lem6896584) (@lem6896583)). Qed.
Lemma lem6896586 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6896587 : term92 = term60.
Proof. exact (MK_COMB (@lem6896586) (@lem6896585)). Qed.
Lemma lem6896588 : term87 = term60.
Proof. exact (TRANS (@lem6896581) (@lem6896587)). Qed.
Lemma lem6896589 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6896590 : term114 = term102.
Proof. exact (MK_COMB (@lem6896589) (@lem6896588)). Qed.
Lemma lem6896591 : term910 = term903.
Proof. exact (MK_COMB (@lem6896590) (@lem6896578)). Qed.
Lemma lem6896592 : term903 = term911.
Proof. exact (@lem1367763 term8 term8). Qed.
Lemma lem6896593 : term912 = term913.
Proof. exact (@lem706885). Qed.
Lemma lem6896594 : (term912 = term913) = (term914 = term915).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term913). Qed.
Lemma lem6896595 : term914 = term915.
Proof. exact (EQ_MP (@lem6896594) (@lem6896593)). Qed.
Lemma lem6896596 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6896597 : term916 = term917.
Proof. exact (MK_COMB (@lem6896596) (@lem6896595)). Qed.
Lemma lem6896598 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6896599 : term911 = term906.
Proof. exact (MK_COMB (@lem6896598) (@lem6896597)). Qed.
Lemma lem6896600 : term903 = term906.
Proof. exact (TRANS (@lem6896592) (@lem6896599)). Qed.
Lemma lem6896601 : term910 = term906.
Proof. exact (TRANS (@lem6896591) (@lem6896600)). Qed.
Lemma lem6896602 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6896603 : term918 = term919.
Proof. exact (MK_COMB (@lem6896602) (@lem6896601)). Qed.
Lemma lem6896604 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem6896605 : term920 = term921.
Proof. exact (MK_COMB (@lem6896603) (@lem6896604)). Qed.
Lemma lem6896607 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6896608 : term921 = term922.
Proof. exact (@lem6896607 term915 term8). Qed.
Lemma lem6896609 : term923 = term913.
Proof. exact (@lem996237 term913). Qed.
Lemma lem6896610 : (term923 = term913) = (term924 = term915).
Proof. exact (@lem1007663 term913 (BIT1 0) term913). Qed.
Lemma lem6896611 : term924 = term915.
Proof. exact (EQ_MP (@lem6896610) (@lem6896609)). Qed.
Lemma lem6896612 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6896613 : term925 = term917.
Proof. exact (MK_COMB (@lem6896612) (@lem6896611)). Qed.
Lemma lem6896614 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6896615 : term922 = term906.
Proof. exact (MK_COMB (@lem6896614) (@lem6896613)). Qed.
Lemma lem6896616 : term921 = term906.
Proof. exact (TRANS (@lem6896608) (@lem6896615)). Qed.
Lemma lem6896617 : term920 = term906.
Proof. exact (TRANS (@lem6896605) (@lem6896616)). Qed.
Lemma lem6896619 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6896620 : term69 = term70.
Proof. exact (@lem6896619 term8 term8). Qed.
Lemma lem6896621 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6896622 : term72 = term8.
Proof. exact (EQ_MP (@lem6896621) (@lem940073)). Qed.
Lemma lem6896623 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6896624 : term70 = term43.
Proof. exact (MK_COMB (@lem6896623) (@lem6896622)). Qed.
Lemma lem6896625 : term69 = term43.
Proof. exact (TRANS (@lem6896620) (@lem6896624)). Qed.
Lemma lem6896626 : term919 = term919.
Proof. exact (eq_refl term919). Qed.
Lemma lem6896627 : term926 = term921.
Proof. exact (MK_COMB (@lem6896626) (@lem6896625)). Qed.
Lemma lem6896629 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6896630 : term921 = term922.
Proof. exact (@lem6896629 term915 term8). Qed.
Lemma lem6896631 : term923 = term913.
Proof. exact (@lem996237 term913). Qed.
Lemma lem6896632 : (term923 = term913) = (term924 = term915).
Proof. exact (@lem1007663 term913 (BIT1 0) term913). Qed.
Lemma lem6896633 : term924 = term915.
Proof. exact (EQ_MP (@lem6896632) (@lem6896631)). Qed.
Lemma lem6896634 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6896635 : term925 = term917.
Proof. exact (MK_COMB (@lem6896634) (@lem6896633)). Qed.
Lemma lem6896636 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6896637 : term922 = term906.
Proof. exact (MK_COMB (@lem6896636) (@lem6896635)). Qed.
Lemma lem6896638 : term921 = term906.
Proof. exact (TRANS (@lem6896630) (@lem6896637)). Qed.
Lemma lem6896639 : term926 = term906.
Proof. exact (TRANS (@lem6896627) (@lem6896638)). Qed.
Lemma lem6896640 : term906 = term926.
Proof. exact (SYM (@lem6896639)). Qed.
Lemma lem6896641 : term920 = term926.
Proof. exact (TRANS (@lem6896617) (@lem6896640)). Qed.
Lemma lem6896642 : term904 = term927.
Proof. exact (@lem6896568 (@lem6896641)). Qed.
Lemma lem6896643 : term903 = term927.
Proof. exact (TRANS (@lem6896534) (@lem6896642)). Qed.
Lemma lem6896645 (x : real) : (term76 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6896646 : term927 = term906.
Proof. exact (@lem6896645 term906). Qed.
Lemma lem6896647 : term903 = term906.
Proof. exact (TRANS (@lem6896643) (@lem6896646)). Qed.
Lemma lem6896648 (_92033 : int) : (term947 _92033) = term928.
Proof. exact (MK_COMB (@lem6896525 _92033) (@lem6896647)). Qed.
Lemma lem6896649 (_92033 : int) : (term946 _92033) = term928.
Proof. exact (TRANS (@lem6896417 _92033) (@lem6896648 _92033)). Qed.
Lemma lem6896650 : term928 = term906.
Proof. exact (@lem1982721 term906). Qed.
Lemma lem6896651 (_92033 : int) : (term946 _92033) = term906.
Proof. exact (TRANS (@lem6896649 _92033) (@lem6896650)). Qed.
Lemma lem6896652 (_92032 : int) (_92033 : int) : (term945 _92032 _92033) = term928.
Proof. exact (MK_COMB (@lem6896416 _92032) (@lem6896651 _92033)). Qed.
Lemma lem6896653 (_92032 : int) (_92033 : int) : (term944 _92032 _92033) = term928.
Proof. exact (TRANS (@lem6896308 _92032 _92033) (@lem6896652 _92032 _92033)). Qed.
Lemma lem6896654 : term928 = term906.
Proof. exact (@lem1982721 term906). Qed.
Lemma lem6896655 (_92032 : int) (_92033 : int) : (term944 _92032 _92033) = term906.
Proof. exact (TRANS (@lem6896653 _92032 _92033) (@lem6896654)). Qed.
Lemma lem6896656 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6896657 (_92032 : int) (_92033 : int) : (term948 _92032 _92033) = term930.
Proof. exact (MK_COMB (@lem6896656) (@lem6896655 _92032 _92033)). Qed.
Lemma lem6896658 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6896659 (_92032 : int) (_92033 : int) : (term943 _92032 _92033) = term931.
Proof. exact (MK_COMB (@lem6896657 _92032 _92033) (@lem6896658)). Qed.
Lemma lem6896660 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term940 A _92034 f j dom neut _92032 _92033) : term931.
Proof. exact (EQ_MP (@lem6896659 _92032 _92033) (@lem6896307 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896662 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6896663 : term931 = term932.
Proof. exact (@lem6896662 term31 term906). Qed.
Lemma lem6896665 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6896666 : term906 = term927.
Proof. exact (@lem6896665 term915). Qed.
Lemma lem6896668 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6896669 : term31 = term57.
Proof. exact (@lem6896668 (NUMERAL 0)). Qed.
Lemma lem6896670 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6896671 : term33 = term134.
Proof. exact (MK_COMB (@lem6896670) (@lem6896669)). Qed.
Lemma lem6896672 : term932 = term933.
Proof. exact (MK_COMB (@lem6896671) (@lem6896666)). Qed.
Lemma lem6896673 : term934.
Proof. exact (@lem1980026 term31 term43 term906 term43). Qed.
Lemma lem6896675 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896676 : term108 = term109.
Proof. exact (@lem6896675 (NUMERAL 0) term8). Qed.
Lemma lem6896677 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896678 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896679 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896678 h1) (fun h1 : term109 = True => @lem6896677)). Qed.
Lemma lem6896680 : term109 = True.
Proof. exact (EQ_MP (@lem6896679) (@lem6896677)). Qed.
Lemma lem6896681 : term108 = True.
Proof. exact (TRANS (@lem6896676) (@lem6896680)). Qed.
Lemma lem6896682 : True = term108.
Proof. exact (SYM (@lem6896681)). Qed.
Lemma lem6896683 : term108.
Proof. exact (EQ_MP (@lem6896682) (@lem0)). Qed.
Lemma lem6896684 : term935.
Proof. exact (@lem6896673 (@lem6896683)). Qed.
Lemma lem6896686 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896687 : term108 = term109.
Proof. exact (@lem6896686 (NUMERAL 0) term8). Qed.
Lemma lem6896688 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896689 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896690 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896689 h1) (fun h1 : term109 = True => @lem6896688)). Qed.
Lemma lem6896691 : term109 = True.
Proof. exact (EQ_MP (@lem6896690) (@lem6896688)). Qed.
Lemma lem6896692 : term108 = True.
Proof. exact (TRANS (@lem6896687) (@lem6896691)). Qed.
Lemma lem6896693 : True = term108.
Proof. exact (SYM (@lem6896692)). Qed.
Lemma lem6896694 : term108.
Proof. exact (EQ_MP (@lem6896693) (@lem0)). Qed.
Lemma lem6896695 : term933 = term936.
Proof. exact (@lem6896684 (@lem6896694)). Qed.
Lemma lem6896697 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6896698 : term921 = term922.
Proof. exact (@lem6896697 term915 term8). Qed.
Lemma lem6896699 : term923 = term913.
Proof. exact (@lem996237 term913). Qed.
Lemma lem6896700 : (term923 = term913) = (term924 = term915).
Proof. exact (@lem1007663 term913 (BIT1 0) term913). Qed.
Lemma lem6896701 : term924 = term915.
Proof. exact (EQ_MP (@lem6896700) (@lem6896699)). Qed.
Lemma lem6896702 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6896703 : term925 = term917.
Proof. exact (MK_COMB (@lem6896702) (@lem6896701)). Qed.
Lemma lem6896704 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6896705 : term922 = term906.
Proof. exact (MK_COMB (@lem6896704) (@lem6896703)). Qed.
Lemma lem6896706 : term921 = term906.
Proof. exact (TRANS (@lem6896698) (@lem6896705)). Qed.
Lemma lem6896708 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6896709 : term120 = term31.
Proof. exact (@lem6896708 term8). Qed.
Lemma lem6896710 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6896711 : term139 = term33.
Proof. exact (MK_COMB (@lem6896710) (@lem6896709)). Qed.
Lemma lem6896712 : term936 = term932.
Proof. exact (MK_COMB (@lem6896711) (@lem6896706)). Qed.
Lemma lem6896714 (m : nat) (n : nat) : (term140 m n) = (term141 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6896715 : term932 = term937.
Proof. exact (@lem6896714 (NUMERAL 0) term915). Qed.
Lemma lem6896716 : term938 = term913.
Proof. exact (@lem912803). Qed.
Lemma lem6896717 (h1 : term938 = term913) : (term915 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term913 h1). Qed.
Lemma lem6896718 : (term938 = term913) = ((term915 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term938 = term913 => @lem6896717 h1) (fun h1 : (term915 = (NUMERAL 0)) = False => @lem6896716)). Qed.
Lemma lem6896719 : (term915 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6896718) (@lem6896716)). Qed.
Lemma lem6896720 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6896721 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6896722 : term143 = (and True).
Proof. exact (MK_COMB (@lem6896721) (@lem6896720)). Qed.
Lemma lem6896723 : term937 = (True /\ False).
Proof. exact (MK_COMB (@lem6896722) (@lem6896719)). Qed.
Lemma lem6896725 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6896726 : term937 = False.
Proof. exact (TRANS (@lem6896723) (@lem6896725)). Qed.
Lemma lem6896727 : term932 = False.
Proof. exact (TRANS (@lem6896715) (@lem6896726)). Qed.
Lemma lem6896728 : term936 = False.
Proof. exact (TRANS (@lem6896712) (@lem6896727)). Qed.
Lemma lem6896729 : term933 = False.
Proof. exact (TRANS (@lem6896695) (@lem6896728)). Qed.
Lemma lem6896730 : term932 = False.
Proof. exact (TRANS (@lem6896672) (@lem6896729)). Qed.
Lemma lem6896731 : term931 = False.
Proof. exact (TRANS (@lem6896663) (@lem6896730)). Qed.
Lemma lem6896732 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term940 A _92034 f j dom neut _92032 _92033) : False.
Proof. exact (EQ_MP (@lem6896731) (@lem6896660 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896733 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term949 A _92034 f j dom neut _92032 _92033) : term949 A _92034 f j dom neut _92032 _92033.
Proof. exact (h1). Qed.
Lemma lem6896734 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term949 A _92034 f j dom neut _92032 _92033) : term865 A _92034 f j dom neut _92032 _92033.
Proof. exact (proj2 (@lem6896733 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896736 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term949 A _92034 f j dom neut _92032 _92033) : term852 A _92034 f j dom neut _92032 _92033.
Proof. exact (proj2 (@lem6896734 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896738 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term949 A _92034 f j dom neut _92032 _92033) : term839 A _92034 f j dom neut _92032 _92033.
Proof. exact (proj2 (@lem6896736 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896740 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term949 A _92034 f j dom neut _92032 _92033) : term793 _92032 _92033.
Proof. exact (proj2 (@lem6896738 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896741 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term949 A _92034 f j dom neut _92032 _92033) : term816 A _92033 _92032 _92034 f j dom neut.
Proof. exact (proj1 (@lem6896738 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896743 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term949 A _92034 f j dom neut _92032 _92033) : term800 _92032 _92033.
Proof. exact (proj1 (@lem6896741 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896749 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6896750 : term874 = term108.
Proof. exact (@lem6896749 term31 term43). Qed.
Lemma lem6896752 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6896753 : term43 = term86.
Proof. exact (@lem6896752 term8). Qed.
Lemma lem6896755 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6896756 : term31 = term57.
Proof. exact (@lem6896755 (NUMERAL 0)). Qed.
Lemma lem6896757 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6896758 : term875 = term876.
Proof. exact (MK_COMB (@lem6896757) (@lem6896756)). Qed.
Lemma lem6896759 : term108 = term877.
Proof. exact (MK_COMB (@lem6896758) (@lem6896753)). Qed.
Lemma lem6896760 : term878.
Proof. exact (@lem1980255 term31 term43 term43 term43). Qed.
Lemma lem6896762 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896763 : term108 = term109.
Proof. exact (@lem6896762 (NUMERAL 0) term8). Qed.
Lemma lem6896764 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896765 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896766 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896765 h1) (fun h1 : term109 = True => @lem6896764)). Qed.
Lemma lem6896767 : term109 = True.
Proof. exact (EQ_MP (@lem6896766) (@lem6896764)). Qed.
Lemma lem6896768 : term108 = True.
Proof. exact (TRANS (@lem6896763) (@lem6896767)). Qed.
Lemma lem6896769 : True = term108.
Proof. exact (SYM (@lem6896768)). Qed.
Lemma lem6896770 : term108.
Proof. exact (EQ_MP (@lem6896769) (@lem0)). Qed.
Lemma lem6896771 : term879.
Proof. exact (@lem6896760 (@lem6896770)). Qed.
Lemma lem6896773 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896774 : term108 = term109.
Proof. exact (@lem6896773 (NUMERAL 0) term8). Qed.
Lemma lem6896775 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896776 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896777 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896776 h1) (fun h1 : term109 = True => @lem6896775)). Qed.
Lemma lem6896778 : term109 = True.
Proof. exact (EQ_MP (@lem6896777) (@lem6896775)). Qed.
Lemma lem6896779 : term108 = True.
Proof. exact (TRANS (@lem6896774) (@lem6896778)). Qed.
Lemma lem6896780 : True = term108.
Proof. exact (SYM (@lem6896779)). Qed.
Lemma lem6896781 : term108.
Proof. exact (EQ_MP (@lem6896780) (@lem0)). Qed.
Lemma lem6896782 : term877 = term880.
Proof. exact (@lem6896771 (@lem6896781)). Qed.
Lemma lem6896784 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6896785 : term69 = term70.
Proof. exact (@lem6896784 term8 term8). Qed.
Lemma lem6896786 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6896787 : term72 = term8.
Proof. exact (EQ_MP (@lem6896786) (@lem940073)). Qed.
Lemma lem6896788 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6896789 : term70 = term43.
Proof. exact (MK_COMB (@lem6896788) (@lem6896787)). Qed.
Lemma lem6896790 : term69 = term43.
Proof. exact (TRANS (@lem6896785) (@lem6896789)). Qed.
Lemma lem6896792 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6896793 : term120 = term31.
Proof. exact (@lem6896792 term8). Qed.
Lemma lem6896794 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6896795 : term881 = term875.
Proof. exact (MK_COMB (@lem6896794) (@lem6896793)). Qed.
Lemma lem6896796 : term880 = term108.
Proof. exact (MK_COMB (@lem6896795) (@lem6896790)). Qed.
Lemma lem6896798 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896799 : term108 = term109.
Proof. exact (@lem6896798 (NUMERAL 0) term8). Qed.
Lemma lem6896800 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896801 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896802 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896801 h1) (fun h1 : term109 = True => @lem6896800)). Qed.
Lemma lem6896803 : term109 = True.
Proof. exact (EQ_MP (@lem6896802) (@lem6896800)). Qed.
Lemma lem6896804 : term108 = True.
Proof. exact (TRANS (@lem6896799) (@lem6896803)). Qed.
Lemma lem6896805 : term880 = True.
Proof. exact (TRANS (@lem6896796) (@lem6896804)). Qed.
Lemma lem6896806 : term877 = True.
Proof. exact (TRANS (@lem6896782) (@lem6896805)). Qed.
Lemma lem6896807 : term108 = True.
Proof. exact (TRANS (@lem6896759) (@lem6896806)). Qed.
Lemma lem6896808 : term874 = True.
Proof. exact (TRANS (@lem6896750) (@lem6896807)). Qed.
Lemma lem6896809 : True = term874.
Proof. exact (SYM (@lem6896808)). Qed.
Lemma lem6896810 : term874.
Proof. exact (EQ_MP (@lem6896809) (@lem0)). Qed.
Lemma lem6896811 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term949 A _92034 f j dom neut _92032 _92033) : term882 _92032 _92033.
Proof. exact (conj (@lem6896810) (@lem6896740 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896813 (x : real) (y : real) : term883 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6896814 (_92032 : int) (_92033 : int) : term884 _92032 _92033.
Proof. exact (@lem6896813 term43 (term790 _92032 _92033)). Qed.
Lemma lem6896815 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term949 A _92034 f j dom neut _92032 _92033) : term885 _92032 _92033.
Proof. exact (@lem6896814 _92032 _92033 (@lem6896811 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896816 (_92032 : int) (_92033 : int) : (term886 _92032 _92033) = (term790 _92032 _92033).
Proof. exact (@lem1982733 (term790 _92032 _92033)). Qed.
Lemma lem6896817 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6896818 (_92032 : int) (_92033 : int) : (term887 _92032 _92033) = (term792 _92032 _92033).
Proof. exact (MK_COMB (@lem6896817) (@lem6896816 _92032 _92033)). Qed.
Lemma lem6896819 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6896820 (_92032 : int) (_92033 : int) : (term885 _92032 _92033) = (term793 _92032 _92033).
Proof. exact (MK_COMB (@lem6896818 _92032 _92033) (@lem6896819)). Qed.
Lemma lem6896821 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term949 A _92034 f j dom neut _92032 _92033) : term793 _92032 _92033.
Proof. exact (EQ_MP (@lem6896820 _92032 _92033) (@lem6896815 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896823 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6896824 : term874 = term108.
Proof. exact (@lem6896823 term31 term43). Qed.
Lemma lem6896826 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6896827 : term43 = term86.
Proof. exact (@lem6896826 term8). Qed.
Lemma lem6896829 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6896830 : term31 = term57.
Proof. exact (@lem6896829 (NUMERAL 0)). Qed.
Lemma lem6896831 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6896832 : term875 = term876.
Proof. exact (MK_COMB (@lem6896831) (@lem6896830)). Qed.
Lemma lem6896833 : term108 = term877.
Proof. exact (MK_COMB (@lem6896832) (@lem6896827)). Qed.
Lemma lem6896834 : term878.
Proof. exact (@lem1980255 term31 term43 term43 term43). Qed.
Lemma lem6896836 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896837 : term108 = term109.
Proof. exact (@lem6896836 (NUMERAL 0) term8). Qed.
Lemma lem6896838 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896839 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896840 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896839 h1) (fun h1 : term109 = True => @lem6896838)). Qed.
Lemma lem6896841 : term109 = True.
Proof. exact (EQ_MP (@lem6896840) (@lem6896838)). Qed.
Lemma lem6896842 : term108 = True.
Proof. exact (TRANS (@lem6896837) (@lem6896841)). Qed.
Lemma lem6896843 : True = term108.
Proof. exact (SYM (@lem6896842)). Qed.
Lemma lem6896844 : term108.
Proof. exact (EQ_MP (@lem6896843) (@lem0)). Qed.
Lemma lem6896845 : term879.
Proof. exact (@lem6896834 (@lem6896844)). Qed.
Lemma lem6896847 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896848 : term108 = term109.
Proof. exact (@lem6896847 (NUMERAL 0) term8). Qed.
Lemma lem6896849 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896850 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896851 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896850 h1) (fun h1 : term109 = True => @lem6896849)). Qed.
Lemma lem6896852 : term109 = True.
Proof. exact (EQ_MP (@lem6896851) (@lem6896849)). Qed.
Lemma lem6896853 : term108 = True.
Proof. exact (TRANS (@lem6896848) (@lem6896852)). Qed.
Lemma lem6896854 : True = term108.
Proof. exact (SYM (@lem6896853)). Qed.
Lemma lem6896855 : term108.
Proof. exact (EQ_MP (@lem6896854) (@lem0)). Qed.
Lemma lem6896856 : term877 = term880.
Proof. exact (@lem6896845 (@lem6896855)). Qed.
Lemma lem6896858 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6896859 : term69 = term70.
Proof. exact (@lem6896858 term8 term8). Qed.
Lemma lem6896860 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6896861 : term72 = term8.
Proof. exact (EQ_MP (@lem6896860) (@lem940073)). Qed.
Lemma lem6896862 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6896863 : term70 = term43.
Proof. exact (MK_COMB (@lem6896862) (@lem6896861)). Qed.
Lemma lem6896864 : term69 = term43.
Proof. exact (TRANS (@lem6896859) (@lem6896863)). Qed.
Lemma lem6896866 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6896867 : term120 = term31.
Proof. exact (@lem6896866 term8). Qed.
Lemma lem6896868 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6896869 : term881 = term875.
Proof. exact (MK_COMB (@lem6896868) (@lem6896867)). Qed.
Lemma lem6896870 : term880 = term108.
Proof. exact (MK_COMB (@lem6896869) (@lem6896864)). Qed.
Lemma lem6896872 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896873 : term108 = term109.
Proof. exact (@lem6896872 (NUMERAL 0) term8). Qed.
Lemma lem6896874 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896875 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896876 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896875 h1) (fun h1 : term109 = True => @lem6896874)). Qed.
Lemma lem6896877 : term109 = True.
Proof. exact (EQ_MP (@lem6896876) (@lem6896874)). Qed.
Lemma lem6896878 : term108 = True.
Proof. exact (TRANS (@lem6896873) (@lem6896877)). Qed.
Lemma lem6896879 : term880 = True.
Proof. exact (TRANS (@lem6896870) (@lem6896878)). Qed.
Lemma lem6896880 : term877 = True.
Proof. exact (TRANS (@lem6896856) (@lem6896879)). Qed.
Lemma lem6896881 : term108 = True.
Proof. exact (TRANS (@lem6896833) (@lem6896880)). Qed.
Lemma lem6896882 : term874 = True.
Proof. exact (TRANS (@lem6896824) (@lem6896881)). Qed.
Lemma lem6896883 : True = term874.
Proof. exact (SYM (@lem6896882)). Qed.
Lemma lem6896884 : term874.
Proof. exact (EQ_MP (@lem6896883) (@lem0)). Qed.
Lemma lem6896885 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term949 A _92034 f j dom neut _92032 _92033) : term950 _92032 _92033.
Proof. exact (conj (@lem6896884) (@lem6896743 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896887 (x : real) (y : real) : term883 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6896888 (_92032 : int) (_92033 : int) : term951 _92032 _92033.
Proof. exact (@lem6896887 term43 (term797 _92032 _92033)). Qed.
Lemma lem6896889 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term949 A _92034 f j dom neut _92032 _92033) : term952 _92032 _92033.
Proof. exact (@lem6896888 _92032 _92033 (@lem6896885 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896890 (_92032 : int) (_92033 : int) : (term953 _92032 _92033) = (term797 _92032 _92033).
Proof. exact (@lem1982733 (term797 _92032 _92033)). Qed.
Lemma lem6896891 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6896892 (_92032 : int) (_92033 : int) : (term954 _92032 _92033) = (term799 _92032 _92033).
Proof. exact (MK_COMB (@lem6896891) (@lem6896890 _92032 _92033)). Qed.
Lemma lem6896893 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6896894 (_92032 : int) (_92033 : int) : (term952 _92032 _92033) = (term800 _92032 _92033).
Proof. exact (MK_COMB (@lem6896892 _92032 _92033) (@lem6896893)). Qed.
Lemma lem6896895 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term949 A _92034 f j dom neut _92032 _92033) : term800 _92032 _92033.
Proof. exact (EQ_MP (@lem6896894 _92032 _92033) (@lem6896889 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896896 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term949 A _92034 f j dom neut _92032 _92033) : term955 _92032 _92033.
Proof. exact (conj (@lem6896895 A _92034 f j dom neut _92032 _92033 h1) (@lem6896821 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896898 (x : real) (y : real) : term893 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem6896899 (_92032 : int) (_92033 : int) : term956 _92032 _92033.
Proof. exact (@lem6896898 (term797 _92032 _92033) (term790 _92032 _92033)). Qed.
Lemma lem6896900 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term949 A _92034 f j dom neut _92032 _92033) : term957 _92032 _92033.
Proof. exact (@lem6896899 _92032 _92033 (@lem6896896 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6896901 (_92032 : int) (_92033 : int) : (term958 _92032 _92033) = (term959 _92032 _92033).
Proof. exact (@lem1982753 (term99 _92032) (real_of_int _92032) (real_of_int _92033) (term96 _92033)). Qed.
Lemma lem6896902 (_92032 : int) : (term899 _92032) = (term101 _92032).
Proof. exact (@lem1982713 term60 (real_of_int _92032)). Qed.
Lemma lem6896904 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6896905 : term43 = term86.
Proof. exact (@lem6896904 term8). Qed.
Lemma lem6896907 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6896908 : term60 = term61.
Proof. exact (@lem6896907 term8). Qed.
Lemma lem6896909 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6896910 : term102 = term103.
Proof. exact (MK_COMB (@lem6896909) (@lem6896908)). Qed.
Lemma lem6896911 : term104 = term105.
Proof. exact (MK_COMB (@lem6896910) (@lem6896905)). Qed.
Lemma lem6896912 : term106.
Proof. exact (@lem1981473 term60 term43 term43 term43 term31 term43). Qed.
Lemma lem6896914 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896915 : term108 = term109.
Proof. exact (@lem6896914 (NUMERAL 0) term8). Qed.
Lemma lem6896916 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896917 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896918 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896917 h1) (fun h1 : term109 = True => @lem6896916)). Qed.
Lemma lem6896919 : term109 = True.
Proof. exact (EQ_MP (@lem6896918) (@lem6896916)). Qed.
Lemma lem6896920 : term108 = True.
Proof. exact (TRANS (@lem6896915) (@lem6896919)). Qed.
Lemma lem6896921 : True = term108.
Proof. exact (SYM (@lem6896920)). Qed.
Lemma lem6896922 : term108.
Proof. exact (EQ_MP (@lem6896921) (@lem0)). Qed.
Lemma lem6896923 : term111.
Proof. exact (@lem6896912 (@lem6896922)). Qed.
Lemma lem6896925 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896926 : term108 = term109.
Proof. exact (@lem6896925 (NUMERAL 0) term8). Qed.
Lemma lem6896927 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896928 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896929 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896928 h1) (fun h1 : term109 = True => @lem6896927)). Qed.
Lemma lem6896930 : term109 = True.
Proof. exact (EQ_MP (@lem6896929) (@lem6896927)). Qed.
Lemma lem6896931 : term108 = True.
Proof. exact (TRANS (@lem6896926) (@lem6896930)). Qed.
Lemma lem6896932 : True = term108.
Proof. exact (SYM (@lem6896931)). Qed.
Lemma lem6896933 : term108.
Proof. exact (EQ_MP (@lem6896932) (@lem0)). Qed.
Lemma lem6896934 : term112.
Proof. exact (@lem6896923 (@lem6896933)). Qed.
Lemma lem6896936 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6896937 : term108 = term109.
Proof. exact (@lem6896936 (NUMERAL 0) term8). Qed.
Lemma lem6896938 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6896939 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6896940 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6896939 h1) (fun h1 : term109 = True => @lem6896938)). Qed.
Lemma lem6896941 : term109 = True.
Proof. exact (EQ_MP (@lem6896940) (@lem6896938)). Qed.
Lemma lem6896942 : term108 = True.
Proof. exact (TRANS (@lem6896937) (@lem6896941)). Qed.
Lemma lem6896943 : True = term108.
Proof. exact (SYM (@lem6896942)). Qed.
Lemma lem6896944 : term108.
Proof. exact (EQ_MP (@lem6896943) (@lem0)). Qed.
Lemma lem6896945 : term113.
Proof. exact (@lem6896934 (@lem6896944)). Qed.
Lemma lem6896947 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6896948 : term69 = term70.
Proof. exact (@lem6896947 term8 term8). Qed.
Lemma lem6896949 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6896950 : term72 = term8.
Proof. exact (EQ_MP (@lem6896949) (@lem940073)). Qed.
Lemma lem6896951 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6896952 : term70 = term43.
Proof. exact (MK_COMB (@lem6896951) (@lem6896950)). Qed.
Lemma lem6896953 : term69 = term43.
Proof. exact (TRANS (@lem6896948) (@lem6896952)). Qed.
Lemma lem6896955 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6896956 : term87 = term92.
Proof. exact (@lem6896955 term8 term8). Qed.
Lemma lem6896957 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6896958 : term72 = term8.
Proof. exact (EQ_MP (@lem6896957) (@lem940073)). Qed.
Lemma lem6896959 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6896960 : term70 = term43.
Proof. exact (MK_COMB (@lem6896959) (@lem6896958)). Qed.
Lemma lem6896961 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6896962 : term92 = term60.
Proof. exact (MK_COMB (@lem6896961) (@lem6896960)). Qed.
Lemma lem6896963 : term87 = term60.
Proof. exact (TRANS (@lem6896956) (@lem6896962)). Qed.
Lemma lem6896964 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6896965 : term114 = term102.
Proof. exact (MK_COMB (@lem6896964) (@lem6896963)). Qed.
Lemma lem6896966 : term115 = term104.
Proof. exact (MK_COMB (@lem6896965) (@lem6896953)). Qed.
Lemma lem6896968 (m : nat) : (term116 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6896969 : term104 = term31.
Proof. exact (@lem6896968 term8). Qed.
Lemma lem6896970 : term115 = term31.
Proof. exact (TRANS (@lem6896966) (@lem6896969)). Qed.
Lemma lem6896971 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6896972 : term117 = term118.
Proof. exact (MK_COMB (@lem6896971) (@lem6896970)). Qed.
Lemma lem6896973 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem6896974 : term119 = term120.
Proof. exact (MK_COMB (@lem6896972) (@lem6896973)). Qed.
Lemma lem6896976 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6896977 : term120 = term31.
Proof. exact (@lem6896976 term8). Qed.
Lemma lem6896978 : term119 = term31.
Proof. exact (TRANS (@lem6896974) (@lem6896977)). Qed.
Lemma lem6896980 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6896981 : term69 = term70.
Proof. exact (@lem6896980 term8 term8). Qed.
Lemma lem6896982 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6896983 : term72 = term8.
Proof. exact (EQ_MP (@lem6896982) (@lem940073)). Qed.
Lemma lem6896984 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6896985 : term70 = term43.
Proof. exact (MK_COMB (@lem6896984) (@lem6896983)). Qed.
Lemma lem6896986 : term69 = term43.
Proof. exact (TRANS (@lem6896981) (@lem6896985)). Qed.
Lemma lem6896987 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem6896988 : term122 = term120.
Proof. exact (MK_COMB (@lem6896987) (@lem6896986)). Qed.
Lemma lem6896990 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6896991 : term120 = term31.
Proof. exact (@lem6896990 term8). Qed.
Lemma lem6896992 : term122 = term31.
Proof. exact (TRANS (@lem6896988) (@lem6896991)). Qed.
Lemma lem6896993 : term31 = term122.
Proof. exact (SYM (@lem6896992)). Qed.
Lemma lem6896994 : term119 = term122.
Proof. exact (TRANS (@lem6896978) (@lem6896993)). Qed.
Lemma lem6896995 : term105 = term57.
Proof. exact (@lem6896945 (@lem6896994)). Qed.
Lemma lem6896996 : term104 = term57.
Proof. exact (TRANS (@lem6896911) (@lem6896995)). Qed.
Lemma lem6896998 (x : real) : (term76 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6896999 : term57 = term31.
Proof. exact (@lem6896998 term31). Qed.
Lemma lem6897000 : term104 = term31.
Proof. exact (TRANS (@lem6896996) (@lem6896999)). Qed.
Lemma lem6897001 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6897002 : term123 = term118.
Proof. exact (MK_COMB (@lem6897001) (@lem6897000)). Qed.
Lemma lem6897003 (_92032 : int) : (real_of_int _92032) = (real_of_int _92032).
Proof. exact (eq_refl (real_of_int _92032)). Qed.
Lemma lem6897004 (_92032 : int) : (term101 _92032) = (term124 _92032).
Proof. exact (MK_COMB (@lem6897002) (@lem6897003 _92032)). Qed.
Lemma lem6897005 (_92032 : int) : (term899 _92032) = (term124 _92032).
Proof. exact (TRANS (@lem6896902 _92032) (@lem6897004 _92032)). Qed.
Lemma lem6897006 (_92032 : int) : (term124 _92032) = term31.
Proof. exact (@lem1982719 (real_of_int _92032)). Qed.
Lemma lem6897007 (_92032 : int) : (term899 _92032) = term31.
Proof. exact (TRANS (@lem6897005 _92032) (@lem6897006 _92032)). Qed.
Lemma lem6897008 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6897009 (_92032 : int) : (term900 _92032) = term126.
Proof. exact (MK_COMB (@lem6897008) (@lem6897007 _92032)). Qed.
Lemma lem6897010 (_92033 : int) : (term97 _92033) = (term98 _92033).
Proof. exact (@lem1982763 (real_of_int _92033) (term99 _92033) term60). Qed.
Lemma lem6897011 (_92033 : int) : (term100 _92033) = (term101 _92033).
Proof. exact (@lem1982715 term60 (real_of_int _92033)). Qed.
Lemma lem6897013 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6897014 : term43 = term86.
Proof. exact (@lem6897013 term8). Qed.
Lemma lem6897016 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6897017 : term60 = term61.
Proof. exact (@lem6897016 term8). Qed.
Lemma lem6897018 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6897019 : term102 = term103.
Proof. exact (MK_COMB (@lem6897018) (@lem6897017)). Qed.
Lemma lem6897020 : term104 = term105.
Proof. exact (MK_COMB (@lem6897019) (@lem6897014)). Qed.
Lemma lem6897021 : term106.
Proof. exact (@lem1981473 term60 term43 term43 term43 term31 term43). Qed.
Lemma lem6897023 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6897024 : term108 = term109.
Proof. exact (@lem6897023 (NUMERAL 0) term8). Qed.
Lemma lem6897025 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6897026 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6897027 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6897026 h1) (fun h1 : term109 = True => @lem6897025)). Qed.
Lemma lem6897028 : term109 = True.
Proof. exact (EQ_MP (@lem6897027) (@lem6897025)). Qed.
Lemma lem6897029 : term108 = True.
Proof. exact (TRANS (@lem6897024) (@lem6897028)). Qed.
Lemma lem6897030 : True = term108.
Proof. exact (SYM (@lem6897029)). Qed.
Lemma lem6897031 : term108.
Proof. exact (EQ_MP (@lem6897030) (@lem0)). Qed.
Lemma lem6897032 : term111.
Proof. exact (@lem6897021 (@lem6897031)). Qed.
Lemma lem6897034 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6897035 : term108 = term109.
Proof. exact (@lem6897034 (NUMERAL 0) term8). Qed.
Lemma lem6897036 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6897037 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6897038 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6897037 h1) (fun h1 : term109 = True => @lem6897036)). Qed.
Lemma lem6897039 : term109 = True.
Proof. exact (EQ_MP (@lem6897038) (@lem6897036)). Qed.
Lemma lem6897040 : term108 = True.
Proof. exact (TRANS (@lem6897035) (@lem6897039)). Qed.
Lemma lem6897041 : True = term108.
Proof. exact (SYM (@lem6897040)). Qed.
Lemma lem6897042 : term108.
Proof. exact (EQ_MP (@lem6897041) (@lem0)). Qed.
Lemma lem6897043 : term112.
Proof. exact (@lem6897032 (@lem6897042)). Qed.
Lemma lem6897045 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6897046 : term108 = term109.
Proof. exact (@lem6897045 (NUMERAL 0) term8). Qed.
Lemma lem6897047 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6897048 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6897049 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6897048 h1) (fun h1 : term109 = True => @lem6897047)). Qed.
Lemma lem6897050 : term109 = True.
Proof. exact (EQ_MP (@lem6897049) (@lem6897047)). Qed.
Lemma lem6897051 : term108 = True.
Proof. exact (TRANS (@lem6897046) (@lem6897050)). Qed.
Lemma lem6897052 : True = term108.
Proof. exact (SYM (@lem6897051)). Qed.
Lemma lem6897053 : term108.
Proof. exact (EQ_MP (@lem6897052) (@lem0)). Qed.
Lemma lem6897054 : term113.
Proof. exact (@lem6897043 (@lem6897053)). Qed.
Lemma lem6897056 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6897057 : term69 = term70.
Proof. exact (@lem6897056 term8 term8). Qed.
Lemma lem6897058 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6897059 : term72 = term8.
Proof. exact (EQ_MP (@lem6897058) (@lem940073)). Qed.
Lemma lem6897060 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6897061 : term70 = term43.
Proof. exact (MK_COMB (@lem6897060) (@lem6897059)). Qed.
Lemma lem6897062 : term69 = term43.
Proof. exact (TRANS (@lem6897057) (@lem6897061)). Qed.
Lemma lem6897064 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6897065 : term87 = term92.
Proof. exact (@lem6897064 term8 term8). Qed.
Lemma lem6897066 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6897067 : term72 = term8.
Proof. exact (EQ_MP (@lem6897066) (@lem940073)). Qed.
Lemma lem6897068 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6897069 : term70 = term43.
Proof. exact (MK_COMB (@lem6897068) (@lem6897067)). Qed.
Lemma lem6897070 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6897071 : term92 = term60.
Proof. exact (MK_COMB (@lem6897070) (@lem6897069)). Qed.
Lemma lem6897072 : term87 = term60.
Proof. exact (TRANS (@lem6897065) (@lem6897071)). Qed.
Lemma lem6897073 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6897074 : term114 = term102.
Proof. exact (MK_COMB (@lem6897073) (@lem6897072)). Qed.
Lemma lem6897075 : term115 = term104.
Proof. exact (MK_COMB (@lem6897074) (@lem6897062)). Qed.
Lemma lem6897077 (m : nat) : (term116 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6897078 : term104 = term31.
Proof. exact (@lem6897077 term8). Qed.
Lemma lem6897079 : term115 = term31.
Proof. exact (TRANS (@lem6897075) (@lem6897078)). Qed.
Lemma lem6897080 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6897081 : term117 = term118.
Proof. exact (MK_COMB (@lem6897080) (@lem6897079)). Qed.
Lemma lem6897082 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem6897083 : term119 = term120.
Proof. exact (MK_COMB (@lem6897081) (@lem6897082)). Qed.
Lemma lem6897085 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6897086 : term120 = term31.
Proof. exact (@lem6897085 term8). Qed.
Lemma lem6897087 : term119 = term31.
Proof. exact (TRANS (@lem6897083) (@lem6897086)). Qed.
Lemma lem6897089 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6897090 : term69 = term70.
Proof. exact (@lem6897089 term8 term8). Qed.
Lemma lem6897091 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6897092 : term72 = term8.
Proof. exact (EQ_MP (@lem6897091) (@lem940073)). Qed.
Lemma lem6897093 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6897094 : term70 = term43.
Proof. exact (MK_COMB (@lem6897093) (@lem6897092)). Qed.
Lemma lem6897095 : term69 = term43.
Proof. exact (TRANS (@lem6897090) (@lem6897094)). Qed.
Lemma lem6897096 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem6897097 : term122 = term120.
Proof. exact (MK_COMB (@lem6897096) (@lem6897095)). Qed.
Lemma lem6897099 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6897100 : term120 = term31.
Proof. exact (@lem6897099 term8). Qed.
Lemma lem6897101 : term122 = term31.
Proof. exact (TRANS (@lem6897097) (@lem6897100)). Qed.
Lemma lem6897102 : term31 = term122.
Proof. exact (SYM (@lem6897101)). Qed.
Lemma lem6897103 : term119 = term122.
Proof. exact (TRANS (@lem6897087) (@lem6897102)). Qed.
Lemma lem6897104 : term105 = term57.
Proof. exact (@lem6897054 (@lem6897103)). Qed.
Lemma lem6897105 : term104 = term57.
Proof. exact (TRANS (@lem6897020) (@lem6897104)). Qed.
Lemma lem6897107 (x : real) : (term76 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6897108 : term57 = term31.
Proof. exact (@lem6897107 term31). Qed.
Lemma lem6897109 : term104 = term31.
Proof. exact (TRANS (@lem6897105) (@lem6897108)). Qed.
Lemma lem6897110 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6897111 : term123 = term118.
Proof. exact (MK_COMB (@lem6897110) (@lem6897109)). Qed.
Lemma lem6897112 (_92033 : int) : (real_of_int _92033) = (real_of_int _92033).
Proof. exact (eq_refl (real_of_int _92033)). Qed.
Lemma lem6897113 (_92033 : int) : (term101 _92033) = (term124 _92033).
Proof. exact (MK_COMB (@lem6897111) (@lem6897112 _92033)). Qed.
Lemma lem6897114 (_92033 : int) : (term100 _92033) = (term124 _92033).
Proof. exact (TRANS (@lem6897011 _92033) (@lem6897113 _92033)). Qed.
Lemma lem6897115 (_92033 : int) : (term124 _92033) = term31.
Proof. exact (@lem1982719 (real_of_int _92033)). Qed.
Lemma lem6897116 (_92033 : int) : (term100 _92033) = term31.
Proof. exact (TRANS (@lem6897114 _92033) (@lem6897115 _92033)). Qed.
Lemma lem6897117 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6897118 (_92033 : int) : (term125 _92033) = term126.
Proof. exact (MK_COMB (@lem6897117) (@lem6897116 _92033)). Qed.
Lemma lem6897119 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem6897120 (_92033 : int) : (term98 _92033) = term127.
Proof. exact (MK_COMB (@lem6897118 _92033) (@lem6897119)). Qed.
Lemma lem6897121 (_92033 : int) : (term97 _92033) = term127.
Proof. exact (TRANS (@lem6897010 _92033) (@lem6897120 _92033)). Qed.
Lemma lem6897122 : term127 = term60.
Proof. exact (@lem1982721 term60). Qed.
Lemma lem6897123 (_92033 : int) : (term97 _92033) = term60.
Proof. exact (TRANS (@lem6897121 _92033) (@lem6897122)). Qed.
Lemma lem6897124 (_92032 : int) (_92033 : int) : (term959 _92032 _92033) = term127.
Proof. exact (MK_COMB (@lem6897009 _92032) (@lem6897123 _92033)). Qed.
Lemma lem6897125 (_92032 : int) (_92033 : int) : (term958 _92032 _92033) = term127.
Proof. exact (TRANS (@lem6896901 _92032 _92033) (@lem6897124 _92032 _92033)). Qed.
Lemma lem6897126 : term127 = term60.
Proof. exact (@lem1982721 term60). Qed.
Lemma lem6897127 (_92032 : int) (_92033 : int) : (term958 _92032 _92033) = term60.
Proof. exact (TRANS (@lem6897125 _92032 _92033) (@lem6897126)). Qed.
Lemma lem6897128 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6897129 (_92032 : int) (_92033 : int) : (term960 _92032 _92033) = term129.
Proof. exact (MK_COMB (@lem6897128) (@lem6897127 _92032 _92033)). Qed.
Lemma lem6897130 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem6897131 (_92032 : int) (_92033 : int) : (term957 _92032 _92033) = term130.
Proof. exact (MK_COMB (@lem6897129 _92032 _92033) (@lem6897130)). Qed.
Lemma lem6897132 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term949 A _92034 f j dom neut _92032 _92033) : term130.
Proof. exact (EQ_MP (@lem6897131 _92032 _92033) (@lem6896900 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6897134 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6897135 : term130 = term133.
Proof. exact (@lem6897134 term31 term60). Qed.
Lemma lem6897137 (x : nat) : (term58 x) = (term59 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6897138 : term60 = term61.
Proof. exact (@lem6897137 term8). Qed.
Lemma lem6897140 (x : nat) : (real_of_num x) = (term56 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6897141 : term31 = term57.
Proof. exact (@lem6897140 (NUMERAL 0)). Qed.
Lemma lem6897142 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6897143 : term33 = term134.
Proof. exact (MK_COMB (@lem6897142) (@lem6897141)). Qed.
Lemma lem6897144 : term133 = term135.
Proof. exact (MK_COMB (@lem6897143) (@lem6897138)). Qed.
Lemma lem6897145 : term136.
Proof. exact (@lem1980026 term31 term43 term60 term43). Qed.
Lemma lem6897147 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6897148 : term108 = term109.
Proof. exact (@lem6897147 (NUMERAL 0) term8). Qed.
Lemma lem6897149 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6897150 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6897151 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6897150 h1) (fun h1 : term109 = True => @lem6897149)). Qed.
Lemma lem6897152 : term109 = True.
Proof. exact (EQ_MP (@lem6897151) (@lem6897149)). Qed.
Lemma lem6897153 : term108 = True.
Proof. exact (TRANS (@lem6897148) (@lem6897152)). Qed.
Lemma lem6897154 : True = term108.
Proof. exact (SYM (@lem6897153)). Qed.
Lemma lem6897155 : term108.
Proof. exact (EQ_MP (@lem6897154) (@lem0)). Qed.
Lemma lem6897156 : term137.
Proof. exact (@lem6897145 (@lem6897155)). Qed.
Lemma lem6897158 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6897159 : term108 = term109.
Proof. exact (@lem6897158 (NUMERAL 0) term8). Qed.
Lemma lem6897160 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6897161 (h1 : term110 = (BIT1 0)) : term109 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6897162 : (term110 = (BIT1 0)) = (term109 = True).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6897161 h1) (fun h1 : term109 = True => @lem6897160)). Qed.
Lemma lem6897163 : term109 = True.
Proof. exact (EQ_MP (@lem6897162) (@lem6897160)). Qed.
Lemma lem6897164 : term108 = True.
Proof. exact (TRANS (@lem6897159) (@lem6897163)). Qed.
Lemma lem6897165 : True = term108.
Proof. exact (SYM (@lem6897164)). Qed.
Lemma lem6897166 : term108.
Proof. exact (EQ_MP (@lem6897165) (@lem0)). Qed.
Lemma lem6897167 : term135 = term138.
Proof. exact (@lem6897156 (@lem6897166)). Qed.
Lemma lem6897169 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6897170 : term87 = term92.
Proof. exact (@lem6897169 term8 term8). Qed.
Lemma lem6897171 : (term71 = (BIT1 0)) = (term72 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6897172 : term72 = term8.
Proof. exact (EQ_MP (@lem6897171) (@lem940073)). Qed.
Lemma lem6897173 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6897174 : term70 = term43.
Proof. exact (MK_COMB (@lem6897173) (@lem6897172)). Qed.
Lemma lem6897175 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6897176 : term92 = term60.
Proof. exact (MK_COMB (@lem6897175) (@lem6897174)). Qed.
Lemma lem6897177 : term87 = term60.
Proof. exact (TRANS (@lem6897170) (@lem6897176)). Qed.
Lemma lem6897179 (x : nat) : (term121 x) = term31.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6897180 : term120 = term31.
Proof. exact (@lem6897179 term8). Qed.
Lemma lem6897181 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6897182 : term139 = term33.
Proof. exact (MK_COMB (@lem6897181) (@lem6897180)). Qed.
Lemma lem6897183 : term138 = term133.
Proof. exact (MK_COMB (@lem6897182) (@lem6897177)). Qed.
Lemma lem6897185 (m : nat) (n : nat) : (term140 m n) = (term141 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6897186 : term133 = term142.
Proof. exact (@lem6897185 (NUMERAL 0) term8). Qed.
Lemma lem6897187 : term110 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6897188 (h1 : term110 = (BIT1 0)) : (term8 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6897189 : (term110 = (BIT1 0)) = ((term8 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term110 = (BIT1 0) => @lem6897188 h1) (fun h1 : (term8 = (NUMERAL 0)) = False => @lem6897187)). Qed.
Lemma lem6897190 : (term8 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6897189) (@lem6897187)). Qed.
Lemma lem6897191 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6897192 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6897193 : term143 = (and True).
Proof. exact (MK_COMB (@lem6897192) (@lem6897191)). Qed.
Lemma lem6897194 : term142 = (True /\ False).
Proof. exact (MK_COMB (@lem6897193) (@lem6897190)). Qed.
Lemma lem6897196 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6897197 : term142 = False.
Proof. exact (TRANS (@lem6897194) (@lem6897196)). Qed.
Lemma lem6897198 : term133 = False.
Proof. exact (TRANS (@lem6897186) (@lem6897197)). Qed.
Lemma lem6897199 : term138 = False.
Proof. exact (TRANS (@lem6897183) (@lem6897198)). Qed.
Lemma lem6897200 : term135 = False.
Proof. exact (TRANS (@lem6897167) (@lem6897199)). Qed.
Lemma lem6897201 : term133 = False.
Proof. exact (TRANS (@lem6897144) (@lem6897200)). Qed.
Lemma lem6897202 : term130 = False.
Proof. exact (TRANS (@lem6897135) (@lem6897201)). Qed.
Lemma lem6897203 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term949 A _92034 f j dom neut _92032 _92033) : False.
Proof. exact (EQ_MP (@lem6897202) (@lem6897132 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6897204 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term863 A _92034 f j dom neut _92032 _92033) : False.
Proof. exact (or_elim (@lem6896139 A _92034 f j dom neut _92032 _92033 h1) (fun h0 : term940 A _92034 f j dom neut _92032 _92033 => @lem6896732 A _92034 f j dom neut _92032 _92033 h0) (fun h0 : term949 A _92034 f j dom neut _92032 _92033 => @lem6897203 A _92034 f j dom neut _92032 _92033 h0)). Qed.
Lemma lem6897205 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term872 A _92034 f j dom neut _92032 _92033) : False.
Proof. exact (or_elim (@lem6894950 A _92034 f j dom neut _92032 _92033 h1) (fun h0 : term867 _92034 _92032 _92033 => @lem6896138 _92034 _92032 _92033 h0) (fun h0 : term863 A _92034 f j dom neut _92032 _92033 => @lem6897204 A _92034 f j dom neut _92032 _92033 h0)). Qed.
Lemma lem6897207 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term872 A _92034 f j dom neut _92032 _92033) : term872 A _92034 f j dom neut _92032 _92033.
Proof. exact (h1). Qed.
Lemma lem6897208 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term872 A _92034 f j dom neut _92032 _92033) : (term872 A _92034 f j dom neut _92032 _92033) = False.
Proof. exact (prop_ext (fun h2 : term872 A _92034 f j dom neut _92032 _92033 => @lem6897205 A _92034 f j dom neut _92032 _92033 h1) (fun h2 : False => @lem6897207 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6897209 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) (h1 : term872 A _92034 f j dom neut _92032 _92033) : False.
Proof. exact (EQ_MP (@lem6897208 A _92034 f j dom neut _92032 _92033 h1) (@lem6897207 A _92034 f j dom neut _92032 _92033 h1)). Qed.
Lemma lem6897210 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92033 : int) (_92032 : int) (h1 : term786 A _92034 f j dom neut _92033 _92032) : term786 A _92034 f j dom neut _92033 _92032.
Proof. exact (h1). Qed.
Lemma lem6897211 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92033 : int) (_92032 : int) (h1 : term786 A _92034 f j dom neut _92033 _92032) : term872 A _92034 f j dom neut _92032 _92033.
Proof. exact (EQ_MP (@lem6894928 A _92034 f j dom neut _92032 _92033) (@lem6897210 A _92034 f j dom neut _92033 _92032 h1)). Qed.
Lemma lem6897212 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92033 : int) (_92032 : int) (h1 : term786 A _92034 f j dom neut _92033 _92032) : (term872 A _92034 f j dom neut _92032 _92033) = False.
Proof. exact (prop_ext (fun h2 : term872 A _92034 f j dom neut _92032 _92033 => @lem6897209 A _92034 f j dom neut _92032 _92033 h2) (fun h2 : False => @lem6897211 A _92034 f j dom neut _92033 _92032 h1)). Qed.
Lemma lem6897213 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92033 : int) (_92032 : int) (h1 : term786 A _92034 f j dom neut _92033 _92032) : False.
Proof. exact (EQ_MP (@lem6897212 A _92034 f j dom neut _92033 _92032 h1) (@lem6897211 A _92034 f j dom neut _92033 _92032 h1)). Qed.
Lemma lem6897214 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92033 : int) (_92032 : int) : term961 A _92034 f j dom neut _92033 _92032.
Proof. exact (fun h0 : term786 A _92034 f j dom neut _92033 _92032 => @lem6897213 A _92034 f j dom neut _92033 _92032 h0). Qed.
Lemma lem6897215 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92033 : int) (_92032 : int) : term962 A _92034 f j dom neut _92033 _92032.
Proof. exact (@lem1386578 (term963 A _92034 f j dom neut _92033 _92032)). Qed.
Lemma lem6897218 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92033 : int) (_92032 : int) : term963 A _92034 f j dom neut _92033 _92032.
Proof. exact (@lem6897215 A _92034 f j dom neut _92033 _92032 (@lem6897214 A _92034 f j dom neut _92033 _92032)). Qed.
Lemma lem6897219 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term785 A _92034 f j dom neut _92033 _92032) = (term760 A _92034 f j dom neut _92032 _92033).
Proof. exact (SYM (@lem6893827 A _92034 f j dom neut _92033 _92032)). Qed.
Lemma lem6897220 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6897221 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : (term963 A _92034 f j dom neut _92033 _92032) = (term700 A _92034 f j dom neut _92032 _92033).
Proof. exact (MK_COMB (@lem6897220) (@lem6897219 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6897222 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : term700 A _92034 f j dom neut _92032 _92033.
Proof. exact (EQ_MP (@lem6897221 A _92034 f j dom neut _92032 _92033) (@lem6897218 A _92034 f j dom neut _92033 _92032)). Qed.
Lemma lem6897223 {A : Type'} (_92034 : int) (f : nat -> A) (j : nat) (dom : A -> Prop) (neut : A) (_92032 : int) (_92033 : int) : term701 A _92034 f j dom neut _92032 _92033.
Proof. exact (EQ_MP (@lem6893398 A _92034 f j dom neut _92032 _92033) (@lem6897222 A _92034 f j dom neut _92032 _92033)). Qed.
Lemma lem6897224 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (j : nat) (m : nat) : term964 A n f dom neut j m.
Proof. exact (@lem6897223 A (int_of_num n) f j dom neut (int_of_num j) (int_of_num m)). Qed.
Lemma lem6897225 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (j : nat) (m : nat) : term965 A n f dom neut j m.
Proof. exact (@lem6897224 A n f dom neut j m (@lem6893391 j)). Qed.
Lemma lem6897226 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (j : nat) (m : nat) : term966 A n f dom neut j m.
Proof. exact (@lem6897225 A n f dom neut j m (@lem6893394 m)). Qed.
Lemma lem6897227 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (j : nat) (m : nat) : term697 A n f dom neut j m.
Proof. exact (@lem6897226 A n f dom neut j m (@lem6893397 n)). Qed.
Lemma lem6897228 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : term699 A n f dom neut m.
Proof. exact (fun j : nat => @lem6897227 A n f dom neut j m). Qed.
Lemma lem6897229 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term699 A n f dom neut m) = (term631 A n f dom neut m).
Proof. exact (SYM (@lem6893388 A n f dom neut m)). Qed.
Lemma lem6897230 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : term631 A n f dom neut m.
Proof. exact (EQ_MP (@lem6897229 A n f dom neut m) (@lem6897228 A n f dom neut m)). Qed.
Lemma lem6897231 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term631 A n f dom neut m) = ((term631 A n f dom neut m) = True).
Proof. exact (@lem7 (term631 A n f dom neut m)). Qed.
Lemma lem6897232 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : (term631 A n f dom neut m) = True.
Proof. exact (EQ_MP (@lem6897231 A n f dom neut m) (@lem6897230 A n f dom neut m)). Qed.
Lemma lem6897233 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : True = (term631 A n f dom neut m).
Proof. exact (SYM (@lem6897232 A n f dom neut m)). Qed.
Lemma lem6897234 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : term631 A n f dom neut m.
Proof. exact (EQ_MP (@lem6897233 A n f dom neut m) (@lem0)). Qed.
Lemma lem6897235 {A : Type'} (n : nat) (f : nat -> A) (dom : A -> Prop) (neut : A) (m : nat) : term556 A n f dom neut m.
Proof. exact (EQ_MP (@lem6892984 A n f dom neut m) (@lem6897234 A n f dom neut m)). Qed.
Lemma lem6897249 (m : nat) (p : nat) (n : nat) : (term154 p m n) = (term155 m p n).
Proof. exact (EQ_MP (@lem6889677 m p n) (@lem6889676 m n p)). Qed.
Lemma lem6897250 (m : nat) (n : nat) : (term967 m n) = (term968 m n).
Proof. exact (@lem6897249 (term3 m) m n). Qed.
Lemma lem6897254 (m : nat) : (term1 m) = False.
Proof. exact (@lem6889668 m (@lem6889667 m)). Qed.
Lemma lem6897255 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6897256 (m : nat) : (term969 m) = (and False).
Proof. exact (MK_COMB (@lem6897255) (@lem6897254 m)). Qed.
Lemma lem6897257 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem6897258 (m : nat) (n : nat) : (term968 m n) = (term970 m n).
Proof. exact (MK_COMB (@lem6897256 m) (@lem6897257 m n)). Qed.
Lemma lem6897260 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem6897261 (m : nat) (n : nat) : (term970 m n) = False.
Proof. exact (@lem6897260 (Peano.le m n)). Qed.
Lemma lem6897262 (m : nat) (n : nat) : (term968 m n) = False.
Proof. exact (TRANS (@lem6897258 m n) (@lem6897261 m n)). Qed.
Lemma lem6897263 (m : nat) (n : nat) : (term967 m n) = False.
Proof. exact (TRANS (@lem6897250 m n) (@lem6897262 m n)). Qed.
Lemma lem6897264 {A : Type'} (f : nat -> A) (m : nat) (neut : A) : (term971 A f m neut) = (term971 A f m neut).
Proof. exact (eq_refl (term971 A f m neut)). Qed.
Lemma lem6897265 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (neut : A) : (term972 A f neut m n) = (term973 A f m neut).
Proof. exact (MK_COMB (@lem6897264 A f m neut) (@lem6897263 m n)). Qed.
Lemma lem6897267 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem6897268 {A : Type'} (f : nat -> A) (m : nat) (neut : A) : (term973 A f m neut) = ((f m) = neut).
Proof. exact (@lem6897267 ((f m) = neut)). Qed.
Lemma lem6897271 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (neut : A) : (term972 A f neut m n) = ((f m) = neut).
Proof. exact (TRANS (@lem6897265 A n f m neut) (@lem6897268 A f m neut)). Qed.
Lemma lem6897272 {A : Type'} (f : nat -> A) (m : nat) (dom : A -> Prop) : (term974 A f m dom) = (term974 A f m dom).
Proof. exact (eq_refl (term974 A f m dom)). Qed.
Lemma lem6897273 {A : Type'} (n : nat) (dom : A -> Prop) (f : nat -> A) (m : nat) (neut : A) : (term975 A dom f neut m n) = (term976 A dom f m neut).
Proof. exact (MK_COMB (@lem6897272 A f m dom) (@lem6897271 A n f m neut)). Qed.
Lemma lem6897276 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem6897277 {A : Type'} (n : nat) (dom : A -> Prop) (f : nat -> A) (m : nat) (neut : A) : (term977 A dom f neut m n) = (term978 A dom f m neut).
Proof. exact (MK_COMB (@lem6897276 A) (@lem6897273 A n dom f m neut)). Qed.
Lemma lem6897278 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : (term979 A dom neut op m n f) = (term979 A dom neut op m n f).
Proof. exact (eq_refl (term979 A dom neut op m n f)). Qed.
Lemma lem6897279 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : (term980 A dom neut op m n f) = (term981 A dom neut op m n f).
Proof. exact (MK_COMB (@lem6897277 A n dom f m neut) (@lem6897278 A dom neut op m n f)). Qed.
Lemma lem6897280 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : (term982 A dom neut op m n f) = (term982 A dom neut op m n f).
Proof. exact (eq_refl (term982 A dom neut op m n f)). Qed.
Lemma lem6897281 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : (term557 A dom neut op m n f) = (term183 A dom neut op m n f).
Proof. exact (MK_COMB (@lem6897279 A dom neut op m n f) (@lem6897280 A dom neut op m n f)). Qed.
Lemma lem6897282 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : (term219 A dom neut op m n f) = (term219 A dom neut op m n f).
Proof. exact (eq_refl (term219 A dom neut op m n f)). Qed.
Lemma lem6897283 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : ((term217 A dom neut op m n f) = (term557 A dom neut op m n f)) = ((term217 A dom neut op m n f) = (term183 A dom neut op m n f)).
Proof. exact (MK_COMB (@lem6897282 A dom neut op m n f) (@lem6897281 A dom neut op m n f)). Qed.
Lemma lem6897286 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6897287 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : (term983 A dom neut op m n f) = (term984 A dom neut op m n f).
Proof. exact (MK_COMB (@lem6897286) (@lem6897283 A dom neut op m n f)). Qed.
Lemma lem6897294 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : ((term217 A dom neut op m n f) = (term183 A dom neut op m n f)) = ((term217 A dom neut op m n f) = (term183 A dom neut op m n f)).
Proof. exact (eq_refl ((term217 A dom neut op m n f) = (term183 A dom neut op m n f))). Qed.
Lemma lem6897295 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : (term985 A dom neut op m n f) = (term986 A dom neut op m n f).
Proof. exact (MK_COMB (@lem6897287 A dom neut op m n f) (@lem6897294 A dom neut op m n f)). Qed.
Lemma lem6897299 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem6897300 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : (term986 A dom neut op m n f) = True.
Proof. exact (@lem6897299 ((term217 A dom neut op m n f) = (term183 A dom neut op m n f))). Qed.
Lemma lem6897301 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : (term985 A dom neut op m n f) = True.
Proof. exact (TRANS (@lem6897295 A dom neut op m n f) (@lem6897300 A dom neut op m n f)). Qed.
Lemma lem6897302 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : True = (term985 A dom neut op m n f).
Proof. exact (SYM (@lem6897301 A dom neut op m n f)). Qed.
Lemma lem6897303 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : term985 A dom neut op m n f.
Proof. exact (EQ_MP (@lem6897302 A dom neut op m n f) (@lem0)). Qed.
Lemma lem6897304 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : term987 A dom neut op m n f.
Proof. exact (conj (@lem6897235 A n f dom neut m) (@lem6897303 A dom neut op m n f)). Qed.
Lemma lem6897305 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : term988 A dom neut op m n f.
Proof. exact (@lem6892278 A dom neut op m n f (@lem6897304 A dom neut op m n f)). Qed.
Lemma lem6897306 {A : Type'} (m : nat) (n : nat) (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (h1 : term175 A dom neut op f) : (term217 A dom neut op m n f) = (term183 A dom neut op m n f).
Proof. exact (@lem6897305 A dom neut op m n f (@lem6892275 A m n dom neut op f h1)). Qed.
Lemma lem6897307 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : term989 A dom neut op m n f.
Proof. exact (fun h0 : term175 A dom neut op f => @lem6897306 A m n dom neut op f h0). Qed.
Lemma lem6897308 {A : Type'} (m : nat) (n : nat) (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (h1 : term175 A dom neut op f) : (term217 A dom neut op m n f) = (term183 A dom neut op m n f).
Proof. exact (@lem6897307 A dom neut op m n f (@lem6889789 A dom neut op f h1)). Qed.
Lemma lem6897309 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (m : nat) (n : nat) (h1 : term175 A dom neut op f) (h2 : Peano.le m n) : (term216 A dom neut op m n f) = (term183 A dom neut op m n f).
Proof. exact (EQ_MP (@lem6890091 A dom neut op f m n h2) (@lem6897308 A m n dom neut op f h1)). Qed.
Lemma lem6897311 {A : Type'} (dom : A -> Prop) (op : type1400 A) (f : nat -> A) (neut : A) (m : nat) (n : nat) (h1 : term200 m n) : term185 A dom op m n f neut.
Proof. exact (fun h0 : term175 A dom neut op f => @lem6892266 A m n dom neut op f h1 h0). Qed.
Lemma lem6897312 {A : Type'} (dom : A -> Prop) (op : type1400 A) (f : nat -> A) (neut : A) (m : nat) (n : nat) (h1 : term200 m n) : (term200 m n) = (term185 A dom op m n f neut).
Proof. exact (prop_ext (fun h2 : term200 m n => @lem6897311 A dom op f neut m n h1) (fun h2 : term185 A dom op m n f neut => @lem6889772 m n h1)). Qed.
Lemma lem6897313 {A : Type'} (dom : A -> Prop) (op : type1400 A) (f : nat -> A) (neut : A) (m : nat) (n : nat) (h1 : term200 m n) : term185 A dom op m n f neut.
Proof. exact (EQ_MP (@lem6897312 A dom op f neut m n h1) (@lem6889772 m n h1)). Qed.
Lemma lem6897314 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : term188 A dom op m n f neut.
Proof. exact (fun h0 : term200 m n => @lem6897313 A dom op f neut m n h0). Qed.
Lemma lem6897315 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (m : nat) (n : nat) (h1 : Peano.le m n) : term190 A dom neut op m n f.
Proof. exact (fun h0 : term175 A dom neut op f => @lem6897309 A dom neut op f m n h0 h1). Qed.
Lemma lem6897316 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (m : nat) (n : nat) (h1 : Peano.le m n) : (Peano.le m n) = (term190 A dom neut op m n f).
Proof. exact (prop_ext (fun h2 : Peano.le m n => @lem6897315 A dom neut op f m n h1) (fun h2 : term190 A dom neut op m n f => @lem6889755 m n h1)). Qed.
Lemma lem6897317 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (f : nat -> A) (m : nat) (n : nat) (h1 : Peano.le m n) : term190 A dom neut op m n f.
Proof. exact (EQ_MP (@lem6897316 A dom neut op f m n h1) (@lem6889755 m n h1)). Qed.
Lemma lem6897318 {A : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) : term193 A dom neut op m n f.
Proof. exact (fun h0 : Peano.le m n => @lem6897317 A dom neut op f m n h0). Qed.
Lemma lem6897319 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : term196 A dom op m n f neut.
Proof. exact (conj (@lem6897318 A dom neut op m n f) (@lem6897314 A dom op m n f neut)). Qed.
Lemma lem6897320 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : term197 A dom op m n f neut.
Proof. exact (EQ_MP (@lem6889754 A dom op m n f neut) (@lem6897319 A dom op m n f neut)). Qed.
Lemma lem6897321 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (n : nat) (f : nat -> A) (neut : A) : (term216 A dom neut op m n f) = (term990 A dom op m n f neut).
Proof. exact (@lem6897320 A dom op m n f neut (@lem6889736 A dom neut op f)). Qed.
Lemma lem6897326 {A : Type'} (dom : A -> Prop) (op : type1400 A) (m : nat) (f : nat -> A) (neut : A) : term991 A dom op m f neut.
Proof. exact (fun n : nat => @lem6897321 A dom op m n f neut). Qed.
Lemma lem6897331 {A : Type'} (dom : A -> Prop) (op : type1400 A) (f : nat -> A) (neut : A) : term992 A dom op f neut.
Proof. exact (fun m : nat => @lem6897326 A dom op m f neut). Qed.
Lemma lem6897336 {A : Type'} (dom : A -> Prop) (op : type1400 A) (neut : A) : term993 A dom op neut.
Proof. exact (fun f : nat -> A => @lem6897331 A dom op f neut). Qed.
Lemma lem6897341 {A : Type'} (dom : A -> Prop) (neut : A) : term994 A dom neut.
Proof. exact (fun op : type1400 A => @lem6897336 A dom op neut). Qed.
Lemma lem6897346 {A : Type'} (dom : A -> Prop) : term995 A dom.
Proof. exact (fun neut : A => @lem6897341 A dom neut). Qed.
Lemma lem6897351 {A : Type'} : term996 A.
Proof. exact (fun dom : A -> Prop => @lem6897346 A dom). Qed.
