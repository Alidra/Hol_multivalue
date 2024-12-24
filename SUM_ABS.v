Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_ABS_term_abbrevs.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import REAL_ABS_NUM_spec.
Require Import SUM_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm12653_spec.
Require Import thm1339240_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm14781_spec.
Require Import thm1482680_spec.
Require Import thm1482705_spec.
Require Import thm1482981_spec.
Require Import thm15222_spec.
Require Import thm17362_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980255_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982711_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982717_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982757_spec.
Require Import thm1982761_spec.
Require Import thm1982781_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988289_spec.
Require Import thm1988291_spec.
Require Import thm1988297_spec.
Require Import thm1988332_spec.
Require Import thm1988348_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Lemma lem7081261 (a : real) (x : real) (b : real) : (term0 a x b) = (term1 a x b).
Proof. exact (@lem17362 (term2 a b) (term3 a x b)). Qed.
Lemma lem7081262 (b : real) (a : real) : (term2 a b) = (term4 b a).
Proof. exact (@lem1988287 b (real_abs a)). Qed.
Lemma lem7081277 (b : real) (a : real) : (term5 b a) = (term6 b a).
Proof. exact (@lem1982792 b (real_abs a)). Qed.
Lemma lem7081278 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7081279 (b : real) (a : real) : (term7 b a) = (term8 b a).
Proof. exact (MK_COMB (@lem7081278) (@lem7081277 b a)). Qed.
Lemma lem7081280 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem7081281 (b : real) (a : real) : (term4 b a) = (term10 b a).
Proof. exact (MK_COMB (@lem7081279 b a) (@lem7081280)). Qed.
Lemma lem7081282 (b : real) (a : real) : (term2 a b) = (term10 b a).
Proof. exact (TRANS (@lem7081262 b a) (@lem7081281 b a)). Qed.
Lemma lem7081283 (a : real) (x : real) (b : real) : (term11 a x b) = (term12 a x b).
Proof. exact (@lem1988297 (term13 x a) (term14 x b)). Qed.
Lemma lem7081292 (b : real) (x : real) : (term14 x b) = (term15 b x).
Proof. exact (@lem1982761 b (real_abs x)). Qed.
Lemma lem7081299 (a : real) (x : real) : (real_add x a) = (real_add a x).
Proof. exact (@lem1982761 a x). Qed.
Lemma lem7081300 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem7081301 (a : real) (x : real) : (term13 x a) = (term13 a x).
Proof. exact (MK_COMB (@lem7081300) (@lem7081299 a x)). Qed.
Lemma lem7081302 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7081303 (a : real) (x : real) : (term16 x a) = (term16 a x).
Proof. exact (MK_COMB (@lem7081302) (@lem7081301 a x)). Qed.
Lemma lem7081304 (a : real) (b : real) (x : real) : (term17 a x b) = (term18 a b x).
Proof. exact (MK_COMB (@lem7081303 a x) (@lem7081292 b x)). Qed.
Lemma lem7081305 (a : real) (b : real) (x : real) : (term18 a b x) = (term19 a b x).
Proof. exact (@lem1982792 (term13 a x) (term15 b x)). Qed.
Lemma lem7081312 (b : real) (x : real) : (term20 b x) = (term21 b x).
Proof. exact (@lem1982781 b term22 (real_abs x)). Qed.
Lemma lem7081313 (a : real) (x : real) : (term23 a x) = (term23 a x).
Proof. exact (eq_refl (term23 a x)). Qed.
Lemma lem7081314 (a : real) (b : real) (x : real) : (term19 a b x) = (term24 a b x).
Proof. exact (MK_COMB (@lem7081313 a x) (@lem7081312 b x)). Qed.
Lemma lem7081315 (b : real) (a : real) (x : real) : (term24 a b x) = (term25 b a x).
Proof. exact (@lem1982757 (term26 b) (term13 a x) (term27 x)). Qed.
Lemma lem7081316 (a : real) (x : real) : (term28 a x) = (term29 a x).
Proof. exact (@lem1982761 (term27 x) (term13 a x)). Qed.
Lemma lem7081317 (b : real) : (term30 b) = (term30 b).
Proof. exact (eq_refl (term30 b)). Qed.
Lemma lem7081318 (b : real) (a : real) (x : real) : (term25 b a x) = (term31 b a x).
Proof. exact (MK_COMB (@lem7081317 b) (@lem7081316 a x)). Qed.
Lemma lem7081319 (b : real) (a : real) (x : real) : (term24 a b x) = (term31 b a x).
Proof. exact (TRANS (@lem7081315 b a x) (@lem7081318 b a x)). Qed.
Lemma lem7081320 (b : real) (a : real) (x : real) : (term19 a b x) = (term31 b a x).
Proof. exact (TRANS (@lem7081314 a b x) (@lem7081319 b a x)). Qed.
Lemma lem7081321 (b : real) (a : real) (x : real) : (term18 a b x) = (term31 b a x).
Proof. exact (TRANS (@lem7081305 a b x) (@lem7081320 b a x)). Qed.
Lemma lem7081322 (b : real) (a : real) (x : real) : (term17 a x b) = (term31 b a x).
Proof. exact (TRANS (@lem7081304 a b x) (@lem7081321 b a x)). Qed.
Lemma lem7081323 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7081324 (b : real) (a : real) (x : real) : (term32 a x b) = (term33 b a x).
Proof. exact (MK_COMB (@lem7081323) (@lem7081322 b a x)). Qed.
Lemma lem7081325 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem7081326 (b : real) (a : real) (x : real) : (term12 a x b) = (term34 b a x).
Proof. exact (MK_COMB (@lem7081324 b a x) (@lem7081325)). Qed.
Lemma lem7081327 (b : real) (a : real) (x : real) : (term11 a x b) = (term34 b a x).
Proof. exact (TRANS (@lem7081283 a x b) (@lem7081326 b a x)). Qed.
Lemma lem7081328 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7081329 (b : real) (a : real) : (term35 a b) = (term36 b a).
Proof. exact (MK_COMB (@lem7081328) (@lem7081282 b a)). Qed.
Lemma lem7081330 (b : real) (a : real) (x : real) : (term1 a x b) = (term37 b a x).
Proof. exact (MK_COMB (@lem7081329 b a) (@lem7081327 b a x)). Qed.
Lemma lem7081345 (b : real) (a : real) (x : real) : (term0 a x b) = (term37 b a x).
Proof. exact (TRANS (@lem7081261 a x b) (@lem7081330 b a x)). Qed.
Lemma lem7081347 (a : real) (x : real) (r : real) : (term38 a x r) = (term39 a x r).
Proof. exact (proj1 (@lem1482680 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem7081348 (b : real) (a : real) : (term10 b a) = (term40 b a).
Proof. exact (@lem7081347 b a term9). Qed.
Lemma lem7081355 (a : real) : (term41 a) = a.
Proof. exact (@lem1982733 a). Qed.
Lemma lem7081358 (b : real) : (real_add b) = (real_add b).
Proof. exact (eq_refl (real_add b)). Qed.
Lemma lem7081359 (b : real) (a : real) : (term42 b a) = (real_add b a).
Proof. exact (MK_COMB (@lem7081358 b) (@lem7081355 a)). Qed.
Lemma lem7081360 (a : real) (b : real) : (real_add b a) = (real_add a b).
Proof. exact (@lem1982761 a b). Qed.
Lemma lem7081361 (a : real) (b : real) : (term42 b a) = (real_add a b).
Proof. exact (TRANS (@lem7081359 b a) (@lem7081360 a b)). Qed.
Lemma lem7081362 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7081363 (a : real) (b : real) : (term43 b a) = (term44 a b).
Proof. exact (MK_COMB (@lem7081362) (@lem7081361 a b)). Qed.
Lemma lem7081364 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem7081365 (a : real) (b : real) : (term45 b a) = (term46 a b).
Proof. exact (MK_COMB (@lem7081363 a b) (@lem7081364)). Qed.
Lemma lem7081378 (a : real) (b : real) : (term47 b a) = (term48 a b).
Proof. exact (@lem1982761 (term26 a) b). Qed.
Lemma lem7081379 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7081380 (a : real) (b : real) : (term49 b a) = (term50 a b).
Proof. exact (MK_COMB (@lem7081379) (@lem7081378 a b)). Qed.
Lemma lem7081381 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem7081382 (a : real) (b : real) : (term51 b a) = (term52 a b).
Proof. exact (MK_COMB (@lem7081380 a b) (@lem7081381)). Qed.
Lemma lem7081383 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7081384 (a : real) (b : real) : (term53 b a) = (term54 a b).
Proof. exact (MK_COMB (@lem7081383) (@lem7081382 a b)). Qed.
Lemma lem7081385 (a : real) (b : real) : (term40 b a) = (term55 a b).
Proof. exact (MK_COMB (@lem7081384 a b) (@lem7081365 a b)). Qed.
Lemma lem7081386 (a : real) (b : real) : (term10 b a) = (term55 a b).
Proof. exact (TRANS (@lem7081348 b a) (@lem7081385 a b)). Qed.
Lemma lem7081387 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7081388 (a : real) (b : real) : (term36 b a) = (term56 a b).
Proof. exact (MK_COMB (@lem7081387) (@lem7081386 a b)). Qed.
Lemma lem7081390 (a : real) (x : real) (b : real) (r : real) : (term57 a x b r) = (term58 a x b r).
Proof. exact (proj1 (@lem1482705 x a b (@el real) (@el real) r)). Qed.
Lemma lem7081391 (b : real) (a : real) (x : real) : (term34 b a x) = (term59 b a x).
Proof. exact (@lem7081390 (term26 b) x (term13 a x) term9). Qed.
Lemma lem7081400 (a : real) (x : real) : (term13 a x) = (term13 a x).
Proof. exact (eq_refl (term13 a x)). Qed.
Lemma lem7081407 (x : real) : (term41 x) = x.
Proof. exact (@lem1982733 x). Qed.
Lemma lem7081408 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7081409 (x : real) : (term60 x) = (real_add x).
Proof. exact (MK_COMB (@lem7081408) (@lem7081407 x)). Qed.
Lemma lem7081412 (a : real) (x : real) : (term61 a x) = (term62 a x).
Proof. exact (MK_COMB (@lem7081409 x) (@lem7081400 a x)). Qed.
Lemma lem7081421 (b : real) : (term30 b) = (term30 b).
Proof. exact (eq_refl (term30 b)). Qed.
Lemma lem7081424 (b : real) (a : real) (x : real) : (term63 b a x) = (term64 b a x).
Proof. exact (MK_COMB (@lem7081421 b) (@lem7081412 a x)). Qed.
Lemma lem7081425 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7081426 (b : real) (a : real) (x : real) : (term65 b a x) = (term66 b a x).
Proof. exact (MK_COMB (@lem7081425) (@lem7081424 b a x)). Qed.
Lemma lem7081427 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem7081428 (b : real) (a : real) (x : real) : (term67 b a x) = (term68 b a x).
Proof. exact (MK_COMB (@lem7081426 b a x) (@lem7081427)). Qed.
Lemma lem7081467 (b : real) (a : real) (x : real) : (term69 b a x) = (term69 b a x).
Proof. exact (eq_refl (term69 b a x)). Qed.
Lemma lem7081468 (b : real) (a : real) (x : real) : (term59 b a x) = (term70 b a x).
Proof. exact (MK_COMB (@lem7081467 b a x) (@lem7081428 b a x)). Qed.
Lemma lem7081469 (b : real) (a : real) (x : real) : (term34 b a x) = (term70 b a x).
Proof. exact (TRANS (@lem7081391 b a x) (@lem7081468 b a x)). Qed.
Lemma lem7081470 (b : real) (a : real) (x : real) : (term37 b a x) = (term71 b a x).
Proof. exact (MK_COMB (@lem7081388 a b) (@lem7081469 b a x)). Qed.
Lemma lem7081471 (b : real) (a : real) (x : real) : (term72 b a x) = (term71 b a x).
Proof. exact (eq_refl (term72 b a x)). Qed.
Lemma lem7081472 (b : real) (a : real) (x : real) : (term71 b a x) = (term72 b a x).
Proof. exact (SYM (@lem7081471 b a x)). Qed.
Lemma lem7081473 (b : real) (a : real) (x : real) : (term72 b a x) = (term73 b a x).
Proof. exact (@lem1482981 (term74 a b x) (real_add a x)). Qed.
Lemma lem7081474 (b : real) (a : real) (x : real) : (term71 b a x) = (term73 b a x).
Proof. exact (TRANS (@lem7081472 b a x) (@lem7081473 b a x)). Qed.
Lemma lem7081475 (b : real) (a : real) (x : real) : (term75 b a x) = (term76 b a x).
Proof. exact (eq_refl (term75 b a x)). Qed.
Lemma lem7081476 (a : real) (x : real) : (term77 a x) = (term77 a x).
Proof. exact (eq_refl (term77 a x)). Qed.
Lemma lem7081477 (b : real) (a : real) (x : real) : (term78 b a x) = (term79 b a x).
Proof. exact (MK_COMB (@lem7081476 a x) (@lem7081475 b a x)). Qed.
Lemma lem7081478 (b : real) (a : real) (x : real) : (term80 b a x) = (term81 b a x).
Proof. exact (eq_refl (term80 b a x)). Qed.
Lemma lem7081479 (a : real) (x : real) : (term82 a x) = (term82 a x).
Proof. exact (eq_refl (term82 a x)). Qed.
Lemma lem7081480 (b : real) (a : real) (x : real) : (term83 b a x) = (term84 b a x).
Proof. exact (MK_COMB (@lem7081479 a x) (@lem7081478 b a x)). Qed.
Lemma lem7081481 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7081482 (b : real) (a : real) (x : real) : (term85 b a x) = (term86 b a x).
Proof. exact (MK_COMB (@lem7081481) (@lem7081480 b a x)). Qed.
Lemma lem7081483 (b : real) (a : real) (x : real) : (term73 b a x) = (term87 b a x).
Proof. exact (MK_COMB (@lem7081482 b a x) (@lem7081477 b a x)). Qed.
Lemma lem7081484 (b : real) (a : real) (x : real) : (term88 b a x) = (term88 b a x).
Proof. exact (eq_refl (term88 b a x)). Qed.
Lemma lem7081485 (b : real) (a : real) (x : real) : ((term71 b a x) = (term73 b a x)) = ((term71 b a x) = (term87 b a x)).
Proof. exact (MK_COMB (@lem7081484 b a x) (@lem7081483 b a x)). Qed.
Lemma lem7081486 (b : real) (a : real) (x : real) : (term71 b a x) = (term87 b a x).
Proof. exact (EQ_MP (@lem7081485 b a x) (@lem7081474 b a x)). Qed.
Lemma lem7081487 (a : real) (x : real) : (term46 a x) = (term89 a x).
Proof. exact (@lem1988291 (real_add a x) term9). Qed.
Lemma lem7081499 (a : real) (x : real) : (term90 a x) = (term91 a x).
Proof. exact (@lem1982792 (real_add a x) term9). Qed.
Lemma lem7081501 (x : nat) : (real_of_num x) = (term92 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7081502 : term9 = term93.
Proof. exact (@lem7081501 (NUMERAL 0)). Qed.
Lemma lem7081504 (x : nat) : (term94 x) = (term95 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7081505 : term22 = term96.
Proof. exact (@lem7081504 term97). Qed.
Lemma lem7081506 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7081507 : term98 = term99.
Proof. exact (MK_COMB (@lem7081506) (@lem7081505)). Qed.
Lemma lem7081508 : term100 = term101.
Proof. exact (MK_COMB (@lem7081507) (@lem7081502)). Qed.
Lemma lem7081509 : term101 = term102.
Proof. exact (@lem1981613 term22 term9 term103 term103). Qed.
Lemma lem7081511 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7081512 : term106 = term107.
Proof. exact (@lem7081511 term97 term97). Qed.
Lemma lem7081513 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7081514 : term109 = term97.
Proof. exact (EQ_MP (@lem7081513) (@lem940073)). Qed.
Lemma lem7081515 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7081516 : term107 = term103.
Proof. exact (MK_COMB (@lem7081515) (@lem7081514)). Qed.
Lemma lem7081517 : term106 = term103.
Proof. exact (TRANS (@lem7081512) (@lem7081516)). Qed.
Lemma lem7081519 (x : nat) : (term110 x) = term9.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7081520 : term100 = term9.
Proof. exact (@lem7081519 term97). Qed.
Lemma lem7081521 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7081522 : term111 = term112.
Proof. exact (MK_COMB (@lem7081521) (@lem7081520)). Qed.
Lemma lem7081523 : term102 = term93.
Proof. exact (MK_COMB (@lem7081522) (@lem7081517)). Qed.
Lemma lem7081524 : term101 = term93.
Proof. exact (TRANS (@lem7081509) (@lem7081523)). Qed.
Lemma lem7081525 : term100 = term93.
Proof. exact (TRANS (@lem7081508) (@lem7081524)). Qed.
Lemma lem7081527 (x : real) : (term113 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7081528 : term93 = term9.
Proof. exact (@lem7081527 term9). Qed.
Lemma lem7081529 : term100 = term9.
Proof. exact (TRANS (@lem7081525) (@lem7081528)). Qed.
Lemma lem7081530 (a : real) (x : real) : (term114 a x) = (term114 a x).
Proof. exact (eq_refl (term114 a x)). Qed.
Lemma lem7081531 (a : real) (x : real) : (term91 a x) = (term115 a x).
Proof. exact (MK_COMB (@lem7081530 a x) (@lem7081529)). Qed.
Lemma lem7081532 (a : real) (x : real) : (term115 a x) = (real_add a x).
Proof. exact (@lem1982723 (real_add a x)). Qed.
Lemma lem7081533 (a : real) (x : real) : (term91 a x) = (real_add a x).
Proof. exact (TRANS (@lem7081531 a x) (@lem7081532 a x)). Qed.
Lemma lem7081535 (a : real) (x : real) : (term90 a x) = (real_add a x).
Proof. exact (TRANS (@lem7081499 a x) (@lem7081533 a x)). Qed.
Lemma lem7081536 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7081537 (a : real) (x : real) : (term116 a x) = (term44 a x).
Proof. exact (MK_COMB (@lem7081536) (@lem7081535 a x)). Qed.
Lemma lem7081538 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem7081539 (a : real) (x : real) : (term89 a x) = (term46 a x).
Proof. exact (MK_COMB (@lem7081537 a x) (@lem7081538)). Qed.
Lemma lem7081540 (a : real) (x : real) : (term46 a x) = (term46 a x).
Proof. exact (TRANS (@lem7081487 a x) (@lem7081539 a x)). Qed.
Lemma lem7081541 (a : real) (b : real) : (term52 a b) = (term117 a b).
Proof. exact (@lem1988291 (term48 a b) term9). Qed.
Lemma lem7081559 (a : real) (b : real) : (term118 a b) = (term119 a b).
Proof. exact (@lem1982792 (term48 a b) term9). Qed.
Lemma lem7081561 (x : nat) : (real_of_num x) = (term92 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7081562 : term9 = term93.
Proof. exact (@lem7081561 (NUMERAL 0)). Qed.
Lemma lem7081564 (x : nat) : (term94 x) = (term95 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7081565 : term22 = term96.
Proof. exact (@lem7081564 term97). Qed.
Lemma lem7081566 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7081567 : term98 = term99.
Proof. exact (MK_COMB (@lem7081566) (@lem7081565)). Qed.
Lemma lem7081568 : term100 = term101.
Proof. exact (MK_COMB (@lem7081567) (@lem7081562)). Qed.
Lemma lem7081569 : term101 = term102.
Proof. exact (@lem1981613 term22 term9 term103 term103). Qed.
Lemma lem7081571 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7081572 : term106 = term107.
Proof. exact (@lem7081571 term97 term97). Qed.
Lemma lem7081573 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7081574 : term109 = term97.
Proof. exact (EQ_MP (@lem7081573) (@lem940073)). Qed.
Lemma lem7081575 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7081576 : term107 = term103.
Proof. exact (MK_COMB (@lem7081575) (@lem7081574)). Qed.
Lemma lem7081577 : term106 = term103.
Proof. exact (TRANS (@lem7081572) (@lem7081576)). Qed.
Lemma lem7081579 (x : nat) : (term110 x) = term9.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7081580 : term100 = term9.
Proof. exact (@lem7081579 term97). Qed.
Lemma lem7081581 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7081582 : term111 = term112.
Proof. exact (MK_COMB (@lem7081581) (@lem7081580)). Qed.
Lemma lem7081583 : term102 = term93.
Proof. exact (MK_COMB (@lem7081582) (@lem7081577)). Qed.
Lemma lem7081584 : term101 = term93.
Proof. exact (TRANS (@lem7081569) (@lem7081583)). Qed.
Lemma lem7081585 : term100 = term93.
Proof. exact (TRANS (@lem7081568) (@lem7081584)). Qed.
Lemma lem7081587 (x : real) : (term113 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7081588 : term93 = term9.
Proof. exact (@lem7081587 term9). Qed.
Lemma lem7081589 : term100 = term9.
Proof. exact (TRANS (@lem7081585) (@lem7081588)). Qed.
Lemma lem7081590 (a : real) (b : real) : (term120 a b) = (term120 a b).
Proof. exact (eq_refl (term120 a b)). Qed.
Lemma lem7081591 (a : real) (b : real) : (term119 a b) = (term121 a b).
Proof. exact (MK_COMB (@lem7081590 a b) (@lem7081589)). Qed.
Lemma lem7081592 (a : real) (b : real) : (term121 a b) = (term48 a b).
Proof. exact (@lem1982723 (term48 a b)). Qed.
Lemma lem7081593 (a : real) (b : real) : (term119 a b) = (term48 a b).
Proof. exact (TRANS (@lem7081591 a b) (@lem7081592 a b)). Qed.
Lemma lem7081595 (a : real) (b : real) : (term118 a b) = (term48 a b).
Proof. exact (TRANS (@lem7081559 a b) (@lem7081593 a b)). Qed.
Lemma lem7081596 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7081597 (a : real) (b : real) : (term122 a b) = (term50 a b).
Proof. exact (MK_COMB (@lem7081596) (@lem7081595 a b)). Qed.
Lemma lem7081598 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem7081599 (a : real) (b : real) : (term117 a b) = (term52 a b).
Proof. exact (MK_COMB (@lem7081597 a b) (@lem7081598)). Qed.
Lemma lem7081600 (a : real) (b : real) : (term52 a b) = (term52 a b).
Proof. exact (TRANS (@lem7081541 a b) (@lem7081599 a b)). Qed.
Lemma lem7081601 (a : real) (b : real) : (term46 a b) = (term89 a b).
Proof. exact (@lem1988291 (real_add a b) term9). Qed.
Lemma lem7081613 (a : real) (b : real) : (term90 a b) = (term91 a b).
Proof. exact (@lem1982792 (real_add a b) term9). Qed.
Lemma lem7081615 (x : nat) : (real_of_num x) = (term92 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7081616 : term9 = term93.
Proof. exact (@lem7081615 (NUMERAL 0)). Qed.
Lemma lem7081618 (x : nat) : (term94 x) = (term95 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7081619 : term22 = term96.
Proof. exact (@lem7081618 term97). Qed.
Lemma lem7081620 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7081621 : term98 = term99.
Proof. exact (MK_COMB (@lem7081620) (@lem7081619)). Qed.
Lemma lem7081622 : term100 = term101.
Proof. exact (MK_COMB (@lem7081621) (@lem7081616)). Qed.
Lemma lem7081623 : term101 = term102.
Proof. exact (@lem1981613 term22 term9 term103 term103). Qed.
Lemma lem7081625 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7081626 : term106 = term107.
Proof. exact (@lem7081625 term97 term97). Qed.
Lemma lem7081627 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7081628 : term109 = term97.
Proof. exact (EQ_MP (@lem7081627) (@lem940073)). Qed.
Lemma lem7081629 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7081630 : term107 = term103.
Proof. exact (MK_COMB (@lem7081629) (@lem7081628)). Qed.
Lemma lem7081631 : term106 = term103.
Proof. exact (TRANS (@lem7081626) (@lem7081630)). Qed.
Lemma lem7081633 (x : nat) : (term110 x) = term9.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7081634 : term100 = term9.
Proof. exact (@lem7081633 term97). Qed.
Lemma lem7081635 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7081636 : term111 = term112.
Proof. exact (MK_COMB (@lem7081635) (@lem7081634)). Qed.
Lemma lem7081637 : term102 = term93.
Proof. exact (MK_COMB (@lem7081636) (@lem7081631)). Qed.
Lemma lem7081638 : term101 = term93.
Proof. exact (TRANS (@lem7081623) (@lem7081637)). Qed.
Lemma lem7081639 : term100 = term93.
Proof. exact (TRANS (@lem7081622) (@lem7081638)). Qed.
Lemma lem7081641 (x : real) : (term113 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7081642 : term93 = term9.
Proof. exact (@lem7081641 term9). Qed.
Lemma lem7081643 : term100 = term9.
Proof. exact (TRANS (@lem7081639) (@lem7081642)). Qed.
Lemma lem7081644 (a : real) (b : real) : (term114 a b) = (term114 a b).
Proof. exact (eq_refl (term114 a b)). Qed.
Lemma lem7081645 (a : real) (b : real) : (term91 a b) = (term115 a b).
Proof. exact (MK_COMB (@lem7081644 a b) (@lem7081643)). Qed.
Lemma lem7081646 (a : real) (b : real) : (term115 a b) = (real_add a b).
Proof. exact (@lem1982723 (real_add a b)). Qed.
Lemma lem7081647 (a : real) (b : real) : (term91 a b) = (real_add a b).
Proof. exact (TRANS (@lem7081645 a b) (@lem7081646 a b)). Qed.
Lemma lem7081649 (a : real) (b : real) : (term90 a b) = (real_add a b).
Proof. exact (TRANS (@lem7081613 a b) (@lem7081647 a b)). Qed.
Lemma lem7081650 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7081651 (a : real) (b : real) : (term116 a b) = (term44 a b).
Proof. exact (MK_COMB (@lem7081650) (@lem7081649 a b)). Qed.
Lemma lem7081652 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem7081653 (a : real) (b : real) : (term89 a b) = (term46 a b).
Proof. exact (MK_COMB (@lem7081651 a b) (@lem7081652)). Qed.
Lemma lem7081654 (a : real) (b : real) : (term46 a b) = (term46 a b).
Proof. exact (TRANS (@lem7081601 a b) (@lem7081653 a b)). Qed.
Lemma lem7081655 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7081656 (a : real) (b : real) : (term54 a b) = (term54 a b).
Proof. exact (MK_COMB (@lem7081655) (@lem7081600 a b)). Qed.
Lemma lem7081657 (a : real) (b : real) : (term55 a b) = (term55 a b).
Proof. exact (MK_COMB (@lem7081656 a b) (@lem7081654 a b)). Qed.
Lemma lem7081658 (b : real) (a : real) (x : real) : (term123 b a x) = (term124 b a x).
Proof. exact (@lem1988289 (term125 b a x) term9). Qed.
Lemma lem7081659 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem7081677 (a : real) (x : real) : (term126 a x) = (term127 a x).
Proof. exact (@lem1982757 a (term26 x) x). Qed.
Lemma lem7081678 (x : real) : (term128 x) = (term129 x).
Proof. exact (@lem1982713 term22 x). Qed.
Lemma lem7081680 (x : nat) : (real_of_num x) = (term92 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7081681 : term103 = term130.
Proof. exact (@lem7081680 term97). Qed.
Lemma lem7081683 (x : nat) : (term94 x) = (term95 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7081684 : term22 = term96.
Proof. exact (@lem7081683 term97). Qed.
Lemma lem7081685 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7081686 : term131 = term132.
Proof. exact (MK_COMB (@lem7081685) (@lem7081684)). Qed.
Lemma lem7081687 : term133 = term134.
Proof. exact (MK_COMB (@lem7081686) (@lem7081681)). Qed.
Lemma lem7081688 : term135.
Proof. exact (@lem1981473 term22 term103 term103 term103 term9 term103). Qed.
Lemma lem7081690 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7081691 : term137 = term138.
Proof. exact (@lem7081690 (NUMERAL 0) term97). Qed.
Lemma lem7081692 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7081693 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7081694 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7081693 h1) (fun h1 : term138 = True => @lem7081692)). Qed.
Lemma lem7081695 : term138 = True.
Proof. exact (EQ_MP (@lem7081694) (@lem7081692)). Qed.
Lemma lem7081696 : term137 = True.
Proof. exact (TRANS (@lem7081691) (@lem7081695)). Qed.
Lemma lem7081697 : True = term137.
Proof. exact (SYM (@lem7081696)). Qed.
Lemma lem7081698 : term137.
Proof. exact (EQ_MP (@lem7081697) (@lem0)). Qed.
Lemma lem7081699 : term140.
Proof. exact (@lem7081688 (@lem7081698)). Qed.
Lemma lem7081701 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7081702 : term137 = term138.
Proof. exact (@lem7081701 (NUMERAL 0) term97). Qed.
Lemma lem7081703 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7081704 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7081705 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7081704 h1) (fun h1 : term138 = True => @lem7081703)). Qed.
Lemma lem7081706 : term138 = True.
Proof. exact (EQ_MP (@lem7081705) (@lem7081703)). Qed.
Lemma lem7081707 : term137 = True.
Proof. exact (TRANS (@lem7081702) (@lem7081706)). Qed.
Lemma lem7081708 : True = term137.
Proof. exact (SYM (@lem7081707)). Qed.
Lemma lem7081709 : term137.
Proof. exact (EQ_MP (@lem7081708) (@lem0)). Qed.
Lemma lem7081710 : term141.
Proof. exact (@lem7081699 (@lem7081709)). Qed.
Lemma lem7081712 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7081713 : term137 = term138.
Proof. exact (@lem7081712 (NUMERAL 0) term97). Qed.
Lemma lem7081714 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7081715 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7081716 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7081715 h1) (fun h1 : term138 = True => @lem7081714)). Qed.
Lemma lem7081717 : term138 = True.
Proof. exact (EQ_MP (@lem7081716) (@lem7081714)). Qed.
Lemma lem7081718 : term137 = True.
Proof. exact (TRANS (@lem7081713) (@lem7081717)). Qed.
Lemma lem7081719 : True = term137.
Proof. exact (SYM (@lem7081718)). Qed.
Lemma lem7081720 : term137.
Proof. exact (EQ_MP (@lem7081719) (@lem0)). Qed.
Lemma lem7081721 : term142.
Proof. exact (@lem7081710 (@lem7081720)). Qed.
Lemma lem7081723 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7081724 : term106 = term107.
Proof. exact (@lem7081723 term97 term97). Qed.
Lemma lem7081725 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7081726 : term109 = term97.
Proof. exact (EQ_MP (@lem7081725) (@lem940073)). Qed.
Lemma lem7081727 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7081728 : term107 = term103.
Proof. exact (MK_COMB (@lem7081727) (@lem7081726)). Qed.
Lemma lem7081729 : term106 = term103.
Proof. exact (TRANS (@lem7081724) (@lem7081728)). Qed.
Lemma lem7081731 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7081732 : term145 = term146.
Proof. exact (@lem7081731 term97 term97). Qed.
Lemma lem7081733 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7081734 : term109 = term97.
Proof. exact (EQ_MP (@lem7081733) (@lem940073)). Qed.
Lemma lem7081735 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7081736 : term107 = term103.
Proof. exact (MK_COMB (@lem7081735) (@lem7081734)). Qed.
Lemma lem7081737 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7081738 : term146 = term22.
Proof. exact (MK_COMB (@lem7081737) (@lem7081736)). Qed.
Lemma lem7081739 : term145 = term22.
Proof. exact (TRANS (@lem7081732) (@lem7081738)). Qed.
Lemma lem7081740 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7081741 : term147 = term131.
Proof. exact (MK_COMB (@lem7081740) (@lem7081739)). Qed.
Lemma lem7081742 : term148 = term133.
Proof. exact (MK_COMB (@lem7081741) (@lem7081729)). Qed.
Lemma lem7081744 (m : nat) : (term149 m) = term9.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7081745 : term133 = term9.
Proof. exact (@lem7081744 term97). Qed.
Lemma lem7081746 : term148 = term9.
Proof. exact (TRANS (@lem7081742) (@lem7081745)). Qed.
Lemma lem7081747 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7081748 : term150 = term151.
Proof. exact (MK_COMB (@lem7081747) (@lem7081746)). Qed.
Lemma lem7081749 : term103 = term103.
Proof. exact (eq_refl term103). Qed.
Lemma lem7081750 : term152 = term153.
Proof. exact (MK_COMB (@lem7081748) (@lem7081749)). Qed.
Lemma lem7081752 (x : nat) : (term154 x) = term9.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7081753 : term153 = term9.
Proof. exact (@lem7081752 term97). Qed.
Lemma lem7081754 : term152 = term9.
Proof. exact (TRANS (@lem7081750) (@lem7081753)). Qed.
Lemma lem7081756 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7081757 : term106 = term107.
Proof. exact (@lem7081756 term97 term97). Qed.
Lemma lem7081758 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7081759 : term109 = term97.
Proof. exact (EQ_MP (@lem7081758) (@lem940073)). Qed.
Lemma lem7081760 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7081761 : term107 = term103.
Proof. exact (MK_COMB (@lem7081760) (@lem7081759)). Qed.
Lemma lem7081762 : term106 = term103.
Proof. exact (TRANS (@lem7081757) (@lem7081761)). Qed.
Lemma lem7081763 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem7081764 : term155 = term153.
Proof. exact (MK_COMB (@lem7081763) (@lem7081762)). Qed.
Lemma lem7081766 (x : nat) : (term154 x) = term9.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7081767 : term153 = term9.
Proof. exact (@lem7081766 term97). Qed.
Lemma lem7081768 : term155 = term9.
Proof. exact (TRANS (@lem7081764) (@lem7081767)). Qed.
Lemma lem7081769 : term9 = term155.
Proof. exact (SYM (@lem7081768)). Qed.
Lemma lem7081770 : term152 = term155.
Proof. exact (TRANS (@lem7081754) (@lem7081769)). Qed.
Lemma lem7081771 : term134 = term93.
Proof. exact (@lem7081721 (@lem7081770)). Qed.
Lemma lem7081772 : term133 = term93.
Proof. exact (TRANS (@lem7081687) (@lem7081771)). Qed.
Lemma lem7081774 (x : real) : (term113 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7081775 : term93 = term9.
Proof. exact (@lem7081774 term9). Qed.
Lemma lem7081776 : term133 = term9.
Proof. exact (TRANS (@lem7081772) (@lem7081775)). Qed.
Lemma lem7081777 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7081778 : term156 = term151.
Proof. exact (MK_COMB (@lem7081777) (@lem7081776)). Qed.
Lemma lem7081779 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7081780 (x : real) : (term129 x) = (term157 x).
Proof. exact (MK_COMB (@lem7081778) (@lem7081779 x)). Qed.
Lemma lem7081781 (x : real) : (term128 x) = (term157 x).
Proof. exact (TRANS (@lem7081678 x) (@lem7081780 x)). Qed.
Lemma lem7081782 (x : real) : (term157 x) = term9.
Proof. exact (@lem1982719 x). Qed.
Lemma lem7081783 (x : real) : (term128 x) = term9.
Proof. exact (TRANS (@lem7081781 x) (@lem7081782 x)). Qed.
Lemma lem7081784 (a : real) : (real_add a) = (real_add a).
Proof. exact (eq_refl (real_add a)). Qed.
Lemma lem7081785 (x : real) (a : real) : (term127 a x) = (term158 a).
Proof. exact (MK_COMB (@lem7081784 a) (@lem7081783 x)). Qed.
Lemma lem7081786 (x : real) (a : real) : (term126 a x) = (term158 a).
Proof. exact (TRANS (@lem7081677 a x) (@lem7081785 x a)). Qed.
Lemma lem7081787 (a : real) : (term158 a) = a.
Proof. exact (@lem1982723 a). Qed.
Lemma lem7081789 (x : real) (a : real) : (term126 a x) = a.
Proof. exact (TRANS (@lem7081786 x a) (@lem7081787 a)). Qed.
Lemma lem7081798 (b : real) : (term30 b) = (term30 b).
Proof. exact (eq_refl (term30 b)). Qed.
Lemma lem7081799 (x : real) (b : real) (a : real) : (term125 b a x) = (term48 b a).
Proof. exact (MK_COMB (@lem7081798 b) (@lem7081789 x a)). Qed.
Lemma lem7081800 (a : real) (b : real) : (term48 b a) = (term47 a b).
Proof. exact (@lem1982761 a (term26 b)). Qed.
Lemma lem7081801 (x : real) (a : real) (b : real) : (term125 b a x) = (term47 a b).
Proof. exact (TRANS (@lem7081799 x b a) (@lem7081800 a b)). Qed.
Lemma lem7081802 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7081803 (x : real) (a : real) (b : real) : (term159 b a x) = (term160 a b).
Proof. exact (MK_COMB (@lem7081802) (@lem7081801 x a b)). Qed.
Lemma lem7081804 (x : real) (a : real) (b : real) : (term161 b a x) = (term162 a b).
Proof. exact (MK_COMB (@lem7081803 x a b) (@lem7081659)). Qed.
Lemma lem7081805 (a : real) (b : real) : (term162 a b) = (term163 a b).
Proof. exact (@lem1982792 (term47 a b) term9). Qed.
Lemma lem7081807 (x : nat) : (real_of_num x) = (term92 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7081808 : term9 = term93.
Proof. exact (@lem7081807 (NUMERAL 0)). Qed.
Lemma lem7081810 (x : nat) : (term94 x) = (term95 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7081811 : term22 = term96.
Proof. exact (@lem7081810 term97). Qed.
Lemma lem7081812 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7081813 : term98 = term99.
Proof. exact (MK_COMB (@lem7081812) (@lem7081811)). Qed.
Lemma lem7081814 : term100 = term101.
Proof. exact (MK_COMB (@lem7081813) (@lem7081808)). Qed.
Lemma lem7081815 : term101 = term102.
Proof. exact (@lem1981613 term22 term9 term103 term103). Qed.
Lemma lem7081817 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7081818 : term106 = term107.
Proof. exact (@lem7081817 term97 term97). Qed.
Lemma lem7081819 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7081820 : term109 = term97.
Proof. exact (EQ_MP (@lem7081819) (@lem940073)). Qed.
Lemma lem7081821 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7081822 : term107 = term103.
Proof. exact (MK_COMB (@lem7081821) (@lem7081820)). Qed.
Lemma lem7081823 : term106 = term103.
Proof. exact (TRANS (@lem7081818) (@lem7081822)). Qed.
Lemma lem7081825 (x : nat) : (term110 x) = term9.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7081826 : term100 = term9.
Proof. exact (@lem7081825 term97). Qed.
Lemma lem7081827 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7081828 : term111 = term112.
Proof. exact (MK_COMB (@lem7081827) (@lem7081826)). Qed.
Lemma lem7081829 : term102 = term93.
Proof. exact (MK_COMB (@lem7081828) (@lem7081823)). Qed.
Lemma lem7081830 : term101 = term93.
Proof. exact (TRANS (@lem7081815) (@lem7081829)). Qed.
Lemma lem7081831 : term100 = term93.
Proof. exact (TRANS (@lem7081814) (@lem7081830)). Qed.
Lemma lem7081833 (x : real) : (term113 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7081834 : term93 = term9.
Proof. exact (@lem7081833 term9). Qed.
Lemma lem7081835 : term100 = term9.
Proof. exact (TRANS (@lem7081831) (@lem7081834)). Qed.
Lemma lem7081836 (a : real) (b : real) : (term164 a b) = (term164 a b).
Proof. exact (eq_refl (term164 a b)). Qed.
Lemma lem7081837 (a : real) (b : real) : (term163 a b) = (term165 a b).
Proof. exact (MK_COMB (@lem7081836 a b) (@lem7081835)). Qed.
Lemma lem7081838 (a : real) (b : real) : (term165 a b) = (term47 a b).
Proof. exact (@lem1982723 (term47 a b)). Qed.
Lemma lem7081839 (a : real) (b : real) : (term163 a b) = (term47 a b).
Proof. exact (TRANS (@lem7081837 a b) (@lem7081838 a b)). Qed.
Lemma lem7081840 (a : real) (b : real) : (term162 a b) = (term47 a b).
Proof. exact (TRANS (@lem7081805 a b) (@lem7081839 a b)). Qed.
Lemma lem7081841 (x : real) (a : real) (b : real) : (term161 b a x) = (term47 a b).
Proof. exact (TRANS (@lem7081804 x a b) (@lem7081840 a b)). Qed.
Lemma lem7081842 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7081843 (x : real) (a : real) (b : real) : (term166 b a x) = (term167 a b).
Proof. exact (MK_COMB (@lem7081842) (@lem7081841 x a b)). Qed.
Lemma lem7081844 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem7081845 (x : real) (a : real) (b : real) : (term124 b a x) = (term168 a b).
Proof. exact (MK_COMB (@lem7081843 x a b) (@lem7081844)). Qed.
Lemma lem7081846 (x : real) (a : real) (b : real) : (term123 b a x) = (term168 a b).
Proof. exact (TRANS (@lem7081658 b a x) (@lem7081845 x a b)). Qed.
Lemma lem7081847 (b : real) (a : real) (x : real) : (term169 b a x) = (term170 b a x).
Proof. exact (@lem1988289 (term171 b a x) term9). Qed.
Lemma lem7081848 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem7081860 (a : real) (x : real) : (term172 a x) = (term173 a x).
Proof. exact (@lem1982757 a x x). Qed.
Lemma lem7081861 (x : real) : (real_add x x) = (term174 x).
Proof. exact (@lem1982717 x). Qed.
Lemma lem7081863 (x : nat) : (real_of_num x) = (term92 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7081864 : term103 = term130.
Proof. exact (@lem7081863 term97). Qed.
Lemma lem7081866 (x : nat) : (real_of_num x) = (term92 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7081867 : term103 = term130.
Proof. exact (@lem7081866 term97). Qed.
Lemma lem7081868 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7081869 : term175 = term176.
Proof. exact (MK_COMB (@lem7081868) (@lem7081867)). Qed.
Lemma lem7081870 : term177 = term178.
Proof. exact (MK_COMB (@lem7081869) (@lem7081864)). Qed.
Lemma lem7081871 : term179.
Proof. exact (@lem1981473 term103 term103 term103 term103 term180 term103). Qed.
Lemma lem7081873 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7081874 : term137 = term138.
Proof. exact (@lem7081873 (NUMERAL 0) term97). Qed.
Lemma lem7081875 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7081876 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7081877 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7081876 h1) (fun h1 : term138 = True => @lem7081875)). Qed.
Lemma lem7081878 : term138 = True.
Proof. exact (EQ_MP (@lem7081877) (@lem7081875)). Qed.
Lemma lem7081879 : term137 = True.
Proof. exact (TRANS (@lem7081874) (@lem7081878)). Qed.
Lemma lem7081880 : True = term137.
Proof. exact (SYM (@lem7081879)). Qed.
Lemma lem7081881 : term137.
Proof. exact (EQ_MP (@lem7081880) (@lem0)). Qed.
Lemma lem7081882 : term181.
Proof. exact (@lem7081871 (@lem7081881)). Qed.
Lemma lem7081884 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7081885 : term137 = term138.
Proof. exact (@lem7081884 (NUMERAL 0) term97). Qed.
Lemma lem7081886 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7081887 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7081888 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7081887 h1) (fun h1 : term138 = True => @lem7081886)). Qed.
Lemma lem7081889 : term138 = True.
Proof. exact (EQ_MP (@lem7081888) (@lem7081886)). Qed.
Lemma lem7081890 : term137 = True.
Proof. exact (TRANS (@lem7081885) (@lem7081889)). Qed.
Lemma lem7081891 : True = term137.
Proof. exact (SYM (@lem7081890)). Qed.
Lemma lem7081892 : term137.
Proof. exact (EQ_MP (@lem7081891) (@lem0)). Qed.
Lemma lem7081893 : term182.
Proof. exact (@lem7081882 (@lem7081892)). Qed.
Lemma lem7081895 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7081896 : term137 = term138.
Proof. exact (@lem7081895 (NUMERAL 0) term97). Qed.
Lemma lem7081897 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7081898 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7081899 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7081898 h1) (fun h1 : term138 = True => @lem7081897)). Qed.
Lemma lem7081900 : term138 = True.
Proof. exact (EQ_MP (@lem7081899) (@lem7081897)). Qed.
Lemma lem7081901 : term137 = True.
Proof. exact (TRANS (@lem7081896) (@lem7081900)). Qed.
Lemma lem7081902 : True = term137.
Proof. exact (SYM (@lem7081901)). Qed.
Lemma lem7081903 : term137.
Proof. exact (EQ_MP (@lem7081902) (@lem0)). Qed.
Lemma lem7081904 : term183.
Proof. exact (@lem7081893 (@lem7081903)). Qed.
Lemma lem7081906 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7081907 : term106 = term107.
Proof. exact (@lem7081906 term97 term97). Qed.
Lemma lem7081908 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7081909 : term109 = term97.
Proof. exact (EQ_MP (@lem7081908) (@lem940073)). Qed.
Lemma lem7081910 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7081911 : term107 = term103.
Proof. exact (MK_COMB (@lem7081910) (@lem7081909)). Qed.
Lemma lem7081912 : term106 = term103.
Proof. exact (TRANS (@lem7081907) (@lem7081911)). Qed.
Lemma lem7081914 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7081915 : term106 = term107.
Proof. exact (@lem7081914 term97 term97). Qed.
Lemma lem7081916 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7081917 : term109 = term97.
Proof. exact (EQ_MP (@lem7081916) (@lem940073)). Qed.
Lemma lem7081918 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7081919 : term107 = term103.
Proof. exact (MK_COMB (@lem7081918) (@lem7081917)). Qed.
Lemma lem7081920 : term106 = term103.
Proof. exact (TRANS (@lem7081915) (@lem7081919)). Qed.
Lemma lem7081921 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7081922 : term184 = term175.
Proof. exact (MK_COMB (@lem7081921) (@lem7081920)). Qed.
Lemma lem7081923 : term185 = term177.
Proof. exact (MK_COMB (@lem7081922) (@lem7081912)). Qed.
Lemma lem7081924 : term177 = term186.
Proof. exact (@lem1367770 term97 term97). Qed.
Lemma lem7081925 : term187 = term188.
Proof. exact (@lem706885). Qed.
Lemma lem7081926 : (term187 = term188) = (term189 = term190).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term188). Qed.
Lemma lem7081927 : term189 = term190.
Proof. exact (EQ_MP (@lem7081926) (@lem7081925)). Qed.
Lemma lem7081928 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7081929 : term186 = term180.
Proof. exact (MK_COMB (@lem7081928) (@lem7081927)). Qed.
Lemma lem7081930 : term177 = term180.
Proof. exact (TRANS (@lem7081924) (@lem7081929)). Qed.
Lemma lem7081931 : term185 = term180.
Proof. exact (TRANS (@lem7081923) (@lem7081930)). Qed.
Lemma lem7081932 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7081933 : term191 = term192.
Proof. exact (MK_COMB (@lem7081932) (@lem7081931)). Qed.
Lemma lem7081934 : term103 = term103.
Proof. exact (eq_refl term103). Qed.
Lemma lem7081935 : term193 = term194.
Proof. exact (MK_COMB (@lem7081933) (@lem7081934)). Qed.
Lemma lem7081937 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7081938 : term194 = term195.
Proof. exact (@lem7081937 term190 term97). Qed.
Lemma lem7081939 : term196 = term188.
Proof. exact (@lem996237 term188). Qed.
Lemma lem7081940 : (term196 = term188) = (term197 = term190).
Proof. exact (@lem1007663 term188 (BIT1 0) term188). Qed.
Lemma lem7081941 : term197 = term190.
Proof. exact (EQ_MP (@lem7081940) (@lem7081939)). Qed.
Lemma lem7081942 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7081943 : term195 = term180.
Proof. exact (MK_COMB (@lem7081942) (@lem7081941)). Qed.
Lemma lem7081944 : term194 = term180.
Proof. exact (TRANS (@lem7081938) (@lem7081943)). Qed.
Lemma lem7081945 : term193 = term180.
Proof. exact (TRANS (@lem7081935) (@lem7081944)). Qed.
Lemma lem7081947 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7081948 : term106 = term107.
Proof. exact (@lem7081947 term97 term97). Qed.
Lemma lem7081949 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7081950 : term109 = term97.
Proof. exact (EQ_MP (@lem7081949) (@lem940073)). Qed.
Lemma lem7081951 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7081952 : term107 = term103.
Proof. exact (MK_COMB (@lem7081951) (@lem7081950)). Qed.
Lemma lem7081953 : term106 = term103.
Proof. exact (TRANS (@lem7081948) (@lem7081952)). Qed.
Lemma lem7081954 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem7081955 : term198 = term194.
Proof. exact (MK_COMB (@lem7081954) (@lem7081953)). Qed.
Lemma lem7081957 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7081958 : term194 = term195.
Proof. exact (@lem7081957 term190 term97). Qed.
Lemma lem7081959 : term196 = term188.
Proof. exact (@lem996237 term188). Qed.
Lemma lem7081960 : (term196 = term188) = (term197 = term190).
Proof. exact (@lem1007663 term188 (BIT1 0) term188). Qed.
Lemma lem7081961 : term197 = term190.
Proof. exact (EQ_MP (@lem7081960) (@lem7081959)). Qed.
Lemma lem7081962 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7081963 : term195 = term180.
Proof. exact (MK_COMB (@lem7081962) (@lem7081961)). Qed.
Lemma lem7081964 : term194 = term180.
Proof. exact (TRANS (@lem7081958) (@lem7081963)). Qed.
Lemma lem7081965 : term198 = term180.
Proof. exact (TRANS (@lem7081955) (@lem7081964)). Qed.
Lemma lem7081966 : term180 = term198.
Proof. exact (SYM (@lem7081965)). Qed.
Lemma lem7081967 : term193 = term198.
Proof. exact (TRANS (@lem7081945) (@lem7081966)). Qed.
Lemma lem7081968 : term178 = term199.
Proof. exact (@lem7081904 (@lem7081967)). Qed.
Lemma lem7081969 : term177 = term199.
Proof. exact (TRANS (@lem7081870) (@lem7081968)). Qed.
Lemma lem7081971 (x : real) : (term113 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7081972 : term199 = term180.
Proof. exact (@lem7081971 term180). Qed.
Lemma lem7081973 : term177 = term180.
Proof. exact (TRANS (@lem7081969) (@lem7081972)). Qed.
Lemma lem7081974 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7081975 : term200 = term192.
Proof. exact (MK_COMB (@lem7081974) (@lem7081973)). Qed.
Lemma lem7081976 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7081977 (x : real) : (term174 x) = (term201 x).
Proof. exact (MK_COMB (@lem7081975) (@lem7081976 x)). Qed.
Lemma lem7081978 (x : real) : (real_add x x) = (term201 x).
Proof. exact (TRANS (@lem7081861 x) (@lem7081977 x)). Qed.
Lemma lem7081979 (a : real) : (real_add a) = (real_add a).
Proof. exact (eq_refl (real_add a)). Qed.
Lemma lem7081980 (a : real) (x : real) : (term173 a x) = (term202 a x).
Proof. exact (MK_COMB (@lem7081979 a) (@lem7081978 x)). Qed.
Lemma lem7081982 (a : real) (x : real) : (term172 a x) = (term202 a x).
Proof. exact (TRANS (@lem7081860 a x) (@lem7081980 a x)). Qed.
Lemma lem7081991 (b : real) : (term30 b) = (term30 b).
Proof. exact (eq_refl (term30 b)). Qed.
Lemma lem7081992 (b : real) (a : real) (x : real) : (term171 b a x) = (term203 b a x).
Proof. exact (MK_COMB (@lem7081991 b) (@lem7081982 a x)). Qed.
Lemma lem7081997 (a : real) (b : real) (x : real) : (term203 b a x) = (term204 a b x).
Proof. exact (@lem1982757 a (term26 b) (term201 x)). Qed.
Lemma lem7081998 (a : real) (b : real) (x : real) : (term171 b a x) = (term204 a b x).
Proof. exact (TRANS (@lem7081992 b a x) (@lem7081997 a b x)). Qed.
Lemma lem7081999 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7082000 (a : real) (b : real) (x : real) : (term205 b a x) = (term206 a b x).
Proof. exact (MK_COMB (@lem7081999) (@lem7081998 a b x)). Qed.
Lemma lem7082001 (a : real) (b : real) (x : real) : (term207 b a x) = (term208 a b x).
Proof. exact (MK_COMB (@lem7082000 a b x) (@lem7081848)). Qed.
Lemma lem7082002 (a : real) (b : real) (x : real) : (term208 a b x) = (term209 a b x).
Proof. exact (@lem1982792 (term204 a b x) term9). Qed.
Lemma lem7082004 (x : nat) : (real_of_num x) = (term92 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7082005 : term9 = term93.
Proof. exact (@lem7082004 (NUMERAL 0)). Qed.
Lemma lem7082007 (x : nat) : (term94 x) = (term95 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7082008 : term22 = term96.
Proof. exact (@lem7082007 term97). Qed.
Lemma lem7082009 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7082010 : term98 = term99.
Proof. exact (MK_COMB (@lem7082009) (@lem7082008)). Qed.
Lemma lem7082011 : term100 = term101.
Proof. exact (MK_COMB (@lem7082010) (@lem7082005)). Qed.
Lemma lem7082012 : term101 = term102.
Proof. exact (@lem1981613 term22 term9 term103 term103). Qed.
Lemma lem7082014 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7082015 : term106 = term107.
Proof. exact (@lem7082014 term97 term97). Qed.
Lemma lem7082016 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7082017 : term109 = term97.
Proof. exact (EQ_MP (@lem7082016) (@lem940073)). Qed.
Lemma lem7082018 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7082019 : term107 = term103.
Proof. exact (MK_COMB (@lem7082018) (@lem7082017)). Qed.
Lemma lem7082020 : term106 = term103.
Proof. exact (TRANS (@lem7082015) (@lem7082019)). Qed.
Lemma lem7082022 (x : nat) : (term110 x) = term9.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7082023 : term100 = term9.
Proof. exact (@lem7082022 term97). Qed.
Lemma lem7082024 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7082025 : term111 = term112.
Proof. exact (MK_COMB (@lem7082024) (@lem7082023)). Qed.
Lemma lem7082026 : term102 = term93.
Proof. exact (MK_COMB (@lem7082025) (@lem7082020)). Qed.
Lemma lem7082027 : term101 = term93.
Proof. exact (TRANS (@lem7082012) (@lem7082026)). Qed.
Lemma lem7082028 : term100 = term93.
Proof. exact (TRANS (@lem7082011) (@lem7082027)). Qed.
Lemma lem7082030 (x : real) : (term113 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7082031 : term93 = term9.
Proof. exact (@lem7082030 term9). Qed.
Lemma lem7082032 : term100 = term9.
Proof. exact (TRANS (@lem7082028) (@lem7082031)). Qed.
Lemma lem7082033 (a : real) (b : real) (x : real) : (term210 a b x) = (term210 a b x).
Proof. exact (eq_refl (term210 a b x)). Qed.
Lemma lem7082034 (a : real) (b : real) (x : real) : (term209 a b x) = (term211 a b x).
Proof. exact (MK_COMB (@lem7082033 a b x) (@lem7082032)). Qed.
Lemma lem7082035 (a : real) (b : real) (x : real) : (term211 a b x) = (term204 a b x).
Proof. exact (@lem1982723 (term204 a b x)). Qed.
Lemma lem7082036 (a : real) (b : real) (x : real) : (term209 a b x) = (term204 a b x).
Proof. exact (TRANS (@lem7082034 a b x) (@lem7082035 a b x)). Qed.
Lemma lem7082037 (a : real) (b : real) (x : real) : (term208 a b x) = (term204 a b x).
Proof. exact (TRANS (@lem7082002 a b x) (@lem7082036 a b x)). Qed.
Lemma lem7082038 (a : real) (b : real) (x : real) : (term207 b a x) = (term204 a b x).
Proof. exact (TRANS (@lem7082001 a b x) (@lem7082037 a b x)). Qed.
Lemma lem7082039 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7082040 (a : real) (b : real) (x : real) : (term212 b a x) = (term213 a b x).
Proof. exact (MK_COMB (@lem7082039) (@lem7082038 a b x)). Qed.
Lemma lem7082041 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem7082042 (a : real) (b : real) (x : real) : (term170 b a x) = (term214 a b x).
Proof. exact (MK_COMB (@lem7082040 a b x) (@lem7082041)). Qed.
Lemma lem7082043 (a : real) (b : real) (x : real) : (term169 b a x) = (term214 a b x).
Proof. exact (TRANS (@lem7081847 b a x) (@lem7082042 a b x)). Qed.
Lemma lem7082044 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7082045 (x : real) (a : real) (b : real) : (term215 b a x) = (term216 a b).
Proof. exact (MK_COMB (@lem7082044) (@lem7081846 x a b)). Qed.
Lemma lem7082046 (a : real) (b : real) (x : real) : (term217 b a x) = (term218 a b x).
Proof. exact (MK_COMB (@lem7082045 x a b) (@lem7082043 a b x)). Qed.
Lemma lem7082047 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7082048 (a : real) (b : real) : (term56 a b) = (term56 a b).
Proof. exact (MK_COMB (@lem7082047) (@lem7081657 a b)). Qed.
Lemma lem7082049 (a : real) (b : real) (x : real) : (term81 b a x) = (term219 a b x).
Proof. exact (MK_COMB (@lem7082048 a b) (@lem7082046 a b x)). Qed.
Lemma lem7082050 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7082051 (a : real) (x : real) : (term82 a x) = (term82 a x).
Proof. exact (MK_COMB (@lem7082050) (@lem7081540 a x)). Qed.
Lemma lem7082052 (a : real) (b : real) (x : real) : (term84 b a x) = (term220 a b x).
Proof. exact (MK_COMB (@lem7082051 a x) (@lem7082049 a b x)). Qed.
Lemma lem7082053 (a : real) (x : real) : (term221 a x) = (term222 a x).
Proof. exact (@lem1988289 term9 (real_add a x)). Qed.
Lemma lem7082065 (a : real) (x : real) : (term223 a x) = (term224 a x).
Proof. exact (@lem1982792 term9 (real_add a x)). Qed.
Lemma lem7082072 (a : real) (x : real) : (term225 a x) = (term226 a x).
Proof. exact (@lem1982781 a term22 x). Qed.
Lemma lem7082073 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem7082074 (a : real) (x : real) : (term224 a x) = (term228 a x).
Proof. exact (MK_COMB (@lem7082073) (@lem7082072 a x)). Qed.
Lemma lem7082075 (a : real) (x : real) : (term228 a x) = (term226 a x).
Proof. exact (@lem1982721 (term226 a x)). Qed.
Lemma lem7082076 (a : real) (x : real) : (term224 a x) = (term226 a x).
Proof. exact (TRANS (@lem7082074 a x) (@lem7082075 a x)). Qed.
Lemma lem7082078 (a : real) (x : real) : (term223 a x) = (term226 a x).
Proof. exact (TRANS (@lem7082065 a x) (@lem7082076 a x)). Qed.
Lemma lem7082079 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7082080 (a : real) (x : real) : (term229 a x) = (term230 a x).
Proof. exact (MK_COMB (@lem7082079) (@lem7082078 a x)). Qed.
Lemma lem7082081 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem7082082 (a : real) (x : real) : (term222 a x) = (term231 a x).
Proof. exact (MK_COMB (@lem7082080 a x) (@lem7082081)). Qed.
Lemma lem7082083 (a : real) (x : real) : (term221 a x) = (term231 a x).
Proof. exact (TRANS (@lem7082053 a x) (@lem7082082 a x)). Qed.
Lemma lem7082084 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7082085 (a : real) (b : real) : (term54 a b) = (term54 a b).
Proof. exact (MK_COMB (@lem7082084) (@lem7081600 a b)). Qed.
Lemma lem7082086 (a : real) (b : real) : (term55 a b) = (term55 a b).
Proof. exact (MK_COMB (@lem7082085 a b) (@lem7081654 a b)). Qed.
Lemma lem7082087 (b : real) (a : real) (x : real) : (term232 b a x) = (term233 b a x).
Proof. exact (@lem1988289 (term234 b a x) term9). Qed.
Lemma lem7082088 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem7082098 (a : real) (x : real) : (term235 a x) = (term225 a x).
Proof. exact (@lem1982785 (real_add a x)). Qed.
Lemma lem7082105 (a : real) (x : real) : (term225 a x) = (term226 a x).
Proof. exact (@lem1982781 a term22 x). Qed.
Lemma lem7082107 (a : real) (x : real) : (term235 a x) = (term226 a x).
Proof. exact (TRANS (@lem7082098 a x) (@lem7082105 a x)). Qed.
Lemma lem7082116 (x : real) : (term30 x) = (term30 x).
Proof. exact (eq_refl (term30 x)). Qed.
Lemma lem7082117 (a : real) (x : real) : (term236 a x) = (term237 a x).
Proof. exact (MK_COMB (@lem7082116 x) (@lem7082107 a x)). Qed.
Lemma lem7082118 (a : real) (x : real) : (term237 a x) = (term238 a x).
Proof. exact (@lem1982757 (term26 a) (term26 x) (term26 x)). Qed.
Lemma lem7082119 (x : real) : (term239 x) = (term240 x).
Proof. exact (@lem1982711 term22 term22 x). Qed.
Lemma lem7082121 (x : nat) : (term94 x) = (term95 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7082122 : term22 = term96.
Proof. exact (@lem7082121 term97). Qed.
Lemma lem7082124 (x : nat) : (term94 x) = (term95 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7082125 : term22 = term96.
Proof. exact (@lem7082124 term97). Qed.
Lemma lem7082126 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7082127 : term131 = term132.
Proof. exact (MK_COMB (@lem7082126) (@lem7082125)). Qed.
Lemma lem7082128 : term241 = term242.
Proof. exact (MK_COMB (@lem7082127) (@lem7082122)). Qed.
Lemma lem7082129 : term243.
Proof. exact (@lem1981473 term22 term103 term22 term103 term244 term103). Qed.
Lemma lem7082131 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7082132 : term137 = term138.
Proof. exact (@lem7082131 (NUMERAL 0) term97). Qed.
Lemma lem7082133 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7082134 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7082135 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7082134 h1) (fun h1 : term138 = True => @lem7082133)). Qed.
Lemma lem7082136 : term138 = True.
Proof. exact (EQ_MP (@lem7082135) (@lem7082133)). Qed.
Lemma lem7082137 : term137 = True.
Proof. exact (TRANS (@lem7082132) (@lem7082136)). Qed.
Lemma lem7082138 : True = term137.
Proof. exact (SYM (@lem7082137)). Qed.
Lemma lem7082139 : term137.
Proof. exact (EQ_MP (@lem7082138) (@lem0)). Qed.
Lemma lem7082140 : term245.
Proof. exact (@lem7082129 (@lem7082139)). Qed.
Lemma lem7082142 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7082143 : term137 = term138.
Proof. exact (@lem7082142 (NUMERAL 0) term97). Qed.
Lemma lem7082144 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7082145 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7082146 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7082145 h1) (fun h1 : term138 = True => @lem7082144)). Qed.
Lemma lem7082147 : term138 = True.
Proof. exact (EQ_MP (@lem7082146) (@lem7082144)). Qed.
Lemma lem7082148 : term137 = True.
Proof. exact (TRANS (@lem7082143) (@lem7082147)). Qed.
Lemma lem7082149 : True = term137.
Proof. exact (SYM (@lem7082148)). Qed.
Lemma lem7082150 : term137.
Proof. exact (EQ_MP (@lem7082149) (@lem0)). Qed.
Lemma lem7082151 : term246.
Proof. exact (@lem7082140 (@lem7082150)). Qed.
Lemma lem7082153 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7082154 : term137 = term138.
Proof. exact (@lem7082153 (NUMERAL 0) term97). Qed.
Lemma lem7082155 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7082156 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7082157 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7082156 h1) (fun h1 : term138 = True => @lem7082155)). Qed.
Lemma lem7082158 : term138 = True.
Proof. exact (EQ_MP (@lem7082157) (@lem7082155)). Qed.
Lemma lem7082159 : term137 = True.
Proof. exact (TRANS (@lem7082154) (@lem7082158)). Qed.
Lemma lem7082160 : True = term137.
Proof. exact (SYM (@lem7082159)). Qed.
Lemma lem7082161 : term137.
Proof. exact (EQ_MP (@lem7082160) (@lem0)). Qed.
Lemma lem7082162 : term247.
Proof. exact (@lem7082151 (@lem7082161)). Qed.
Lemma lem7082164 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7082165 : term145 = term146.
Proof. exact (@lem7082164 term97 term97). Qed.
Lemma lem7082166 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7082167 : term109 = term97.
Proof. exact (EQ_MP (@lem7082166) (@lem940073)). Qed.
Lemma lem7082168 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7082169 : term107 = term103.
Proof. exact (MK_COMB (@lem7082168) (@lem7082167)). Qed.
Lemma lem7082170 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7082171 : term146 = term22.
Proof. exact (MK_COMB (@lem7082170) (@lem7082169)). Qed.
Lemma lem7082172 : term145 = term22.
Proof. exact (TRANS (@lem7082165) (@lem7082171)). Qed.
Lemma lem7082174 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7082175 : term145 = term146.
Proof. exact (@lem7082174 term97 term97). Qed.
Lemma lem7082176 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7082177 : term109 = term97.
Proof. exact (EQ_MP (@lem7082176) (@lem940073)). Qed.
Lemma lem7082178 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7082179 : term107 = term103.
Proof. exact (MK_COMB (@lem7082178) (@lem7082177)). Qed.
Lemma lem7082180 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7082181 : term146 = term22.
Proof. exact (MK_COMB (@lem7082180) (@lem7082179)). Qed.
Lemma lem7082182 : term145 = term22.
Proof. exact (TRANS (@lem7082175) (@lem7082181)). Qed.
Lemma lem7082183 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7082184 : term147 = term131.
Proof. exact (MK_COMB (@lem7082183) (@lem7082182)). Qed.
Lemma lem7082185 : term248 = term241.
Proof. exact (MK_COMB (@lem7082184) (@lem7082172)). Qed.
Lemma lem7082186 : term241 = term249.
Proof. exact (@lem1367763 term97 term97). Qed.
Lemma lem7082187 : term187 = term188.
Proof. exact (@lem706885). Qed.
Lemma lem7082188 : (term187 = term188) = (term189 = term190).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term188). Qed.
Lemma lem7082189 : term189 = term190.
Proof. exact (EQ_MP (@lem7082188) (@lem7082187)). Qed.
Lemma lem7082190 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7082191 : term186 = term180.
Proof. exact (MK_COMB (@lem7082190) (@lem7082189)). Qed.
Lemma lem7082192 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7082193 : term249 = term244.
Proof. exact (MK_COMB (@lem7082192) (@lem7082191)). Qed.
Lemma lem7082194 : term241 = term244.
Proof. exact (TRANS (@lem7082186) (@lem7082193)). Qed.
Lemma lem7082195 : term248 = term244.
Proof. exact (TRANS (@lem7082185) (@lem7082194)). Qed.
Lemma lem7082196 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7082197 : term250 = term251.
Proof. exact (MK_COMB (@lem7082196) (@lem7082195)). Qed.
Lemma lem7082198 : term103 = term103.
Proof. exact (eq_refl term103). Qed.
Lemma lem7082199 : term252 = term253.
Proof. exact (MK_COMB (@lem7082197) (@lem7082198)). Qed.
Lemma lem7082201 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7082202 : term253 = term254.
Proof. exact (@lem7082201 term190 term97). Qed.
Lemma lem7082203 : term196 = term188.
Proof. exact (@lem996237 term188). Qed.
Lemma lem7082204 : (term196 = term188) = (term197 = term190).
Proof. exact (@lem1007663 term188 (BIT1 0) term188). Qed.
Lemma lem7082205 : term197 = term190.
Proof. exact (EQ_MP (@lem7082204) (@lem7082203)). Qed.
Lemma lem7082206 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7082207 : term195 = term180.
Proof. exact (MK_COMB (@lem7082206) (@lem7082205)). Qed.
Lemma lem7082208 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7082209 : term254 = term244.
Proof. exact (MK_COMB (@lem7082208) (@lem7082207)). Qed.
Lemma lem7082210 : term253 = term244.
Proof. exact (TRANS (@lem7082202) (@lem7082209)). Qed.
Lemma lem7082211 : term252 = term244.
Proof. exact (TRANS (@lem7082199) (@lem7082210)). Qed.
Lemma lem7082213 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7082214 : term106 = term107.
Proof. exact (@lem7082213 term97 term97). Qed.
Lemma lem7082215 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7082216 : term109 = term97.
Proof. exact (EQ_MP (@lem7082215) (@lem940073)). Qed.
Lemma lem7082217 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7082218 : term107 = term103.
Proof. exact (MK_COMB (@lem7082217) (@lem7082216)). Qed.
Lemma lem7082219 : term106 = term103.
Proof. exact (TRANS (@lem7082214) (@lem7082218)). Qed.
Lemma lem7082220 : term251 = term251.
Proof. exact (eq_refl term251). Qed.
Lemma lem7082221 : term255 = term253.
Proof. exact (MK_COMB (@lem7082220) (@lem7082219)). Qed.
Lemma lem7082223 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7082224 : term253 = term254.
Proof. exact (@lem7082223 term190 term97). Qed.
Lemma lem7082225 : term196 = term188.
Proof. exact (@lem996237 term188). Qed.
Lemma lem7082226 : (term196 = term188) = (term197 = term190).
Proof. exact (@lem1007663 term188 (BIT1 0) term188). Qed.
Lemma lem7082227 : term197 = term190.
Proof. exact (EQ_MP (@lem7082226) (@lem7082225)). Qed.
Lemma lem7082228 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7082229 : term195 = term180.
Proof. exact (MK_COMB (@lem7082228) (@lem7082227)). Qed.
Lemma lem7082230 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7082231 : term254 = term244.
Proof. exact (MK_COMB (@lem7082230) (@lem7082229)). Qed.
Lemma lem7082232 : term253 = term244.
Proof. exact (TRANS (@lem7082224) (@lem7082231)). Qed.
Lemma lem7082233 : term255 = term244.
Proof. exact (TRANS (@lem7082221) (@lem7082232)). Qed.
Lemma lem7082234 : term244 = term255.
Proof. exact (SYM (@lem7082233)). Qed.
Lemma lem7082235 : term252 = term255.
Proof. exact (TRANS (@lem7082211) (@lem7082234)). Qed.
Lemma lem7082236 : term242 = term256.
Proof. exact (@lem7082162 (@lem7082235)). Qed.
Lemma lem7082237 : term241 = term256.
Proof. exact (TRANS (@lem7082128) (@lem7082236)). Qed.
Lemma lem7082239 (x : real) : (term113 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7082240 : term256 = term244.
Proof. exact (@lem7082239 term244). Qed.
Lemma lem7082241 : term241 = term244.
Proof. exact (TRANS (@lem7082237) (@lem7082240)). Qed.
Lemma lem7082242 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7082243 : term257 = term251.
Proof. exact (MK_COMB (@lem7082242) (@lem7082241)). Qed.
Lemma lem7082244 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7082245 (x : real) : (term240 x) = (term258 x).
Proof. exact (MK_COMB (@lem7082243) (@lem7082244 x)). Qed.
Lemma lem7082246 (x : real) : (term239 x) = (term258 x).
Proof. exact (TRANS (@lem7082119 x) (@lem7082245 x)). Qed.
Lemma lem7082247 (a : real) : (term30 a) = (term30 a).
Proof. exact (eq_refl (term30 a)). Qed.
Lemma lem7082248 (a : real) (x : real) : (term238 a x) = (term259 a x).
Proof. exact (MK_COMB (@lem7082247 a) (@lem7082246 x)). Qed.
Lemma lem7082249 (a : real) (x : real) : (term237 a x) = (term259 a x).
Proof. exact (TRANS (@lem7082118 a x) (@lem7082248 a x)). Qed.
Lemma lem7082250 (a : real) (x : real) : (term236 a x) = (term259 a x).
Proof. exact (TRANS (@lem7082117 a x) (@lem7082249 a x)). Qed.
Lemma lem7082259 (b : real) : (term30 b) = (term30 b).
Proof. exact (eq_refl (term30 b)). Qed.
Lemma lem7082260 (b : real) (a : real) (x : real) : (term234 b a x) = (term260 b a x).
Proof. exact (MK_COMB (@lem7082259 b) (@lem7082250 a x)). Qed.
Lemma lem7082265 (a : real) (b : real) (x : real) : (term260 b a x) = (term260 a b x).
Proof. exact (@lem1982757 (term26 a) (term26 b) (term258 x)). Qed.
Lemma lem7082266 (a : real) (b : real) (x : real) : (term234 b a x) = (term260 a b x).
Proof. exact (TRANS (@lem7082260 b a x) (@lem7082265 a b x)). Qed.
Lemma lem7082267 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7082268 (a : real) (b : real) (x : real) : (term261 b a x) = (term262 a b x).
Proof. exact (MK_COMB (@lem7082267) (@lem7082266 a b x)). Qed.
Lemma lem7082269 (a : real) (b : real) (x : real) : (term263 b a x) = (term264 a b x).
Proof. exact (MK_COMB (@lem7082268 a b x) (@lem7082088)). Qed.
Lemma lem7082270 (a : real) (b : real) (x : real) : (term264 a b x) = (term265 a b x).
Proof. exact (@lem1982792 (term260 a b x) term9). Qed.
Lemma lem7082272 (x : nat) : (real_of_num x) = (term92 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7082273 : term9 = term93.
Proof. exact (@lem7082272 (NUMERAL 0)). Qed.
Lemma lem7082275 (x : nat) : (term94 x) = (term95 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7082276 : term22 = term96.
Proof. exact (@lem7082275 term97). Qed.
Lemma lem7082277 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7082278 : term98 = term99.
Proof. exact (MK_COMB (@lem7082277) (@lem7082276)). Qed.
Lemma lem7082279 : term100 = term101.
Proof. exact (MK_COMB (@lem7082278) (@lem7082273)). Qed.
Lemma lem7082280 : term101 = term102.
Proof. exact (@lem1981613 term22 term9 term103 term103). Qed.
Lemma lem7082282 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7082283 : term106 = term107.
Proof. exact (@lem7082282 term97 term97). Qed.
Lemma lem7082284 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7082285 : term109 = term97.
Proof. exact (EQ_MP (@lem7082284) (@lem940073)). Qed.
Lemma lem7082286 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7082287 : term107 = term103.
Proof. exact (MK_COMB (@lem7082286) (@lem7082285)). Qed.
Lemma lem7082288 : term106 = term103.
Proof. exact (TRANS (@lem7082283) (@lem7082287)). Qed.
Lemma lem7082290 (x : nat) : (term110 x) = term9.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7082291 : term100 = term9.
Proof. exact (@lem7082290 term97). Qed.
Lemma lem7082292 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7082293 : term111 = term112.
Proof. exact (MK_COMB (@lem7082292) (@lem7082291)). Qed.
Lemma lem7082294 : term102 = term93.
Proof. exact (MK_COMB (@lem7082293) (@lem7082288)). Qed.
Lemma lem7082295 : term101 = term93.
Proof. exact (TRANS (@lem7082280) (@lem7082294)). Qed.
Lemma lem7082296 : term100 = term93.
Proof. exact (TRANS (@lem7082279) (@lem7082295)). Qed.
Lemma lem7082298 (x : real) : (term113 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7082299 : term93 = term9.
Proof. exact (@lem7082298 term9). Qed.
Lemma lem7082300 : term100 = term9.
Proof. exact (TRANS (@lem7082296) (@lem7082299)). Qed.
Lemma lem7082301 (a : real) (b : real) (x : real) : (term266 a b x) = (term266 a b x).
Proof. exact (eq_refl (term266 a b x)). Qed.
Lemma lem7082302 (a : real) (b : real) (x : real) : (term265 a b x) = (term267 a b x).
Proof. exact (MK_COMB (@lem7082301 a b x) (@lem7082300)). Qed.
Lemma lem7082303 (a : real) (b : real) (x : real) : (term267 a b x) = (term260 a b x).
Proof. exact (@lem1982723 (term260 a b x)). Qed.
Lemma lem7082304 (a : real) (b : real) (x : real) : (term265 a b x) = (term260 a b x).
Proof. exact (TRANS (@lem7082302 a b x) (@lem7082303 a b x)). Qed.
Lemma lem7082305 (a : real) (b : real) (x : real) : (term264 a b x) = (term260 a b x).
Proof. exact (TRANS (@lem7082270 a b x) (@lem7082304 a b x)). Qed.
Lemma lem7082306 (a : real) (b : real) (x : real) : (term263 b a x) = (term260 a b x).
Proof. exact (TRANS (@lem7082269 a b x) (@lem7082305 a b x)). Qed.
Lemma lem7082307 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7082308 (a : real) (b : real) (x : real) : (term268 b a x) = (term269 a b x).
Proof. exact (MK_COMB (@lem7082307) (@lem7082306 a b x)). Qed.
Lemma lem7082309 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem7082310 (a : real) (b : real) (x : real) : (term233 b a x) = (term270 a b x).
Proof. exact (MK_COMB (@lem7082308 a b x) (@lem7082309)). Qed.
Lemma lem7082311 (a : real) (b : real) (x : real) : (term232 b a x) = (term270 a b x).
Proof. exact (TRANS (@lem7082087 b a x) (@lem7082310 a b x)). Qed.
Lemma lem7082312 (b : real) (a : real) (x : real) : (term271 b a x) = (term272 b a x).
Proof. exact (@lem1988289 (term273 b a x) term9). Qed.
Lemma lem7082313 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem7082323 (a : real) (x : real) : (term235 a x) = (term225 a x).
Proof. exact (@lem1982785 (real_add a x)). Qed.
Lemma lem7082330 (a : real) (x : real) : (term225 a x) = (term226 a x).
Proof. exact (@lem1982781 a term22 x). Qed.
Lemma lem7082332 (a : real) (x : real) : (term235 a x) = (term226 a x).
Proof. exact (TRANS (@lem7082323 a x) (@lem7082330 a x)). Qed.
Lemma lem7082335 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem7082336 (a : real) (x : real) : (term274 a x) = (term275 a x).
Proof. exact (MK_COMB (@lem7082335 x) (@lem7082332 a x)). Qed.
Lemma lem7082337 (a : real) (x : real) : (term275 a x) = (term276 a x).
Proof. exact (@lem1982757 (term26 a) x (term26 x)). Qed.
Lemma lem7082338 (x : real) : (term277 x) = (term129 x).
Proof. exact (@lem1982715 term22 x). Qed.
Lemma lem7082340 (x : nat) : (real_of_num x) = (term92 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7082341 : term103 = term130.
Proof. exact (@lem7082340 term97). Qed.
Lemma lem7082343 (x : nat) : (term94 x) = (term95 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7082344 : term22 = term96.
Proof. exact (@lem7082343 term97). Qed.
Lemma lem7082345 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7082346 : term131 = term132.
Proof. exact (MK_COMB (@lem7082345) (@lem7082344)). Qed.
Lemma lem7082347 : term133 = term134.
Proof. exact (MK_COMB (@lem7082346) (@lem7082341)). Qed.
Lemma lem7082348 : term135.
Proof. exact (@lem1981473 term22 term103 term103 term103 term9 term103). Qed.
Lemma lem7082350 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7082351 : term137 = term138.
Proof. exact (@lem7082350 (NUMERAL 0) term97). Qed.
Lemma lem7082352 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7082353 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7082354 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7082353 h1) (fun h1 : term138 = True => @lem7082352)). Qed.
Lemma lem7082355 : term138 = True.
Proof. exact (EQ_MP (@lem7082354) (@lem7082352)). Qed.
Lemma lem7082356 : term137 = True.
Proof. exact (TRANS (@lem7082351) (@lem7082355)). Qed.
Lemma lem7082357 : True = term137.
Proof. exact (SYM (@lem7082356)). Qed.
Lemma lem7082358 : term137.
Proof. exact (EQ_MP (@lem7082357) (@lem0)). Qed.
Lemma lem7082359 : term140.
Proof. exact (@lem7082348 (@lem7082358)). Qed.
Lemma lem7082361 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7082362 : term137 = term138.
Proof. exact (@lem7082361 (NUMERAL 0) term97). Qed.
Lemma lem7082363 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7082364 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7082365 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7082364 h1) (fun h1 : term138 = True => @lem7082363)). Qed.
Lemma lem7082366 : term138 = True.
Proof. exact (EQ_MP (@lem7082365) (@lem7082363)). Qed.
Lemma lem7082367 : term137 = True.
Proof. exact (TRANS (@lem7082362) (@lem7082366)). Qed.
Lemma lem7082368 : True = term137.
Proof. exact (SYM (@lem7082367)). Qed.
Lemma lem7082369 : term137.
Proof. exact (EQ_MP (@lem7082368) (@lem0)). Qed.
Lemma lem7082370 : term141.
Proof. exact (@lem7082359 (@lem7082369)). Qed.
Lemma lem7082372 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7082373 : term137 = term138.
Proof. exact (@lem7082372 (NUMERAL 0) term97). Qed.
Lemma lem7082374 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7082375 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7082376 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7082375 h1) (fun h1 : term138 = True => @lem7082374)). Qed.
Lemma lem7082377 : term138 = True.
Proof. exact (EQ_MP (@lem7082376) (@lem7082374)). Qed.
Lemma lem7082378 : term137 = True.
Proof. exact (TRANS (@lem7082373) (@lem7082377)). Qed.
Lemma lem7082379 : True = term137.
Proof. exact (SYM (@lem7082378)). Qed.
Lemma lem7082380 : term137.
Proof. exact (EQ_MP (@lem7082379) (@lem0)). Qed.
Lemma lem7082381 : term142.
Proof. exact (@lem7082370 (@lem7082380)). Qed.
Lemma lem7082383 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7082384 : term106 = term107.
Proof. exact (@lem7082383 term97 term97). Qed.
Lemma lem7082385 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7082386 : term109 = term97.
Proof. exact (EQ_MP (@lem7082385) (@lem940073)). Qed.
Lemma lem7082387 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7082388 : term107 = term103.
Proof. exact (MK_COMB (@lem7082387) (@lem7082386)). Qed.
Lemma lem7082389 : term106 = term103.
Proof. exact (TRANS (@lem7082384) (@lem7082388)). Qed.
Lemma lem7082391 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7082392 : term145 = term146.
Proof. exact (@lem7082391 term97 term97). Qed.
Lemma lem7082393 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7082394 : term109 = term97.
Proof. exact (EQ_MP (@lem7082393) (@lem940073)). Qed.
Lemma lem7082395 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7082396 : term107 = term103.
Proof. exact (MK_COMB (@lem7082395) (@lem7082394)). Qed.
Lemma lem7082397 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7082398 : term146 = term22.
Proof. exact (MK_COMB (@lem7082397) (@lem7082396)). Qed.
Lemma lem7082399 : term145 = term22.
Proof. exact (TRANS (@lem7082392) (@lem7082398)). Qed.
Lemma lem7082400 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7082401 : term147 = term131.
Proof. exact (MK_COMB (@lem7082400) (@lem7082399)). Qed.
Lemma lem7082402 : term148 = term133.
Proof. exact (MK_COMB (@lem7082401) (@lem7082389)). Qed.
Lemma lem7082404 (m : nat) : (term149 m) = term9.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7082405 : term133 = term9.
Proof. exact (@lem7082404 term97). Qed.
Lemma lem7082406 : term148 = term9.
Proof. exact (TRANS (@lem7082402) (@lem7082405)). Qed.
Lemma lem7082407 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7082408 : term150 = term151.
Proof. exact (MK_COMB (@lem7082407) (@lem7082406)). Qed.
Lemma lem7082409 : term103 = term103.
Proof. exact (eq_refl term103). Qed.
Lemma lem7082410 : term152 = term153.
Proof. exact (MK_COMB (@lem7082408) (@lem7082409)). Qed.
Lemma lem7082412 (x : nat) : (term154 x) = term9.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7082413 : term153 = term9.
Proof. exact (@lem7082412 term97). Qed.
Lemma lem7082414 : term152 = term9.
Proof. exact (TRANS (@lem7082410) (@lem7082413)). Qed.
Lemma lem7082416 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7082417 : term106 = term107.
Proof. exact (@lem7082416 term97 term97). Qed.
Lemma lem7082418 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7082419 : term109 = term97.
Proof. exact (EQ_MP (@lem7082418) (@lem940073)). Qed.
Lemma lem7082420 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7082421 : term107 = term103.
Proof. exact (MK_COMB (@lem7082420) (@lem7082419)). Qed.
Lemma lem7082422 : term106 = term103.
Proof. exact (TRANS (@lem7082417) (@lem7082421)). Qed.
Lemma lem7082423 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem7082424 : term155 = term153.
Proof. exact (MK_COMB (@lem7082423) (@lem7082422)). Qed.
Lemma lem7082426 (x : nat) : (term154 x) = term9.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7082427 : term153 = term9.
Proof. exact (@lem7082426 term97). Qed.
Lemma lem7082428 : term155 = term9.
Proof. exact (TRANS (@lem7082424) (@lem7082427)). Qed.
Lemma lem7082429 : term9 = term155.
Proof. exact (SYM (@lem7082428)). Qed.
Lemma lem7082430 : term152 = term155.
Proof. exact (TRANS (@lem7082414) (@lem7082429)). Qed.
Lemma lem7082431 : term134 = term93.
Proof. exact (@lem7082381 (@lem7082430)). Qed.
Lemma lem7082432 : term133 = term93.
Proof. exact (TRANS (@lem7082347) (@lem7082431)). Qed.
Lemma lem7082434 (x : real) : (term113 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7082435 : term93 = term9.
Proof. exact (@lem7082434 term9). Qed.
Lemma lem7082436 : term133 = term9.
Proof. exact (TRANS (@lem7082432) (@lem7082435)). Qed.
Lemma lem7082437 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7082438 : term156 = term151.
Proof. exact (MK_COMB (@lem7082437) (@lem7082436)). Qed.
Lemma lem7082439 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7082440 (x : real) : (term129 x) = (term157 x).
Proof. exact (MK_COMB (@lem7082438) (@lem7082439 x)). Qed.
Lemma lem7082441 (x : real) : (term277 x) = (term157 x).
Proof. exact (TRANS (@lem7082338 x) (@lem7082440 x)). Qed.
Lemma lem7082442 (x : real) : (term157 x) = term9.
Proof. exact (@lem1982719 x). Qed.
Lemma lem7082443 (x : real) : (term277 x) = term9.
Proof. exact (TRANS (@lem7082441 x) (@lem7082442 x)). Qed.
Lemma lem7082444 (a : real) : (term30 a) = (term30 a).
Proof. exact (eq_refl (term30 a)). Qed.
Lemma lem7082445 (x : real) (a : real) : (term276 a x) = (term278 a).
Proof. exact (MK_COMB (@lem7082444 a) (@lem7082443 x)). Qed.
Lemma lem7082446 (x : real) (a : real) : (term275 a x) = (term278 a).
Proof. exact (TRANS (@lem7082337 a x) (@lem7082445 x a)). Qed.
Lemma lem7082447 (a : real) : (term278 a) = (term26 a).
Proof. exact (@lem1982723 (term26 a)). Qed.
Lemma lem7082448 (x : real) (a : real) : (term275 a x) = (term26 a).
Proof. exact (TRANS (@lem7082446 x a) (@lem7082447 a)). Qed.
Lemma lem7082449 (x : real) (a : real) : (term274 a x) = (term26 a).
Proof. exact (TRANS (@lem7082336 a x) (@lem7082448 x a)). Qed.
Lemma lem7082458 (b : real) : (term30 b) = (term30 b).
Proof. exact (eq_refl (term30 b)). Qed.
Lemma lem7082459 (x : real) (b : real) (a : real) : (term273 b a x) = (term226 b a).
Proof. exact (MK_COMB (@lem7082458 b) (@lem7082449 x a)). Qed.
Lemma lem7082460 (a : real) (b : real) : (term226 b a) = (term226 a b).
Proof. exact (@lem1982761 (term26 a) (term26 b)). Qed.
Lemma lem7082461 (x : real) (a : real) (b : real) : (term273 b a x) = (term226 a b).
Proof. exact (TRANS (@lem7082459 x b a) (@lem7082460 a b)). Qed.
Lemma lem7082462 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7082463 (x : real) (a : real) (b : real) : (term279 b a x) = (term280 a b).
Proof. exact (MK_COMB (@lem7082462) (@lem7082461 x a b)). Qed.
Lemma lem7082464 (x : real) (a : real) (b : real) : (term281 b a x) = (term282 a b).
Proof. exact (MK_COMB (@lem7082463 x a b) (@lem7082313)). Qed.
Lemma lem7082465 (a : real) (b : real) : (term282 a b) = (term283 a b).
Proof. exact (@lem1982792 (term226 a b) term9). Qed.
Lemma lem7082467 (x : nat) : (real_of_num x) = (term92 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7082468 : term9 = term93.
Proof. exact (@lem7082467 (NUMERAL 0)). Qed.
Lemma lem7082470 (x : nat) : (term94 x) = (term95 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7082471 : term22 = term96.
Proof. exact (@lem7082470 term97). Qed.
Lemma lem7082472 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7082473 : term98 = term99.
Proof. exact (MK_COMB (@lem7082472) (@lem7082471)). Qed.
Lemma lem7082474 : term100 = term101.
Proof. exact (MK_COMB (@lem7082473) (@lem7082468)). Qed.
Lemma lem7082475 : term101 = term102.
Proof. exact (@lem1981613 term22 term9 term103 term103). Qed.
Lemma lem7082477 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7082478 : term106 = term107.
Proof. exact (@lem7082477 term97 term97). Qed.
Lemma lem7082479 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7082480 : term109 = term97.
Proof. exact (EQ_MP (@lem7082479) (@lem940073)). Qed.
Lemma lem7082481 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7082482 : term107 = term103.
Proof. exact (MK_COMB (@lem7082481) (@lem7082480)). Qed.
Lemma lem7082483 : term106 = term103.
Proof. exact (TRANS (@lem7082478) (@lem7082482)). Qed.
Lemma lem7082485 (x : nat) : (term110 x) = term9.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7082486 : term100 = term9.
Proof. exact (@lem7082485 term97). Qed.
Lemma lem7082487 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7082488 : term111 = term112.
Proof. exact (MK_COMB (@lem7082487) (@lem7082486)). Qed.
Lemma lem7082489 : term102 = term93.
Proof. exact (MK_COMB (@lem7082488) (@lem7082483)). Qed.
Lemma lem7082490 : term101 = term93.
Proof. exact (TRANS (@lem7082475) (@lem7082489)). Qed.
Lemma lem7082491 : term100 = term93.
Proof. exact (TRANS (@lem7082474) (@lem7082490)). Qed.
Lemma lem7082493 (x : real) : (term113 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7082494 : term93 = term9.
Proof. exact (@lem7082493 term9). Qed.
Lemma lem7082495 : term100 = term9.
Proof. exact (TRANS (@lem7082491) (@lem7082494)). Qed.
Lemma lem7082496 (a : real) (b : real) : (term284 a b) = (term284 a b).
Proof. exact (eq_refl (term284 a b)). Qed.
Lemma lem7082497 (a : real) (b : real) : (term283 a b) = (term285 a b).
Proof. exact (MK_COMB (@lem7082496 a b) (@lem7082495)). Qed.
Lemma lem7082498 (a : real) (b : real) : (term285 a b) = (term226 a b).
Proof. exact (@lem1982723 (term226 a b)). Qed.
Lemma lem7082499 (a : real) (b : real) : (term283 a b) = (term226 a b).
Proof. exact (TRANS (@lem7082497 a b) (@lem7082498 a b)). Qed.
Lemma lem7082500 (a : real) (b : real) : (term282 a b) = (term226 a b).
Proof. exact (TRANS (@lem7082465 a b) (@lem7082499 a b)). Qed.
Lemma lem7082501 (x : real) (a : real) (b : real) : (term281 b a x) = (term226 a b).
Proof. exact (TRANS (@lem7082464 x a b) (@lem7082500 a b)). Qed.
Lemma lem7082502 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7082503 (x : real) (a : real) (b : real) : (term286 b a x) = (term230 a b).
Proof. exact (MK_COMB (@lem7082502) (@lem7082501 x a b)). Qed.
Lemma lem7082504 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem7082505 (x : real) (a : real) (b : real) : (term272 b a x) = (term231 a b).
Proof. exact (MK_COMB (@lem7082503 x a b) (@lem7082504)). Qed.
Lemma lem7082506 (x : real) (a : real) (b : real) : (term271 b a x) = (term231 a b).
Proof. exact (TRANS (@lem7082312 b a x) (@lem7082505 x a b)). Qed.
Lemma lem7082507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7082508 (a : real) (b : real) (x : real) : (term287 b a x) = (term288 a b x).
Proof. exact (MK_COMB (@lem7082507) (@lem7082311 a b x)). Qed.
Lemma lem7082509 (x : real) (a : real) (b : real) : (term289 b a x) = (term290 x a b).
Proof. exact (MK_COMB (@lem7082508 a b x) (@lem7082506 x a b)). Qed.
Lemma lem7082510 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7082511 (a : real) (b : real) : (term56 a b) = (term56 a b).
Proof. exact (MK_COMB (@lem7082510) (@lem7082086 a b)). Qed.
Lemma lem7082512 (x : real) (a : real) (b : real) : (term76 b a x) = (term291 x a b).
Proof. exact (MK_COMB (@lem7082511 a b) (@lem7082509 x a b)). Qed.
Lemma lem7082513 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7082514 (a : real) (x : real) : (term77 a x) = (term292 a x).
Proof. exact (MK_COMB (@lem7082513) (@lem7082083 a x)). Qed.
Lemma lem7082515 (x : real) (a : real) (b : real) : (term79 b a x) = (term293 x a b).
Proof. exact (MK_COMB (@lem7082514 a x) (@lem7082512 x a b)). Qed.
Lemma lem7082516 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7082517 (a : real) (b : real) (x : real) : (term86 b a x) = (term294 a b x).
Proof. exact (MK_COMB (@lem7082516) (@lem7082052 a b x)). Qed.
Lemma lem7082518 (x : real) (a : real) (b : real) : (term87 b a x) = (term295 x a b).
Proof. exact (MK_COMB (@lem7082517 a b x) (@lem7082515 x a b)). Qed.
Lemma lem7082529 (x : real) (a : real) (b : real) : (term71 b a x) = (term295 x a b).
Proof. exact (TRANS (@lem7081486 b a x) (@lem7082518 x a b)). Qed.
Lemma lem7082530 (x : real) (a : real) (b : real) : (term37 b a x) = (term295 x a b).
Proof. exact (TRANS (@lem7081470 b a x) (@lem7082529 x a b)). Qed.
Lemma lem7082531 (x : real) (a : real) (b : real) (h1 : term295 x a b) : term295 x a b.
Proof. exact (h1). Qed.
Lemma lem7082532 (a : real) (b : real) (x : real) (h1 : term220 a b x) : term220 a b x.
Proof. exact (h1). Qed.
Lemma lem7082533 (a : real) (b : real) (x : real) (h1 : term220 a b x) : term219 a b x.
Proof. exact (proj2 (@lem7082532 a b x h1)). Qed.
Lemma lem7082535 (a : real) (b : real) (x : real) (h1 : term220 a b x) : term218 a b x.
Proof. exact (proj2 (@lem7082533 a b x h1)). Qed.
Lemma lem7082536 (a : real) (b : real) (x : real) (h1 : term220 a b x) : term55 a b.
Proof. exact (proj1 (@lem7082533 a b x h1)). Qed.
Lemma lem7082538 (a : real) (b : real) (x : real) (h1 : term220 a b x) : term52 a b.
Proof. exact (proj1 (@lem7082536 a b x h1)). Qed.
Lemma lem7082540 (a : real) (b : real) (x : real) (h1 : term220 a b x) : term168 a b.
Proof. exact (proj1 (@lem7082535 a b x h1)). Qed.
Lemma lem7082542 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7082543 : term296 = term137.
Proof. exact (@lem7082542 term9 term103). Qed.
Lemma lem7082545 (x : nat) : (real_of_num x) = (term92 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7082546 : term103 = term130.
Proof. exact (@lem7082545 term97). Qed.
Lemma lem7082548 (x : nat) : (real_of_num x) = (term92 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7082549 : term9 = term93.
Proof. exact (@lem7082548 (NUMERAL 0)). Qed.
Lemma lem7082550 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7082551 : term297 = term298.
Proof. exact (MK_COMB (@lem7082550) (@lem7082549)). Qed.
Lemma lem7082552 : term137 = term299.
Proof. exact (MK_COMB (@lem7082551) (@lem7082546)). Qed.
Lemma lem7082553 : term300.
Proof. exact (@lem1980255 term9 term103 term103 term103). Qed.
Lemma lem7082555 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7082556 : term137 = term138.
Proof. exact (@lem7082555 (NUMERAL 0) term97). Qed.
Lemma lem7082557 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7082558 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7082559 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7082558 h1) (fun h1 : term138 = True => @lem7082557)). Qed.
Lemma lem7082560 : term138 = True.
Proof. exact (EQ_MP (@lem7082559) (@lem7082557)). Qed.
Lemma lem7082561 : term137 = True.
Proof. exact (TRANS (@lem7082556) (@lem7082560)). Qed.
Lemma lem7082562 : True = term137.
Proof. exact (SYM (@lem7082561)). Qed.
Lemma lem7082563 : term137.
Proof. exact (EQ_MP (@lem7082562) (@lem0)). Qed.
Lemma lem7082564 : term301.
Proof. exact (@lem7082553 (@lem7082563)). Qed.
Lemma lem7082566 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7082567 : term137 = term138.
Proof. exact (@lem7082566 (NUMERAL 0) term97). Qed.
Lemma lem7082568 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7082569 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7082570 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7082569 h1) (fun h1 : term138 = True => @lem7082568)). Qed.
Lemma lem7082571 : term138 = True.
Proof. exact (EQ_MP (@lem7082570) (@lem7082568)). Qed.
Lemma lem7082572 : term137 = True.
Proof. exact (TRANS (@lem7082567) (@lem7082571)). Qed.
Lemma lem7082573 : True = term137.
Proof. exact (SYM (@lem7082572)). Qed.
Lemma lem7082574 : term137.
Proof. exact (EQ_MP (@lem7082573) (@lem0)). Qed.
Lemma lem7082575 : term299 = term302.
Proof. exact (@lem7082564 (@lem7082574)). Qed.
Lemma lem7082577 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7082578 : term106 = term107.
Proof. exact (@lem7082577 term97 term97). Qed.
Lemma lem7082579 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7082580 : term109 = term97.
Proof. exact (EQ_MP (@lem7082579) (@lem940073)). Qed.
Lemma lem7082581 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7082582 : term107 = term103.
Proof. exact (MK_COMB (@lem7082581) (@lem7082580)). Qed.
Lemma lem7082583 : term106 = term103.
Proof. exact (TRANS (@lem7082578) (@lem7082582)). Qed.
Lemma lem7082585 (x : nat) : (term154 x) = term9.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7082586 : term153 = term9.
Proof. exact (@lem7082585 term97). Qed.
Lemma lem7082587 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7082588 : term303 = term297.
Proof. exact (MK_COMB (@lem7082587) (@lem7082586)). Qed.
Lemma lem7082589 : term302 = term137.
Proof. exact (MK_COMB (@lem7082588) (@lem7082583)). Qed.
Lemma lem7082591 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7082592 : term137 = term138.
Proof. exact (@lem7082591 (NUMERAL 0) term97). Qed.
Lemma lem7082593 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7082594 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7082595 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7082594 h1) (fun h1 : term138 = True => @lem7082593)). Qed.
Lemma lem7082596 : term138 = True.
Proof. exact (EQ_MP (@lem7082595) (@lem7082593)). Qed.
Lemma lem7082597 : term137 = True.
Proof. exact (TRANS (@lem7082592) (@lem7082596)). Qed.
Lemma lem7082598 : term302 = True.
Proof. exact (TRANS (@lem7082589) (@lem7082597)). Qed.
Lemma lem7082599 : term299 = True.
Proof. exact (TRANS (@lem7082575) (@lem7082598)). Qed.
Lemma lem7082600 : term137 = True.
Proof. exact (TRANS (@lem7082552) (@lem7082599)). Qed.
Lemma lem7082601 : term296 = True.
Proof. exact (TRANS (@lem7082543) (@lem7082600)). Qed.
Lemma lem7082602 : True = term296.
Proof. exact (SYM (@lem7082601)). Qed.
Lemma lem7082603 : term296.
Proof. exact (EQ_MP (@lem7082602) (@lem0)). Qed.
Lemma lem7082604 (a : real) (b : real) (x : real) (h1 : term220 a b x) : term304 a b.
Proof. exact (conj (@lem7082603) (@lem7082538 a b x h1)). Qed.
Lemma lem7082606 (x : real) (y : real) : term305 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7082607 (a : real) (b : real) : term306 a b.
Proof. exact (@lem7082606 term103 (term48 a b)). Qed.
Lemma lem7082608 (a : real) (b : real) (x : real) (h1 : term220 a b x) : term307 a b.
Proof. exact (@lem7082607 a b (@lem7082604 a b x h1)). Qed.
Lemma lem7082609 (a : real) (b : real) : (term308 a b) = (term48 a b).
Proof. exact (@lem1982733 (term48 a b)). Qed.
Lemma lem7082610 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7082611 (a : real) (b : real) : (term309 a b) = (term50 a b).
Proof. exact (MK_COMB (@lem7082610) (@lem7082609 a b)). Qed.
Lemma lem7082612 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem7082613 (a : real) (b : real) : (term307 a b) = (term52 a b).
Proof. exact (MK_COMB (@lem7082611 a b) (@lem7082612)). Qed.
Lemma lem7082614 (a : real) (b : real) (x : real) (h1 : term220 a b x) : term52 a b.
Proof. exact (EQ_MP (@lem7082613 a b) (@lem7082608 a b x h1)). Qed.
Lemma lem7082616 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7082617 : term296 = term137.
Proof. exact (@lem7082616 term9 term103). Qed.
Lemma lem7082619 (x : nat) : (real_of_num x) = (term92 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7082620 : term103 = term130.
Proof. exact (@lem7082619 term97). Qed.
Lemma lem7082622 (x : nat) : (real_of_num x) = (term92 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7082623 : term9 = term93.
Proof. exact (@lem7082622 (NUMERAL 0)). Qed.
Lemma lem7082624 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7082625 : term297 = term298.
Proof. exact (MK_COMB (@lem7082624) (@lem7082623)). Qed.
Lemma lem7082626 : term137 = term299.
Proof. exact (MK_COMB (@lem7082625) (@lem7082620)). Qed.
Lemma lem7082627 : term300.
Proof. exact (@lem1980255 term9 term103 term103 term103). Qed.
Lemma lem7082629 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7082630 : term137 = term138.
Proof. exact (@lem7082629 (NUMERAL 0) term97). Qed.
Lemma lem7082631 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7082632 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7082633 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7082632 h1) (fun h1 : term138 = True => @lem7082631)). Qed.
Lemma lem7082634 : term138 = True.
Proof. exact (EQ_MP (@lem7082633) (@lem7082631)). Qed.
Lemma lem7082635 : term137 = True.
Proof. exact (TRANS (@lem7082630) (@lem7082634)). Qed.
Lemma lem7082636 : True = term137.
Proof. exact (SYM (@lem7082635)). Qed.
Lemma lem7082637 : term137.
Proof. exact (EQ_MP (@lem7082636) (@lem0)). Qed.
Lemma lem7082638 : term301.
Proof. exact (@lem7082627 (@lem7082637)). Qed.
Lemma lem7082640 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7082641 : term137 = term138.
Proof. exact (@lem7082640 (NUMERAL 0) term97). Qed.
Lemma lem7082642 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7082643 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7082644 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7082643 h1) (fun h1 : term138 = True => @lem7082642)). Qed.
Lemma lem7082645 : term138 = True.
Proof. exact (EQ_MP (@lem7082644) (@lem7082642)). Qed.
Lemma lem7082646 : term137 = True.
Proof. exact (TRANS (@lem7082641) (@lem7082645)). Qed.
Lemma lem7082647 : True = term137.
Proof. exact (SYM (@lem7082646)). Qed.
Lemma lem7082648 : term137.
Proof. exact (EQ_MP (@lem7082647) (@lem0)). Qed.
Lemma lem7082649 : term299 = term302.
Proof. exact (@lem7082638 (@lem7082648)). Qed.
Lemma lem7082651 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7082652 : term106 = term107.
Proof. exact (@lem7082651 term97 term97). Qed.
Lemma lem7082653 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7082654 : term109 = term97.
Proof. exact (EQ_MP (@lem7082653) (@lem940073)). Qed.
Lemma lem7082655 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7082656 : term107 = term103.
Proof. exact (MK_COMB (@lem7082655) (@lem7082654)). Qed.
Lemma lem7082657 : term106 = term103.
Proof. exact (TRANS (@lem7082652) (@lem7082656)). Qed.
Lemma lem7082659 (x : nat) : (term154 x) = term9.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7082660 : term153 = term9.
Proof. exact (@lem7082659 term97). Qed.
Lemma lem7082661 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7082662 : term303 = term297.
Proof. exact (MK_COMB (@lem7082661) (@lem7082660)). Qed.
Lemma lem7082663 : term302 = term137.
Proof. exact (MK_COMB (@lem7082662) (@lem7082657)). Qed.
Lemma lem7082665 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7082666 : term137 = term138.
Proof. exact (@lem7082665 (NUMERAL 0) term97). Qed.
Lemma lem7082667 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7082668 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7082669 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7082668 h1) (fun h1 : term138 = True => @lem7082667)). Qed.
Lemma lem7082670 : term138 = True.
Proof. exact (EQ_MP (@lem7082669) (@lem7082667)). Qed.
Lemma lem7082671 : term137 = True.
Proof. exact (TRANS (@lem7082666) (@lem7082670)). Qed.
Lemma lem7082672 : term302 = True.
Proof. exact (TRANS (@lem7082663) (@lem7082671)). Qed.
Lemma lem7082673 : term299 = True.
Proof. exact (TRANS (@lem7082649) (@lem7082672)). Qed.
Lemma lem7082674 : term137 = True.
Proof. exact (TRANS (@lem7082626) (@lem7082673)). Qed.
Lemma lem7082675 : term296 = True.
Proof. exact (TRANS (@lem7082617) (@lem7082674)). Qed.
Lemma lem7082676 : True = term296.
Proof. exact (SYM (@lem7082675)). Qed.
Lemma lem7082677 : term296.
Proof. exact (EQ_MP (@lem7082676) (@lem0)). Qed.
Lemma lem7082678 (a : real) (b : real) (x : real) (h1 : term220 a b x) : term310 a b.
Proof. exact (conj (@lem7082677) (@lem7082540 a b x h1)). Qed.
Lemma lem7082680 (x : real) (y : real) : term311 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem7082681 (a : real) (b : real) : term312 a b.
Proof. exact (@lem7082680 term103 (term47 a b)). Qed.
Lemma lem7082682 (a : real) (b : real) (x : real) (h1 : term220 a b x) : term313 a b.
Proof. exact (@lem7082681 a b (@lem7082678 a b x h1)). Qed.
Lemma lem7082683 (a : real) (b : real) : (term314 a b) = (term47 a b).
Proof. exact (@lem1982733 (term47 a b)). Qed.
Lemma lem7082684 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7082685 (a : real) (b : real) : (term315 a b) = (term167 a b).
Proof. exact (MK_COMB (@lem7082684) (@lem7082683 a b)). Qed.
Lemma lem7082686 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem7082687 (a : real) (b : real) : (term313 a b) = (term168 a b).
Proof. exact (MK_COMB (@lem7082685 a b) (@lem7082686)). Qed.
Lemma lem7082688 (a : real) (b : real) (x : real) (h1 : term220 a b x) : term168 a b.
Proof. exact (EQ_MP (@lem7082687 a b) (@lem7082682 a b x h1)). Qed.
Lemma lem7082689 (a : real) (b : real) (x : real) (h1 : term220 a b x) : term316 a b.
Proof. exact (conj (@lem7082688 a b x h1) (@lem7082614 a b x h1)). Qed.
Lemma lem7082691 (x : real) (y : real) : term317 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem7082692 (a : real) (b : real) : term318 a b.
Proof. exact (@lem7082691 (term47 a b) (term48 a b)). Qed.
Lemma lem7082693 (a : real) (b : real) (x : real) (h1 : term220 a b x) : term319 a b.
Proof. exact (@lem7082692 a b (@lem7082689 a b x h1)). Qed.
Lemma lem7082694 (a : real) (b : real) : (term320 a b) = (term321 a b).
Proof. exact (@lem1982753 a (term26 a) (term26 b) b). Qed.
Lemma lem7082695 (a : real) : (term277 a) = (term129 a).
Proof. exact (@lem1982715 term22 a). Qed.
Lemma lem7082697 (x : nat) : (real_of_num x) = (term92 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7082698 : term103 = term130.
Proof. exact (@lem7082697 term97). Qed.
Lemma lem7082700 (x : nat) : (term94 x) = (term95 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7082701 : term22 = term96.
Proof. exact (@lem7082700 term97). Qed.
Lemma lem7082702 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7082703 : term131 = term132.
Proof. exact (MK_COMB (@lem7082702) (@lem7082701)). Qed.
Lemma lem7082704 : term133 = term134.
Proof. exact (MK_COMB (@lem7082703) (@lem7082698)). Qed.
Lemma lem7082705 : term135.
Proof. exact (@lem1981473 term22 term103 term103 term103 term9 term103). Qed.
Lemma lem7082707 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7082708 : term137 = term138.
Proof. exact (@lem7082707 (NUMERAL 0) term97). Qed.
Lemma lem7082709 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7082710 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7082711 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7082710 h1) (fun h1 : term138 = True => @lem7082709)). Qed.
Lemma lem7082712 : term138 = True.
Proof. exact (EQ_MP (@lem7082711) (@lem7082709)). Qed.
Lemma lem7082713 : term137 = True.
Proof. exact (TRANS (@lem7082708) (@lem7082712)). Qed.
Lemma lem7082714 : True = term137.
Proof. exact (SYM (@lem7082713)). Qed.
Lemma lem7082715 : term137.
Proof. exact (EQ_MP (@lem7082714) (@lem0)). Qed.
Lemma lem7082716 : term140.
Proof. exact (@lem7082705 (@lem7082715)). Qed.
Lemma lem7082718 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7082719 : term137 = term138.
Proof. exact (@lem7082718 (NUMERAL 0) term97). Qed.
Lemma lem7082720 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7082721 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7082722 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7082721 h1) (fun h1 : term138 = True => @lem7082720)). Qed.
Lemma lem7082723 : term138 = True.
Proof. exact (EQ_MP (@lem7082722) (@lem7082720)). Qed.
Lemma lem7082724 : term137 = True.
Proof. exact (TRANS (@lem7082719) (@lem7082723)). Qed.
Lemma lem7082725 : True = term137.
Proof. exact (SYM (@lem7082724)). Qed.
Lemma lem7082726 : term137.
Proof. exact (EQ_MP (@lem7082725) (@lem0)). Qed.
Lemma lem7082727 : term141.
Proof. exact (@lem7082716 (@lem7082726)). Qed.
Lemma lem7082729 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7082730 : term137 = term138.
Proof. exact (@lem7082729 (NUMERAL 0) term97). Qed.
Lemma lem7082731 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7082732 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7082733 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7082732 h1) (fun h1 : term138 = True => @lem7082731)). Qed.
Lemma lem7082734 : term138 = True.
Proof. exact (EQ_MP (@lem7082733) (@lem7082731)). Qed.
Lemma lem7082735 : term137 = True.
Proof. exact (TRANS (@lem7082730) (@lem7082734)). Qed.
Lemma lem7082736 : True = term137.
Proof. exact (SYM (@lem7082735)). Qed.
Lemma lem7082737 : term137.
Proof. exact (EQ_MP (@lem7082736) (@lem0)). Qed.
Lemma lem7082738 : term142.
Proof. exact (@lem7082727 (@lem7082737)). Qed.
Lemma lem7082740 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7082741 : term106 = term107.
Proof. exact (@lem7082740 term97 term97). Qed.
Lemma lem7082742 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7082743 : term109 = term97.
Proof. exact (EQ_MP (@lem7082742) (@lem940073)). Qed.
Lemma lem7082744 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7082745 : term107 = term103.
Proof. exact (MK_COMB (@lem7082744) (@lem7082743)). Qed.
Lemma lem7082746 : term106 = term103.
Proof. exact (TRANS (@lem7082741) (@lem7082745)). Qed.
Lemma lem7082748 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7082749 : term145 = term146.
Proof. exact (@lem7082748 term97 term97). Qed.
Lemma lem7082750 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7082751 : term109 = term97.
Proof. exact (EQ_MP (@lem7082750) (@lem940073)). Qed.
Lemma lem7082752 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7082753 : term107 = term103.
Proof. exact (MK_COMB (@lem7082752) (@lem7082751)). Qed.
Lemma lem7082754 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7082755 : term146 = term22.
Proof. exact (MK_COMB (@lem7082754) (@lem7082753)). Qed.
Lemma lem7082756 : term145 = term22.
Proof. exact (TRANS (@lem7082749) (@lem7082755)). Qed.
Lemma lem7082757 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7082758 : term147 = term131.
Proof. exact (MK_COMB (@lem7082757) (@lem7082756)). Qed.
Lemma lem7082759 : term148 = term133.
Proof. exact (MK_COMB (@lem7082758) (@lem7082746)). Qed.
Lemma lem7082761 (m : nat) : (term149 m) = term9.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7082762 : term133 = term9.
Proof. exact (@lem7082761 term97). Qed.
Lemma lem7082763 : term148 = term9.
Proof. exact (TRANS (@lem7082759) (@lem7082762)). Qed.
Lemma lem7082764 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7082765 : term150 = term151.
Proof. exact (MK_COMB (@lem7082764) (@lem7082763)). Qed.
Lemma lem7082766 : term103 = term103.
Proof. exact (eq_refl term103). Qed.
Lemma lem7082767 : term152 = term153.
Proof. exact (MK_COMB (@lem7082765) (@lem7082766)). Qed.
Lemma lem7082769 (x : nat) : (term154 x) = term9.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7082770 : term153 = term9.
Proof. exact (@lem7082769 term97). Qed.
Lemma lem7082771 : term152 = term9.
Proof. exact (TRANS (@lem7082767) (@lem7082770)). Qed.
Lemma lem7082773 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7082774 : term106 = term107.
Proof. exact (@lem7082773 term97 term97). Qed.
Lemma lem7082775 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7082776 : term109 = term97.
Proof. exact (EQ_MP (@lem7082775) (@lem940073)). Qed.
Lemma lem7082777 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7082778 : term107 = term103.
Proof. exact (MK_COMB (@lem7082777) (@lem7082776)). Qed.
Lemma lem7082779 : term106 = term103.
Proof. exact (TRANS (@lem7082774) (@lem7082778)). Qed.
Lemma lem7082780 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem7082781 : term155 = term153.
Proof. exact (MK_COMB (@lem7082780) (@lem7082779)). Qed.
Lemma lem7082783 (x : nat) : (term154 x) = term9.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7082784 : term153 = term9.
Proof. exact (@lem7082783 term97). Qed.
Lemma lem7082785 : term155 = term9.
Proof. exact (TRANS (@lem7082781) (@lem7082784)). Qed.
Lemma lem7082786 : term9 = term155.
Proof. exact (SYM (@lem7082785)). Qed.
Lemma lem7082787 : term152 = term155.
Proof. exact (TRANS (@lem7082771) (@lem7082786)). Qed.
Lemma lem7082788 : term134 = term93.
Proof. exact (@lem7082738 (@lem7082787)). Qed.
Lemma lem7082789 : term133 = term93.
Proof. exact (TRANS (@lem7082704) (@lem7082788)). Qed.
Lemma lem7082791 (x : real) : (term113 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7082792 : term93 = term9.
Proof. exact (@lem7082791 term9). Qed.
Lemma lem7082793 : term133 = term9.
Proof. exact (TRANS (@lem7082789) (@lem7082792)). Qed.
Lemma lem7082794 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7082795 : term156 = term151.
Proof. exact (MK_COMB (@lem7082794) (@lem7082793)). Qed.
Lemma lem7082796 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem7082797 (a : real) : (term129 a) = (term157 a).
Proof. exact (MK_COMB (@lem7082795) (@lem7082796 a)). Qed.
Lemma lem7082798 (a : real) : (term277 a) = (term157 a).
Proof. exact (TRANS (@lem7082695 a) (@lem7082797 a)). Qed.
Lemma lem7082799 (a : real) : (term157 a) = term9.
Proof. exact (@lem1982719 a). Qed.
Lemma lem7082800 (a : real) : (term277 a) = term9.
Proof. exact (TRANS (@lem7082798 a) (@lem7082799 a)). Qed.
Lemma lem7082801 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7082802 (a : real) : (term322 a) = term227.
Proof. exact (MK_COMB (@lem7082801) (@lem7082800 a)). Qed.
Lemma lem7082803 (b : real) : (term128 b) = (term129 b).
Proof. exact (@lem1982713 term22 b). Qed.
Lemma lem7082805 (x : nat) : (real_of_num x) = (term92 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7082806 : term103 = term130.
Proof. exact (@lem7082805 term97). Qed.
Lemma lem7082808 (x : nat) : (term94 x) = (term95 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7082809 : term22 = term96.
Proof. exact (@lem7082808 term97). Qed.
Lemma lem7082810 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7082811 : term131 = term132.
Proof. exact (MK_COMB (@lem7082810) (@lem7082809)). Qed.
Lemma lem7082812 : term133 = term134.
Proof. exact (MK_COMB (@lem7082811) (@lem7082806)). Qed.
Lemma lem7082813 : term135.
Proof. exact (@lem1981473 term22 term103 term103 term103 term9 term103). Qed.
Lemma lem7082815 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7082816 : term137 = term138.
Proof. exact (@lem7082815 (NUMERAL 0) term97). Qed.
Lemma lem7082817 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7082818 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7082819 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7082818 h1) (fun h1 : term138 = True => @lem7082817)). Qed.
Lemma lem7082820 : term138 = True.
Proof. exact (EQ_MP (@lem7082819) (@lem7082817)). Qed.
Lemma lem7082821 : term137 = True.
Proof. exact (TRANS (@lem7082816) (@lem7082820)). Qed.
Lemma lem7082822 : True = term137.
Proof. exact (SYM (@lem7082821)). Qed.
Lemma lem7082823 : term137.
Proof. exact (EQ_MP (@lem7082822) (@lem0)). Qed.
Lemma lem7082824 : term140.
Proof. exact (@lem7082813 (@lem7082823)). Qed.
Lemma lem7082826 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7082827 : term137 = term138.
Proof. exact (@lem7082826 (NUMERAL 0) term97). Qed.
Lemma lem7082828 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7082829 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7082830 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7082829 h1) (fun h1 : term138 = True => @lem7082828)). Qed.
Lemma lem7082831 : term138 = True.
Proof. exact (EQ_MP (@lem7082830) (@lem7082828)). Qed.
Lemma lem7082832 : term137 = True.
Proof. exact (TRANS (@lem7082827) (@lem7082831)). Qed.
Lemma lem7082833 : True = term137.
Proof. exact (SYM (@lem7082832)). Qed.
Lemma lem7082834 : term137.
Proof. exact (EQ_MP (@lem7082833) (@lem0)). Qed.
Lemma lem7082835 : term141.
Proof. exact (@lem7082824 (@lem7082834)). Qed.
Lemma lem7082837 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7082838 : term137 = term138.
Proof. exact (@lem7082837 (NUMERAL 0) term97). Qed.
Lemma lem7082839 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7082840 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7082841 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7082840 h1) (fun h1 : term138 = True => @lem7082839)). Qed.
Lemma lem7082842 : term138 = True.
Proof. exact (EQ_MP (@lem7082841) (@lem7082839)). Qed.
Lemma lem7082843 : term137 = True.
Proof. exact (TRANS (@lem7082838) (@lem7082842)). Qed.
Lemma lem7082844 : True = term137.
Proof. exact (SYM (@lem7082843)). Qed.
Lemma lem7082845 : term137.
Proof. exact (EQ_MP (@lem7082844) (@lem0)). Qed.
Lemma lem7082846 : term142.
Proof. exact (@lem7082835 (@lem7082845)). Qed.
Lemma lem7082848 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7082849 : term106 = term107.
Proof. exact (@lem7082848 term97 term97). Qed.
Lemma lem7082850 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7082851 : term109 = term97.
Proof. exact (EQ_MP (@lem7082850) (@lem940073)). Qed.
Lemma lem7082852 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7082853 : term107 = term103.
Proof. exact (MK_COMB (@lem7082852) (@lem7082851)). Qed.
Lemma lem7082854 : term106 = term103.
Proof. exact (TRANS (@lem7082849) (@lem7082853)). Qed.
Lemma lem7082856 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7082857 : term145 = term146.
Proof. exact (@lem7082856 term97 term97). Qed.
Lemma lem7082858 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7082859 : term109 = term97.
Proof. exact (EQ_MP (@lem7082858) (@lem940073)). Qed.
Lemma lem7082860 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7082861 : term107 = term103.
Proof. exact (MK_COMB (@lem7082860) (@lem7082859)). Qed.
Lemma lem7082862 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7082863 : term146 = term22.
Proof. exact (MK_COMB (@lem7082862) (@lem7082861)). Qed.
Lemma lem7082864 : term145 = term22.
Proof. exact (TRANS (@lem7082857) (@lem7082863)). Qed.
Lemma lem7082865 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7082866 : term147 = term131.
Proof. exact (MK_COMB (@lem7082865) (@lem7082864)). Qed.
Lemma lem7082867 : term148 = term133.
Proof. exact (MK_COMB (@lem7082866) (@lem7082854)). Qed.
Lemma lem7082869 (m : nat) : (term149 m) = term9.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7082870 : term133 = term9.
Proof. exact (@lem7082869 term97). Qed.
Lemma lem7082871 : term148 = term9.
Proof. exact (TRANS (@lem7082867) (@lem7082870)). Qed.
Lemma lem7082872 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7082873 : term150 = term151.
Proof. exact (MK_COMB (@lem7082872) (@lem7082871)). Qed.
Lemma lem7082874 : term103 = term103.
Proof. exact (eq_refl term103). Qed.
Lemma lem7082875 : term152 = term153.
Proof. exact (MK_COMB (@lem7082873) (@lem7082874)). Qed.
Lemma lem7082877 (x : nat) : (term154 x) = term9.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7082878 : term153 = term9.
Proof. exact (@lem7082877 term97). Qed.
Lemma lem7082879 : term152 = term9.
Proof. exact (TRANS (@lem7082875) (@lem7082878)). Qed.
Lemma lem7082881 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7082882 : term106 = term107.
Proof. exact (@lem7082881 term97 term97). Qed.
Lemma lem7082883 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7082884 : term109 = term97.
Proof. exact (EQ_MP (@lem7082883) (@lem940073)). Qed.
Lemma lem7082885 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7082886 : term107 = term103.
Proof. exact (MK_COMB (@lem7082885) (@lem7082884)). Qed.
Lemma lem7082887 : term106 = term103.
Proof. exact (TRANS (@lem7082882) (@lem7082886)). Qed.
Lemma lem7082888 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem7082889 : term155 = term153.
Proof. exact (MK_COMB (@lem7082888) (@lem7082887)). Qed.
Lemma lem7082891 (x : nat) : (term154 x) = term9.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7082892 : term153 = term9.
Proof. exact (@lem7082891 term97). Qed.
Lemma lem7082893 : term155 = term9.
Proof. exact (TRANS (@lem7082889) (@lem7082892)). Qed.
Lemma lem7082894 : term9 = term155.
Proof. exact (SYM (@lem7082893)). Qed.
Lemma lem7082895 : term152 = term155.
Proof. exact (TRANS (@lem7082879) (@lem7082894)). Qed.
Lemma lem7082896 : term134 = term93.
Proof. exact (@lem7082846 (@lem7082895)). Qed.
Lemma lem7082897 : term133 = term93.
Proof. exact (TRANS (@lem7082812) (@lem7082896)). Qed.
Lemma lem7082899 (x : real) : (term113 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7082900 : term93 = term9.
Proof. exact (@lem7082899 term9). Qed.
Lemma lem7082901 : term133 = term9.
Proof. exact (TRANS (@lem7082897) (@lem7082900)). Qed.
Lemma lem7082902 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7082903 : term156 = term151.
Proof. exact (MK_COMB (@lem7082902) (@lem7082901)). Qed.
Lemma lem7082904 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7082905 (b : real) : (term129 b) = (term157 b).
Proof. exact (MK_COMB (@lem7082903) (@lem7082904 b)). Qed.
Lemma lem7082906 (b : real) : (term128 b) = (term157 b).
Proof. exact (TRANS (@lem7082803 b) (@lem7082905 b)). Qed.
Lemma lem7082907 (b : real) : (term157 b) = term9.
Proof. exact (@lem1982719 b). Qed.
Lemma lem7082908 (b : real) : (term128 b) = term9.
Proof. exact (TRANS (@lem7082906 b) (@lem7082907 b)). Qed.
Lemma lem7082909 (a : real) (b : real) : (term321 a b) = term323.
Proof. exact (MK_COMB (@lem7082802 a) (@lem7082908 b)). Qed.
Lemma lem7082910 (a : real) (b : real) : (term320 a b) = term323.
Proof. exact (TRANS (@lem7082694 a b) (@lem7082909 a b)). Qed.
Lemma lem7082911 : term323 = term9.
Proof. exact (@lem1982721 term9). Qed.
Lemma lem7082912 (a : real) (b : real) : (term320 a b) = term9.
Proof. exact (TRANS (@lem7082910 a b) (@lem7082911)). Qed.
Lemma lem7082913 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7082914 (a : real) (b : real) : (term324 a b) = term325.
Proof. exact (MK_COMB (@lem7082913) (@lem7082912 a b)). Qed.
Lemma lem7082915 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem7082916 (a : real) (b : real) : (term319 a b) = term326.
Proof. exact (MK_COMB (@lem7082914 a b) (@lem7082915)). Qed.
Lemma lem7082917 (a : real) (b : real) (x : real) (h1 : term220 a b x) : term326.
Proof. exact (EQ_MP (@lem7082916 a b) (@lem7082693 a b x h1)). Qed.
Lemma lem7082919 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7082920 : term326 = term327.
Proof. exact (@lem7082919 term9 term9). Qed.
Lemma lem7082922 (x : nat) : (real_of_num x) = (term92 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7082923 : term9 = term93.
Proof. exact (@lem7082922 (NUMERAL 0)). Qed.
Lemma lem7082925 (x : nat) : (real_of_num x) = (term92 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7082926 : term9 = term93.
Proof. exact (@lem7082925 (NUMERAL 0)). Qed.
Lemma lem7082927 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7082928 : term297 = term298.
Proof. exact (MK_COMB (@lem7082927) (@lem7082926)). Qed.
Lemma lem7082929 : term327 = term328.
Proof. exact (MK_COMB (@lem7082928) (@lem7082923)). Qed.
Lemma lem7082930 : term329.
Proof. exact (@lem1980255 term9 term103 term9 term103). Qed.
Lemma lem7082932 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7082933 : term137 = term138.
Proof. exact (@lem7082932 (NUMERAL 0) term97). Qed.
Lemma lem7082934 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7082935 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7082936 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7082935 h1) (fun h1 : term138 = True => @lem7082934)). Qed.
Lemma lem7082937 : term138 = True.
Proof. exact (EQ_MP (@lem7082936) (@lem7082934)). Qed.
Lemma lem7082938 : term137 = True.
Proof. exact (TRANS (@lem7082933) (@lem7082937)). Qed.
Lemma lem7082939 : True = term137.
Proof. exact (SYM (@lem7082938)). Qed.
Lemma lem7082940 : term137.
Proof. exact (EQ_MP (@lem7082939) (@lem0)). Qed.
Lemma lem7082941 : term330.
Proof. exact (@lem7082930 (@lem7082940)). Qed.
Lemma lem7082943 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7082944 : term137 = term138.
Proof. exact (@lem7082943 (NUMERAL 0) term97). Qed.
Lemma lem7082945 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7082946 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7082947 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7082946 h1) (fun h1 : term138 = True => @lem7082945)). Qed.
Lemma lem7082948 : term138 = True.
Proof. exact (EQ_MP (@lem7082947) (@lem7082945)). Qed.
Lemma lem7082949 : term137 = True.
Proof. exact (TRANS (@lem7082944) (@lem7082948)). Qed.
Lemma lem7082950 : True = term137.
Proof. exact (SYM (@lem7082949)). Qed.
Lemma lem7082951 : term137.
Proof. exact (EQ_MP (@lem7082950) (@lem0)). Qed.
Lemma lem7082952 : term328 = term331.
Proof. exact (@lem7082941 (@lem7082951)). Qed.
Lemma lem7082954 (x : nat) : (term154 x) = term9.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7082955 : term153 = term9.
Proof. exact (@lem7082954 term97). Qed.
Lemma lem7082957 (x : nat) : (term154 x) = term9.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7082958 : term153 = term9.
Proof. exact (@lem7082957 term97). Qed.
Lemma lem7082959 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7082960 : term303 = term297.
Proof. exact (MK_COMB (@lem7082959) (@lem7082958)). Qed.
Lemma lem7082961 : term331 = term327.
Proof. exact (MK_COMB (@lem7082960) (@lem7082955)). Qed.
Lemma lem7082963 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7082964 : term327 = term332.
Proof. exact (@lem7082963 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7082965 : term332 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7082966 : term327 = False.
Proof. exact (TRANS (@lem7082964) (@lem7082965)). Qed.
Lemma lem7082967 : term331 = False.
Proof. exact (TRANS (@lem7082961) (@lem7082966)). Qed.
Lemma lem7082968 : term328 = False.
Proof. exact (TRANS (@lem7082952) (@lem7082967)). Qed.
Lemma lem7082969 : term327 = False.
Proof. exact (TRANS (@lem7082929) (@lem7082968)). Qed.
Lemma lem7082970 : term326 = False.
Proof. exact (TRANS (@lem7082920) (@lem7082969)). Qed.
Lemma lem7082971 (a : real) (b : real) (x : real) (h1 : term220 a b x) : False.
Proof. exact (EQ_MP (@lem7082970) (@lem7082917 a b x h1)). Qed.
Lemma lem7082972 (x : real) (a : real) (b : real) (h1 : term293 x a b) : term293 x a b.
Proof. exact (h1). Qed.
Lemma lem7082973 (x : real) (a : real) (b : real) (h1 : term293 x a b) : term291 x a b.
Proof. exact (proj2 (@lem7082972 x a b h1)). Qed.
Lemma lem7082975 (x : real) (a : real) (b : real) (h1 : term293 x a b) : term290 x a b.
Proof. exact (proj2 (@lem7082973 x a b h1)). Qed.
Lemma lem7082976 (x : real) (a : real) (b : real) (h1 : term293 x a b) : term55 a b.
Proof. exact (proj1 (@lem7082973 x a b h1)). Qed.
Lemma lem7082977 (x : real) (a : real) (b : real) (h1 : term293 x a b) : term46 a b.
Proof. exact (proj2 (@lem7082976 x a b h1)). Qed.
Lemma lem7082979 (x : real) (a : real) (b : real) (h1 : term293 x a b) : term231 a b.
Proof. exact (proj2 (@lem7082975 x a b h1)). Qed.
Lemma lem7082982 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7082983 : term296 = term137.
Proof. exact (@lem7082982 term9 term103). Qed.
Lemma lem7082985 (x : nat) : (real_of_num x) = (term92 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7082986 : term103 = term130.
Proof. exact (@lem7082985 term97). Qed.
Lemma lem7082988 (x : nat) : (real_of_num x) = (term92 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7082989 : term9 = term93.
Proof. exact (@lem7082988 (NUMERAL 0)). Qed.
Lemma lem7082990 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7082991 : term297 = term298.
Proof. exact (MK_COMB (@lem7082990) (@lem7082989)). Qed.
Lemma lem7082992 : term137 = term299.
Proof. exact (MK_COMB (@lem7082991) (@lem7082986)). Qed.
Lemma lem7082993 : term300.
Proof. exact (@lem1980255 term9 term103 term103 term103). Qed.
Lemma lem7082995 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7082996 : term137 = term138.
Proof. exact (@lem7082995 (NUMERAL 0) term97). Qed.
Lemma lem7082997 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7082998 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7082999 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7082998 h1) (fun h1 : term138 = True => @lem7082997)). Qed.
Lemma lem7083000 : term138 = True.
Proof. exact (EQ_MP (@lem7082999) (@lem7082997)). Qed.
Lemma lem7083001 : term137 = True.
Proof. exact (TRANS (@lem7082996) (@lem7083000)). Qed.
Lemma lem7083002 : True = term137.
Proof. exact (SYM (@lem7083001)). Qed.
Lemma lem7083003 : term137.
Proof. exact (EQ_MP (@lem7083002) (@lem0)). Qed.
Lemma lem7083004 : term301.
Proof. exact (@lem7082993 (@lem7083003)). Qed.
Lemma lem7083006 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7083007 : term137 = term138.
Proof. exact (@lem7083006 (NUMERAL 0) term97). Qed.
Lemma lem7083008 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7083009 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7083010 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7083009 h1) (fun h1 : term138 = True => @lem7083008)). Qed.
Lemma lem7083011 : term138 = True.
Proof. exact (EQ_MP (@lem7083010) (@lem7083008)). Qed.
Lemma lem7083012 : term137 = True.
Proof. exact (TRANS (@lem7083007) (@lem7083011)). Qed.
Lemma lem7083013 : True = term137.
Proof. exact (SYM (@lem7083012)). Qed.
Lemma lem7083014 : term137.
Proof. exact (EQ_MP (@lem7083013) (@lem0)). Qed.
Lemma lem7083015 : term299 = term302.
Proof. exact (@lem7083004 (@lem7083014)). Qed.
Lemma lem7083017 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7083018 : term106 = term107.
Proof. exact (@lem7083017 term97 term97). Qed.
Lemma lem7083019 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7083020 : term109 = term97.
Proof. exact (EQ_MP (@lem7083019) (@lem940073)). Qed.
Lemma lem7083021 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7083022 : term107 = term103.
Proof. exact (MK_COMB (@lem7083021) (@lem7083020)). Qed.
Lemma lem7083023 : term106 = term103.
Proof. exact (TRANS (@lem7083018) (@lem7083022)). Qed.
Lemma lem7083025 (x : nat) : (term154 x) = term9.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7083026 : term153 = term9.
Proof. exact (@lem7083025 term97). Qed.
Lemma lem7083027 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7083028 : term303 = term297.
Proof. exact (MK_COMB (@lem7083027) (@lem7083026)). Qed.
Lemma lem7083029 : term302 = term137.
Proof. exact (MK_COMB (@lem7083028) (@lem7083023)). Qed.
Lemma lem7083031 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7083032 : term137 = term138.
Proof. exact (@lem7083031 (NUMERAL 0) term97). Qed.
Lemma lem7083033 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7083034 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7083035 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7083034 h1) (fun h1 : term138 = True => @lem7083033)). Qed.
Lemma lem7083036 : term138 = True.
Proof. exact (EQ_MP (@lem7083035) (@lem7083033)). Qed.
Lemma lem7083037 : term137 = True.
Proof. exact (TRANS (@lem7083032) (@lem7083036)). Qed.
Lemma lem7083038 : term302 = True.
Proof. exact (TRANS (@lem7083029) (@lem7083037)). Qed.
Lemma lem7083039 : term299 = True.
Proof. exact (TRANS (@lem7083015) (@lem7083038)). Qed.
Lemma lem7083040 : term137 = True.
Proof. exact (TRANS (@lem7082992) (@lem7083039)). Qed.
Lemma lem7083041 : term296 = True.
Proof. exact (TRANS (@lem7082983) (@lem7083040)). Qed.
Lemma lem7083042 : True = term296.
Proof. exact (SYM (@lem7083041)). Qed.
Lemma lem7083043 : term296.
Proof. exact (EQ_MP (@lem7083042) (@lem0)). Qed.
Lemma lem7083044 (x : real) (a : real) (b : real) (h1 : term293 x a b) : term333 a b.
Proof. exact (conj (@lem7083043) (@lem7082977 x a b h1)). Qed.
Lemma lem7083046 (x : real) (y : real) : term305 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7083047 (a : real) (b : real) : term334 a b.
Proof. exact (@lem7083046 term103 (real_add a b)). Qed.
Lemma lem7083048 (x : real) (a : real) (b : real) (h1 : term293 x a b) : term335 a b.
Proof. exact (@lem7083047 a b (@lem7083044 x a b h1)). Qed.
Lemma lem7083049 (a : real) (b : real) : (term336 a b) = (real_add a b).
Proof. exact (@lem1982733 (real_add a b)). Qed.
Lemma lem7083050 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7083051 (a : real) (b : real) : (term337 a b) = (term44 a b).
Proof. exact (MK_COMB (@lem7083050) (@lem7083049 a b)). Qed.
Lemma lem7083052 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem7083053 (a : real) (b : real) : (term335 a b) = (term46 a b).
Proof. exact (MK_COMB (@lem7083051 a b) (@lem7083052)). Qed.
Lemma lem7083054 (x : real) (a : real) (b : real) (h1 : term293 x a b) : term46 a b.
Proof. exact (EQ_MP (@lem7083053 a b) (@lem7083048 x a b h1)). Qed.
Lemma lem7083056 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7083057 : term296 = term137.
Proof. exact (@lem7083056 term9 term103). Qed.
Lemma lem7083059 (x : nat) : (real_of_num x) = (term92 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7083060 : term103 = term130.
Proof. exact (@lem7083059 term97). Qed.
Lemma lem7083062 (x : nat) : (real_of_num x) = (term92 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7083063 : term9 = term93.
Proof. exact (@lem7083062 (NUMERAL 0)). Qed.
Lemma lem7083064 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7083065 : term297 = term298.
Proof. exact (MK_COMB (@lem7083064) (@lem7083063)). Qed.
Lemma lem7083066 : term137 = term299.
Proof. exact (MK_COMB (@lem7083065) (@lem7083060)). Qed.
Lemma lem7083067 : term300.
Proof. exact (@lem1980255 term9 term103 term103 term103). Qed.
Lemma lem7083069 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7083070 : term137 = term138.
Proof. exact (@lem7083069 (NUMERAL 0) term97). Qed.
Lemma lem7083071 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7083072 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7083073 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7083072 h1) (fun h1 : term138 = True => @lem7083071)). Qed.
Lemma lem7083074 : term138 = True.
Proof. exact (EQ_MP (@lem7083073) (@lem7083071)). Qed.
Lemma lem7083075 : term137 = True.
Proof. exact (TRANS (@lem7083070) (@lem7083074)). Qed.
Lemma lem7083076 : True = term137.
Proof. exact (SYM (@lem7083075)). Qed.
Lemma lem7083077 : term137.
Proof. exact (EQ_MP (@lem7083076) (@lem0)). Qed.
Lemma lem7083078 : term301.
Proof. exact (@lem7083067 (@lem7083077)). Qed.
Lemma lem7083080 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7083081 : term137 = term138.
Proof. exact (@lem7083080 (NUMERAL 0) term97). Qed.
Lemma lem7083082 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7083083 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7083084 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7083083 h1) (fun h1 : term138 = True => @lem7083082)). Qed.
Lemma lem7083085 : term138 = True.
Proof. exact (EQ_MP (@lem7083084) (@lem7083082)). Qed.
Lemma lem7083086 : term137 = True.
Proof. exact (TRANS (@lem7083081) (@lem7083085)). Qed.
Lemma lem7083087 : True = term137.
Proof. exact (SYM (@lem7083086)). Qed.
Lemma lem7083088 : term137.
Proof. exact (EQ_MP (@lem7083087) (@lem0)). Qed.
Lemma lem7083089 : term299 = term302.
Proof. exact (@lem7083078 (@lem7083088)). Qed.
Lemma lem7083091 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7083092 : term106 = term107.
Proof. exact (@lem7083091 term97 term97). Qed.
Lemma lem7083093 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7083094 : term109 = term97.
Proof. exact (EQ_MP (@lem7083093) (@lem940073)). Qed.
Lemma lem7083095 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7083096 : term107 = term103.
Proof. exact (MK_COMB (@lem7083095) (@lem7083094)). Qed.
Lemma lem7083097 : term106 = term103.
Proof. exact (TRANS (@lem7083092) (@lem7083096)). Qed.
Lemma lem7083099 (x : nat) : (term154 x) = term9.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7083100 : term153 = term9.
Proof. exact (@lem7083099 term97). Qed.
Lemma lem7083101 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7083102 : term303 = term297.
Proof. exact (MK_COMB (@lem7083101) (@lem7083100)). Qed.
Lemma lem7083103 : term302 = term137.
Proof. exact (MK_COMB (@lem7083102) (@lem7083097)). Qed.
Lemma lem7083105 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7083106 : term137 = term138.
Proof. exact (@lem7083105 (NUMERAL 0) term97). Qed.
Lemma lem7083107 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7083108 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7083109 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7083108 h1) (fun h1 : term138 = True => @lem7083107)). Qed.
Lemma lem7083110 : term138 = True.
Proof. exact (EQ_MP (@lem7083109) (@lem7083107)). Qed.
Lemma lem7083111 : term137 = True.
Proof. exact (TRANS (@lem7083106) (@lem7083110)). Qed.
Lemma lem7083112 : term302 = True.
Proof. exact (TRANS (@lem7083103) (@lem7083111)). Qed.
Lemma lem7083113 : term299 = True.
Proof. exact (TRANS (@lem7083089) (@lem7083112)). Qed.
Lemma lem7083114 : term137 = True.
Proof. exact (TRANS (@lem7083066) (@lem7083113)). Qed.
Lemma lem7083115 : term296 = True.
Proof. exact (TRANS (@lem7083057) (@lem7083114)). Qed.
Lemma lem7083116 : True = term296.
Proof. exact (SYM (@lem7083115)). Qed.
Lemma lem7083117 : term296.
Proof. exact (EQ_MP (@lem7083116) (@lem0)). Qed.
Lemma lem7083118 (x : real) (a : real) (b : real) (h1 : term293 x a b) : term338 a b.
Proof. exact (conj (@lem7083117) (@lem7082979 x a b h1)). Qed.
Lemma lem7083120 (x : real) (y : real) : term311 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem7083121 (a : real) (b : real) : term339 a b.
Proof. exact (@lem7083120 term103 (term226 a b)). Qed.
Lemma lem7083122 (x : real) (a : real) (b : real) (h1 : term293 x a b) : term340 a b.
Proof. exact (@lem7083121 a b (@lem7083118 x a b h1)). Qed.
Lemma lem7083123 (a : real) (b : real) : (term341 a b) = (term226 a b).
Proof. exact (@lem1982733 (term226 a b)). Qed.
Lemma lem7083124 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7083125 (a : real) (b : real) : (term342 a b) = (term230 a b).
Proof. exact (MK_COMB (@lem7083124) (@lem7083123 a b)). Qed.
Lemma lem7083126 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem7083127 (a : real) (b : real) : (term340 a b) = (term231 a b).
Proof. exact (MK_COMB (@lem7083125 a b) (@lem7083126)). Qed.
Lemma lem7083128 (x : real) (a : real) (b : real) (h1 : term293 x a b) : term231 a b.
Proof. exact (EQ_MP (@lem7083127 a b) (@lem7083122 x a b h1)). Qed.
Lemma lem7083129 (x : real) (a : real) (b : real) (h1 : term293 x a b) : term343 a b.
Proof. exact (conj (@lem7083128 x a b h1) (@lem7083054 x a b h1)). Qed.
Lemma lem7083131 (x : real) (y : real) : term317 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem7083132 (a : real) (b : real) : term344 a b.
Proof. exact (@lem7083131 (term226 a b) (real_add a b)). Qed.
Lemma lem7083133 (x : real) (a : real) (b : real) (h1 : term293 x a b) : term345 a b.
Proof. exact (@lem7083132 a b (@lem7083129 x a b h1)). Qed.
Lemma lem7083134 (a : real) (b : real) : (term346 a b) = (term347 a b).
Proof. exact (@lem1982753 (term26 a) a (term26 b) b). Qed.
Lemma lem7083135 (a : real) : (term128 a) = (term129 a).
Proof. exact (@lem1982713 term22 a). Qed.
Lemma lem7083137 (x : nat) : (real_of_num x) = (term92 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7083138 : term103 = term130.
Proof. exact (@lem7083137 term97). Qed.
Lemma lem7083140 (x : nat) : (term94 x) = (term95 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7083141 : term22 = term96.
Proof. exact (@lem7083140 term97). Qed.
Lemma lem7083142 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7083143 : term131 = term132.
Proof. exact (MK_COMB (@lem7083142) (@lem7083141)). Qed.
Lemma lem7083144 : term133 = term134.
Proof. exact (MK_COMB (@lem7083143) (@lem7083138)). Qed.
Lemma lem7083145 : term135.
Proof. exact (@lem1981473 term22 term103 term103 term103 term9 term103). Qed.
Lemma lem7083147 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7083148 : term137 = term138.
Proof. exact (@lem7083147 (NUMERAL 0) term97). Qed.
Lemma lem7083149 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7083150 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7083151 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7083150 h1) (fun h1 : term138 = True => @lem7083149)). Qed.
Lemma lem7083152 : term138 = True.
Proof. exact (EQ_MP (@lem7083151) (@lem7083149)). Qed.
Lemma lem7083153 : term137 = True.
Proof. exact (TRANS (@lem7083148) (@lem7083152)). Qed.
Lemma lem7083154 : True = term137.
Proof. exact (SYM (@lem7083153)). Qed.
Lemma lem7083155 : term137.
Proof. exact (EQ_MP (@lem7083154) (@lem0)). Qed.
Lemma lem7083156 : term140.
Proof. exact (@lem7083145 (@lem7083155)). Qed.
Lemma lem7083158 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7083159 : term137 = term138.
Proof. exact (@lem7083158 (NUMERAL 0) term97). Qed.
Lemma lem7083160 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7083161 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7083162 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7083161 h1) (fun h1 : term138 = True => @lem7083160)). Qed.
Lemma lem7083163 : term138 = True.
Proof. exact (EQ_MP (@lem7083162) (@lem7083160)). Qed.
Lemma lem7083164 : term137 = True.
Proof. exact (TRANS (@lem7083159) (@lem7083163)). Qed.
Lemma lem7083165 : True = term137.
Proof. exact (SYM (@lem7083164)). Qed.
Lemma lem7083166 : term137.
Proof. exact (EQ_MP (@lem7083165) (@lem0)). Qed.
Lemma lem7083167 : term141.
Proof. exact (@lem7083156 (@lem7083166)). Qed.
Lemma lem7083169 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7083170 : term137 = term138.
Proof. exact (@lem7083169 (NUMERAL 0) term97). Qed.
Lemma lem7083171 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7083172 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7083173 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7083172 h1) (fun h1 : term138 = True => @lem7083171)). Qed.
Lemma lem7083174 : term138 = True.
Proof. exact (EQ_MP (@lem7083173) (@lem7083171)). Qed.
Lemma lem7083175 : term137 = True.
Proof. exact (TRANS (@lem7083170) (@lem7083174)). Qed.
Lemma lem7083176 : True = term137.
Proof. exact (SYM (@lem7083175)). Qed.
Lemma lem7083177 : term137.
Proof. exact (EQ_MP (@lem7083176) (@lem0)). Qed.
Lemma lem7083178 : term142.
Proof. exact (@lem7083167 (@lem7083177)). Qed.
Lemma lem7083180 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7083181 : term106 = term107.
Proof. exact (@lem7083180 term97 term97). Qed.
Lemma lem7083182 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7083183 : term109 = term97.
Proof. exact (EQ_MP (@lem7083182) (@lem940073)). Qed.
Lemma lem7083184 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7083185 : term107 = term103.
Proof. exact (MK_COMB (@lem7083184) (@lem7083183)). Qed.
Lemma lem7083186 : term106 = term103.
Proof. exact (TRANS (@lem7083181) (@lem7083185)). Qed.
Lemma lem7083188 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7083189 : term145 = term146.
Proof. exact (@lem7083188 term97 term97). Qed.
Lemma lem7083190 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7083191 : term109 = term97.
Proof. exact (EQ_MP (@lem7083190) (@lem940073)). Qed.
Lemma lem7083192 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7083193 : term107 = term103.
Proof. exact (MK_COMB (@lem7083192) (@lem7083191)). Qed.
Lemma lem7083194 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7083195 : term146 = term22.
Proof. exact (MK_COMB (@lem7083194) (@lem7083193)). Qed.
Lemma lem7083196 : term145 = term22.
Proof. exact (TRANS (@lem7083189) (@lem7083195)). Qed.
Lemma lem7083197 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7083198 : term147 = term131.
Proof. exact (MK_COMB (@lem7083197) (@lem7083196)). Qed.
Lemma lem7083199 : term148 = term133.
Proof. exact (MK_COMB (@lem7083198) (@lem7083186)). Qed.
Lemma lem7083201 (m : nat) : (term149 m) = term9.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7083202 : term133 = term9.
Proof. exact (@lem7083201 term97). Qed.
Lemma lem7083203 : term148 = term9.
Proof. exact (TRANS (@lem7083199) (@lem7083202)). Qed.
Lemma lem7083204 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7083205 : term150 = term151.
Proof. exact (MK_COMB (@lem7083204) (@lem7083203)). Qed.
Lemma lem7083206 : term103 = term103.
Proof. exact (eq_refl term103). Qed.
Lemma lem7083207 : term152 = term153.
Proof. exact (MK_COMB (@lem7083205) (@lem7083206)). Qed.
Lemma lem7083209 (x : nat) : (term154 x) = term9.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7083210 : term153 = term9.
Proof. exact (@lem7083209 term97). Qed.
Lemma lem7083211 : term152 = term9.
Proof. exact (TRANS (@lem7083207) (@lem7083210)). Qed.
Lemma lem7083213 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7083214 : term106 = term107.
Proof. exact (@lem7083213 term97 term97). Qed.
Lemma lem7083215 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7083216 : term109 = term97.
Proof. exact (EQ_MP (@lem7083215) (@lem940073)). Qed.
Lemma lem7083217 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7083218 : term107 = term103.
Proof. exact (MK_COMB (@lem7083217) (@lem7083216)). Qed.
Lemma lem7083219 : term106 = term103.
Proof. exact (TRANS (@lem7083214) (@lem7083218)). Qed.
Lemma lem7083220 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem7083221 : term155 = term153.
Proof. exact (MK_COMB (@lem7083220) (@lem7083219)). Qed.
Lemma lem7083223 (x : nat) : (term154 x) = term9.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7083224 : term153 = term9.
Proof. exact (@lem7083223 term97). Qed.
Lemma lem7083225 : term155 = term9.
Proof. exact (TRANS (@lem7083221) (@lem7083224)). Qed.
Lemma lem7083226 : term9 = term155.
Proof. exact (SYM (@lem7083225)). Qed.
Lemma lem7083227 : term152 = term155.
Proof. exact (TRANS (@lem7083211) (@lem7083226)). Qed.
Lemma lem7083228 : term134 = term93.
Proof. exact (@lem7083178 (@lem7083227)). Qed.
Lemma lem7083229 : term133 = term93.
Proof. exact (TRANS (@lem7083144) (@lem7083228)). Qed.
Lemma lem7083231 (x : real) : (term113 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7083232 : term93 = term9.
Proof. exact (@lem7083231 term9). Qed.
Lemma lem7083233 : term133 = term9.
Proof. exact (TRANS (@lem7083229) (@lem7083232)). Qed.
Lemma lem7083234 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7083235 : term156 = term151.
Proof. exact (MK_COMB (@lem7083234) (@lem7083233)). Qed.
Lemma lem7083236 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem7083237 (a : real) : (term129 a) = (term157 a).
Proof. exact (MK_COMB (@lem7083235) (@lem7083236 a)). Qed.
Lemma lem7083238 (a : real) : (term128 a) = (term157 a).
Proof. exact (TRANS (@lem7083135 a) (@lem7083237 a)). Qed.
Lemma lem7083239 (a : real) : (term157 a) = term9.
Proof. exact (@lem1982719 a). Qed.
Lemma lem7083240 (a : real) : (term128 a) = term9.
Proof. exact (TRANS (@lem7083238 a) (@lem7083239 a)). Qed.
Lemma lem7083241 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7083242 (a : real) : (term348 a) = term227.
Proof. exact (MK_COMB (@lem7083241) (@lem7083240 a)). Qed.
Lemma lem7083243 (b : real) : (term128 b) = (term129 b).
Proof. exact (@lem1982713 term22 b). Qed.
Lemma lem7083245 (x : nat) : (real_of_num x) = (term92 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7083246 : term103 = term130.
Proof. exact (@lem7083245 term97). Qed.
Lemma lem7083248 (x : nat) : (term94 x) = (term95 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7083249 : term22 = term96.
Proof. exact (@lem7083248 term97). Qed.
Lemma lem7083250 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7083251 : term131 = term132.
Proof. exact (MK_COMB (@lem7083250) (@lem7083249)). Qed.
Lemma lem7083252 : term133 = term134.
Proof. exact (MK_COMB (@lem7083251) (@lem7083246)). Qed.
Lemma lem7083253 : term135.
Proof. exact (@lem1981473 term22 term103 term103 term103 term9 term103). Qed.
Lemma lem7083255 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7083256 : term137 = term138.
Proof. exact (@lem7083255 (NUMERAL 0) term97). Qed.
Lemma lem7083257 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7083258 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7083259 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7083258 h1) (fun h1 : term138 = True => @lem7083257)). Qed.
Lemma lem7083260 : term138 = True.
Proof. exact (EQ_MP (@lem7083259) (@lem7083257)). Qed.
Lemma lem7083261 : term137 = True.
Proof. exact (TRANS (@lem7083256) (@lem7083260)). Qed.
Lemma lem7083262 : True = term137.
Proof. exact (SYM (@lem7083261)). Qed.
Lemma lem7083263 : term137.
Proof. exact (EQ_MP (@lem7083262) (@lem0)). Qed.
Lemma lem7083264 : term140.
Proof. exact (@lem7083253 (@lem7083263)). Qed.
Lemma lem7083266 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7083267 : term137 = term138.
Proof. exact (@lem7083266 (NUMERAL 0) term97). Qed.
Lemma lem7083268 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7083269 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7083270 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7083269 h1) (fun h1 : term138 = True => @lem7083268)). Qed.
Lemma lem7083271 : term138 = True.
Proof. exact (EQ_MP (@lem7083270) (@lem7083268)). Qed.
Lemma lem7083272 : term137 = True.
Proof. exact (TRANS (@lem7083267) (@lem7083271)). Qed.
Lemma lem7083273 : True = term137.
Proof. exact (SYM (@lem7083272)). Qed.
Lemma lem7083274 : term137.
Proof. exact (EQ_MP (@lem7083273) (@lem0)). Qed.
Lemma lem7083275 : term141.
Proof. exact (@lem7083264 (@lem7083274)). Qed.
Lemma lem7083277 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7083278 : term137 = term138.
Proof. exact (@lem7083277 (NUMERAL 0) term97). Qed.
Lemma lem7083279 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7083280 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7083281 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7083280 h1) (fun h1 : term138 = True => @lem7083279)). Qed.
Lemma lem7083282 : term138 = True.
Proof. exact (EQ_MP (@lem7083281) (@lem7083279)). Qed.
Lemma lem7083283 : term137 = True.
Proof. exact (TRANS (@lem7083278) (@lem7083282)). Qed.
Lemma lem7083284 : True = term137.
Proof. exact (SYM (@lem7083283)). Qed.
Lemma lem7083285 : term137.
Proof. exact (EQ_MP (@lem7083284) (@lem0)). Qed.
Lemma lem7083286 : term142.
Proof. exact (@lem7083275 (@lem7083285)). Qed.
Lemma lem7083288 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7083289 : term106 = term107.
Proof. exact (@lem7083288 term97 term97). Qed.
Lemma lem7083290 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7083291 : term109 = term97.
Proof. exact (EQ_MP (@lem7083290) (@lem940073)). Qed.
Lemma lem7083292 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7083293 : term107 = term103.
Proof. exact (MK_COMB (@lem7083292) (@lem7083291)). Qed.
Lemma lem7083294 : term106 = term103.
Proof. exact (TRANS (@lem7083289) (@lem7083293)). Qed.
Lemma lem7083296 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7083297 : term145 = term146.
Proof. exact (@lem7083296 term97 term97). Qed.
Lemma lem7083298 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7083299 : term109 = term97.
Proof. exact (EQ_MP (@lem7083298) (@lem940073)). Qed.
Lemma lem7083300 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7083301 : term107 = term103.
Proof. exact (MK_COMB (@lem7083300) (@lem7083299)). Qed.
Lemma lem7083302 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7083303 : term146 = term22.
Proof. exact (MK_COMB (@lem7083302) (@lem7083301)). Qed.
Lemma lem7083304 : term145 = term22.
Proof. exact (TRANS (@lem7083297) (@lem7083303)). Qed.
Lemma lem7083305 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7083306 : term147 = term131.
Proof. exact (MK_COMB (@lem7083305) (@lem7083304)). Qed.
Lemma lem7083307 : term148 = term133.
Proof. exact (MK_COMB (@lem7083306) (@lem7083294)). Qed.
Lemma lem7083309 (m : nat) : (term149 m) = term9.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7083310 : term133 = term9.
Proof. exact (@lem7083309 term97). Qed.
Lemma lem7083311 : term148 = term9.
Proof. exact (TRANS (@lem7083307) (@lem7083310)). Qed.
Lemma lem7083312 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7083313 : term150 = term151.
Proof. exact (MK_COMB (@lem7083312) (@lem7083311)). Qed.
Lemma lem7083314 : term103 = term103.
Proof. exact (eq_refl term103). Qed.
Lemma lem7083315 : term152 = term153.
Proof. exact (MK_COMB (@lem7083313) (@lem7083314)). Qed.
Lemma lem7083317 (x : nat) : (term154 x) = term9.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7083318 : term153 = term9.
Proof. exact (@lem7083317 term97). Qed.
Lemma lem7083319 : term152 = term9.
Proof. exact (TRANS (@lem7083315) (@lem7083318)). Qed.
Lemma lem7083321 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7083322 : term106 = term107.
Proof. exact (@lem7083321 term97 term97). Qed.
Lemma lem7083323 : (term108 = (BIT1 0)) = (term109 = term97).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7083324 : term109 = term97.
Proof. exact (EQ_MP (@lem7083323) (@lem940073)). Qed.
Lemma lem7083325 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7083326 : term107 = term103.
Proof. exact (MK_COMB (@lem7083325) (@lem7083324)). Qed.
Lemma lem7083327 : term106 = term103.
Proof. exact (TRANS (@lem7083322) (@lem7083326)). Qed.
Lemma lem7083328 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem7083329 : term155 = term153.
Proof. exact (MK_COMB (@lem7083328) (@lem7083327)). Qed.
Lemma lem7083331 (x : nat) : (term154 x) = term9.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7083332 : term153 = term9.
Proof. exact (@lem7083331 term97). Qed.
Lemma lem7083333 : term155 = term9.
Proof. exact (TRANS (@lem7083329) (@lem7083332)). Qed.
Lemma lem7083334 : term9 = term155.
Proof. exact (SYM (@lem7083333)). Qed.
Lemma lem7083335 : term152 = term155.
Proof. exact (TRANS (@lem7083319) (@lem7083334)). Qed.
Lemma lem7083336 : term134 = term93.
Proof. exact (@lem7083286 (@lem7083335)). Qed.
Lemma lem7083337 : term133 = term93.
Proof. exact (TRANS (@lem7083252) (@lem7083336)). Qed.
Lemma lem7083339 (x : real) : (term113 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7083340 : term93 = term9.
Proof. exact (@lem7083339 term9). Qed.
Lemma lem7083341 : term133 = term9.
Proof. exact (TRANS (@lem7083337) (@lem7083340)). Qed.
Lemma lem7083342 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7083343 : term156 = term151.
Proof. exact (MK_COMB (@lem7083342) (@lem7083341)). Qed.
Lemma lem7083344 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7083345 (b : real) : (term129 b) = (term157 b).
Proof. exact (MK_COMB (@lem7083343) (@lem7083344 b)). Qed.
Lemma lem7083346 (b : real) : (term128 b) = (term157 b).
Proof. exact (TRANS (@lem7083243 b) (@lem7083345 b)). Qed.
Lemma lem7083347 (b : real) : (term157 b) = term9.
Proof. exact (@lem1982719 b). Qed.
Lemma lem7083348 (b : real) : (term128 b) = term9.
Proof. exact (TRANS (@lem7083346 b) (@lem7083347 b)). Qed.
Lemma lem7083349 (a : real) (b : real) : (term347 a b) = term323.
Proof. exact (MK_COMB (@lem7083242 a) (@lem7083348 b)). Qed.
Lemma lem7083350 (a : real) (b : real) : (term346 a b) = term323.
Proof. exact (TRANS (@lem7083134 a b) (@lem7083349 a b)). Qed.
Lemma lem7083351 : term323 = term9.
Proof. exact (@lem1982721 term9). Qed.
Lemma lem7083352 (a : real) (b : real) : (term346 a b) = term9.
Proof. exact (TRANS (@lem7083350 a b) (@lem7083351)). Qed.
Lemma lem7083353 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7083354 (a : real) (b : real) : (term349 a b) = term325.
Proof. exact (MK_COMB (@lem7083353) (@lem7083352 a b)). Qed.
Lemma lem7083355 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem7083356 (a : real) (b : real) : (term345 a b) = term326.
Proof. exact (MK_COMB (@lem7083354 a b) (@lem7083355)). Qed.
Lemma lem7083357 (x : real) (a : real) (b : real) (h1 : term293 x a b) : term326.
Proof. exact (EQ_MP (@lem7083356 a b) (@lem7083133 x a b h1)). Qed.
Lemma lem7083359 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7083360 : term326 = term327.
Proof. exact (@lem7083359 term9 term9). Qed.
Lemma lem7083362 (x : nat) : (real_of_num x) = (term92 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7083363 : term9 = term93.
Proof. exact (@lem7083362 (NUMERAL 0)). Qed.
Lemma lem7083365 (x : nat) : (real_of_num x) = (term92 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7083366 : term9 = term93.
Proof. exact (@lem7083365 (NUMERAL 0)). Qed.
Lemma lem7083367 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7083368 : term297 = term298.
Proof. exact (MK_COMB (@lem7083367) (@lem7083366)). Qed.
Lemma lem7083369 : term327 = term328.
Proof. exact (MK_COMB (@lem7083368) (@lem7083363)). Qed.
Lemma lem7083370 : term329.
Proof. exact (@lem1980255 term9 term103 term9 term103). Qed.
Lemma lem7083372 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7083373 : term137 = term138.
Proof. exact (@lem7083372 (NUMERAL 0) term97). Qed.
Lemma lem7083374 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7083375 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7083376 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7083375 h1) (fun h1 : term138 = True => @lem7083374)). Qed.
Lemma lem7083377 : term138 = True.
Proof. exact (EQ_MP (@lem7083376) (@lem7083374)). Qed.
Lemma lem7083378 : term137 = True.
Proof. exact (TRANS (@lem7083373) (@lem7083377)). Qed.
Lemma lem7083379 : True = term137.
Proof. exact (SYM (@lem7083378)). Qed.
Lemma lem7083380 : term137.
Proof. exact (EQ_MP (@lem7083379) (@lem0)). Qed.
Lemma lem7083381 : term330.
Proof. exact (@lem7083370 (@lem7083380)). Qed.
Lemma lem7083383 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7083384 : term137 = term138.
Proof. exact (@lem7083383 (NUMERAL 0) term97). Qed.
Lemma lem7083385 : term139 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7083386 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7083387 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem7083386 h1) (fun h1 : term138 = True => @lem7083385)). Qed.
Lemma lem7083388 : term138 = True.
Proof. exact (EQ_MP (@lem7083387) (@lem7083385)). Qed.
Lemma lem7083389 : term137 = True.
Proof. exact (TRANS (@lem7083384) (@lem7083388)). Qed.
Lemma lem7083390 : True = term137.
Proof. exact (SYM (@lem7083389)). Qed.
Lemma lem7083391 : term137.
Proof. exact (EQ_MP (@lem7083390) (@lem0)). Qed.
Lemma lem7083392 : term328 = term331.
Proof. exact (@lem7083381 (@lem7083391)). Qed.
Lemma lem7083394 (x : nat) : (term154 x) = term9.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7083395 : term153 = term9.
Proof. exact (@lem7083394 term97). Qed.
Lemma lem7083397 (x : nat) : (term154 x) = term9.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7083398 : term153 = term9.
Proof. exact (@lem7083397 term97). Qed.
Lemma lem7083399 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7083400 : term303 = term297.
Proof. exact (MK_COMB (@lem7083399) (@lem7083398)). Qed.
Lemma lem7083401 : term331 = term327.
Proof. exact (MK_COMB (@lem7083400) (@lem7083395)). Qed.
Lemma lem7083403 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7083404 : term327 = term332.
Proof. exact (@lem7083403 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7083405 : term332 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7083406 : term327 = False.
Proof. exact (TRANS (@lem7083404) (@lem7083405)). Qed.
Lemma lem7083407 : term331 = False.
Proof. exact (TRANS (@lem7083401) (@lem7083406)). Qed.
Lemma lem7083408 : term328 = False.
Proof. exact (TRANS (@lem7083392) (@lem7083407)). Qed.
Lemma lem7083409 : term327 = False.
Proof. exact (TRANS (@lem7083369) (@lem7083408)). Qed.
Lemma lem7083410 : term326 = False.
Proof. exact (TRANS (@lem7083360) (@lem7083409)). Qed.
Lemma lem7083411 (x : real) (a : real) (b : real) (h1 : term293 x a b) : False.
Proof. exact (EQ_MP (@lem7083410) (@lem7083357 x a b h1)). Qed.
Lemma lem7083412 (x : real) (a : real) (b : real) (h1 : term295 x a b) : False.
Proof. exact (or_elim (@lem7082531 x a b h1) (fun h0 : term220 a b x => @lem7082971 a b x h0) (fun h0 : term293 x a b => @lem7083411 x a b h0)). Qed.
Lemma lem7083413 (b : real) (a : real) (x : real) (h1 : term37 b a x) : term37 b a x.
Proof. exact (h1). Qed.
Lemma lem7083414 (b : real) (a : real) (x : real) (h1 : term37 b a x) : term295 x a b.
Proof. exact (EQ_MP (@lem7082530 x a b) (@lem7083413 b a x h1)). Qed.
Lemma lem7083415 (b : real) (a : real) (x : real) (h1 : term37 b a x) : (term295 x a b) = False.
Proof. exact (prop_ext (fun h2 : term295 x a b => @lem7083412 x a b h2) (fun h2 : False => @lem7083414 b a x h1)). Qed.
Lemma lem7083416 (b : real) (a : real) (x : real) (h1 : term37 b a x) : False.
Proof. exact (EQ_MP (@lem7083415 b a x h1) (@lem7083414 b a x h1)). Qed.
Lemma lem7083417 (a : real) (x : real) (b : real) (h1 : term0 a x b) : term0 a x b.
Proof. exact (h1). Qed.
Lemma lem7083418 (a : real) (x : real) (b : real) (h1 : term0 a x b) : term37 b a x.
Proof. exact (EQ_MP (@lem7081345 b a x) (@lem7083417 a x b h1)). Qed.
Lemma lem7083419 (a : real) (x : real) (b : real) (h1 : term0 a x b) : (term37 b a x) = False.
Proof. exact (prop_ext (fun h2 : term37 b a x => @lem7083416 b a x h2) (fun h2 : False => @lem7083418 a x b h1)). Qed.
Lemma lem7083420 (a : real) (x : real) (b : real) (h1 : term0 a x b) : False.
Proof. exact (EQ_MP (@lem7083419 a x b h1) (@lem7083418 a x b h1)). Qed.
Lemma lem7083421 (a : real) (x : real) (b : real) : term350 a x b.
Proof. exact (fun h0 : term0 a x b => @lem7083420 a x b h0). Qed.
Lemma lem7083422 (a : real) (x : real) (b : real) : term351 a x b.
Proof. exact (@lem1386578 (term352 a x b)). Qed.
Lemma lem7083425 (a : real) (x : real) (b : real) : term352 a x b.
Proof. exact (@lem7083422 a x b (@lem7083421 a x b)). Qed.
Lemma lem7083426 (a : real) (b : real) (h1 : term2 a b) : term2 a b.
Proof. exact (h1). Qed.
Lemma lem7083427 (x : real) (a : real) (b : real) (h1 : term2 a b) : term3 a x b.
Proof. exact (@lem7083425 a x b (@lem7083426 a b h1)). Qed.
Lemma lem7083428 (a : real) (x : real) (b : real) : (term3 a x b) = ((term3 a x b) = True).
Proof. exact (@lem7 (term3 a x b)). Qed.
Lemma lem7083429 (x : real) (a : real) (b : real) (h1 : term2 a b) : (term3 a x b) = True.
Proof. exact (EQ_MP (@lem7083428 a x b) (@lem7083427 x a b h1)). Qed.
Lemma lem7083435 (x : real) : term353 x.
Proof. exact (@lem1339240 x). Qed.
Lemma lem7083436 (x : real) : (term353 x) = (real_le x x).
Proof. exact (eq_refl (term353 x)). Qed.
Lemma lem7083437 (x : real) : real_le x x.
Proof. exact (EQ_MP (@lem7083436 x) (@lem7083435 x)). Qed.
Lemma lem7083438 (x : real) : (real_le x x) = ((real_le x x) = True).
Proof. exact (@lem7 (real_le x x)). Qed.
Lemma lem7083440 (n : nat) : term354 n.
Proof. exact (@lem1362923 n). Qed.
Lemma lem7083441 (n : nat) : (term354 n) = ((term355 n) = (real_of_num n)).
Proof. exact (eq_refl (term354 n)). Qed.
Lemma lem7083443 {_131524 : Type'} : term356 _131524.
Proof. exact (proj2 (@lem7067645 Prop _131524)). Qed.
Lemma lem7083444 {_131524 : Type'} (x : _131524) : term357 _131524 x.
Proof. exact (@lem7083443 _131524 x). Qed.
Lemma lem7083445 {_131524 : Type'} (x : _131524) : (term357 _131524 x) = (term358 _131524 x).
Proof. exact (eq_refl (term357 _131524 x)). Qed.
Lemma lem7083446 {_131524 : Type'} (x : _131524) : term358 _131524 x.
Proof. exact (EQ_MP (@lem7083445 _131524 x) (@lem7083444 _131524 x)). Qed.
Lemma lem7083447 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : term359 _131524 x f.
Proof. exact (@lem7083446 _131524 x f). Qed.
Lemma lem7083448 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : (term359 _131524 x f) = (term360 _131524 x f).
Proof. exact (eq_refl (term359 _131524 x f)). Qed.
Lemma lem7083449 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : term360 _131524 x f.
Proof. exact (EQ_MP (@lem7083448 _131524 x f) (@lem7083447 _131524 x f)). Qed.
Lemma lem7083450 {_131524 : Type'} (x : _131524) (f : _131524 -> real) (s : _131524 -> Prop) : term361 _131524 x f s.
Proof. exact (@lem7083449 _131524 x f s). Qed.
Lemma lem7083451 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : (term361 _131524 x f s) = (term362 _131524 x s f).
Proof. exact (eq_refl (term361 _131524 x f s)). Qed.
Lemma lem7083452 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term362 _131524 x s f.
Proof. exact (EQ_MP (@lem7083451 _131524 x s f) (@lem7083450 _131524 x f s)). Qed.
Lemma lem7083453 {_131524 : Type'} (s : _131524 -> Prop) (h1 : @FINITE _131524 s) : @FINITE _131524 s.
Proof. exact (h1). Qed.
Lemma lem7083454 {_131524 : Type'} (x : _131524) (f : _131524 -> real) (s : _131524 -> Prop) (h1 : @FINITE _131524 s) : (term363 _131524 x s f) = (term364 _131524 x s f).
Proof. exact (@lem7083452 _131524 x s f (@lem7083453 _131524 s h1)). Qed.
Lemma lem7083460 {_131483 : Type'} : term365 _131483.
Proof. exact (proj1 (@lem7067645 _131483 Prop)). Qed.
Lemma lem7083461 {_131483 : Type'} (f : _131483 -> real) : term366 _131483 f.
Proof. exact (@lem7083460 _131483 f). Qed.
Lemma lem7083462 {_131483 : Type'} (f : _131483 -> real) : (term366 _131483 f) = ((@sum _131483 (@EMPTY _131483) f) = term9).
Proof. exact (eq_refl (term366 _131483 f)). Qed.
Lemma lem7083464 {A : Type'} (h1 : term367 A) : term367 A.
Proof. exact (h1). Qed.
Lemma lem7083465 {A : Type'} (P : type686 A) (h1 : term367 A) : term368 A P.
Proof. exact (@lem7083464 A h1 P). Qed.
Lemma lem7083466 {A : Type'} (P : type686 A) : (term368 A P) = (term369 A P).
Proof. exact (eq_refl (term368 A P)). Qed.
Lemma lem7083467 {A : Type'} (P : type686 A) (h1 : term367 A) : term369 A P.
Proof. exact (EQ_MP (@lem7083466 A P) (@lem7083465 A P h1)). Qed.
Lemma lem7083468 {A : Type'} (P : type686 A) (h1 : term370 A P) : term370 A P.
Proof. exact (h1). Qed.
Lemma lem7083469 {A : Type'} (P : type686 A) (h1 : term367 A) (h2 : term370 A P) : term371 A P.
Proof. exact (@lem7083467 A P h1 (@lem7083468 A P h2)). Qed.
Lemma lem7083470 {A : Type'} (P : type686 A) (h1 : term370 A P) : term372 A P.
Proof. exact (fun h0 : term367 A => @lem7083469 A P h0 h1). Qed.
Lemma lem7083471 {A : Type'} (h1 : term367 A) : term367 A.
Proof. exact (h1). Qed.
Lemma lem7083472 {A : Type'} (P : type686 A) (h1 : term367 A) (h2 : term370 A P) : term371 A P.
Proof. exact (@lem7083470 A P h2 (@lem7083471 A h1)). Qed.
Lemma lem7083473 {A : Type'} (P : type686 A) (h1 : term367 A) : term369 A P.
Proof. exact (fun h0 : term370 A P => @lem7083472 A P h1 h0). Qed.
Lemma lem7083474 {A : Type'} (h1 : term367 A) : term367 A.
Proof. exact (fun P : type686 A => @lem7083473 A P h1). Qed.
Lemma lem7083475 {A : Type'} : term373 A.
Proof. exact (fun h0 : term367 A => @lem7083474 A h0). Qed.
Lemma lem7083476 {A : Type'} : term367 A.
Proof. exact (@lem7083475 A (@lem3558722 A)). Qed.
Lemma lem7083477 {A : Type'} (P : type686 A) : term368 A P.
Proof. exact (@lem7083476 A P). Qed.
Lemma lem7083478 {A : Type'} (P : type686 A) : (term368 A P) = (term369 A P).
Proof. exact (eq_refl (term368 A P)). Qed.
Lemma lem7083481 {A : Type'} (P : type686 A) : term369 A P.
Proof. exact (EQ_MP (@lem7083478 A P) (@lem7083477 A P)). Qed.
Lemma lem7083482 {_132408 : Type'} (P : type686 _132408) : term369 _132408 P.
Proof. exact (@lem7083481 _132408 P). Qed.
Lemma lem7083483 {_132408 : Type'} (f : _132408 -> real) : term374 _132408 f.
Proof. exact (@lem7083482 _132408 (term375 _132408 f)). Qed.
Lemma lem7083484 {_132408 : Type'} (f : _132408 -> real) : (term376 _132408 f) = (term377 _132408 f).
Proof. exact (eq_refl (term376 _132408 f)). Qed.
Lemma lem7083485 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7083486 {_132408 : Type'} (f : _132408 -> real) : (term378 _132408 f) = (term379 _132408 f).
Proof. exact (MK_COMB (@lem7083485) (@lem7083484 _132408 f)). Qed.
Lemma lem7083487 {_132408 : Type'} (s : _132408 -> Prop) (f : _132408 -> real) : (term380 _132408 f s) = (term381 _132408 s f).
Proof. exact (eq_refl (term380 _132408 f s)). Qed.
Lemma lem7083488 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7083489 {_132408 : Type'} (s : _132408 -> Prop) (f : _132408 -> real) : (term382 _132408 f s) = (term383 _132408 s f).
Proof. exact (MK_COMB (@lem7083488) (@lem7083487 _132408 s f)). Qed.
Lemma lem7083490 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) : (term384 _132408 x s) = (term384 _132408 x s).
Proof. exact (eq_refl (term384 _132408 x s)). Qed.
Lemma lem7083491 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) : (term385 _132408 f x s) = (term386 _132408 f x s).
Proof. exact (MK_COMB (@lem7083489 _132408 s f) (@lem7083490 _132408 x s)). Qed.
Lemma lem7083492 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7083493 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) : (term387 _132408 f x s) = (term388 _132408 f x s).
Proof. exact (MK_COMB (@lem7083492) (@lem7083491 _132408 f x s)). Qed.
Lemma lem7083494 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) : (term389 _132408 f x s) = (term390 _132408 x s f).
Proof. exact (eq_refl (term389 _132408 f x s)). Qed.
Lemma lem7083495 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) : (term391 _132408 f x s) = (term392 _132408 x s f).
Proof. exact (MK_COMB (@lem7083493 _132408 f x s) (@lem7083494 _132408 x s f)). Qed.
Lemma lem7083496 {_132408 : Type'} (x : _132408) (f : _132408 -> real) : (term393 _132408 f x) = (term394 _132408 x f).
Proof. exact (fun_ext (fun s : _132408 -> Prop => @lem7083495 _132408 x s f)). Qed.
Lemma lem7083497 {_132408 : Type'} : (@all (_132408 -> Prop)) = (@all (_132408 -> Prop)).
Proof. exact (eq_refl (@all (_132408 -> Prop))). Qed.
Lemma lem7083498 {_132408 : Type'} (x : _132408) (f : _132408 -> real) : (term395 _132408 f x) = (term396 _132408 x f).
Proof. exact (MK_COMB (@lem7083497 _132408) (@lem7083496 _132408 x f)). Qed.
Lemma lem7083499 {_132408 : Type'} (f : _132408 -> real) : (term397 _132408 f) = (term398 _132408 f).
Proof. exact (fun_ext (fun x : _132408 => @lem7083498 _132408 x f)). Qed.
Lemma lem7083500 {_132408 : Type'} : (@all _132408) = (@all _132408).
Proof. exact (eq_refl (@all _132408)). Qed.
Lemma lem7083501 {_132408 : Type'} (f : _132408 -> real) : (term399 _132408 f) = (term400 _132408 f).
Proof. exact (MK_COMB (@lem7083500 _132408) (@lem7083499 _132408 f)). Qed.
Lemma lem7083502 {_132408 : Type'} (f : _132408 -> real) : (term401 _132408 f) = (term402 _132408 f).
Proof. exact (MK_COMB (@lem7083486 _132408 f) (@lem7083501 _132408 f)). Qed.
Lemma lem7083503 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7083504 {_132408 : Type'} (f : _132408 -> real) : (term403 _132408 f) = (term404 _132408 f).
Proof. exact (MK_COMB (@lem7083503) (@lem7083502 _132408 f)). Qed.
Lemma lem7083505 {_132408 : Type'} (s : _132408 -> Prop) (f : _132408 -> real) : (term380 _132408 f s) = (term381 _132408 s f).
Proof. exact (eq_refl (term380 _132408 f s)). Qed.
Lemma lem7083506 {_132408 : Type'} (s : _132408 -> Prop) : (term405 _132408 s) = (term405 _132408 s).
Proof. exact (eq_refl (term405 _132408 s)). Qed.
Lemma lem7083507 {_132408 : Type'} (s : _132408 -> Prop) (f : _132408 -> real) : (term406 _132408 f s) = (term407 _132408 s f).
Proof. exact (MK_COMB (@lem7083506 _132408 s) (@lem7083505 _132408 s f)). Qed.
Lemma lem7083508 {_132408 : Type'} (f : _132408 -> real) : (term408 _132408 f) = (term409 _132408 f).
Proof. exact (fun_ext (fun s : _132408 -> Prop => @lem7083507 _132408 s f)). Qed.
Lemma lem7083509 {_132408 : Type'} : (@all (_132408 -> Prop)) = (@all (_132408 -> Prop)).
Proof. exact (eq_refl (@all (_132408 -> Prop))). Qed.
Lemma lem7083510 {_132408 : Type'} (f : _132408 -> real) : (term410 _132408 f) = (term411 _132408 f).
Proof. exact (MK_COMB (@lem7083509 _132408) (@lem7083508 _132408 f)). Qed.
Lemma lem7083511 {_132408 : Type'} (f : _132408 -> real) : (term374 _132408 f) = (term412 _132408 f).
Proof. exact (MK_COMB (@lem7083504 _132408 f) (@lem7083510 _132408 f)). Qed.
Lemma lem7083512 {_132408 : Type'} (f : _132408 -> real) : term412 _132408 f.
Proof. exact (EQ_MP (@lem7083511 _132408 f) (@lem7083483 _132408 f)). Qed.
Lemma lem7083518 {_131483 : Type'} (f : _131483 -> real) : (@sum _131483 (@EMPTY _131483) f) = term9.
Proof. exact (EQ_MP (@lem7083462 _131483 f) (@lem7083461 _131483 f)). Qed.
Lemma lem7083519 {_132408 : Type'} (f : _132408 -> real) : (@sum _132408 (@EMPTY _132408) f) = term9.
Proof. exact (@lem7083518 _132408 f). Qed.
Lemma lem7083520 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem7083521 {_132408 : Type'} (f : _132408 -> real) : (term413 _132408 f) = term414.
Proof. exact (MK_COMB (@lem7083520) (@lem7083519 _132408 f)). Qed.
Lemma lem7083523 (n : nat) : (term355 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem7083441 n) (@lem7083440 n)). Qed.
Lemma lem7083524 : term414 = term9.
Proof. exact (@lem7083523 (NUMERAL 0)). Qed.
Lemma lem7083525 {_132408 : Type'} (f : _132408 -> real) : (term413 _132408 f) = term9.
Proof. exact (TRANS (@lem7083521 _132408 f) (@lem7083524)). Qed.
Lemma lem7083526 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7083527 {_132408 : Type'} (f : _132408 -> real) : (term415 _132408 f) = term416.
Proof. exact (MK_COMB (@lem7083526) (@lem7083525 _132408 f)). Qed.
Lemma lem7083529 {_131483 : Type'} (f : _131483 -> real) : (@sum _131483 (@EMPTY _131483) f) = term9.
Proof. exact (EQ_MP (@lem7083462 _131483 f) (@lem7083461 _131483 f)). Qed.
Lemma lem7083530 {_132408 : Type'} (f : _132408 -> real) : (@sum _132408 (@EMPTY _132408) f) = term9.
Proof. exact (@lem7083529 _132408 f). Qed.
Lemma lem7083531 {_132408 : Type'} (f : _132408 -> real) : (term417 _132408 f) = term9.
Proof. exact (@lem7083530 _132408 (term418 _132408 f)). Qed.
Lemma lem7083532 {_132408 : Type'} (f : _132408 -> real) : (term377 _132408 f) = term419.
Proof. exact (MK_COMB (@lem7083527 _132408 f) (@lem7083531 _132408 f)). Qed.
Lemma lem7083534 (x : real) : (real_le x x) = True.
Proof. exact (EQ_MP (@lem7083438 x) (@lem7083437 x)). Qed.
Lemma lem7083535 : term419 = True.
Proof. exact (@lem7083534 term9). Qed.
Lemma lem7083536 {_132408 : Type'} (f : _132408 -> real) : (term377 _132408 f) = True.
Proof. exact (TRANS (@lem7083532 _132408 f) (@lem7083535)). Qed.
Lemma lem7083537 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7083538 {_132408 : Type'} (f : _132408 -> real) : (term379 _132408 f) = (and True).
Proof. exact (MK_COMB (@lem7083537) (@lem7083536 _132408 f)). Qed.
Lemma lem7083550 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term420 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7083551 (p : Prop) (q : Prop) (p' : Prop) : term421 p q p'.
Proof. exact (fun q' : Prop => @lem7083550 p q p' q'). Qed.
Lemma lem7083552 (p : Prop) (q : Prop) : term422 p q.
Proof. exact (fun p' : Prop => @lem7083551 p q p'). Qed.
Lemma lem7083553 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) : term423 _132408 x s f.
Proof. exact (@lem7083552 (term386 _132408 f x s) (term390 _132408 x s f)). Qed.
Lemma lem7083554 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) (p' : Prop) : term424 _132408 x s f p'.
Proof. exact (@lem7083553 _132408 x s f p'). Qed.
Lemma lem7083555 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) (p' : Prop) : (term424 _132408 x s f p') = (term425 _132408 x s f p').
Proof. exact (eq_refl (term424 _132408 x s f p')). Qed.
Lemma lem7083556 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) (p' : Prop) : term425 _132408 x s f p'.
Proof. exact (EQ_MP (@lem7083555 _132408 x s f p') (@lem7083554 _132408 x s f p')). Qed.
Lemma lem7083557 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) (p' : Prop) (q' : Prop) : term426 _132408 x s f p' q'.
Proof. exact (@lem7083556 _132408 x s f p' q'). Qed.
Lemma lem7083558 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) (p' : Prop) (q' : Prop) : (term426 _132408 x s f p' q') = (term427 _132408 x s f p' q').
Proof. exact (eq_refl (term426 _132408 x s f p' q')). Qed.
Lemma lem7083559 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) (p' : Prop) (q' : Prop) : term427 _132408 x s f p' q'.
Proof. exact (EQ_MP (@lem7083558 _132408 x s f p' q') (@lem7083557 _132408 x s f p' q')). Qed.
Lemma lem7083566 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) : (term386 _132408 f x s) = (term386 _132408 f x s).
Proof. exact (eq_refl (term386 _132408 f x s)). Qed.
Lemma lem7083567 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (q' : Prop) : term428 _132408 f x s q'.
Proof. exact (@lem7083559 _132408 x s f (term386 _132408 f x s) q'). Qed.
Lemma lem7083568 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (q' : Prop) : term429 _132408 f x s q'.
Proof. exact (@lem7083567 _132408 f x s q' (@lem7083566 _132408 f x s)). Qed.
Lemma lem7083569 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : term386 _132408 f x s.
Proof. exact (h1). Qed.
Lemma lem7083570 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : term384 _132408 x s.
Proof. exact (proj2 (@lem7083569 _132408 f x s h1)). Qed.
Lemma lem7083571 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : @FINITE _132408 s.
Proof. exact (proj2 (@lem7083570 _132408 f x s h1)). Qed.
Lemma lem7083572 {_132408 : Type'} (s : _132408 -> Prop) : (@FINITE _132408 s) = ((@FINITE _132408 s) = True).
Proof. exact (@lem7 (@FINITE _132408 s)). Qed.
Lemma lem7083574 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : term430 _132408 x s.
Proof. exact (proj1 (@lem7083570 _132408 f x s h1)). Qed.
Lemma lem7083575 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) : term431 _132408 x s.
Proof. exact (@lem82 (@IN _132408 x s)). Qed.
Lemma lem7083577 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : term381 _132408 s f.
Proof. exact (proj1 (@lem7083569 _132408 f x s h1)). Qed.
Lemma lem7083578 {_132408 : Type'} (s : _132408 -> Prop) (f : _132408 -> real) : (term381 _132408 s f) = ((term381 _132408 s f) = True).
Proof. exact (@lem7 (term381 _132408 s f)). Qed.
Lemma lem7083583 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term362 _131524 x s f.
Proof. exact (fun h0 : @FINITE _131524 s => @lem7083454 _131524 x f s h0). Qed.
Lemma lem7083584 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) : term362 _132408 x s f.
Proof. exact (@lem7083583 _132408 x s f). Qed.
Lemma lem7083586 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : (@FINITE _132408 s) = True.
Proof. exact (EQ_MP (@lem7083572 _132408 s) (@lem7083571 _132408 f x s h1)). Qed.
Lemma lem7083587 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : True = (@FINITE _132408 s).
Proof. exact (SYM (@lem7083586 _132408 f x s h1)). Qed.
Lemma lem7083588 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : @FINITE _132408 s.
Proof. exact (EQ_MP (@lem7083587 _132408 f x s h1) (@lem0)). Qed.
Lemma lem7083589 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : (term363 _132408 x s f) = (term364 _132408 x s f).
Proof. exact (@lem7083584 _132408 x s f (@lem7083588 _132408 f x s h1)). Qed.
Lemma lem7083591 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term432 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7083592 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term433 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7083591 _2963 g t e g' t' e'). Qed.
Lemma lem7083593 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term434 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7083592 _2963 g t e g' t'). Qed.
Lemma lem7083594 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term435 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7083593 _2963 g t e g'). Qed.
Lemma lem7083595 (g : Prop) (t : real) (e : real) : term436 g t e.
Proof. exact (@lem7083594 real g t e). Qed.
Lemma lem7083596 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) : term437 _132408 x s f.
Proof. exact (@lem7083595 (@IN _132408 x s) (@sum _132408 s f) (term438 _132408 x s f)). Qed.
Lemma lem7083597 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) (g' : Prop) : term439 _132408 x s f g'.
Proof. exact (@lem7083596 _132408 x s f g'). Qed.
Lemma lem7083598 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) (g' : Prop) : (term439 _132408 x s f g') = (term440 _132408 x s f g').
Proof. exact (eq_refl (term439 _132408 x s f g')). Qed.
Lemma lem7083599 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) (g' : Prop) : term440 _132408 x s f g'.
Proof. exact (EQ_MP (@lem7083598 _132408 x s f g') (@lem7083597 _132408 x s f g')). Qed.
Lemma lem7083600 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) (g' : Prop) (t' : real) : term441 _132408 x s f g' t'.
Proof. exact (@lem7083599 _132408 x s f g' t'). Qed.
Lemma lem7083601 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) (g' : Prop) (t' : real) : (term441 _132408 x s f g' t') = (term442 _132408 x s f g' t').
Proof. exact (eq_refl (term441 _132408 x s f g' t')). Qed.
Lemma lem7083602 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) (g' : Prop) (t' : real) : term442 _132408 x s f g' t'.
Proof. exact (EQ_MP (@lem7083601 _132408 x s f g' t') (@lem7083600 _132408 x s f g' t')). Qed.
Lemma lem7083603 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) (g' : Prop) (t' : real) (e' : real) : term443 _132408 x s f g' t' e'.
Proof. exact (@lem7083602 _132408 x s f g' t' e'). Qed.
Lemma lem7083604 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) (g' : Prop) (t' : real) (e' : real) : (term443 _132408 x s f g' t' e') = (term444 _132408 x s f g' t' e').
Proof. exact (eq_refl (term443 _132408 x s f g' t' e')). Qed.
Lemma lem7083605 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) (g' : Prop) (t' : real) (e' : real) : term444 _132408 x s f g' t' e'.
Proof. exact (EQ_MP (@lem7083604 _132408 x s f g' t' e') (@lem7083603 _132408 x s f g' t' e')). Qed.
Lemma lem7083607 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : (@IN _132408 x s) = False.
Proof. exact (@lem7083575 _132408 x s (@lem7083574 _132408 f x s h1)). Qed.
Lemma lem7083608 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) (t' : real) (e' : real) : term445 _132408 x s f t' e'.
Proof. exact (@lem7083605 _132408 x s f False t' e'). Qed.
Lemma lem7083609 {_132408 : Type'} (t' : real) (e' : real) (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : term446 _132408 x s f t' e'.
Proof. exact (@lem7083608 _132408 x s f t' e' (@lem7083607 _132408 f x s h1)). Qed.
Lemma lem7083613 {_132408 : Type'} (s : _132408 -> Prop) (f : _132408 -> real) : (@sum _132408 s f) = (@sum _132408 s f).
Proof. exact (eq_refl (@sum _132408 s f)). Qed.
Lemma lem7083614 {_132408 : Type'} (s : _132408 -> Prop) (f : _132408 -> real) : term447 _132408 s f.
Proof. exact (fun h0 : False => @lem7083613 _132408 s f). Qed.
Lemma lem7083615 {_132408 : Type'} (e' : real) (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : term448 _132408 x s f e'.
Proof. exact (@lem7083609 _132408 (@sum _132408 s f) e' f x s h1). Qed.
Lemma lem7083616 {_132408 : Type'} (e' : real) (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : term449 _132408 x s f e'.
Proof. exact (@lem7083615 _132408 e' f x s h1 (@lem7083614 _132408 s f)). Qed.
Lemma lem7083622 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) : (term438 _132408 x s f) = (term438 _132408 x s f).
Proof. exact (eq_refl (term438 _132408 x s f)). Qed.
Lemma lem7083623 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) : term450 _132408 x s f.
Proof. exact (fun h0 : ~ False => @lem7083622 _132408 x s f). Qed.
Lemma lem7083624 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : term451 _132408 x s f.
Proof. exact (@lem7083616 _132408 (term438 _132408 x s f) f x s h1). Qed.
Lemma lem7083625 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : (term364 _132408 x s f) = (term452 _132408 x s f).
Proof. exact (@lem7083624 _132408 f x s h1 (@lem7083623 _132408 x s f)). Qed.
Lemma lem7083627 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7083628 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7083627 real t1 t2). Qed.
Lemma lem7083629 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) : (term452 _132408 x s f) = (term438 _132408 x s f).
Proof. exact (@lem7083628 (@sum _132408 s f) (term438 _132408 x s f)). Qed.
Lemma lem7083630 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : (term364 _132408 x s f) = (term438 _132408 x s f).
Proof. exact (TRANS (@lem7083625 _132408 f x s h1) (@lem7083629 _132408 x s f)). Qed.
Lemma lem7083631 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : (term363 _132408 x s f) = (term438 _132408 x s f).
Proof. exact (TRANS (@lem7083589 _132408 f x s h1) (@lem7083630 _132408 f x s h1)). Qed.
Lemma lem7083632 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem7083633 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : (term453 _132408 x s f) = (term454 _132408 x s f).
Proof. exact (MK_COMB (@lem7083632) (@lem7083631 _132408 f x s h1)). Qed.
Lemma lem7083634 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7083635 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : (term455 _132408 x s f) = (term456 _132408 x s f).
Proof. exact (MK_COMB (@lem7083634) (@lem7083633 _132408 f x s h1)). Qed.
Lemma lem7083637 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term362 _131524 x s f.
Proof. exact (fun h0 : @FINITE _131524 s => @lem7083454 _131524 x f s h0). Qed.
Lemma lem7083638 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) : term362 _132408 x s f.
Proof. exact (@lem7083637 _132408 x s f). Qed.
Lemma lem7083639 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) : term457 _132408 x s f.
Proof. exact (@lem7083638 _132408 x s (term418 _132408 f)). Qed.
Lemma lem7083641 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : (@FINITE _132408 s) = True.
Proof. exact (EQ_MP (@lem7083572 _132408 s) (@lem7083571 _132408 f x s h1)). Qed.
Lemma lem7083642 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : True = (@FINITE _132408 s).
Proof. exact (SYM (@lem7083641 _132408 f x s h1)). Qed.
Lemma lem7083643 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : @FINITE _132408 s.
Proof. exact (EQ_MP (@lem7083642 _132408 f x s h1) (@lem0)). Qed.
Lemma lem7083644 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : (term458 _132408 x s f) = (term459 _132408 x s f).
Proof. exact (@lem7083639 _132408 x s f (@lem7083643 _132408 f x s h1)). Qed.
Lemma lem7083646 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term432 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7083647 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term433 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7083646 _2963 g t e g' t' e'). Qed.
Lemma lem7083648 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term434 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7083647 _2963 g t e g' t'). Qed.
Lemma lem7083649 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term435 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7083648 _2963 g t e g'). Qed.
Lemma lem7083650 (g : Prop) (t : real) (e : real) : term436 g t e.
Proof. exact (@lem7083649 real g t e). Qed.
Lemma lem7083651 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) : term460 _132408 x s f.
Proof. exact (@lem7083650 (@IN _132408 x s) (term461 _132408 s f) (term462 _132408 x s f)). Qed.
Lemma lem7083652 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) (g' : Prop) : term463 _132408 x s f g'.
Proof. exact (@lem7083651 _132408 x s f g'). Qed.
Lemma lem7083653 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) (g' : Prop) : (term463 _132408 x s f g') = (term464 _132408 x s f g').
Proof. exact (eq_refl (term463 _132408 x s f g')). Qed.
Lemma lem7083654 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) (g' : Prop) : term464 _132408 x s f g'.
Proof. exact (EQ_MP (@lem7083653 _132408 x s f g') (@lem7083652 _132408 x s f g')). Qed.
Lemma lem7083655 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) (g' : Prop) (t' : real) : term465 _132408 x s f g' t'.
Proof. exact (@lem7083654 _132408 x s f g' t'). Qed.
Lemma lem7083656 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) (g' : Prop) (t' : real) : (term465 _132408 x s f g' t') = (term466 _132408 x s f g' t').
Proof. exact (eq_refl (term465 _132408 x s f g' t')). Qed.
Lemma lem7083657 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) (g' : Prop) (t' : real) : term466 _132408 x s f g' t'.
Proof. exact (EQ_MP (@lem7083656 _132408 x s f g' t') (@lem7083655 _132408 x s f g' t')). Qed.
Lemma lem7083658 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) (g' : Prop) (t' : real) (e' : real) : term467 _132408 x s f g' t' e'.
Proof. exact (@lem7083657 _132408 x s f g' t' e'). Qed.
Lemma lem7083659 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) (g' : Prop) (t' : real) (e' : real) : (term467 _132408 x s f g' t' e') = (term468 _132408 x s f g' t' e').
Proof. exact (eq_refl (term467 _132408 x s f g' t' e')). Qed.
Lemma lem7083660 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) (g' : Prop) (t' : real) (e' : real) : term468 _132408 x s f g' t' e'.
Proof. exact (EQ_MP (@lem7083659 _132408 x s f g' t' e') (@lem7083658 _132408 x s f g' t' e')). Qed.
Lemma lem7083662 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : (@IN _132408 x s) = False.
Proof. exact (@lem7083575 _132408 x s (@lem7083574 _132408 f x s h1)). Qed.
Lemma lem7083663 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) (t' : real) (e' : real) : term469 _132408 x s f t' e'.
Proof. exact (@lem7083660 _132408 x s f False t' e'). Qed.
Lemma lem7083664 {_132408 : Type'} (t' : real) (e' : real) (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : term470 _132408 x s f t' e'.
Proof. exact (@lem7083663 _132408 x s f t' e' (@lem7083662 _132408 f x s h1)). Qed.
Lemma lem7083668 {_132408 : Type'} (s : _132408 -> Prop) (f : _132408 -> real) : (term461 _132408 s f) = (term461 _132408 s f).
Proof. exact (eq_refl (term461 _132408 s f)). Qed.
Lemma lem7083669 {_132408 : Type'} (s : _132408 -> Prop) (f : _132408 -> real) : term471 _132408 s f.
Proof. exact (fun h0 : False => @lem7083668 _132408 s f). Qed.
Lemma lem7083670 {_132408 : Type'} (e' : real) (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : term472 _132408 x s f e'.
Proof. exact (@lem7083664 _132408 (term461 _132408 s f) e' f x s h1). Qed.
Lemma lem7083671 {_132408 : Type'} (e' : real) (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : term473 _132408 x s f e'.
Proof. exact (@lem7083670 _132408 e' f x s h1 (@lem7083669 _132408 s f)). Qed.
Lemma lem7083678 {A B : Type'} (f : A -> B) (y : A) : (term474 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7083679 {_132408 : Type'} (f : _132408 -> real) (y : _132408) : (term475 _132408 f y) = (f y).
Proof. exact (@lem7083678 _132408 real f y). Qed.
Lemma lem7083680 {_132408 : Type'} (f : _132408 -> real) (x : _132408) : (term476 _132408 f x) = (term477 _132408 f x).
Proof. exact (@lem7083679 _132408 (term418 _132408 f) x). Qed.
Lemma lem7083681 {_132408 : Type'} (f : _132408 -> real) (x : _132408) : (term477 _132408 f x) = (term478 _132408 f x).
Proof. exact (eq_refl (term477 _132408 f x)). Qed.
Lemma lem7083682 {_132408 : Type'} (f : _132408 -> real) : (term479 _132408 f) = (term418 _132408 f).
Proof. exact (fun_ext (fun x : _132408 => @lem7083681 _132408 f x)). Qed.
Lemma lem7083683 {_132408 : Type'} (x : _132408) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7083684 {_132408 : Type'} (f : _132408 -> real) (x : _132408) : (term476 _132408 f x) = (term477 _132408 f x).
Proof. exact (MK_COMB (@lem7083682 _132408 f) (@lem7083683 _132408 x)). Qed.
Lemma lem7083685 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7083686 {_132408 : Type'} (f : _132408 -> real) (x : _132408) : (term480 _132408 f x) = (term481 _132408 f x).
Proof. exact (MK_COMB (@lem7083685) (@lem7083684 _132408 f x)). Qed.
Lemma lem7083687 {_132408 : Type'} (f : _132408 -> real) (x : _132408) : (term477 _132408 f x) = (term478 _132408 f x).
Proof. exact (eq_refl (term477 _132408 f x)). Qed.
Lemma lem7083688 {_132408 : Type'} (f : _132408 -> real) (x : _132408) : ((term476 _132408 f x) = (term477 _132408 f x)) = ((term477 _132408 f x) = (term478 _132408 f x)).
Proof. exact (MK_COMB (@lem7083686 _132408 f x) (@lem7083687 _132408 f x)). Qed.
Lemma lem7083689 {_132408 : Type'} (f : _132408 -> real) (x : _132408) : (term477 _132408 f x) = (term478 _132408 f x).
Proof. exact (EQ_MP (@lem7083688 _132408 f x) (@lem7083680 _132408 f x)). Qed.
Lemma lem7083690 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7083691 {_132408 : Type'} (f : _132408 -> real) (x : _132408) : (term482 _132408 f x) = (term483 _132408 f x).
Proof. exact (MK_COMB (@lem7083690) (@lem7083689 _132408 f x)). Qed.
Lemma lem7083692 {_132408 : Type'} (s : _132408 -> Prop) (f : _132408 -> real) : (term461 _132408 s f) = (term461 _132408 s f).
Proof. exact (eq_refl (term461 _132408 s f)). Qed.
Lemma lem7083693 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) : (term462 _132408 x s f) = (term484 _132408 x s f).
Proof. exact (MK_COMB (@lem7083691 _132408 f x) (@lem7083692 _132408 s f)). Qed.
Lemma lem7083694 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) : term485 _132408 x s f.
Proof. exact (fun h0 : ~ False => @lem7083693 _132408 x s f). Qed.
Lemma lem7083695 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : term486 _132408 x s f.
Proof. exact (@lem7083671 _132408 (term484 _132408 x s f) f x s h1). Qed.
Lemma lem7083696 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : (term459 _132408 x s f) = (term487 _132408 x s f).
Proof. exact (@lem7083695 _132408 f x s h1 (@lem7083694 _132408 x s f)). Qed.
Lemma lem7083698 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7083699 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7083698 real t1 t2). Qed.
Lemma lem7083700 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) : (term487 _132408 x s f) = (term484 _132408 x s f).
Proof. exact (@lem7083699 (term461 _132408 s f) (term484 _132408 x s f)). Qed.
Lemma lem7083701 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : (term459 _132408 x s f) = (term484 _132408 x s f).
Proof. exact (TRANS (@lem7083696 _132408 f x s h1) (@lem7083700 _132408 x s f)). Qed.
Lemma lem7083702 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : (term458 _132408 x s f) = (term484 _132408 x s f).
Proof. exact (TRANS (@lem7083644 _132408 f x s h1) (@lem7083701 _132408 f x s h1)). Qed.
Lemma lem7083703 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : (term390 _132408 x s f) = (term488 _132408 x s f).
Proof. exact (MK_COMB (@lem7083635 _132408 f x s h1) (@lem7083702 _132408 f x s h1)). Qed.
Lemma lem7083705 (a : real) (x : real) (b : real) : term489 a x b.
Proof. exact (fun h0 : term2 a b => @lem7083429 x a b h0). Qed.
Lemma lem7083706 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) : term490 _132408 x s f.
Proof. exact (@lem7083705 (@sum _132408 s f) (f x) (term461 _132408 s f)). Qed.
Lemma lem7083708 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : (term381 _132408 s f) = True.
Proof. exact (EQ_MP (@lem7083578 _132408 s f) (@lem7083577 _132408 f x s h1)). Qed.
Lemma lem7083709 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : (term381 _132408 s f) = True.
Proof. exact (@lem7083708 _132408 f x s h1). Qed.
Lemma lem7083710 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : True = (term381 _132408 s f).
Proof. exact (SYM (@lem7083709 _132408 f x s h1)). Qed.
Lemma lem7083711 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : term381 _132408 s f.
Proof. exact (EQ_MP (@lem7083710 _132408 f x s h1) (@lem0)). Qed.
Lemma lem7083712 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : (term488 _132408 x s f) = True.
Proof. exact (@lem7083706 _132408 x s f (@lem7083711 _132408 f x s h1)). Qed.
Lemma lem7083713 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) (h1 : term386 _132408 f x s) : (term390 _132408 x s f) = True.
Proof. exact (TRANS (@lem7083703 _132408 f x s h1) (@lem7083712 _132408 f x s h1)). Qed.
Lemma lem7083714 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) : term491 _132408 x s f.
Proof. exact (fun h0 : term386 _132408 f x s => @lem7083713 _132408 f x s h0). Qed.
Lemma lem7083715 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) : term492 _132408 f x s.
Proof. exact (@lem7083568 _132408 f x s True). Qed.
Lemma lem7083716 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) : (term392 _132408 x s f) = (term493 _132408 f x s).
Proof. exact (@lem7083715 _132408 f x s (@lem7083714 _132408 x s f)). Qed.
Lemma lem7083718 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7083719 {_132408 : Type'} (f : _132408 -> real) (x : _132408) (s : _132408 -> Prop) : (term493 _132408 f x s) = True.
Proof. exact (@lem7083718 (term386 _132408 f x s)). Qed.
Lemma lem7083720 {_132408 : Type'} (x : _132408) (s : _132408 -> Prop) (f : _132408 -> real) : (term392 _132408 x s f) = True.
Proof. exact (TRANS (@lem7083716 _132408 f x s) (@lem7083719 _132408 f x s)). Qed.
Lemma lem7083721 {_132408 : Type'} (x : _132408) (f : _132408 -> real) : (term394 _132408 x f) = (term494 _132408).
Proof. exact (fun_ext (fun s : _132408 -> Prop => @lem7083720 _132408 x s f)). Qed.
Lemma lem7083722 {_132408 : Type'} : (@all (_132408 -> Prop)) = (@all (_132408 -> Prop)).
Proof. exact (eq_refl (@all (_132408 -> Prop))). Qed.
Lemma lem7083723 {_132408 : Type'} (x : _132408) (f : _132408 -> real) : (term396 _132408 x f) = (term495 _132408).
Proof. exact (MK_COMB (@lem7083722 _132408) (@lem7083721 _132408 x f)). Qed.
Lemma lem7083725 {A : Type'} (t : Prop) : (term496 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7083726 {_132408 : Type'} (t : Prop) : (term497 _132408 t) = t.
Proof. exact (@lem7083725 (_132408 -> Prop) t). Qed.
Lemma lem7083727 {_132408 : Type'} : (term495 _132408) = True.
Proof. exact (@lem7083726 _132408 True). Qed.
Lemma lem7083728 {_132408 : Type'} (x : _132408) (f : _132408 -> real) : (term396 _132408 x f) = True.
Proof. exact (TRANS (@lem7083723 _132408 x f) (@lem7083727 _132408)). Qed.
Lemma lem7083729 {_132408 : Type'} (f : _132408 -> real) : (term398 _132408 f) = (term498 _132408).
Proof. exact (fun_ext (fun x : _132408 => @lem7083728 _132408 x f)). Qed.
Lemma lem7083730 {_132408 : Type'} : (@all _132408) = (@all _132408).
Proof. exact (eq_refl (@all _132408)). Qed.
Lemma lem7083731 {_132408 : Type'} (f : _132408 -> real) : (term400 _132408 f) = (term499 _132408).
Proof. exact (MK_COMB (@lem7083730 _132408) (@lem7083729 _132408 f)). Qed.
Lemma lem7083733 {A : Type'} (t : Prop) : (term496 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7083734 {_132408 : Type'} (t : Prop) : (term496 _132408 t) = t.
Proof. exact (@lem7083733 _132408 t). Qed.
Lemma lem7083735 {_132408 : Type'} : (term499 _132408) = True.
Proof. exact (@lem7083734 _132408 True). Qed.
Lemma lem7083736 {_132408 : Type'} (f : _132408 -> real) : (term400 _132408 f) = True.
Proof. exact (TRANS (@lem7083731 _132408 f) (@lem7083735 _132408)). Qed.
Lemma lem7083737 {_132408 : Type'} (f : _132408 -> real) : (term402 _132408 f) = (True /\ True).
Proof. exact (MK_COMB (@lem7083538 _132408 f) (@lem7083736 _132408 f)). Qed.
Lemma lem7083739 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7083740 : (True /\ True) = True.
Proof. exact (@lem7083739 True). Qed.
Lemma lem7083741 {_132408 : Type'} (f : _132408 -> real) : (term402 _132408 f) = True.
Proof. exact (TRANS (@lem7083737 _132408 f) (@lem7083740)). Qed.
Lemma lem7083742 {_132408 : Type'} (f : _132408 -> real) : True = (term402 _132408 f).
Proof. exact (SYM (@lem7083741 _132408 f)). Qed.
Lemma lem7083743 {_132408 : Type'} (f : _132408 -> real) : term402 _132408 f.
Proof. exact (EQ_MP (@lem7083742 _132408 f) (@lem0)). Qed.
Lemma lem7083744 {_132408 : Type'} (f : _132408 -> real) : term411 _132408 f.
Proof. exact (@lem7083512 _132408 f (@lem7083743 _132408 f)). Qed.
Lemma lem7083749 {_132408 : Type'} : term500 _132408.
Proof. exact (fun f : _132408 -> real => @lem7083744 _132408 f). Qed.
