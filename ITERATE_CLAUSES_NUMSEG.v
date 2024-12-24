Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_CLAUSES_NUMSEG_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FINITE_EMPTY_spec.
Require Import FINITE_NUMSEG_spec.
Require Import INT_POS_spec.
Require Import IN_NUMSEG_spec.
Require Import ITERATE_CLAUSES_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import monoidal_spec.
Require Import thm0_spec.
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
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19024_spec.
Require Import thm19025_spec.
Require Import thm19030_spec.
Require Import thm19031_spec.
Require Import thm19490_spec.
Require Import thm196_spec.
Require Import thm197_spec.
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
Require Import thm21385_spec.
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
Require Import thm5418320_spec.
Require Import thm5418323_spec.
Require Import thm5418325_spec.
Require Import thm5418328_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem6184283 (m : nat) : (S m) = (term0 m).
Proof. exact (EQ_MP (@lem2841417 m) (@lem2841416 m)). Qed.
Lemma lem6184284 (n : nat) : (S n) = (term0 n).
Proof. exact (@lem6184283 n). Qed.
Lemma lem6184285 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem6184286 (n : nat) : (term1 n) = (term2 n).
Proof. exact (MK_COMB (@lem6184285) (@lem6184284 n)). Qed.
Lemma lem6184287 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem6184288 (n : nat) : (term3 n) = (term4 n).
Proof. exact (MK_COMB (@lem6184286 n) (@lem6184287 n)). Qed.
Lemma lem6184289 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6184307 (n : nat) : (term5 n) = (term6 n).
Proof. exact (MK_COMB (@lem6184289) (@lem6184288 n)). Qed.
Lemma lem6184309 (m : nat) (n : nat) : (Peano.le m n) = (term7 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem6184310 (n : nat) : (term4 n) = (term8 n).
Proof. exact (@lem6184309 (term0 n) n). Qed.
Lemma lem6184312 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem6184313 (n : nat) : (term11 n) = (term12 n).
Proof. exact (@lem6184312 n term13). Qed.
Lemma lem6184314 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem6184315 (n : nat) : (term14 n) = (term15 n).
Proof. exact (MK_COMB (@lem6184314) (@lem6184313 n)). Qed.
Lemma lem6184316 (n : nat) : (int_of_num n) = (int_of_num n).
Proof. exact (eq_refl (int_of_num n)). Qed.
Lemma lem6184317 (n : nat) : (term8 n) = (term16 n).
Proof. exact (MK_COMB (@lem6184315 n) (@lem6184316 n)). Qed.
Lemma lem6184318 (n : nat) : (term4 n) = (term16 n).
Proof. exact (TRANS (@lem6184310 n) (@lem6184317 n)). Qed.
Lemma lem6184319 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6184320 (n : nat) : (term6 n) = (term17 n).
Proof. exact (MK_COMB (@lem6184319) (@lem6184318 n)). Qed.
Lemma lem6184321 (n : nat) : (term5 n) = (term17 n).
Proof. exact (TRANS (@lem6184307 n) (@lem6184320 n)). Qed.
Lemma lem6184322 (n : nat) : term18 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem6184323 (n : nat) : (term18 n) = (term19 n).
Proof. exact (eq_refl (term18 n)). Qed.
Lemma lem6184324 (n : nat) : term19 n.
Proof. exact (EQ_MP (@lem6184323 n) (@lem6184322 n)). Qed.
Lemma lem6184325 (_78766 : int) : (term20 _78766) = (term21 _78766).
Proof. exact (@lem2318604 (term21 _78766)). Qed.
Lemma lem6184336 (_78766 : int) : (term22 _78766) = (term23 _78766).
Proof. exact (@lem16933 (term23 _78766)). Qed.
Lemma lem6184338 (_78766 : int) : (term24 _78766) = (term24 _78766).
Proof. exact (eq_refl (term24 _78766)). Qed.
Lemma lem6184339 (_78766 : int) : (term25 _78766) = (term26 _78766).
Proof. exact (MK_COMB (@lem6184338 _78766) (@lem6184336 _78766)). Qed.
Lemma lem6184340 (_78766 : int) : (term27 _78766) = (term25 _78766).
Proof. exact (@lem17362 (term28 _78766) (term29 _78766)). Qed.
Lemma lem6184348 (_78766 : int) : (term27 _78766) = (term26 _78766).
Proof. exact (TRANS (@lem6184340 _78766) (@lem6184339 _78766)). Qed.
Lemma lem6184351 (x : int) (y : int) : (int_le x y) = (term30 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6184352 (_78766 : int) : (term28 _78766) = (term31 _78766).
Proof. exact (@lem6184351 term32 _78766). Qed.
Lemma lem6184354 (n : nat) : (term33 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6184355 : term34 = term35.
Proof. exact (@lem6184354 (NUMERAL 0)). Qed.
Lemma lem6184356 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6184357 : term36 = term37.
Proof. exact (MK_COMB (@lem6184356) (@lem6184355)). Qed.
Lemma lem6184358 (_78766 : int) : (real_of_int _78766) = (real_of_int _78766).
Proof. exact (eq_refl (real_of_int _78766)). Qed.
Lemma lem6184359 (_78766 : int) : (term31 _78766) = (term38 _78766).
Proof. exact (MK_COMB (@lem6184357) (@lem6184358 _78766)). Qed.
Lemma lem6184361 (_78766 : int) : (term28 _78766) = (term38 _78766).
Proof. exact (TRANS (@lem6184352 _78766) (@lem6184359 _78766)). Qed.
Lemma lem6184364 (x : int) (y : int) : (int_le x y) = (term30 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6184365 (_78766 : int) : (term23 _78766) = (term39 _78766).
Proof. exact (@lem6184364 (term40 _78766) _78766). Qed.
Lemma lem6184367 (x : int) (y : int) : (term41 x y) = (term42 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6184368 (_78766 : int) : (term43 _78766) = (term44 _78766).
Proof. exact (@lem6184367 _78766 term45). Qed.
Lemma lem6184370 (n : nat) : (term33 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6184371 : term46 = term47.
Proof. exact (@lem6184370 term13). Qed.
Lemma lem6184372 (_78766 : int) : (term48 _78766) = (term48 _78766).
Proof. exact (eq_refl (term48 _78766)). Qed.
Lemma lem6184373 (_78766 : int) : (term44 _78766) = (term49 _78766).
Proof. exact (MK_COMB (@lem6184372 _78766) (@lem6184371)). Qed.
Lemma lem6184374 (_78766 : int) : (term43 _78766) = (term49 _78766).
Proof. exact (TRANS (@lem6184368 _78766) (@lem6184373 _78766)). Qed.
Lemma lem6184375 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6184376 (_78766 : int) : (term50 _78766) = (term51 _78766).
Proof. exact (MK_COMB (@lem6184375) (@lem6184374 _78766)). Qed.
Lemma lem6184377 (_78766 : int) : (real_of_int _78766) = (real_of_int _78766).
Proof. exact (eq_refl (real_of_int _78766)). Qed.
Lemma lem6184378 (_78766 : int) : (term39 _78766) = (term52 _78766).
Proof. exact (MK_COMB (@lem6184376 _78766) (@lem6184377 _78766)). Qed.
Lemma lem6184380 (_78766 : int) : (term23 _78766) = (term52 _78766).
Proof. exact (TRANS (@lem6184365 _78766) (@lem6184378 _78766)). Qed.
Lemma lem6184381 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6184382 (_78766 : int) : (term24 _78766) = (term53 _78766).
Proof. exact (MK_COMB (@lem6184381) (@lem6184361 _78766)). Qed.
Lemma lem6184383 (_78766 : int) : (term26 _78766) = (term54 _78766).
Proof. exact (MK_COMB (@lem6184382 _78766) (@lem6184380 _78766)). Qed.
Lemma lem6184384 (_78766 : int) : (term27 _78766) = (term54 _78766).
Proof. exact (TRANS (@lem6184348 _78766) (@lem6184383 _78766)). Qed.
Lemma lem6184388 (t : Prop) : (term55 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6184404 (_78766 : int) : (term56 _78766) = (term54 _78766).
Proof. exact (@lem6184388 (term54 _78766)). Qed.
Lemma lem6184405 (_78766 : int) : (term38 _78766) = (term57 _78766).
Proof. exact (@lem1988287 (real_of_int _78766) term35). Qed.
Lemma lem6184411 (_78766 : int) : (term58 _78766) = (term59 _78766).
Proof. exact (@lem1982792 (real_of_int _78766) term35). Qed.
Lemma lem6184413 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6184414 : term35 = term61.
Proof. exact (@lem6184413 (NUMERAL 0)). Qed.
Lemma lem6184416 (x : nat) : (term62 x) = (term63 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6184417 : term64 = term65.
Proof. exact (@lem6184416 term13). Qed.
Lemma lem6184418 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6184419 : term66 = term67.
Proof. exact (MK_COMB (@lem6184418) (@lem6184417)). Qed.
Lemma lem6184420 : term68 = term69.
Proof. exact (MK_COMB (@lem6184419) (@lem6184414)). Qed.
Lemma lem6184421 : term69 = term70.
Proof. exact (@lem1981613 term64 term35 term47 term47). Qed.
Lemma lem6184423 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6184424 : term73 = term74.
Proof. exact (@lem6184423 term13 term13). Qed.
Lemma lem6184425 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6184426 : term76 = term13.
Proof. exact (EQ_MP (@lem6184425) (@lem940073)). Qed.
Lemma lem6184427 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6184428 : term74 = term47.
Proof. exact (MK_COMB (@lem6184427) (@lem6184426)). Qed.
Lemma lem6184429 : term73 = term47.
Proof. exact (TRANS (@lem6184424) (@lem6184428)). Qed.
Lemma lem6184431 (x : nat) : (term77 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6184432 : term68 = term35.
Proof. exact (@lem6184431 term13). Qed.
Lemma lem6184433 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6184434 : term78 = term79.
Proof. exact (MK_COMB (@lem6184433) (@lem6184432)). Qed.
Lemma lem6184435 : term70 = term61.
Proof. exact (MK_COMB (@lem6184434) (@lem6184429)). Qed.
Lemma lem6184436 : term69 = term61.
Proof. exact (TRANS (@lem6184421) (@lem6184435)). Qed.
Lemma lem6184437 : term68 = term61.
Proof. exact (TRANS (@lem6184420) (@lem6184436)). Qed.
Lemma lem6184439 (x : real) : (term80 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6184440 : term61 = term35.
Proof. exact (@lem6184439 term35). Qed.
Lemma lem6184441 : term68 = term35.
Proof. exact (TRANS (@lem6184437) (@lem6184440)). Qed.
Lemma lem6184442 (_78766 : int) : (term48 _78766) = (term48 _78766).
Proof. exact (eq_refl (term48 _78766)). Qed.
Lemma lem6184443 (_78766 : int) : (term59 _78766) = (term81 _78766).
Proof. exact (MK_COMB (@lem6184442 _78766) (@lem6184441)). Qed.
Lemma lem6184444 (_78766 : int) : (term81 _78766) = (real_of_int _78766).
Proof. exact (@lem1982723 (real_of_int _78766)). Qed.
Lemma lem6184445 (_78766 : int) : (term59 _78766) = (real_of_int _78766).
Proof. exact (TRANS (@lem6184443 _78766) (@lem6184444 _78766)). Qed.
Lemma lem6184447 (_78766 : int) : (term58 _78766) = (real_of_int _78766).
Proof. exact (TRANS (@lem6184411 _78766) (@lem6184445 _78766)). Qed.
Lemma lem6184448 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6184449 (_78766 : int) : (term82 _78766) = (term83 _78766).
Proof. exact (MK_COMB (@lem6184448) (@lem6184447 _78766)). Qed.
Lemma lem6184450 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem6184451 (_78766 : int) : (term57 _78766) = (term84 _78766).
Proof. exact (MK_COMB (@lem6184449 _78766) (@lem6184450)). Qed.
Lemma lem6184452 (_78766 : int) : (term38 _78766) = (term84 _78766).
Proof. exact (TRANS (@lem6184405 _78766) (@lem6184451 _78766)). Qed.
Lemma lem6184453 (_78766 : int) : (term52 _78766) = (term85 _78766).
Proof. exact (@lem1988287 (real_of_int _78766) (term49 _78766)). Qed.
Lemma lem6184465 (_78766 : int) : (term86 _78766) = (term87 _78766).
Proof. exact (@lem1982792 (real_of_int _78766) (term49 _78766)). Qed.
Lemma lem6184466 (_78766 : int) : (term88 _78766) = (term89 _78766).
Proof. exact (@lem1982781 (real_of_int _78766) term64 term47). Qed.
Lemma lem6184468 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6184469 : term47 = term90.
Proof. exact (@lem6184468 term13). Qed.
Lemma lem6184471 (x : nat) : (term62 x) = (term63 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6184472 : term64 = term65.
Proof. exact (@lem6184471 term13). Qed.
Lemma lem6184473 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6184474 : term66 = term67.
Proof. exact (MK_COMB (@lem6184473) (@lem6184472)). Qed.
Lemma lem6184475 : term91 = term92.
Proof. exact (MK_COMB (@lem6184474) (@lem6184469)). Qed.
Lemma lem6184476 : term92 = term93.
Proof. exact (@lem1981613 term64 term47 term47 term47). Qed.
Lemma lem6184478 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6184479 : term73 = term74.
Proof. exact (@lem6184478 term13 term13). Qed.
Lemma lem6184480 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6184481 : term76 = term13.
Proof. exact (EQ_MP (@lem6184480) (@lem940073)). Qed.
Lemma lem6184482 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6184483 : term74 = term47.
Proof. exact (MK_COMB (@lem6184482) (@lem6184481)). Qed.
Lemma lem6184484 : term73 = term47.
Proof. exact (TRANS (@lem6184479) (@lem6184483)). Qed.
Lemma lem6184486 (m : nat) (n : nat) : (term94 m n) = (term95 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6184487 : term91 = term96.
Proof. exact (@lem6184486 term13 term13). Qed.
Lemma lem6184488 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6184489 : term76 = term13.
Proof. exact (EQ_MP (@lem6184488) (@lem940073)). Qed.
Lemma lem6184490 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6184491 : term74 = term47.
Proof. exact (MK_COMB (@lem6184490) (@lem6184489)). Qed.
Lemma lem6184492 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6184493 : term96 = term64.
Proof. exact (MK_COMB (@lem6184492) (@lem6184491)). Qed.
Lemma lem6184494 : term91 = term64.
Proof. exact (TRANS (@lem6184487) (@lem6184493)). Qed.
Lemma lem6184495 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6184496 : term97 = term98.
Proof. exact (MK_COMB (@lem6184495) (@lem6184494)). Qed.
Lemma lem6184497 : term93 = term65.
Proof. exact (MK_COMB (@lem6184496) (@lem6184484)). Qed.
Lemma lem6184498 : term92 = term65.
Proof. exact (TRANS (@lem6184476) (@lem6184497)). Qed.
Lemma lem6184499 : term91 = term65.
Proof. exact (TRANS (@lem6184475) (@lem6184498)). Qed.
Lemma lem6184501 (x : real) : (term80 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6184502 : term65 = term64.
Proof. exact (@lem6184501 term64). Qed.
Lemma lem6184503 : term91 = term64.
Proof. exact (TRANS (@lem6184499) (@lem6184502)). Qed.
Lemma lem6184506 (_78766 : int) : (term99 _78766) = (term99 _78766).
Proof. exact (eq_refl (term99 _78766)). Qed.
Lemma lem6184507 (_78766 : int) : (term89 _78766) = (term100 _78766).
Proof. exact (MK_COMB (@lem6184506 _78766) (@lem6184503)). Qed.
Lemma lem6184508 (_78766 : int) : (term88 _78766) = (term100 _78766).
Proof. exact (TRANS (@lem6184466 _78766) (@lem6184507 _78766)). Qed.
Lemma lem6184509 (_78766 : int) : (term48 _78766) = (term48 _78766).
Proof. exact (eq_refl (term48 _78766)). Qed.
Lemma lem6184510 (_78766 : int) : (term87 _78766) = (term101 _78766).
Proof. exact (MK_COMB (@lem6184509 _78766) (@lem6184508 _78766)). Qed.
Lemma lem6184511 (_78766 : int) : (term101 _78766) = (term102 _78766).
Proof. exact (@lem1982763 (real_of_int _78766) (term103 _78766) term64). Qed.
Lemma lem6184512 (_78766 : int) : (term104 _78766) = (term105 _78766).
Proof. exact (@lem1982715 term64 (real_of_int _78766)). Qed.
Lemma lem6184514 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6184515 : term47 = term90.
Proof. exact (@lem6184514 term13). Qed.
Lemma lem6184517 (x : nat) : (term62 x) = (term63 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6184518 : term64 = term65.
Proof. exact (@lem6184517 term13). Qed.
Lemma lem6184519 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6184520 : term106 = term107.
Proof. exact (MK_COMB (@lem6184519) (@lem6184518)). Qed.
Lemma lem6184521 : term108 = term109.
Proof. exact (MK_COMB (@lem6184520) (@lem6184515)). Qed.
Lemma lem6184522 : term110.
Proof. exact (@lem1981473 term64 term47 term47 term47 term35 term47). Qed.
Lemma lem6184524 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6184525 : term112 = term113.
Proof. exact (@lem6184524 (NUMERAL 0) term13). Qed.
Lemma lem6184526 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6184527 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6184528 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem6184527 h1) (fun h1 : term113 = True => @lem6184526)). Qed.
Lemma lem6184529 : term113 = True.
Proof. exact (EQ_MP (@lem6184528) (@lem6184526)). Qed.
Lemma lem6184530 : term112 = True.
Proof. exact (TRANS (@lem6184525) (@lem6184529)). Qed.
Lemma lem6184531 : True = term112.
Proof. exact (SYM (@lem6184530)). Qed.
Lemma lem6184532 : term112.
Proof. exact (EQ_MP (@lem6184531) (@lem0)). Qed.
Lemma lem6184533 : term115.
Proof. exact (@lem6184522 (@lem6184532)). Qed.
Lemma lem6184535 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6184536 : term112 = term113.
Proof. exact (@lem6184535 (NUMERAL 0) term13). Qed.
Lemma lem6184537 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6184538 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6184539 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem6184538 h1) (fun h1 : term113 = True => @lem6184537)). Qed.
Lemma lem6184540 : term113 = True.
Proof. exact (EQ_MP (@lem6184539) (@lem6184537)). Qed.
Lemma lem6184541 : term112 = True.
Proof. exact (TRANS (@lem6184536) (@lem6184540)). Qed.
Lemma lem6184542 : True = term112.
Proof. exact (SYM (@lem6184541)). Qed.
Lemma lem6184543 : term112.
Proof. exact (EQ_MP (@lem6184542) (@lem0)). Qed.
Lemma lem6184544 : term116.
Proof. exact (@lem6184533 (@lem6184543)). Qed.
Lemma lem6184546 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6184547 : term112 = term113.
Proof. exact (@lem6184546 (NUMERAL 0) term13). Qed.
Lemma lem6184548 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6184549 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6184550 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem6184549 h1) (fun h1 : term113 = True => @lem6184548)). Qed.
Lemma lem6184551 : term113 = True.
Proof. exact (EQ_MP (@lem6184550) (@lem6184548)). Qed.
Lemma lem6184552 : term112 = True.
Proof. exact (TRANS (@lem6184547) (@lem6184551)). Qed.
Lemma lem6184553 : True = term112.
Proof. exact (SYM (@lem6184552)). Qed.
Lemma lem6184554 : term112.
Proof. exact (EQ_MP (@lem6184553) (@lem0)). Qed.
Lemma lem6184555 : term117.
Proof. exact (@lem6184544 (@lem6184554)). Qed.
Lemma lem6184557 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6184558 : term73 = term74.
Proof. exact (@lem6184557 term13 term13). Qed.
Lemma lem6184559 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6184560 : term76 = term13.
Proof. exact (EQ_MP (@lem6184559) (@lem940073)). Qed.
Lemma lem6184561 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6184562 : term74 = term47.
Proof. exact (MK_COMB (@lem6184561) (@lem6184560)). Qed.
Lemma lem6184563 : term73 = term47.
Proof. exact (TRANS (@lem6184558) (@lem6184562)). Qed.
Lemma lem6184565 (m : nat) (n : nat) : (term94 m n) = (term95 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6184566 : term91 = term96.
Proof. exact (@lem6184565 term13 term13). Qed.
Lemma lem6184567 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6184568 : term76 = term13.
Proof. exact (EQ_MP (@lem6184567) (@lem940073)). Qed.
Lemma lem6184569 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6184570 : term74 = term47.
Proof. exact (MK_COMB (@lem6184569) (@lem6184568)). Qed.
Lemma lem6184571 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6184572 : term96 = term64.
Proof. exact (MK_COMB (@lem6184571) (@lem6184570)). Qed.
Lemma lem6184573 : term91 = term64.
Proof. exact (TRANS (@lem6184566) (@lem6184572)). Qed.
Lemma lem6184574 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6184575 : term118 = term106.
Proof. exact (MK_COMB (@lem6184574) (@lem6184573)). Qed.
Lemma lem6184576 : term119 = term108.
Proof. exact (MK_COMB (@lem6184575) (@lem6184563)). Qed.
Lemma lem6184578 (m : nat) : (term120 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6184579 : term108 = term35.
Proof. exact (@lem6184578 term13). Qed.
Lemma lem6184580 : term119 = term35.
Proof. exact (TRANS (@lem6184576) (@lem6184579)). Qed.
Lemma lem6184581 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6184582 : term121 = term122.
Proof. exact (MK_COMB (@lem6184581) (@lem6184580)). Qed.
Lemma lem6184583 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem6184584 : term123 = term124.
Proof. exact (MK_COMB (@lem6184582) (@lem6184583)). Qed.
Lemma lem6184586 (x : nat) : (term125 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6184587 : term124 = term35.
Proof. exact (@lem6184586 term13). Qed.
Lemma lem6184588 : term123 = term35.
Proof. exact (TRANS (@lem6184584) (@lem6184587)). Qed.
Lemma lem6184590 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6184591 : term73 = term74.
Proof. exact (@lem6184590 term13 term13). Qed.
Lemma lem6184592 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6184593 : term76 = term13.
Proof. exact (EQ_MP (@lem6184592) (@lem940073)). Qed.
Lemma lem6184594 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6184595 : term74 = term47.
Proof. exact (MK_COMB (@lem6184594) (@lem6184593)). Qed.
Lemma lem6184596 : term73 = term47.
Proof. exact (TRANS (@lem6184591) (@lem6184595)). Qed.
Lemma lem6184597 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem6184598 : term126 = term124.
Proof. exact (MK_COMB (@lem6184597) (@lem6184596)). Qed.
Lemma lem6184600 (x : nat) : (term125 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6184601 : term124 = term35.
Proof. exact (@lem6184600 term13). Qed.
Lemma lem6184602 : term126 = term35.
Proof. exact (TRANS (@lem6184598) (@lem6184601)). Qed.
Lemma lem6184603 : term35 = term126.
Proof. exact (SYM (@lem6184602)). Qed.
Lemma lem6184604 : term123 = term126.
Proof. exact (TRANS (@lem6184588) (@lem6184603)). Qed.
Lemma lem6184605 : term109 = term61.
Proof. exact (@lem6184555 (@lem6184604)). Qed.
Lemma lem6184606 : term108 = term61.
Proof. exact (TRANS (@lem6184521) (@lem6184605)). Qed.
Lemma lem6184608 (x : real) : (term80 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6184609 : term61 = term35.
Proof. exact (@lem6184608 term35). Qed.
Lemma lem6184610 : term108 = term35.
Proof. exact (TRANS (@lem6184606) (@lem6184609)). Qed.
Lemma lem6184611 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6184612 : term127 = term122.
Proof. exact (MK_COMB (@lem6184611) (@lem6184610)). Qed.
Lemma lem6184613 (_78766 : int) : (real_of_int _78766) = (real_of_int _78766).
Proof. exact (eq_refl (real_of_int _78766)). Qed.
Lemma lem6184614 (_78766 : int) : (term105 _78766) = (term128 _78766).
Proof. exact (MK_COMB (@lem6184612) (@lem6184613 _78766)). Qed.
Lemma lem6184615 (_78766 : int) : (term104 _78766) = (term128 _78766).
Proof. exact (TRANS (@lem6184512 _78766) (@lem6184614 _78766)). Qed.
Lemma lem6184616 (_78766 : int) : (term128 _78766) = term35.
Proof. exact (@lem1982719 (real_of_int _78766)). Qed.
Lemma lem6184617 (_78766 : int) : (term104 _78766) = term35.
Proof. exact (TRANS (@lem6184615 _78766) (@lem6184616 _78766)). Qed.
Lemma lem6184618 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6184619 (_78766 : int) : (term129 _78766) = term130.
Proof. exact (MK_COMB (@lem6184618) (@lem6184617 _78766)). Qed.
Lemma lem6184620 : term64 = term64.
Proof. exact (eq_refl term64). Qed.
Lemma lem6184621 (_78766 : int) : (term102 _78766) = term131.
Proof. exact (MK_COMB (@lem6184619 _78766) (@lem6184620)). Qed.
Lemma lem6184622 (_78766 : int) : (term101 _78766) = term131.
Proof. exact (TRANS (@lem6184511 _78766) (@lem6184621 _78766)). Qed.
Lemma lem6184623 : term131 = term64.
Proof. exact (@lem1982721 term64). Qed.
Lemma lem6184624 (_78766 : int) : (term101 _78766) = term64.
Proof. exact (TRANS (@lem6184622 _78766) (@lem6184623)). Qed.
Lemma lem6184625 (_78766 : int) : (term87 _78766) = term64.
Proof. exact (TRANS (@lem6184510 _78766) (@lem6184624 _78766)). Qed.
Lemma lem6184627 (_78766 : int) : (term86 _78766) = term64.
Proof. exact (TRANS (@lem6184465 _78766) (@lem6184625 _78766)). Qed.
Lemma lem6184628 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6184629 (_78766 : int) : (term132 _78766) = term133.
Proof. exact (MK_COMB (@lem6184628) (@lem6184627 _78766)). Qed.
Lemma lem6184630 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem6184631 (_78766 : int) : (term85 _78766) = term134.
Proof. exact (MK_COMB (@lem6184629 _78766) (@lem6184630)). Qed.
Lemma lem6184632 (_78766 : int) : (term52 _78766) = term134.
Proof. exact (TRANS (@lem6184453 _78766) (@lem6184631 _78766)). Qed.
Lemma lem6184633 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6184634 (_78766 : int) : (term53 _78766) = (term135 _78766).
Proof. exact (MK_COMB (@lem6184633) (@lem6184452 _78766)). Qed.
Lemma lem6184635 (_78766 : int) : (term54 _78766) = (term136 _78766).
Proof. exact (MK_COMB (@lem6184634 _78766) (@lem6184632 _78766)). Qed.
Lemma lem6184650 (_78766 : int) : (term56 _78766) = (term136 _78766).
Proof. exact (TRANS (@lem6184404 _78766) (@lem6184635 _78766)). Qed.
Lemma lem6184654 (_78766 : int) (h1 : term136 _78766) : term136 _78766.
Proof. exact (h1). Qed.
Lemma lem6184655 (_78766 : int) (h1 : term136 _78766) : term134.
Proof. exact (proj2 (@lem6184654 _78766 h1)). Qed.
Lemma lem6184658 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6184659 : term134 = term137.
Proof. exact (@lem6184658 term35 term64). Qed.
Lemma lem6184661 (x : nat) : (term62 x) = (term63 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6184662 : term64 = term65.
Proof. exact (@lem6184661 term13). Qed.
Lemma lem6184664 (x : nat) : (real_of_num x) = (term60 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6184665 : term35 = term61.
Proof. exact (@lem6184664 (NUMERAL 0)). Qed.
Lemma lem6184666 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6184667 : term37 = term138.
Proof. exact (MK_COMB (@lem6184666) (@lem6184665)). Qed.
Lemma lem6184668 : term137 = term139.
Proof. exact (MK_COMB (@lem6184667) (@lem6184662)). Qed.
Lemma lem6184669 : term140.
Proof. exact (@lem1980026 term35 term47 term64 term47). Qed.
Lemma lem6184671 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6184672 : term112 = term113.
Proof. exact (@lem6184671 (NUMERAL 0) term13). Qed.
Lemma lem6184673 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6184674 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6184675 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem6184674 h1) (fun h1 : term113 = True => @lem6184673)). Qed.
Lemma lem6184676 : term113 = True.
Proof. exact (EQ_MP (@lem6184675) (@lem6184673)). Qed.
Lemma lem6184677 : term112 = True.
Proof. exact (TRANS (@lem6184672) (@lem6184676)). Qed.
Lemma lem6184678 : True = term112.
Proof. exact (SYM (@lem6184677)). Qed.
Lemma lem6184679 : term112.
Proof. exact (EQ_MP (@lem6184678) (@lem0)). Qed.
Lemma lem6184680 : term141.
Proof. exact (@lem6184669 (@lem6184679)). Qed.
Lemma lem6184682 (m : nat) (n : nat) : (term111 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6184683 : term112 = term113.
Proof. exact (@lem6184682 (NUMERAL 0) term13). Qed.
Lemma lem6184684 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6184685 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6184686 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem6184685 h1) (fun h1 : term113 = True => @lem6184684)). Qed.
Lemma lem6184687 : term113 = True.
Proof. exact (EQ_MP (@lem6184686) (@lem6184684)). Qed.
Lemma lem6184688 : term112 = True.
Proof. exact (TRANS (@lem6184683) (@lem6184687)). Qed.
Lemma lem6184689 : True = term112.
Proof. exact (SYM (@lem6184688)). Qed.
Lemma lem6184690 : term112.
Proof. exact (EQ_MP (@lem6184689) (@lem0)). Qed.
Lemma lem6184691 : term139 = term142.
Proof. exact (@lem6184680 (@lem6184690)). Qed.
Lemma lem6184693 (m : nat) (n : nat) : (term94 m n) = (term95 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6184694 : term91 = term96.
Proof. exact (@lem6184693 term13 term13). Qed.
Lemma lem6184695 : (term75 = (BIT1 0)) = (term76 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6184696 : term76 = term13.
Proof. exact (EQ_MP (@lem6184695) (@lem940073)). Qed.
Lemma lem6184697 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6184698 : term74 = term47.
Proof. exact (MK_COMB (@lem6184697) (@lem6184696)). Qed.
Lemma lem6184699 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6184700 : term96 = term64.
Proof. exact (MK_COMB (@lem6184699) (@lem6184698)). Qed.
Lemma lem6184701 : term91 = term64.
Proof. exact (TRANS (@lem6184694) (@lem6184700)). Qed.
Lemma lem6184703 (x : nat) : (term125 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6184704 : term124 = term35.
Proof. exact (@lem6184703 term13). Qed.
Lemma lem6184705 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6184706 : term143 = term37.
Proof. exact (MK_COMB (@lem6184705) (@lem6184704)). Qed.
Lemma lem6184707 : term142 = term137.
Proof. exact (MK_COMB (@lem6184706) (@lem6184701)). Qed.
Lemma lem6184709 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6184710 : term137 = term146.
Proof. exact (@lem6184709 (NUMERAL 0) term13). Qed.
Lemma lem6184711 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6184712 (h1 : term114 = (BIT1 0)) : (term13 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6184713 : (term114 = (BIT1 0)) = ((term13 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem6184712 h1) (fun h1 : (term13 = (NUMERAL 0)) = False => @lem6184711)). Qed.
Lemma lem6184714 : (term13 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6184713) (@lem6184711)). Qed.
Lemma lem6184715 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6184716 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6184717 : term147 = (and True).
Proof. exact (MK_COMB (@lem6184716) (@lem6184715)). Qed.
Lemma lem6184718 : term146 = (True /\ False).
Proof. exact (MK_COMB (@lem6184717) (@lem6184714)). Qed.
Lemma lem6184720 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6184721 : term146 = False.
Proof. exact (TRANS (@lem6184718) (@lem6184720)). Qed.
Lemma lem6184722 : term137 = False.
Proof. exact (TRANS (@lem6184710) (@lem6184721)). Qed.
Lemma lem6184723 : term142 = False.
Proof. exact (TRANS (@lem6184707) (@lem6184722)). Qed.
Lemma lem6184724 : term139 = False.
Proof. exact (TRANS (@lem6184691) (@lem6184723)). Qed.
Lemma lem6184725 : term137 = False.
Proof. exact (TRANS (@lem6184668) (@lem6184724)). Qed.
Lemma lem6184726 : term134 = False.
Proof. exact (TRANS (@lem6184659) (@lem6184725)). Qed.
Lemma lem6184727 (_78766 : int) (h1 : term136 _78766) : False.
Proof. exact (EQ_MP (@lem6184726) (@lem6184655 _78766 h1)). Qed.
Lemma lem6184729 (_78766 : int) (h1 : term136 _78766) : term136 _78766.
Proof. exact (h1). Qed.
Lemma lem6184730 (_78766 : int) (h1 : term136 _78766) : (term136 _78766) = False.
Proof. exact (prop_ext (fun h2 : term136 _78766 => @lem6184727 _78766 h1) (fun h2 : False => @lem6184729 _78766 h1)). Qed.
Lemma lem6184731 (_78766 : int) (h1 : term136 _78766) : False.
Proof. exact (EQ_MP (@lem6184730 _78766 h1) (@lem6184729 _78766 h1)). Qed.
Lemma lem6184732 (_78766 : int) (h1 : term56 _78766) : term56 _78766.
Proof. exact (h1). Qed.
Lemma lem6184733 (_78766 : int) (h1 : term56 _78766) : term136 _78766.
Proof. exact (EQ_MP (@lem6184650 _78766) (@lem6184732 _78766 h1)). Qed.
Lemma lem6184734 (_78766 : int) (h1 : term56 _78766) : (term136 _78766) = False.
Proof. exact (prop_ext (fun h2 : term136 _78766 => @lem6184731 _78766 h2) (fun h2 : False => @lem6184733 _78766 h1)). Qed.
Lemma lem6184735 (_78766 : int) (h1 : term56 _78766) : False.
Proof. exact (EQ_MP (@lem6184734 _78766 h1) (@lem6184733 _78766 h1)). Qed.
Lemma lem6184736 (_78766 : int) : term148 _78766.
Proof. exact (fun h0 : term56 _78766 => @lem6184735 _78766 h0). Qed.
Lemma lem6184737 (_78766 : int) : term149 _78766.
Proof. exact (@lem1386578 (term150 _78766)). Qed.
Lemma lem6184740 (_78766 : int) : term150 _78766.
Proof. exact (@lem6184737 _78766 (@lem6184736 _78766)). Qed.
Lemma lem6184741 (_78766 : int) : (term54 _78766) = (term27 _78766).
Proof. exact (SYM (@lem6184384 _78766)). Qed.
Lemma lem6184742 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6184743 (_78766 : int) : (term150 _78766) = (term20 _78766).
Proof. exact (MK_COMB (@lem6184742) (@lem6184741 _78766)). Qed.
Lemma lem6184744 (_78766 : int) : term20 _78766.
Proof. exact (EQ_MP (@lem6184743 _78766) (@lem6184740 _78766)). Qed.
Lemma lem6184745 (_78766 : int) : term21 _78766.
Proof. exact (EQ_MP (@lem6184325 _78766) (@lem6184744 _78766)). Qed.
Lemma lem6184746 (n : nat) : term151 n.
Proof. exact (@lem6184745 (int_of_num n)). Qed.
Lemma lem6184747 (n : nat) : term17 n.
Proof. exact (@lem6184746 n (@lem6184324 n)). Qed.
Lemma lem6184748 (n : nat) : (term17 n) = (term5 n).
Proof. exact (SYM (@lem6184321 n)). Qed.
Lemma lem6184749 (n : nat) : term5 n.
Proof. exact (EQ_MP (@lem6184748 n) (@lem6184747 n)). Qed.
Lemma lem6184750 {A : Type'} (x : A) : term152 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem6184751 {A : Type'} (x : A) : (term152 A x) = (term153 A x).
Proof. exact (eq_refl (term152 A x)). Qed.
Lemma lem6184752 {A : Type'} (x : A) : term153 A x.
Proof. exact (EQ_MP (@lem6184751 A x) (@lem6184750 A x)). Qed.
Lemma lem6184753 {A : Type'} (x : A) : term154 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem6184755 (n : nat) : term155 n.
Proof. exact (@lem82 (term3 n)). Qed.
Lemma lem6184757 : term156.
Proof. exact (EQ_MP (@lem5418323) (@lem5418320)). Qed.
Lemma lem6184758 (m : nat) : term157 m.
Proof. exact (@lem6184757 m). Qed.
Lemma lem6184759 (m : nat) : (term157 m) = (term158 m).
Proof. exact (eq_refl (term157 m)). Qed.
Lemma lem6184760 (m : nat) : term158 m.
Proof. exact (EQ_MP (@lem6184759 m) (@lem6184758 m)). Qed.
Lemma lem6184761 (m : nat) (n : nat) : term159 m n.
Proof. exact (@lem6184760 m n). Qed.
Lemma lem6184762 (m : nat) (n : nat) : (term159 m n) = ((term160 m n) = (term161 m n)).
Proof. exact (eq_refl (term159 m n)). Qed.
Lemma lem6184764 : term162.
Proof. exact (EQ_MP (@lem5418328) (@lem5418325)). Qed.
Lemma lem6184765 (m : nat) : term163 m.
Proof. exact (@lem6184764 m). Qed.
Lemma lem6184766 (m : nat) : (term163 m) = ((term164 m) = (term165 m)).
Proof. exact (eq_refl (term163 m)). Qed.
Lemma lem6184783 (m : nat) : (term164 m) = (term165 m).
Proof. exact (EQ_MP (@lem6184766 m) (@lem6184765 m)). Qed.
Lemma lem6184788 {_123419 : Type'} (op : type1400 _123419) : (@iterate _123419 nat op) = (@iterate _123419 nat op).
Proof. exact (eq_refl (@iterate _123419 nat op)). Qed.
Lemma lem6184789 {_123419 : Type'} (op : type1400 _123419) (m : nat) : (term166 _123419 op m) = (term167 _123419 op m).
Proof. exact (MK_COMB (@lem6184788 _123419 op) (@lem6184783 m)). Qed.
Lemma lem6184790 {_123419 : Type'} (f : nat -> _123419) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6184791 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) : (term168 _123419 op m f) = (term169 _123419 op m f).
Proof. exact (MK_COMB (@lem6184789 _123419 op m) (@lem6184790 _123419 f)). Qed.
Lemma lem6184792 {_123419 : Type'} : (@eq _123419) = (@eq _123419).
Proof. exact (eq_refl (@eq _123419)). Qed.
Lemma lem6184793 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) : (term170 _123419 op m f) = (term171 _123419 op m f).
Proof. exact (MK_COMB (@lem6184792 _123419) (@lem6184791 _123419 op m f)). Qed.
Lemma lem6184798 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) : (term172 _123419 m f op) = (term172 _123419 m f op).
Proof. exact (eq_refl (term172 _123419 m f op)). Qed.
Lemma lem6184799 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) : ((term168 _123419 op m f) = (term172 _123419 m f op)) = ((term169 _123419 op m f) = (term172 _123419 m f op)).
Proof. exact (MK_COMB (@lem6184793 _123419 op m f) (@lem6184798 _123419 m f op)). Qed.
Lemma lem6184802 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : (term173 _123419 f op) = (term174 _123419 f op).
Proof. exact (fun_ext (fun m : nat => @lem6184799 _123419 m f op)). Qed.
Lemma lem6184803 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6184804 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : (term175 _123419 f op) = (term176 _123419 f op).
Proof. exact (MK_COMB (@lem6184803) (@lem6184802 _123419 f op)). Qed.
Lemma lem6184809 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6184810 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : (term177 _123419 f op) = (term178 _123419 f op).
Proof. exact (MK_COMB (@lem6184809) (@lem6184804 _123419 f op)). Qed.
Lemma lem6184822 (m : nat) (n : nat) : (term160 m n) = (term161 m n).
Proof. exact (EQ_MP (@lem6184762 m n) (@lem6184761 m n)). Qed.
Lemma lem6184823 {_123419 : Type'} (op : type1400 _123419) : (@iterate _123419 nat op) = (@iterate _123419 nat op).
Proof. exact (eq_refl (@iterate _123419 nat op)). Qed.
Lemma lem6184824 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) : (term179 _123419 op m n) = (term180 _123419 op m n).
Proof. exact (MK_COMB (@lem6184823 _123419 op) (@lem6184822 m n)). Qed.
Lemma lem6184825 {_123419 : Type'} (f : nat -> _123419) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6184826 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term181 _123419 op m n f) = (term182 _123419 op m n f).
Proof. exact (MK_COMB (@lem6184824 _123419 op m n) (@lem6184825 _123419 f)). Qed.
Lemma lem6184827 {_123419 : Type'} : (@eq _123419) = (@eq _123419).
Proof. exact (eq_refl (@eq _123419)). Qed.
Lemma lem6184828 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term183 _123419 op m n f) = (term184 _123419 op m n f).
Proof. exact (MK_COMB (@lem6184827 _123419) (@lem6184826 _123419 op m n f)). Qed.
Lemma lem6184829 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term185 _123419 op m n f) = (term185 _123419 op m n f).
Proof. exact (eq_refl (term185 _123419 op m n f)). Qed.
Lemma lem6184830 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : ((term181 _123419 op m n f) = (term185 _123419 op m n f)) = ((term182 _123419 op m n f) = (term185 _123419 op m n f)).
Proof. exact (MK_COMB (@lem6184828 _123419 op m n f) (@lem6184829 _123419 op m n f)). Qed.
Lemma lem6184833 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) : (term186 _123419 op m f) = (term187 _123419 op m f).
Proof. exact (fun_ext (fun n : nat => @lem6184830 _123419 op m n f)). Qed.
Lemma lem6184834 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6184835 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) : (term188 _123419 op m f) = (term189 _123419 op m f).
Proof. exact (MK_COMB (@lem6184834) (@lem6184833 _123419 op m f)). Qed.
Lemma lem6184840 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : (term190 _123419 op f) = (term191 _123419 op f).
Proof. exact (fun_ext (fun m : nat => @lem6184835 _123419 op m f)). Qed.
Lemma lem6184841 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6184842 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : (term192 _123419 op f) = (term193 _123419 op f).
Proof. exact (MK_COMB (@lem6184841) (@lem6184840 _123419 op f)). Qed.
Lemma lem6184847 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : (term194 _123419 op f) = (term195 _123419 op f).
Proof. exact (MK_COMB (@lem6184810 _123419 f op) (@lem6184842 _123419 op f)). Qed.
Lemma lem6184850 {_123419 : Type'} (op : type1400 _123419) : (term196 _123419 op) = (term196 _123419 op).
Proof. exact (eq_refl (term196 _123419 op)). Qed.
Lemma lem6184851 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : (term197 _123419 op f) = (term198 _123419 op f).
Proof. exact (MK_COMB (@lem6184850 _123419 op) (@lem6184847 _123419 op f)). Qed.
Lemma lem6184854 {_123419 : Type'} (f : nat -> _123419) : (term199 _123419 f) = (term200 _123419 f).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6184851 _123419 op f)). Qed.
Lemma lem6184855 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6184856 {_123419 : Type'} (f : nat -> _123419) : (term201 _123419 f) = (term202 _123419 f).
Proof. exact (MK_COMB (@lem6184855 _123419) (@lem6184854 _123419 f)). Qed.
Lemma lem6184861 {_123419 : Type'} (f : nat -> _123419) : (term202 _123419 f) = (term201 _123419 f).
Proof. exact (SYM (@lem6184856 _123419 f)). Qed.
Lemma lem6184862 {_123419 : Type'} (op : type1400 _123419) (h1 : @monoidal _123419 op) : @monoidal _123419 op.
Proof. exact (h1). Qed.
Lemma lem6184863 (_474 : nat -> Prop) (_475 : Prop) (_476 : type993) (_477 : nat -> Prop) : (term203 _476 _475 _474 _477) = (term204 _474 _475 _476 _477).
Proof. exact (@lem13473 (nat -> Prop) _474 _475 _476 _477). Qed.
Lemma lem6184864 {_123419 : Type'} (_474 : nat -> Prop) (_475 : Prop) (m : nat) (f : nat -> _123419) (op : type1400 _123419) (_477 : nat -> Prop) : (term205 _123419 m f op _475 _474 _477) = (term206 _123419 _474 _475 m f op _477).
Proof. exact (@lem6184863 _474 _475 (term207 _123419 m f op) _477). Qed.
Lemma lem6184865 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) : (term208 _123419 f op m) = (term209 _123419 m f op).
Proof. exact (@lem6184864 _123419 term210 (m = (NUMERAL 0)) m f op (@EMPTY nat)). Qed.
Lemma lem6184866 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) : (term211 _123419 m f op) = ((@iterate _123419 nat op (@EMPTY nat) f) = (term172 _123419 m f op)).
Proof. exact (eq_refl (term211 _123419 m f op)). Qed.
Lemma lem6184867 (m : nat) : (term212 m) = (term212 m).
Proof. exact (eq_refl (term212 m)). Qed.
Lemma lem6184868 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) : (term213 _123419 m f op) = (term214 _123419 m f op).
Proof. exact (MK_COMB (@lem6184867 m) (@lem6184866 _123419 m f op)). Qed.
Lemma lem6184869 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) : (term215 _123419 m f op) = ((term216 _123419 op f) = (term172 _123419 m f op)).
Proof. exact (eq_refl (term215 _123419 m f op)). Qed.
Lemma lem6184870 (m : nat) : (term217 m) = (term217 m).
Proof. exact (eq_refl (term217 m)). Qed.
Lemma lem6184871 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) : (term218 _123419 m f op) = (term219 _123419 m f op).
Proof. exact (MK_COMB (@lem6184870 m) (@lem6184869 _123419 m f op)). Qed.
Lemma lem6184872 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6184873 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) : (term220 _123419 m f op) = (term221 _123419 m f op).
Proof. exact (MK_COMB (@lem6184872) (@lem6184871 _123419 m f op)). Qed.
Lemma lem6184874 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) : (term209 _123419 m f op) = (term222 _123419 m f op).
Proof. exact (MK_COMB (@lem6184873 _123419 m f op) (@lem6184868 _123419 m f op)). Qed.
Lemma lem6184875 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) : (term208 _123419 f op m) = ((term169 _123419 op m f) = (term172 _123419 m f op)).
Proof. exact (eq_refl (term208 _123419 f op m)). Qed.
Lemma lem6184876 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6184877 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) : (term223 _123419 f op m) = (term224 _123419 m f op).
Proof. exact (MK_COMB (@lem6184876) (@lem6184875 _123419 m f op)). Qed.
Lemma lem6184878 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) : ((term208 _123419 f op m) = (term209 _123419 m f op)) = (((term169 _123419 op m f) = (term172 _123419 m f op)) = (term222 _123419 m f op)).
Proof. exact (MK_COMB (@lem6184877 _123419 m f op) (@lem6184874 _123419 m f op)). Qed.
Lemma lem6184879 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) : ((term169 _123419 op m f) = (term172 _123419 m f op)) = (term222 _123419 m f op).
Proof. exact (EQ_MP (@lem6184878 _123419 m f op) (@lem6184865 _123419 m f op)). Qed.
Lemma lem6184880 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) : (term222 _123419 m f op) = ((term169 _123419 op m f) = (term172 _123419 m f op)).
Proof. exact (SYM (@lem6184879 _123419 m f op)). Qed.
Lemma lem6184881 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem6184882 (m : nat) : (m = (NUMERAL 0)) = ((m = (NUMERAL 0)) = True).
Proof. exact (@lem7 (m = (NUMERAL 0))). Qed.
Lemma lem6184883 (m : nat) (h1 : m = (NUMERAL 0)) : (m = (NUMERAL 0)) = True.
Proof. exact (EQ_MP (@lem6184882 m) (@lem6184881 m h1)). Qed.
Lemma lem6184884 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : (term225 _123419 f op) = (term225 _123419 f op).
Proof. exact (eq_refl (term225 _123419 f op)). Qed.
Lemma lem6184885 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (h1 : m = (NUMERAL 0)) : (term226 _123419 f op m) = (term227 _123419 f op).
Proof. exact (MK_COMB (@lem6184884 _123419 f op) (@lem6184883 m h1)). Qed.
Lemma lem6184886 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : (term227 _123419 f op) = ((term216 _123419 op f) = (term228 _123419 f op)).
Proof. exact (eq_refl (term227 _123419 f op)). Qed.
Lemma lem6184887 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) : (term229 _123419 f op m) = (term229 _123419 f op m).
Proof. exact (eq_refl (term229 _123419 f op m)). Qed.
Lemma lem6184888 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) : ((term226 _123419 f op m) = (term227 _123419 f op)) = ((term226 _123419 f op m) = ((term216 _123419 op f) = (term228 _123419 f op))).
Proof. exact (MK_COMB (@lem6184887 _123419 f op m) (@lem6184886 _123419 f op)). Qed.
Lemma lem6184889 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) : (term226 _123419 f op m) = ((term216 _123419 op f) = (term172 _123419 m f op)).
Proof. exact (eq_refl (term226 _123419 f op m)). Qed.
Lemma lem6184890 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6184891 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) : (term229 _123419 f op m) = (term230 _123419 m f op).
Proof. exact (MK_COMB (@lem6184890) (@lem6184889 _123419 m f op)). Qed.
Lemma lem6184892 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : ((term216 _123419 op f) = (term228 _123419 f op)) = ((term216 _123419 op f) = (term228 _123419 f op)).
Proof. exact (eq_refl ((term216 _123419 op f) = (term228 _123419 f op))). Qed.
Lemma lem6184893 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) : ((term226 _123419 f op m) = ((term216 _123419 op f) = (term228 _123419 f op))) = (((term216 _123419 op f) = (term172 _123419 m f op)) = ((term216 _123419 op f) = (term228 _123419 f op))).
Proof. exact (MK_COMB (@lem6184891 _123419 m f op) (@lem6184892 _123419 f op)). Qed.
Lemma lem6184894 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) : ((term226 _123419 f op m) = (term227 _123419 f op)) = (((term216 _123419 op f) = (term172 _123419 m f op)) = ((term216 _123419 op f) = (term228 _123419 f op))).
Proof. exact (TRANS (@lem6184888 _123419 m f op) (@lem6184893 _123419 m f op)). Qed.
Lemma lem6184895 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (h1 : m = (NUMERAL 0)) : ((term216 _123419 op f) = (term172 _123419 m f op)) = ((term216 _123419 op f) = (term228 _123419 f op)).
Proof. exact (EQ_MP (@lem6184894 _123419 m f op) (@lem6184885 _123419 f op m h1)). Qed.
Lemma lem6184896 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (h1 : m = (NUMERAL 0)) : ((term216 _123419 op f) = (term228 _123419 f op)) = ((term216 _123419 op f) = (term172 _123419 m f op)).
Proof. exact (SYM (@lem6184895 _123419 f op m h1)). Qed.
Lemma lem6184897 (m : nat) (h1 : term231 m) : term231 m.
Proof. exact (h1). Qed.
Lemma lem6184898 (m : nat) : term232 m.
Proof. exact (@lem82 (m = (NUMERAL 0))). Qed.
Lemma lem6184899 (m : nat) (h1 : term231 m) : (m = (NUMERAL 0)) = False.
Proof. exact (@lem6184898 m (@lem6184897 m h1)). Qed.
Lemma lem6184900 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : (term233 _123419 f op) = (term233 _123419 f op).
Proof. exact (eq_refl (term233 _123419 f op)). Qed.
Lemma lem6184901 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (h1 : term231 m) : (term234 _123419 f op m) = (term235 _123419 f op).
Proof. exact (MK_COMB (@lem6184900 _123419 f op) (@lem6184899 m h1)). Qed.
Lemma lem6184902 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : (term235 _123419 f op) = ((@iterate _123419 nat op (@EMPTY nat) f) = (term236 _123419 f op)).
Proof. exact (eq_refl (term235 _123419 f op)). Qed.
Lemma lem6184903 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) : (term237 _123419 f op m) = (term237 _123419 f op m).
Proof. exact (eq_refl (term237 _123419 f op m)). Qed.
Lemma lem6184904 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) : ((term234 _123419 f op m) = (term235 _123419 f op)) = ((term234 _123419 f op m) = ((@iterate _123419 nat op (@EMPTY nat) f) = (term236 _123419 f op))).
Proof. exact (MK_COMB (@lem6184903 _123419 f op m) (@lem6184902 _123419 f op)). Qed.
Lemma lem6184905 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) : (term234 _123419 f op m) = ((@iterate _123419 nat op (@EMPTY nat) f) = (term172 _123419 m f op)).
Proof. exact (eq_refl (term234 _123419 f op m)). Qed.
Lemma lem6184906 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6184907 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) : (term237 _123419 f op m) = (term238 _123419 m f op).
Proof. exact (MK_COMB (@lem6184906) (@lem6184905 _123419 m f op)). Qed.
Lemma lem6184908 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : ((@iterate _123419 nat op (@EMPTY nat) f) = (term236 _123419 f op)) = ((@iterate _123419 nat op (@EMPTY nat) f) = (term236 _123419 f op)).
Proof. exact (eq_refl ((@iterate _123419 nat op (@EMPTY nat) f) = (term236 _123419 f op))). Qed.
Lemma lem6184909 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) : ((term234 _123419 f op m) = ((@iterate _123419 nat op (@EMPTY nat) f) = (term236 _123419 f op))) = (((@iterate _123419 nat op (@EMPTY nat) f) = (term172 _123419 m f op)) = ((@iterate _123419 nat op (@EMPTY nat) f) = (term236 _123419 f op))).
Proof. exact (MK_COMB (@lem6184907 _123419 m f op) (@lem6184908 _123419 f op)). Qed.
Lemma lem6184910 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) : ((term234 _123419 f op m) = (term235 _123419 f op)) = (((@iterate _123419 nat op (@EMPTY nat) f) = (term172 _123419 m f op)) = ((@iterate _123419 nat op (@EMPTY nat) f) = (term236 _123419 f op))).
Proof. exact (TRANS (@lem6184904 _123419 m f op) (@lem6184909 _123419 m f op)). Qed.
Lemma lem6184911 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (h1 : term231 m) : ((@iterate _123419 nat op (@EMPTY nat) f) = (term172 _123419 m f op)) = ((@iterate _123419 nat op (@EMPTY nat) f) = (term236 _123419 f op)).
Proof. exact (EQ_MP (@lem6184910 _123419 m f op) (@lem6184901 _123419 f op m h1)). Qed.
Lemma lem6184912 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (h1 : term231 m) : ((@iterate _123419 nat op (@EMPTY nat) f) = (term236 _123419 f op)) = ((@iterate _123419 nat op (@EMPTY nat) f) = (term172 _123419 m f op)).
Proof. exact (SYM (@lem6184911 _123419 f op m h1)). Qed.
Lemma lem6184913 (_474 : nat -> Prop) (_475 : Prop) (_476 : type993) (_477 : nat -> Prop) : (term203 _476 _475 _474 _477) = (term204 _474 _475 _476 _477).
Proof. exact (@lem13473 (nat -> Prop) _474 _475 _476 _477). Qed.
Lemma lem6184914 {_123419 : Type'} (_474 : nat -> Prop) (_475 : Prop) (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) (_477 : nat -> Prop) : (term239 _123419 op m n f _475 _474 _477) = (term240 _123419 _474 _475 op m n f _477).
Proof. exact (@lem6184913 _474 _475 (term241 _123419 op m n f) _477). Qed.
Lemma lem6184915 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (m : nat) (n : nat) : (term242 _123419 op f m n) = (term243 _123419 op f m n).
Proof. exact (@lem6184914 _123419 (term244 m n) (term245 m n) op m n f (dotdot m n)). Qed.
Lemma lem6184916 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term246 _123419 op f m n) = ((term247 _123419 op m n f) = (term185 _123419 op m n f)).
Proof. exact (eq_refl (term246 _123419 op f m n)). Qed.
Lemma lem6184917 (m : nat) (n : nat) : (term248 m n) = (term248 m n).
Proof. exact (eq_refl (term248 m n)). Qed.
Lemma lem6184918 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term249 _123419 op f m n) = (term250 _123419 op m n f).
Proof. exact (MK_COMB (@lem6184917 m n) (@lem6184916 _123419 op m n f)). Qed.
Lemma lem6184919 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term251 _123419 op f m n) = ((term252 _123419 op m n f) = (term185 _123419 op m n f)).
Proof. exact (eq_refl (term251 _123419 op f m n)). Qed.
Lemma lem6184920 (m : nat) (n : nat) : (term253 m n) = (term253 m n).
Proof. exact (eq_refl (term253 m n)). Qed.
Lemma lem6184921 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term254 _123419 op f m n) = (term255 _123419 op m n f).
Proof. exact (MK_COMB (@lem6184920 m n) (@lem6184919 _123419 op m n f)). Qed.
Lemma lem6184922 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6184923 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term256 _123419 op f m n) = (term257 _123419 op m n f).
Proof. exact (MK_COMB (@lem6184922) (@lem6184921 _123419 op m n f)). Qed.
Lemma lem6184924 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term243 _123419 op f m n) = (term258 _123419 op m n f).
Proof. exact (MK_COMB (@lem6184923 _123419 op m n f) (@lem6184918 _123419 op m n f)). Qed.
Lemma lem6184925 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term242 _123419 op f m n) = ((term182 _123419 op m n f) = (term185 _123419 op m n f)).
Proof. exact (eq_refl (term242 _123419 op f m n)). Qed.
Lemma lem6184926 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6184927 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term259 _123419 op f m n) = (term260 _123419 op m n f).
Proof. exact (MK_COMB (@lem6184926) (@lem6184925 _123419 op m n f)). Qed.
Lemma lem6184928 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : ((term242 _123419 op f m n) = (term243 _123419 op f m n)) = (((term182 _123419 op m n f) = (term185 _123419 op m n f)) = (term258 _123419 op m n f)).
Proof. exact (MK_COMB (@lem6184927 _123419 op m n f) (@lem6184924 _123419 op m n f)). Qed.
Lemma lem6184929 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : ((term182 _123419 op m n f) = (term185 _123419 op m n f)) = (term258 _123419 op m n f).
Proof. exact (EQ_MP (@lem6184928 _123419 op m n f) (@lem6184915 _123419 op f m n)). Qed.
Lemma lem6184930 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term258 _123419 op m n f) = ((term182 _123419 op m n f) = (term185 _123419 op m n f)).
Proof. exact (SYM (@lem6184929 _123419 op m n f)). Qed.
Lemma lem6184931 (m : nat) (n : nat) (h1 : term245 m n) : term245 m n.
Proof. exact (h1). Qed.
Lemma lem6184932 (m : nat) (n : nat) : (term245 m n) = ((term245 m n) = True).
Proof. exact (@lem7 (term245 m n)). Qed.
Lemma lem6184933 (m : nat) (n : nat) (h1 : term245 m n) : (term245 m n) = True.
Proof. exact (EQ_MP (@lem6184932 m n) (@lem6184931 m n h1)). Qed.
Lemma lem6184934 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term261 _123419 op m n f) = (term261 _123419 op m n f).
Proof. exact (eq_refl (term261 _123419 op m n f)). Qed.
Lemma lem6184935 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (m : nat) (n : nat) (h1 : term245 m n) : (term262 _123419 op f m n) = (term263 _123419 op m n f).
Proof. exact (MK_COMB (@lem6184934 _123419 op m n f) (@lem6184933 m n h1)). Qed.
Lemma lem6184936 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term263 _123419 op m n f) = ((term252 _123419 op m n f) = (term264 _123419 op m n f)).
Proof. exact (eq_refl (term263 _123419 op m n f)). Qed.
Lemma lem6184937 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (m : nat) (n : nat) : (term265 _123419 op f m n) = (term265 _123419 op f m n).
Proof. exact (eq_refl (term265 _123419 op f m n)). Qed.
Lemma lem6184938 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : ((term262 _123419 op f m n) = (term263 _123419 op m n f)) = ((term262 _123419 op f m n) = ((term252 _123419 op m n f) = (term264 _123419 op m n f))).
Proof. exact (MK_COMB (@lem6184937 _123419 op f m n) (@lem6184936 _123419 op m n f)). Qed.
Lemma lem6184939 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term262 _123419 op f m n) = ((term252 _123419 op m n f) = (term185 _123419 op m n f)).
Proof. exact (eq_refl (term262 _123419 op f m n)). Qed.
Lemma lem6184940 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6184941 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term265 _123419 op f m n) = (term266 _123419 op m n f).
Proof. exact (MK_COMB (@lem6184940) (@lem6184939 _123419 op m n f)). Qed.
Lemma lem6184942 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : ((term252 _123419 op m n f) = (term264 _123419 op m n f)) = ((term252 _123419 op m n f) = (term264 _123419 op m n f)).
Proof. exact (eq_refl ((term252 _123419 op m n f) = (term264 _123419 op m n f))). Qed.
Lemma lem6184943 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : ((term262 _123419 op f m n) = ((term252 _123419 op m n f) = (term264 _123419 op m n f))) = (((term252 _123419 op m n f) = (term185 _123419 op m n f)) = ((term252 _123419 op m n f) = (term264 _123419 op m n f))).
Proof. exact (MK_COMB (@lem6184941 _123419 op m n f) (@lem6184942 _123419 op m n f)). Qed.
Lemma lem6184944 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : ((term262 _123419 op f m n) = (term263 _123419 op m n f)) = (((term252 _123419 op m n f) = (term185 _123419 op m n f)) = ((term252 _123419 op m n f) = (term264 _123419 op m n f))).
Proof. exact (TRANS (@lem6184938 _123419 op m n f) (@lem6184943 _123419 op m n f)). Qed.
Lemma lem6184945 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (m : nat) (n : nat) (h1 : term245 m n) : ((term252 _123419 op m n f) = (term185 _123419 op m n f)) = ((term252 _123419 op m n f) = (term264 _123419 op m n f)).
Proof. exact (EQ_MP (@lem6184944 _123419 op m n f) (@lem6184935 _123419 op f m n h1)). Qed.
Lemma lem6184946 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (m : nat) (n : nat) (h1 : term245 m n) : ((term252 _123419 op m n f) = (term264 _123419 op m n f)) = ((term252 _123419 op m n f) = (term185 _123419 op m n f)).
Proof. exact (SYM (@lem6184945 _123419 op f m n h1)). Qed.
Lemma lem6184947 (m : nat) (n : nat) (h1 : term267 m n) : term267 m n.
Proof. exact (h1). Qed.
Lemma lem6184948 (m : nat) (n : nat) : term268 m n.
Proof. exact (@lem82 (term245 m n)). Qed.
Lemma lem6184949 (m : nat) (n : nat) (h1 : term267 m n) : (term245 m n) = False.
Proof. exact (@lem6184948 m n (@lem6184947 m n h1)). Qed.
Lemma lem6184950 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term269 _123419 op m n f) = (term269 _123419 op m n f).
Proof. exact (eq_refl (term269 _123419 op m n f)). Qed.
Lemma lem6184951 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (m : nat) (n : nat) (h1 : term267 m n) : (term270 _123419 op f m n) = (term271 _123419 op m n f).
Proof. exact (MK_COMB (@lem6184950 _123419 op m n f) (@lem6184949 m n h1)). Qed.
Lemma lem6184952 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term271 _123419 op m n f) = ((term247 _123419 op m n f) = (term272 _123419 op m n f)).
Proof. exact (eq_refl (term271 _123419 op m n f)). Qed.
Lemma lem6184953 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (m : nat) (n : nat) : (term273 _123419 op f m n) = (term273 _123419 op f m n).
Proof. exact (eq_refl (term273 _123419 op f m n)). Qed.
Lemma lem6184954 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : ((term270 _123419 op f m n) = (term271 _123419 op m n f)) = ((term270 _123419 op f m n) = ((term247 _123419 op m n f) = (term272 _123419 op m n f))).
Proof. exact (MK_COMB (@lem6184953 _123419 op f m n) (@lem6184952 _123419 op m n f)). Qed.
Lemma lem6184955 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term270 _123419 op f m n) = ((term247 _123419 op m n f) = (term185 _123419 op m n f)).
Proof. exact (eq_refl (term270 _123419 op f m n)). Qed.
Lemma lem6184956 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6184957 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term273 _123419 op f m n) = (term274 _123419 op m n f).
Proof. exact (MK_COMB (@lem6184956) (@lem6184955 _123419 op m n f)). Qed.
Lemma lem6184958 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : ((term247 _123419 op m n f) = (term272 _123419 op m n f)) = ((term247 _123419 op m n f) = (term272 _123419 op m n f)).
Proof. exact (eq_refl ((term247 _123419 op m n f) = (term272 _123419 op m n f))). Qed.
Lemma lem6184959 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : ((term270 _123419 op f m n) = ((term247 _123419 op m n f) = (term272 _123419 op m n f))) = (((term247 _123419 op m n f) = (term185 _123419 op m n f)) = ((term247 _123419 op m n f) = (term272 _123419 op m n f))).
Proof. exact (MK_COMB (@lem6184957 _123419 op m n f) (@lem6184958 _123419 op m n f)). Qed.
Lemma lem6184960 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : ((term270 _123419 op f m n) = (term271 _123419 op m n f)) = (((term247 _123419 op m n f) = (term185 _123419 op m n f)) = ((term247 _123419 op m n f) = (term272 _123419 op m n f))).
Proof. exact (TRANS (@lem6184954 _123419 op m n f) (@lem6184959 _123419 op m n f)). Qed.
Lemma lem6184961 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (m : nat) (n : nat) (h1 : term267 m n) : ((term247 _123419 op m n f) = (term185 _123419 op m n f)) = ((term247 _123419 op m n f) = (term272 _123419 op m n f)).
Proof. exact (EQ_MP (@lem6184960 _123419 op m n f) (@lem6184951 _123419 op f m n h1)). Qed.
Lemma lem6184962 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (m : nat) (n : nat) (h1 : term267 m n) : ((term247 _123419 op m n f) = (term272 _123419 op m n f)) = ((term247 _123419 op m n f) = (term185 _123419 op m n f)).
Proof. exact (SYM (@lem6184961 _123419 op f m n h1)). Qed.
Lemma lem6184963 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = ((@FINITE _92140 (@EMPTY _92140)) = True).
Proof. exact (@lem7 (@FINITE _92140 (@EMPTY _92140))). Qed.
Lemma lem6184982 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term275 _120477 _120519 _120521 op.
Proof. exact (@lem5753565 _120477 _120519 _120521 op). Qed.
Lemma lem6184983 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term275 _120477 _120519 _120521 op) = (term276 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term275 _120477 _120519 _120521 op)). Qed.
Lemma lem6184984 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term276 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem6184983 _120477 _120519 _120521 op) (@lem6184982 _120477 _120519 _120521 op)). Qed.
Lemma lem6184985 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (h1). Qed.
Lemma lem6184986 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term277 _120477 _120519 _120521 op.
Proof. exact (@lem6184984 _120477 _120519 _120521 op (@lem6184985 _120519 op h1)). Qed.
Lemma lem6184987 {_120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term278 _120519 _120521 op.
Proof. exact (proj2 (@lem6184986 Prop _120519 _120521 op h1)). Qed.
Lemma lem6184988 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term279 _120519 _120521 op f.
Proof. exact (@lem6184987 _120519 _120521 op h1 f). Qed.
Lemma lem6184989 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) : (term279 _120519 _120521 op f) = (term280 _120519 _120521 op f).
Proof. exact (eq_refl (term279 _120519 _120521 op f)). Qed.
Lemma lem6184990 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term280 _120519 _120521 op f.
Proof. exact (EQ_MP (@lem6184989 _120519 _120521 op f) (@lem6184988 _120519 _120521 f op h1)). Qed.
Lemma lem6184991 {_120519 _120521 : Type'} (f : _120521 -> _120519) (x : _120521) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term281 _120519 _120521 op f x.
Proof. exact (@lem6184990 _120519 _120521 f op h1 x). Qed.
Lemma lem6184992 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) : (term281 _120519 _120521 op f x) = (term282 _120519 _120521 x op f).
Proof. exact (eq_refl (term281 _120519 _120521 op f x)). Qed.
Lemma lem6184993 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term282 _120519 _120521 x op f.
Proof. exact (EQ_MP (@lem6184992 _120519 _120521 x op f) (@lem6184991 _120519 _120521 f x op h1)). Qed.
Lemma lem6184994 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term283 _120519 _120521 x op f s.
Proof. exact (@lem6184993 _120519 _120521 x f op h1 s). Qed.
Lemma lem6184995 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term283 _120519 _120521 x op f s) = (term284 _120519 _120521 x op s f).
Proof. exact (eq_refl (term283 _120519 _120521 x op f s)). Qed.
Lemma lem6184996 {_120519 _120521 : Type'} (x : _120521) (s : _120521 -> Prop) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term284 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem6184995 _120519 _120521 x op s f) (@lem6184994 _120519 _120521 x f s op h1)). Qed.
Lemma lem6184997 {_120521 : Type'} (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : @FINITE _120521 s.
Proof. exact (h1). Qed.
Lemma lem6184998 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @FINITE _120521 s) (h2 : @monoidal _120519 op) : (term285 _120519 _120521 op x s f) = (term286 _120519 _120521 x op s f).
Proof. exact (@lem6184996 _120519 _120521 x s f op h2 (@lem6184997 _120521 s h1)). Qed.
Lemma lem6184999 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : term287 _120519 _120521 x op s f.
Proof. exact (fun h0 : @monoidal _120519 op => @lem6184998 _120519 _120521 x f s op h1 h0). Qed.
Lemma lem6185000 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term288 _120519 _120521 x op s f.
Proof. exact (fun h0 : @FINITE _120521 s => @lem6184999 _120519 _120521 x op f s h0). Qed.
Lemma lem6185002 (p : Prop) (q : Prop) (r : Prop) : (term289 p q r) = (term290 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem6185007 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term288 _120519 _120521 x op s f) = (term291 _120519 _120521 x op s f).
Proof. exact (@lem6185002 (@FINITE _120521 s) (@monoidal _120519 op) ((term285 _120519 _120521 op x s f) = (term286 _120519 _120521 x op s f))). Qed.
Lemma lem6185009 {_120477 _120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term292 _120477 _120519 op.
Proof. exact (proj1 (@lem6184986 _120477 _120519 Prop op h1)). Qed.
Lemma lem6185010 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term293 _120477 _120519 op f.
Proof. exact (@lem6185009 _120477 _120519 op h1 f). Qed.
Lemma lem6185011 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : (term293 _120477 _120519 op f) = ((@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op)).
Proof. exact (eq_refl (term293 _120477 _120519 op f)). Qed.
Lemma lem6185012 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : (@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op).
Proof. exact (EQ_MP (@lem6185011 _120477 _120519 f op) (@lem6185010 _120477 _120519 f op h1)). Qed.
Lemma lem6185018 {_123419 : Type'} (op : type1400 _123419) : (@monoidal _123419 op) = ((@monoidal _123419 op) = True).
Proof. exact (@lem7 (@monoidal _123419 op)). Qed.
Lemma lem6185023 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term291 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem6185007 _120519 _120521 x op s f) (@lem6185000 _120519 _120521 x op s f)). Qed.
Lemma lem6185024 {_123419 : Type'} (x : nat) (op : type1400 _123419) (s : nat -> Prop) (f : nat -> _123419) : term294 _123419 x op s f.
Proof. exact (@lem6185023 _123419 nat x op s f). Qed.
Lemma lem6185025 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : term295 _123419 op f.
Proof. exact (@lem6185024 _123419 (NUMERAL 0) op (@EMPTY nat) f). Qed.
Lemma lem6185029 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem6184963 _92140) (@lem3596285 _92140)). Qed.
Lemma lem6185030 : (@FINITE nat (@EMPTY nat)) = True.
Proof. exact (@lem6185029 nat). Qed.
Lemma lem6185031 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6185032 : term296 = (and True).
Proof. exact (MK_COMB (@lem6185031) (@lem6185030)). Qed.
Lemma lem6185034 {_123419 : Type'} (op : type1400 _123419) (h1 : @monoidal _123419 op) : (@monoidal _123419 op) = True.
Proof. exact (EQ_MP (@lem6185018 _123419 op) (@lem6184862 _123419 op h1)). Qed.
Lemma lem6185035 {_123419 : Type'} (op : type1400 _123419) (h1 : @monoidal _123419 op) : (term297 _123419 op) = (True /\ True).
Proof. exact (MK_COMB (@lem6185032) (@lem6185034 _123419 op h1)). Qed.
Lemma lem6185037 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6185038 : (True /\ True) = True.
Proof. exact (@lem6185037 True). Qed.
Lemma lem6185039 {_123419 : Type'} (op : type1400 _123419) (h1 : @monoidal _123419 op) : (term297 _123419 op) = True.
Proof. exact (TRANS (@lem6185035 _123419 op h1) (@lem6185038)). Qed.
Lemma lem6185040 {_123419 : Type'} (op : type1400 _123419) (h1 : @monoidal _123419 op) : True = (term297 _123419 op).
Proof. exact (SYM (@lem6185039 _123419 op h1)). Qed.
Lemma lem6185041 {_123419 : Type'} (op : type1400 _123419) (h1 : @monoidal _123419 op) : term297 _123419 op.
Proof. exact (EQ_MP (@lem6185040 _123419 op h1) (@lem0)). Qed.
Lemma lem6185042 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : (term216 _123419 op f) = (term298 _123419 op f).
Proof. exact (@lem6185025 _123419 op f (@lem6185041 _123419 op h1)). Qed.
Lemma lem6185044 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term299 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6185045 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term300 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6185044 _2963 g t e g' t' e'). Qed.
Lemma lem6185046 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term301 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6185045 _2963 g t e g' t'). Qed.
Lemma lem6185047 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term302 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6185046 _2963 g t e g'). Qed.
Lemma lem6185048 {_123419 : Type'} (g : Prop) (t : _123419) (e : _123419) : term302 _123419 g t e.
Proof. exact (@lem6185047 _123419 g t e). Qed.
Lemma lem6185049 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : term303 _123419 op f.
Proof. exact (@lem6185048 _123419 term304 (@iterate _123419 nat op (@EMPTY nat) f) (term305 _123419 op f)). Qed.
Lemma lem6185050 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (g' : Prop) : term306 _123419 op f g'.
Proof. exact (@lem6185049 _123419 op f g'). Qed.
Lemma lem6185051 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (g' : Prop) : (term306 _123419 op f g') = (term307 _123419 op f g').
Proof. exact (eq_refl (term306 _123419 op f g')). Qed.
Lemma lem6185052 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (g' : Prop) : term307 _123419 op f g'.
Proof. exact (EQ_MP (@lem6185051 _123419 op f g') (@lem6185050 _123419 op f g')). Qed.
Lemma lem6185053 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (g' : Prop) (t' : _123419) : term308 _123419 op f g' t'.
Proof. exact (@lem6185052 _123419 op f g' t'). Qed.
Lemma lem6185054 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (g' : Prop) (t' : _123419) : (term308 _123419 op f g' t') = (term309 _123419 op f g' t').
Proof. exact (eq_refl (term308 _123419 op f g' t')). Qed.
Lemma lem6185055 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (g' : Prop) (t' : _123419) : term309 _123419 op f g' t'.
Proof. exact (EQ_MP (@lem6185054 _123419 op f g' t') (@lem6185053 _123419 op f g' t')). Qed.
Lemma lem6185056 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (g' : Prop) (t' : _123419) (e' : _123419) : term310 _123419 op f g' t' e'.
Proof. exact (@lem6185055 _123419 op f g' t' e'). Qed.
Lemma lem6185057 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (g' : Prop) (t' : _123419) (e' : _123419) : (term310 _123419 op f g' t' e') = (term311 _123419 op f g' t' e').
Proof. exact (eq_refl (term310 _123419 op f g' t' e')). Qed.
Lemma lem6185058 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (g' : Prop) (t' : _123419) (e' : _123419) : term311 _123419 op f g' t' e'.
Proof. exact (EQ_MP (@lem6185057 _123419 op f g' t' e') (@lem6185056 _123419 op f g' t' e')). Qed.
Lemma lem6185059 : term304 = term304.
Proof. exact (eq_refl term304). Qed.
Lemma lem6185060 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (t' : _123419) (e' : _123419) : term312 _123419 op f t' e'.
Proof. exact (@lem6185058 _123419 op f term304 t' e'). Qed.
Lemma lem6185061 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (t' : _123419) (e' : _123419) : term313 _123419 op f t' e'.
Proof. exact (@lem6185060 _123419 op f t' e' (@lem6185059)). Qed.
Lemma lem6185066 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : term314 _120477 _120519 f op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem6185012 _120477 _120519 f op h0). Qed.
Lemma lem6185067 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : term315 _123419 f op.
Proof. exact (@lem6185066 nat _123419 f op). Qed.
Lemma lem6185069 {_123419 : Type'} (op : type1400 _123419) (h1 : @monoidal _123419 op) : (@monoidal _123419 op) = True.
Proof. exact (EQ_MP (@lem6185018 _123419 op) (@lem6184862 _123419 op h1)). Qed.
Lemma lem6185070 {_123419 : Type'} (op : type1400 _123419) (h1 : @monoidal _123419 op) : True = (@monoidal _123419 op).
Proof. exact (SYM (@lem6185069 _123419 op h1)). Qed.
Lemma lem6185071 {_123419 : Type'} (op : type1400 _123419) (h1 : @monoidal _123419 op) : @monoidal _123419 op.
Proof. exact (EQ_MP (@lem6185070 _123419 op h1) (@lem0)). Qed.
Lemma lem6185072 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : (@iterate _123419 nat op (@EMPTY nat) f) = (@neutral _123419 op).
Proof. exact (@lem6185067 _123419 f op (@lem6185071 _123419 op h1)). Qed.
Lemma lem6185073 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : term316 _123419 f op.
Proof. exact (fun h0 : term304 => @lem6185072 _123419 f op h1). Qed.
Lemma lem6185074 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (e' : _123419) : term317 _123419 f op e'.
Proof. exact (@lem6185061 _123419 op f (@neutral _123419 op) e'). Qed.
Lemma lem6185075 {_123419 : Type'} (f : nat -> _123419) (e' : _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : term318 _123419 f op e'.
Proof. exact (@lem6185074 _123419 f op e' (@lem6185073 _123419 f op h1)). Qed.
Lemma lem6185080 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : term314 _120477 _120519 f op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem6185012 _120477 _120519 f op h0). Qed.
Lemma lem6185081 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : term315 _123419 f op.
Proof. exact (@lem6185080 nat _123419 f op). Qed.
Lemma lem6185083 {_123419 : Type'} (op : type1400 _123419) (h1 : @monoidal _123419 op) : (@monoidal _123419 op) = True.
Proof. exact (EQ_MP (@lem6185018 _123419 op) (@lem6184862 _123419 op h1)). Qed.
Lemma lem6185084 {_123419 : Type'} (op : type1400 _123419) (h1 : @monoidal _123419 op) : True = (@monoidal _123419 op).
Proof. exact (SYM (@lem6185083 _123419 op h1)). Qed.
Lemma lem6185085 {_123419 : Type'} (op : type1400 _123419) (h1 : @monoidal _123419 op) : @monoidal _123419 op.
Proof. exact (EQ_MP (@lem6185084 _123419 op h1) (@lem0)). Qed.
Lemma lem6185086 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : (@iterate _123419 nat op (@EMPTY nat) f) = (@neutral _123419 op).
Proof. exact (@lem6185081 _123419 f op (@lem6185085 _123419 op h1)). Qed.
Lemma lem6185087 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : (term319 _123419 op f) = (term319 _123419 op f).
Proof. exact (eq_refl (term319 _123419 op f)). Qed.
Lemma lem6185088 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : (term305 _123419 op f) = (term320 _123419 f op).
Proof. exact (MK_COMB (@lem6185087 _123419 op f) (@lem6185086 _123419 f op h1)). Qed.
Lemma lem6185089 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : term321 _123419 f op.
Proof. exact (fun h0 : term322 => @lem6185088 _123419 f op h1). Qed.
Lemma lem6185090 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : term323 _123419 f op.
Proof. exact (@lem6185075 _123419 f (term320 _123419 f op) op h1). Qed.
Lemma lem6185091 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : (term298 _123419 op f) = (term324 _123419 f op).
Proof. exact (@lem6185090 _123419 f op h1 (@lem6185089 _123419 f op h1)). Qed.
Lemma lem6185125 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : (term216 _123419 op f) = (term324 _123419 f op).
Proof. exact (TRANS (@lem6185042 _123419 f op h1) (@lem6185091 _123419 f op h1)). Qed.
Lemma lem6185126 {_123419 : Type'} : (@eq _123419) = (@eq _123419).
Proof. exact (eq_refl (@eq _123419)). Qed.
Lemma lem6185127 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : (term325 _123419 op f) = (term326 _123419 f op).
Proof. exact (MK_COMB (@lem6185126 _123419) (@lem6185125 _123419 f op h1)). Qed.
Lemma lem6185162 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem6185163 {_123419 : Type'} (t2 : _123419) (t1 : _123419) : (@COND _123419 True t1 t2) = t1.
Proof. exact (@lem6185162 _123419 t2 t1). Qed.
Lemma lem6185164 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : (term228 _123419 f op) = (term327 _123419 f).
Proof. exact (@lem6185163 _123419 (@neutral _123419 op) (term327 _123419 f)). Qed.
Lemma lem6185165 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : ((term216 _123419 op f) = (term228 _123419 f op)) = ((term324 _123419 f op) = (term327 _123419 f)).
Proof. exact (MK_COMB (@lem6185127 _123419 f op h1) (@lem6185164 _123419 op f)). Qed.
Lemma lem6185201 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : ((term324 _123419 f op) = (term327 _123419 f)) = ((term216 _123419 op f) = (term228 _123419 f op)).
Proof. exact (SYM (@lem6185165 _123419 f op h1)). Qed.
Lemma lem6185221 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term275 _120477 _120519 _120521 op.
Proof. exact (@lem5753565 _120477 _120519 _120521 op). Qed.
Lemma lem6185222 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term275 _120477 _120519 _120521 op) = (term276 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term275 _120477 _120519 _120521 op)). Qed.
Lemma lem6185223 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term276 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem6185222 _120477 _120519 _120521 op) (@lem6185221 _120477 _120519 _120521 op)). Qed.
Lemma lem6185224 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (h1). Qed.
Lemma lem6185225 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term277 _120477 _120519 _120521 op.
Proof. exact (@lem6185223 _120477 _120519 _120521 op (@lem6185224 _120519 op h1)). Qed.
Lemma lem6185248 {_120477 _120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term292 _120477 _120519 op.
Proof. exact (proj1 (@lem6185225 _120477 _120519 Prop op h1)). Qed.
Lemma lem6185249 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term293 _120477 _120519 op f.
Proof. exact (@lem6185248 _120477 _120519 op h1 f). Qed.
Lemma lem6185250 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : (term293 _120477 _120519 op f) = ((@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op)).
Proof. exact (eq_refl (term293 _120477 _120519 op f)). Qed.
Lemma lem6185251 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : (@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op).
Proof. exact (EQ_MP (@lem6185250 _120477 _120519 f op) (@lem6185249 _120477 _120519 f op h1)). Qed.
Lemma lem6185257 {_123419 : Type'} (op : type1400 _123419) : (@monoidal _123419 op) = ((@monoidal _123419 op) = True).
Proof. exact (@lem7 (@monoidal _123419 op)). Qed.
Lemma lem6185275 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : term314 _120477 _120519 f op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem6185251 _120477 _120519 f op h0). Qed.
Lemma lem6185276 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : term315 _123419 f op.
Proof. exact (@lem6185275 nat _123419 f op). Qed.
Lemma lem6185278 {_123419 : Type'} (op : type1400 _123419) (h1 : @monoidal _123419 op) : (@monoidal _123419 op) = True.
Proof. exact (EQ_MP (@lem6185257 _123419 op) (@lem6184862 _123419 op h1)). Qed.
Lemma lem6185279 {_123419 : Type'} (op : type1400 _123419) (h1 : @monoidal _123419 op) : True = (@monoidal _123419 op).
Proof. exact (SYM (@lem6185278 _123419 op h1)). Qed.
Lemma lem6185280 {_123419 : Type'} (op : type1400 _123419) (h1 : @monoidal _123419 op) : @monoidal _123419 op.
Proof. exact (EQ_MP (@lem6185279 _123419 op h1) (@lem0)). Qed.
Lemma lem6185281 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : (@iterate _123419 nat op (@EMPTY nat) f) = (@neutral _123419 op).
Proof. exact (@lem6185276 _123419 f op (@lem6185280 _123419 op h1)). Qed.
Lemma lem6185282 {_123419 : Type'} : (@eq _123419) = (@eq _123419).
Proof. exact (eq_refl (@eq _123419)). Qed.
Lemma lem6185283 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : (term328 _123419 op f) = (term329 _123419 op).
Proof. exact (MK_COMB (@lem6185282 _123419) (@lem6185281 _123419 f op h1)). Qed.
Lemma lem6185285 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6185286 {_123419 : Type'} (t1 : _123419) (t2 : _123419) : (@COND _123419 False t1 t2) = t2.
Proof. exact (@lem6185285 _123419 t1 t2). Qed.
Lemma lem6185287 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : (term236 _123419 f op) = (@neutral _123419 op).
Proof. exact (@lem6185286 _123419 (term327 _123419 f) (@neutral _123419 op)). Qed.
Lemma lem6185288 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : ((@iterate _123419 nat op (@EMPTY nat) f) = (term236 _123419 f op)) = ((@neutral _123419 op) = (@neutral _123419 op)).
Proof. exact (MK_COMB (@lem6185283 _123419 f op h1) (@lem6185287 _123419 f op)). Qed.
Lemma lem6185290 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6185291 {_123419 : Type'} (x : _123419) : (x = x) = True.
Proof. exact (@lem6185290 _123419 x). Qed.
Lemma lem6185292 {_123419 : Type'} (op : type1400 _123419) : ((@neutral _123419 op) = (@neutral _123419 op)) = True.
Proof. exact (@lem6185291 _123419 (@neutral _123419 op)). Qed.
Lemma lem6185293 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : ((@iterate _123419 nat op (@EMPTY nat) f) = (term236 _123419 f op)) = True.
Proof. exact (TRANS (@lem6185288 _123419 f op h1) (@lem6185292 _123419 op)). Qed.
Lemma lem6185294 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : True = ((@iterate _123419 nat op (@EMPTY nat) f) = (term236 _123419 f op)).
Proof. exact (SYM (@lem6185293 _123419 f op h1)). Qed.
Lemma lem6185295 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : (@iterate _123419 nat op (@EMPTY nat) f) = (term236 _123419 f op).
Proof. exact (EQ_MP (@lem6185294 _123419 f op h1) (@lem0)). Qed.
Lemma lem6185298 (m : nat) : term330 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem6185299 (m : nat) : (term330 m) = (term331 m).
Proof. exact (eq_refl (term330 m)). Qed.
Lemma lem6185300 (m : nat) : term331 m.
Proof. exact (EQ_MP (@lem6185299 m) (@lem6185298 m)). Qed.
Lemma lem6185301 (m : nat) (n : nat) : term332 m n.
Proof. exact (@lem6185300 m n). Qed.
Lemma lem6185302 (m : nat) (n : nat) : (term332 m n) = (term333 m n).
Proof. exact (eq_refl (term332 m n)). Qed.
Lemma lem6185303 (m : nat) (n : nat) : term333 m n.
Proof. exact (EQ_MP (@lem6185302 m n) (@lem6185301 m n)). Qed.
Lemma lem6185304 (m : nat) (n : nat) (p : nat) : term334 m n p.
Proof. exact (@lem6185303 m n p). Qed.
Lemma lem6185305 (m : nat) (p : nat) (n : nat) : (term334 m n p) = ((term335 p m n) = (term336 m p n)).
Proof. exact (eq_refl (term334 m n p)). Qed.
Lemma lem6185307 (m : nat) : term337 m.
Proof. exact (@lem5329299 m). Qed.
Lemma lem6185308 (m : nat) : (term337 m) = (term338 m).
Proof. exact (eq_refl (term337 m)). Qed.
Lemma lem6185309 (m : nat) : term338 m.
Proof. exact (EQ_MP (@lem6185308 m) (@lem6185307 m)). Qed.
Lemma lem6185310 (m : nat) (n : nat) : term339 m n.
Proof. exact (@lem6185309 m n). Qed.
Lemma lem6185311 (m : nat) (n : nat) : (term339 m n) = (term340 m n).
Proof. exact (eq_refl (term339 m n)). Qed.
Lemma lem6185312 (m : nat) (n : nat) : term340 m n.
Proof. exact (EQ_MP (@lem6185311 m n) (@lem6185310 m n)). Qed.
Lemma lem6185313 (m : nat) (n : nat) : (term340 m n) = ((term340 m n) = True).
Proof. exact (@lem7 (term340 m n)). Qed.
Lemma lem6185315 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term275 _120477 _120519 _120521 op.
Proof. exact (@lem5753565 _120477 _120519 _120521 op). Qed.
Lemma lem6185316 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term275 _120477 _120519 _120521 op) = (term276 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term275 _120477 _120519 _120521 op)). Qed.
Lemma lem6185317 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term276 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem6185316 _120477 _120519 _120521 op) (@lem6185315 _120477 _120519 _120521 op)). Qed.
Lemma lem6185318 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (h1). Qed.
Lemma lem6185319 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term277 _120477 _120519 _120521 op.
Proof. exact (@lem6185317 _120477 _120519 _120521 op (@lem6185318 _120519 op h1)). Qed.
Lemma lem6185320 {_120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term278 _120519 _120521 op.
Proof. exact (proj2 (@lem6185319 Prop _120519 _120521 op h1)). Qed.
Lemma lem6185321 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term279 _120519 _120521 op f.
Proof. exact (@lem6185320 _120519 _120521 op h1 f). Qed.
Lemma lem6185322 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) : (term279 _120519 _120521 op f) = (term280 _120519 _120521 op f).
Proof. exact (eq_refl (term279 _120519 _120521 op f)). Qed.
Lemma lem6185323 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term280 _120519 _120521 op f.
Proof. exact (EQ_MP (@lem6185322 _120519 _120521 op f) (@lem6185321 _120519 _120521 f op h1)). Qed.
Lemma lem6185324 {_120519 _120521 : Type'} (f : _120521 -> _120519) (x : _120521) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term281 _120519 _120521 op f x.
Proof. exact (@lem6185323 _120519 _120521 f op h1 x). Qed.
Lemma lem6185325 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) : (term281 _120519 _120521 op f x) = (term282 _120519 _120521 x op f).
Proof. exact (eq_refl (term281 _120519 _120521 op f x)). Qed.
Lemma lem6185326 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term282 _120519 _120521 x op f.
Proof. exact (EQ_MP (@lem6185325 _120519 _120521 x op f) (@lem6185324 _120519 _120521 f x op h1)). Qed.
Lemma lem6185327 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term283 _120519 _120521 x op f s.
Proof. exact (@lem6185326 _120519 _120521 x f op h1 s). Qed.
Lemma lem6185328 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term283 _120519 _120521 x op f s) = (term284 _120519 _120521 x op s f).
Proof. exact (eq_refl (term283 _120519 _120521 x op f s)). Qed.
Lemma lem6185329 {_120519 _120521 : Type'} (x : _120521) (s : _120521 -> Prop) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term284 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem6185328 _120519 _120521 x op s f) (@lem6185327 _120519 _120521 x f s op h1)). Qed.
Lemma lem6185330 {_120521 : Type'} (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : @FINITE _120521 s.
Proof. exact (h1). Qed.
Lemma lem6185331 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @FINITE _120521 s) (h2 : @monoidal _120519 op) : (term285 _120519 _120521 op x s f) = (term286 _120519 _120521 x op s f).
Proof. exact (@lem6185329 _120519 _120521 x s f op h2 (@lem6185330 _120521 s h1)). Qed.
Lemma lem6185332 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : term287 _120519 _120521 x op s f.
Proof. exact (fun h0 : @monoidal _120519 op => @lem6185331 _120519 _120521 x f s op h1 h0). Qed.
Lemma lem6185333 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term288 _120519 _120521 x op s f.
Proof. exact (fun h0 : @FINITE _120521 s => @lem6185332 _120519 _120521 x op f s h0). Qed.
Lemma lem6185335 (p : Prop) (q : Prop) (r : Prop) : (term289 p q r) = (term290 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem6185340 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term288 _120519 _120521 x op s f) = (term291 _120519 _120521 x op s f).
Proof. exact (@lem6185335 (@FINITE _120521 s) (@monoidal _120519 op) ((term285 _120519 _120521 op x s f) = (term286 _120519 _120521 x op s f))). Qed.
Lemma lem6185351 {_123419 : Type'} (op : type1400 _123419) : (@monoidal _123419 op) = ((@monoidal _123419 op) = True).
Proof. exact (@lem7 (@monoidal _123419 op)). Qed.
Lemma lem6185353 (m : nat) (n : nat) : (term245 m n) = ((term245 m n) = True).
Proof. exact (@lem7 (term245 m n)). Qed.
Lemma lem6185358 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term291 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem6185340 _120519 _120521 x op s f) (@lem6185333 _120519 _120521 x op s f)). Qed.
Lemma lem6185359 {_123419 : Type'} (x : nat) (op : type1400 _123419) (s : nat -> Prop) (f : nat -> _123419) : term294 _123419 x op s f.
Proof. exact (@lem6185358 _123419 nat x op s f). Qed.
Lemma lem6185360 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : term341 _123419 op m n f.
Proof. exact (@lem6185359 _123419 (S n) op (dotdot m n) f). Qed.
Lemma lem6185364 (m : nat) (n : nat) : (term340 m n) = True.
Proof. exact (EQ_MP (@lem6185313 m n) (@lem6185312 m n)). Qed.
Lemma lem6185365 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6185366 (m : nat) (n : nat) : (term342 m n) = (and True).
Proof. exact (MK_COMB (@lem6185365) (@lem6185364 m n)). Qed.
Lemma lem6185368 {_123419 : Type'} (op : type1400 _123419) (h1 : @monoidal _123419 op) : (@monoidal _123419 op) = True.
Proof. exact (EQ_MP (@lem6185351 _123419 op) (@lem6184862 _123419 op h1)). Qed.
Lemma lem6185369 {_123419 : Type'} (m : nat) (n : nat) (op : type1400 _123419) (h1 : @monoidal _123419 op) : (term343 _123419 m n op) = (True /\ True).
Proof. exact (MK_COMB (@lem6185366 m n) (@lem6185368 _123419 op h1)). Qed.
Lemma lem6185371 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6185372 : (True /\ True) = True.
Proof. exact (@lem6185371 True). Qed.
Lemma lem6185373 {_123419 : Type'} (m : nat) (n : nat) (op : type1400 _123419) (h1 : @monoidal _123419 op) : (term343 _123419 m n op) = True.
Proof. exact (TRANS (@lem6185369 _123419 m n op h1) (@lem6185372)). Qed.
Lemma lem6185374 {_123419 : Type'} (m : nat) (n : nat) (op : type1400 _123419) (h1 : @monoidal _123419 op) : True = (term343 _123419 m n op).
Proof. exact (SYM (@lem6185373 _123419 m n op h1)). Qed.
Lemma lem6185375 {_123419 : Type'} (m : nat) (n : nat) (op : type1400 _123419) (h1 : @monoidal _123419 op) : term343 _123419 m n op.
Proof. exact (EQ_MP (@lem6185374 _123419 m n op h1) (@lem0)). Qed.
Lemma lem6185376 {_123419 : Type'} (m : nat) (n : nat) (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : (term252 _123419 op m n f) = (term344 _123419 op m n f).
Proof. exact (@lem6185360 _123419 op m n f (@lem6185375 _123419 m n op h1)). Qed.
Lemma lem6185378 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term299 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6185379 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term300 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6185378 _2963 g t e g' t' e'). Qed.
Lemma lem6185380 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term301 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6185379 _2963 g t e g' t'). Qed.
Lemma lem6185381 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term302 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6185380 _2963 g t e g'). Qed.
Lemma lem6185382 {_123419 : Type'} (g : Prop) (t : _123419) (e : _123419) : term302 _123419 g t e.
Proof. exact (@lem6185381 _123419 g t e). Qed.
Lemma lem6185383 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : term345 _123419 op m n f.
Proof. exact (@lem6185382 _123419 (term346 m n) (term247 _123419 op m n f) (term347 _123419 op m n f)). Qed.
Lemma lem6185384 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) (g' : Prop) : term348 _123419 op m n f g'.
Proof. exact (@lem6185383 _123419 op m n f g'). Qed.
Lemma lem6185385 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) (g' : Prop) : (term348 _123419 op m n f g') = (term349 _123419 op m n f g').
Proof. exact (eq_refl (term348 _123419 op m n f g')). Qed.
Lemma lem6185386 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) (g' : Prop) : term349 _123419 op m n f g'.
Proof. exact (EQ_MP (@lem6185385 _123419 op m n f g') (@lem6185384 _123419 op m n f g')). Qed.
Lemma lem6185387 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) (g' : Prop) (t' : _123419) : term350 _123419 op m n f g' t'.
Proof. exact (@lem6185386 _123419 op m n f g' t'). Qed.
Lemma lem6185388 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) (g' : Prop) (t' : _123419) : (term350 _123419 op m n f g' t') = (term351 _123419 op m n f g' t').
Proof. exact (eq_refl (term350 _123419 op m n f g' t')). Qed.
Lemma lem6185389 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) (g' : Prop) (t' : _123419) : term351 _123419 op m n f g' t'.
Proof. exact (EQ_MP (@lem6185388 _123419 op m n f g' t') (@lem6185387 _123419 op m n f g' t')). Qed.
Lemma lem6185390 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) (g' : Prop) (t' : _123419) (e' : _123419) : term352 _123419 op m n f g' t' e'.
Proof. exact (@lem6185389 _123419 op m n f g' t' e'). Qed.
Lemma lem6185391 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) (g' : Prop) (t' : _123419) (e' : _123419) : (term352 _123419 op m n f g' t' e') = (term353 _123419 op m n f g' t' e').
Proof. exact (eq_refl (term352 _123419 op m n f g' t' e')). Qed.
Lemma lem6185392 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) (g' : Prop) (t' : _123419) (e' : _123419) : term353 _123419 op m n f g' t' e'.
Proof. exact (EQ_MP (@lem6185391 _123419 op m n f g' t' e') (@lem6185390 _123419 op m n f g' t' e')). Qed.
Lemma lem6185394 (m : nat) (p : nat) (n : nat) : (term335 p m n) = (term336 m p n).
Proof. exact (EQ_MP (@lem6185305 m p n) (@lem6185304 m n p)). Qed.
Lemma lem6185395 (m : nat) (n : nat) : (term346 m n) = (term354 m n).
Proof. exact (@lem6185394 m (S n) n). Qed.
Lemma lem6185399 (m : nat) (n : nat) (h1 : term245 m n) : (term245 m n) = True.
Proof. exact (EQ_MP (@lem6185353 m n) (@lem6184931 m n h1)). Qed.
Lemma lem6185400 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6185401 (m : nat) (n : nat) (h1 : term245 m n) : (term355 m n) = (and True).
Proof. exact (MK_COMB (@lem6185400) (@lem6185399 m n h1)). Qed.
Lemma lem6185402 (n : nat) : (term3 n) = (term3 n).
Proof. exact (eq_refl (term3 n)). Qed.
Lemma lem6185403 (m : nat) (n : nat) (h1 : term245 m n) : (term354 m n) = (term356 n).
Proof. exact (MK_COMB (@lem6185401 m n h1) (@lem6185402 n)). Qed.
Lemma lem6185405 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6185406 (n : nat) : (term356 n) = (term3 n).
Proof. exact (@lem6185405 (term3 n)). Qed.
Lemma lem6185407 (m : nat) (n : nat) (h1 : term245 m n) : (term354 m n) = (term3 n).
Proof. exact (TRANS (@lem6185403 m n h1) (@lem6185406 n)). Qed.
Lemma lem6185408 (m : nat) (n : nat) (h1 : term245 m n) : (term346 m n) = (term3 n).
Proof. exact (TRANS (@lem6185395 m n) (@lem6185407 m n h1)). Qed.
Lemma lem6185409 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) (t' : _123419) (e' : _123419) : term357 _123419 op m f n t' e'.
Proof. exact (@lem6185392 _123419 op m n f (term3 n) t' e'). Qed.
Lemma lem6185410 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (t' : _123419) (e' : _123419) (m : nat) (n : nat) (h1 : term245 m n) : term358 _123419 op m f n t' e'.
Proof. exact (@lem6185409 _123419 op m f n t' e' (@lem6185408 m n h1)). Qed.
Lemma lem6185414 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term247 _123419 op m n f) = (term247 _123419 op m n f).
Proof. exact (eq_refl (term247 _123419 op m n f)). Qed.
Lemma lem6185415 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : term359 _123419 op m n f.
Proof. exact (fun h0 : term3 n => @lem6185414 _123419 op m n f). Qed.
Lemma lem6185416 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (e' : _123419) (m : nat) (n : nat) (h1 : term245 m n) : term360 _123419 op m n f e'.
Proof. exact (@lem6185410 _123419 op f (term247 _123419 op m n f) e' m n h1). Qed.
Lemma lem6185417 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (e' : _123419) (m : nat) (n : nat) (h1 : term245 m n) : term361 _123419 op m n f e'.
Proof. exact (@lem6185416 _123419 op f e' m n h1 (@lem6185415 _123419 op m n f)). Qed.
Lemma lem6185421 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term347 _123419 op m n f) = (term347 _123419 op m n f).
Proof. exact (eq_refl (term347 _123419 op m n f)). Qed.
Lemma lem6185422 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : term362 _123419 op m n f.
Proof. exact (fun h0 : term5 n => @lem6185421 _123419 op m n f). Qed.
Lemma lem6185423 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (m : nat) (n : nat) (h1 : term245 m n) : term363 _123419 op m n f.
Proof. exact (@lem6185417 _123419 op f (term347 _123419 op m n f) m n h1). Qed.
Lemma lem6185424 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (m : nat) (n : nat) (h1 : term245 m n) : (term344 _123419 op m n f) = (term364 _123419 op m n f).
Proof. exact (@lem6185423 _123419 op f m n h1 (@lem6185422 _123419 op m n f)). Qed.
Lemma lem6185458 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (n : nat) (h1 : @monoidal _123419 op) (h2 : term245 m n) : (term252 _123419 op m n f) = (term364 _123419 op m n f).
Proof. exact (TRANS (@lem6185376 _123419 m n f op h1) (@lem6185424 _123419 op f m n h2)). Qed.
Lemma lem6185459 {_123419 : Type'} : (@eq _123419) = (@eq _123419).
Proof. exact (eq_refl (@eq _123419)). Qed.
Lemma lem6185460 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (n : nat) (h1 : @monoidal _123419 op) (h2 : term245 m n) : (term365 _123419 op m n f) = (term366 _123419 op m n f).
Proof. exact (MK_COMB (@lem6185459 _123419) (@lem6185458 _123419 f op m n h1 h2)). Qed.
Lemma lem6185495 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem6185496 {_123419 : Type'} (t2 : _123419) (t1 : _123419) : (@COND _123419 True t1 t2) = t1.
Proof. exact (@lem6185495 _123419 t2 t1). Qed.
Lemma lem6185497 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : (term264 _123419 op m n f) = (term367 _123419 op m f n).
Proof. exact (@lem6185496 _123419 (term247 _123419 op m n f) (term367 _123419 op m f n)). Qed.
Lemma lem6185498 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (n : nat) (h1 : @monoidal _123419 op) (h2 : term245 m n) : ((term252 _123419 op m n f) = (term264 _123419 op m n f)) = ((term364 _123419 op m n f) = (term367 _123419 op m f n)).
Proof. exact (MK_COMB (@lem6185460 _123419 f op m n h1 h2) (@lem6185497 _123419 op m f n)). Qed.
Lemma lem6185534 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (n : nat) (h1 : @monoidal _123419 op) (h2 : term245 m n) : ((term364 _123419 op m n f) = (term367 _123419 op m f n)) = ((term252 _123419 op m n f) = (term264 _123419 op m n f)).
Proof. exact (SYM (@lem6185498 _123419 f op m n h1 h2)). Qed.
Lemma lem6185597 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6185598 {_123419 : Type'} (t1 : _123419) (t2 : _123419) : (@COND _123419 False t1 t2) = t2.
Proof. exact (@lem6185597 _123419 t1 t2). Qed.
Lemma lem6185599 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term272 _123419 op m n f) = (term247 _123419 op m n f).
Proof. exact (@lem6185598 _123419 (term367 _123419 op m f n) (term247 _123419 op m n f)). Qed.
Lemma lem6185600 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term368 _123419 op m n f) = (term368 _123419 op m n f).
Proof. exact (eq_refl (term368 _123419 op m n f)). Qed.
Lemma lem6185601 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : ((term247 _123419 op m n f) = (term272 _123419 op m n f)) = ((term247 _123419 op m n f) = (term247 _123419 op m n f)).
Proof. exact (MK_COMB (@lem6185600 _123419 op m n f) (@lem6185599 _123419 op m n f)). Qed.
Lemma lem6185603 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6185604 {_123419 : Type'} (x : _123419) : (x = x) = True.
Proof. exact (@lem6185603 _123419 x). Qed.
Lemma lem6185605 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : ((term247 _123419 op m n f) = (term247 _123419 op m n f)) = True.
Proof. exact (@lem6185604 _123419 (term247 _123419 op m n f)). Qed.
Lemma lem6185606 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : ((term247 _123419 op m n f) = (term272 _123419 op m n f)) = True.
Proof. exact (TRANS (@lem6185601 _123419 op m n f) (@lem6185605 _123419 op m n f)). Qed.
Lemma lem6185607 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : True = ((term247 _123419 op m n f) = (term272 _123419 op m n f)).
Proof. exact (SYM (@lem6185606 _123419 op m n f)). Qed.
Lemma lem6185608 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term247 _123419 op m n f) = (term272 _123419 op m n f).
Proof. exact (EQ_MP (@lem6185607 _123419 op m n f) (@lem0)). Qed.
Lemma lem6185612 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem6184753 A x (@lem6184752 A x)). Qed.
Lemma lem6185613 (x : nat) : (@IN nat x (@EMPTY nat)) = False.
Proof. exact (@lem6185612 nat x). Qed.
Lemma lem6185614 : term304 = False.
Proof. exact (@lem6185613 (NUMERAL 0)). Qed.
Lemma lem6185615 {_123419 : Type'} : (@COND _123419) = (@COND _123419).
Proof. exact (eq_refl (@COND _123419)). Qed.
Lemma lem6185616 {_123419 : Type'} : (term369 _123419) = (@COND _123419 False).
Proof. exact (MK_COMB (@lem6185615 _123419) (@lem6185614)). Qed.
Lemma lem6185617 {_123419 : Type'} (op : type1400 _123419) : (@neutral _123419 op) = (@neutral _123419 op).
Proof. exact (eq_refl (@neutral _123419 op)). Qed.
Lemma lem6185618 {_123419 : Type'} (op : type1400 _123419) : (term370 _123419 op) = (term371 _123419 op).
Proof. exact (MK_COMB (@lem6185616 _123419) (@lem6185617 _123419 op)). Qed.
Lemma lem6185619 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : (term320 _123419 f op) = (term320 _123419 f op).
Proof. exact (eq_refl (term320 _123419 f op)). Qed.
Lemma lem6185620 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : (term324 _123419 f op) = (term372 _123419 f op).
Proof. exact (MK_COMB (@lem6185618 _123419 op) (@lem6185619 _123419 f op)). Qed.
Lemma lem6185622 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6185623 {_123419 : Type'} (t1 : _123419) (t2 : _123419) : (@COND _123419 False t1 t2) = t2.
Proof. exact (@lem6185622 _123419 t1 t2). Qed.
Lemma lem6185624 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : (term372 _123419 f op) = (term320 _123419 f op).
Proof. exact (@lem6185623 _123419 (@neutral _123419 op) (term320 _123419 f op)). Qed.
Lemma lem6185625 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : (term324 _123419 f op) = (term320 _123419 f op).
Proof. exact (TRANS (@lem6185620 _123419 f op) (@lem6185624 _123419 f op)). Qed.
Lemma lem6185626 {_123419 : Type'} : (@eq _123419) = (@eq _123419).
Proof. exact (eq_refl (@eq _123419)). Qed.
Lemma lem6185627 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : (term326 _123419 f op) = (term373 _123419 f op).
Proof. exact (MK_COMB (@lem6185626 _123419) (@lem6185625 _123419 f op)). Qed.
Lemma lem6185628 {_123419 : Type'} (f : nat -> _123419) : (term327 _123419 f) = (term327 _123419 f).
Proof. exact (eq_refl (term327 _123419 f)). Qed.
Lemma lem6185629 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : ((term324 _123419 f op) = (term327 _123419 f)) = ((term320 _123419 f op) = (term327 _123419 f)).
Proof. exact (MK_COMB (@lem6185627 _123419 f op) (@lem6185628 _123419 f)). Qed.
Lemma lem6185632 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : ((term320 _123419 f op) = (term327 _123419 f)) = ((term324 _123419 f op) = (term327 _123419 f)).
Proof. exact (SYM (@lem6185629 _123419 op f)). Qed.
Lemma lem6185636 (n : nat) : (term3 n) = False.
Proof. exact (@lem6184755 n (@lem6184749 n)). Qed.
Lemma lem6185637 {_123419 : Type'} : (@COND _123419) = (@COND _123419).
Proof. exact (eq_refl (@COND _123419)). Qed.
Lemma lem6185638 {_123419 : Type'} (n : nat) : (term374 _123419 n) = (@COND _123419 False).
Proof. exact (MK_COMB (@lem6185637 _123419) (@lem6185636 n)). Qed.
Lemma lem6185639 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term247 _123419 op m n f) = (term247 _123419 op m n f).
Proof. exact (eq_refl (term247 _123419 op m n f)). Qed.
Lemma lem6185640 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term375 _123419 op m n f) = (term376 _123419 op m n f).
Proof. exact (MK_COMB (@lem6185638 _123419 n) (@lem6185639 _123419 op m n f)). Qed.
Lemma lem6185641 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term347 _123419 op m n f) = (term347 _123419 op m n f).
Proof. exact (eq_refl (term347 _123419 op m n f)). Qed.
Lemma lem6185642 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term364 _123419 op m n f) = (term377 _123419 op m n f).
Proof. exact (MK_COMB (@lem6185640 _123419 op m n f) (@lem6185641 _123419 op m n f)). Qed.
Lemma lem6185644 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6185645 {_123419 : Type'} (t1 : _123419) (t2 : _123419) : (@COND _123419 False t1 t2) = t2.
Proof. exact (@lem6185644 _123419 t1 t2). Qed.
Lemma lem6185646 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term377 _123419 op m n f) = (term347 _123419 op m n f).
Proof. exact (@lem6185645 _123419 (term247 _123419 op m n f) (term347 _123419 op m n f)). Qed.
Lemma lem6185647 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term364 _123419 op m n f) = (term347 _123419 op m n f).
Proof. exact (TRANS (@lem6185642 _123419 op m n f) (@lem6185646 _123419 op m n f)). Qed.
Lemma lem6185648 {_123419 : Type'} : (@eq _123419) = (@eq _123419).
Proof. exact (eq_refl (@eq _123419)). Qed.
Lemma lem6185649 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term366 _123419 op m n f) = (term378 _123419 op m n f).
Proof. exact (MK_COMB (@lem6185648 _123419) (@lem6185647 _123419 op m n f)). Qed.
Lemma lem6185650 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : (term367 _123419 op m f n) = (term367 _123419 op m f n).
Proof. exact (eq_refl (term367 _123419 op m f n)). Qed.
Lemma lem6185651 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : ((term364 _123419 op m n f) = (term367 _123419 op m f n)) = ((term347 _123419 op m n f) = (term367 _123419 op m f n)).
Proof. exact (MK_COMB (@lem6185649 _123419 op m n f) (@lem6185650 _123419 op m f n)). Qed.
Lemma lem6185654 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : ((term347 _123419 op m n f) = (term367 _123419 op m f n)) = ((term364 _123419 op m n f) = (term367 _123419 op m f n)).
Proof. exact (SYM (@lem6185651 _123419 op m f n)). Qed.
Lemma lem6185656 (p : Prop) : p = (term379 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6185657 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : ((term320 _123419 f op) = (term327 _123419 f)) = (term380 _123419 op f).
Proof. exact (@lem6185656 ((term320 _123419 f op) = (term327 _123419 f))). Qed.
Lemma lem6185658 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : (term380 _123419 op f) = ((term320 _123419 f op) = (term327 _123419 f)).
Proof. exact (SYM (@lem6185657 _123419 op f)). Qed.
Lemma lem6185659 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (h1 : term381 _123419 op f) : term381 _123419 op f.
Proof. exact (h1). Qed.
Lemma lem6185660 {_123419 : Type'} : term382 _123419.
Proof. exact (@lem5712802 _123419). Qed.
Lemma lem6185661 : term383.
Proof. exact (@lem5712802 nat). Qed.
Lemma lem6185666 {_123419 : Type'} (m : nat) (op : type1400 _123419) (f : nat -> _123419) (h1 : term384 _123419 m op f) : term384 _123419 m op f.
Proof. exact (h1). Qed.
Lemma lem6185667 {_123419 : Type'} (m : nat) (op : type1400 _123419) (f : nat -> _123419) : term385 _123419 m op f.
Proof. exact (fun h0 : term384 _123419 m op f => @lem6185666 _123419 m op f h0). Qed.
Lemma lem6185668 {_123419 : Type'} (m : nat) (op : type1400 _123419) (f : nat -> _123419) (h1 : term385 _123419 m op f) : term385 _123419 m op f.
Proof. exact (h1). Qed.
Lemma lem6185669 {_123419 : Type'} (m : nat) (op : type1400 _123419) (f : nat -> _123419) (h1 : term384 _123419 m op f) : term384 _123419 m op f.
Proof. exact (h1). Qed.
Lemma lem6185670 {_123419 : Type'} (m : nat) (op : type1400 _123419) (f : nat -> _123419) (h1 : term384 _123419 m op f) (h2 : term385 _123419 m op f) : term384 _123419 m op f.
Proof. exact (@lem6185668 _123419 m op f h2 (@lem6185669 _123419 m op f h1)). Qed.
Lemma lem6185671 {_123419 : Type'} (m : nat) (op : type1400 _123419) (f : nat -> _123419) (h1 : term384 _123419 m op f) : term386 _123419 m op f.
Proof. exact (fun h0 : term385 _123419 m op f => @lem6185670 _123419 m op f h1 h0). Qed.
Lemma lem6185672 {_123419 : Type'} (m : nat) (op : type1400 _123419) (f : nat -> _123419) (h1 : term385 _123419 m op f) : term385 _123419 m op f.
Proof. exact (h1). Qed.
Lemma lem6185673 {_123419 : Type'} (m : nat) (op : type1400 _123419) (f : nat -> _123419) (h1 : term384 _123419 m op f) (h2 : term385 _123419 m op f) : term384 _123419 m op f.
Proof. exact (@lem6185671 _123419 m op f h1 (@lem6185672 _123419 m op f h2)). Qed.
Lemma lem6185674 {_123419 : Type'} (m : nat) (op : type1400 _123419) (f : nat -> _123419) (h1 : term385 _123419 m op f) : term385 _123419 m op f.
Proof. exact (fun h0 : term384 _123419 m op f => @lem6185673 _123419 m op f h0 h1). Qed.
Lemma lem6185675 {_123419 : Type'} (m : nat) (op : type1400 _123419) (f : nat -> _123419) : term387 _123419 m op f.
Proof. exact (fun h0 : term385 _123419 m op f => @lem6185674 _123419 m op f h0). Qed.
Lemma lem6185678 {_123419 : Type'} (m : nat) (op : type1400 _123419) (f : nat -> _123419) : term385 _123419 m op f.
Proof. exact (@lem6185675 _123419 m op f (@lem6185667 _123419 m op f)). Qed.
Lemma lem6185679 {_123419 : Type'} (m : nat) (op : type1400 _123419) (f : nat -> _123419) : term385 _123419 m op f.
Proof. exact (@lem6185678 _123419 m op f). Qed.
Lemma lem6185733 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6185734 : term388 = term389.
Proof. exact (@lem6185733 term383). Qed.
Lemma lem6185767 {_123419 : Type'} : (term390 _123419) = (term390 _123419).
Proof. exact (eq_refl (term390 _123419)). Qed.
Lemma lem6185768 {_123419 : Type'} : (term391 _123419) = (term392 _123419).
Proof. exact (MK_COMB (@lem6185767 _123419) (@lem6185734)). Qed.
Lemma lem6185771 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : (term393 _123419 op f) = (term393 _123419 op f).
Proof. exact (eq_refl (term393 _123419 op f)). Qed.
Lemma lem6185772 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : (term394 _123419 op f) = (term395 _123419 op f).
Proof. exact (MK_COMB (@lem6185771 _123419 op f) (@lem6185768 _123419)). Qed.
Lemma lem6185775 (m : nat) : (term217 m) = (term217 m).
Proof. exact (eq_refl (term217 m)). Qed.
Lemma lem6185776 {_123419 : Type'} (m : nat) (op : type1400 _123419) (f : nat -> _123419) : (term396 _123419 m op f) = (term397 _123419 m op f).
Proof. exact (MK_COMB (@lem6185775 m) (@lem6185772 _123419 op f)). Qed.
Lemma lem6185779 {_123419 : Type'} (op : type1400 _123419) : (term196 _123419 op) = (term196 _123419 op).
Proof. exact (eq_refl (term196 _123419 op)). Qed.
Lemma lem6185780 {_123419 : Type'} (m : nat) (op : type1400 _123419) (f : nat -> _123419) : (term384 _123419 m op f) = (term398 _123419 m op f).
Proof. exact (MK_COMB (@lem6185779 _123419 op) (@lem6185776 _123419 m op f)). Qed.
Lemma lem6185783 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : (term399 _123419 op f) = (term400 _123419 op f).
Proof. exact (fun_ext (fun m : nat => @lem6185780 _123419 m op f)). Qed.
Lemma lem6185784 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6185785 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : (term401 _123419 op f) = (term402 _123419 op f).
Proof. exact (MK_COMB (@lem6185784) (@lem6185783 _123419 op f)). Qed.
Lemma lem6185790 {_123419 : Type'} (f : nat -> _123419) : (term403 _123419 f) = (term404 _123419 f).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6185785 _123419 op f)). Qed.
Lemma lem6185791 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6185792 {_123419 : Type'} (f : nat -> _123419) : (term405 _123419 f) = (term406 _123419 f).
Proof. exact (MK_COMB (@lem6185791 _123419) (@lem6185790 _123419 f)). Qed.
Lemma lem6185797 {_123419 : Type'} : (term407 _123419) = (term408 _123419).
Proof. exact (fun_ext (fun f : nat -> _123419 => @lem6185792 _123419 f)). Qed.
Lemma lem6185798 {_123419 : Type'} : (@all (nat -> _123419)) = (@all (nat -> _123419)).
Proof. exact (eq_refl (@all (nat -> _123419))). Qed.
Lemma lem6185807 {_123419 : Type'} : (term409 _123419) = (term410 _123419).
Proof. exact (MK_COMB (@lem6185798 _123419) (@lem6185797 _123419)). Qed.
Lemma lem6185808 (op : type1606) (x : nat) : ((term411 op x) = x) = ((term411 op x) = x).
Proof. exact (eq_refl ((term411 op x) = x)). Qed.
Lemma lem6185809 (op : type1606) : (term412 op) = (term412 op).
Proof. exact (fun_ext (fun x : nat => @lem6185808 op x)). Qed.
Lemma lem6185810 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6185811 (op : type1606) : (term413 op) = (term413 op).
Proof. exact (MK_COMB (@lem6185810) (@lem6185809 op)). Qed.
Lemma lem6185812 (op : type1606) (x : nat) (y : nat) (z : nat) : ((term414 x op y z) = (term415 op x y z)) = ((term414 x op y z) = (term415 op x y z)).
Proof. exact (eq_refl ((term414 x op y z) = (term415 op x y z))). Qed.
Lemma lem6185813 (op : type1606) (x : nat) (y : nat) : (term416 op x y) = (term416 op x y).
Proof. exact (fun_ext (fun z : nat => @lem6185812 op x y z)). Qed.
Lemma lem6185814 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6185815 (op : type1606) (x : nat) (y : nat) : (term417 op x y) = (term417 op x y).
Proof. exact (MK_COMB (@lem6185814) (@lem6185813 op x y)). Qed.
Lemma lem6185816 (op : type1606) (x : nat) : (term418 op x) = (term418 op x).
Proof. exact (fun_ext (fun y : nat => @lem6185815 op x y)). Qed.
Lemma lem6185817 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6185818 (op : type1606) (x : nat) : (term419 op x) = (term419 op x).
Proof. exact (MK_COMB (@lem6185817) (@lem6185816 op x)). Qed.
Lemma lem6185819 (op : type1606) : (term420 op) = (term420 op).
Proof. exact (fun_ext (fun x : nat => @lem6185818 op x)). Qed.
Lemma lem6185820 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6185821 (op : type1606) : (term421 op) = (term421 op).
Proof. exact (MK_COMB (@lem6185820) (@lem6185819 op)). Qed.
Lemma lem6185822 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6185823 (op : type1606) : (term422 op) = (term422 op).
Proof. exact (MK_COMB (@lem6185822) (@lem6185821 op)). Qed.
Lemma lem6185824 (op : type1606) : (term423 op) = (term423 op).
Proof. exact (MK_COMB (@lem6185823 op) (@lem6185811 op)). Qed.
Lemma lem6185825 (op : type1606) (y : nat) (x : nat) : ((op x y) = (op y x)) = ((op x y) = (op y x)).
Proof. exact (eq_refl ((op x y) = (op y x))). Qed.
Lemma lem6185826 (op : type1606) (x : nat) : (term424 op x) = (term424 op x).
Proof. exact (fun_ext (fun y : nat => @lem6185825 op y x)). Qed.
Lemma lem6185827 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6185828 (op : type1606) (x : nat) : (term425 op x) = (term425 op x).
Proof. exact (MK_COMB (@lem6185827) (@lem6185826 op x)). Qed.
Lemma lem6185829 (op : type1606) : (term426 op) = (term426 op).
Proof. exact (fun_ext (fun x : nat => @lem6185828 op x)). Qed.
Lemma lem6185830 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6185831 (op : type1606) : (term427 op) = (term427 op).
Proof. exact (MK_COMB (@lem6185830) (@lem6185829 op)). Qed.
Lemma lem6185832 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6185833 (op : type1606) : (term428 op) = (term428 op).
Proof. exact (MK_COMB (@lem6185832) (@lem6185831 op)). Qed.
Lemma lem6185834 (op : type1606) : (term429 op) = (term429 op).
Proof. exact (MK_COMB (@lem6185833 op) (@lem6185824 op)). Qed.
Lemma lem6185837 (op : type1606) : (term430 op) = (term430 op).
Proof. exact (eq_refl (term430 op)). Qed.
Lemma lem6185838 (op : type1606) : ((@monoidal nat op) = (term429 op)) = ((@monoidal nat op) = (term429 op)).
Proof. exact (MK_COMB (@lem6185837 op) (@lem6185834 op)). Qed.
Lemma lem6185839 : term431 = term431.
Proof. exact (fun_ext (fun op : type1606 => @lem6185838 op)). Qed.
Lemma lem6185840 : (@all (nat -> nat -> nat)) = (@all (nat -> nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat -> nat))). Qed.
Lemma lem6185841 : term383 = term383.
Proof. exact (MK_COMB (@lem6185840) (@lem6185839)). Qed.
Lemma lem6185842 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6185843 : term389 = term389.
Proof. exact (MK_COMB (@lem6185842) (@lem6185841)). Qed.
Lemma lem6185844 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : ((term432 _123419 op x) = x) = ((term432 _123419 op x) = x).
Proof. exact (eq_refl ((term432 _123419 op x) = x)). Qed.
Lemma lem6185845 {_123419 : Type'} (op : type1400 _123419) : (term433 _123419 op) = (term433 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6185844 _123419 op x)). Qed.
Lemma lem6185846 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6185847 {_123419 : Type'} (op : type1400 _123419) : (term434 _123419 op) = (term434 _123419 op).
Proof. exact (MK_COMB (@lem6185846 _123419) (@lem6185845 _123419 op)). Qed.
Lemma lem6185848 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : ((term435 _123419 x op y z) = (term436 _123419 op x y z)) = ((term435 _123419 x op y z) = (term436 _123419 op x y z)).
Proof. exact (eq_refl ((term435 _123419 x op y z) = (term436 _123419 op x y z))). Qed.
Lemma lem6185849 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term437 _123419 op x y) = (term437 _123419 op x y).
Proof. exact (fun_ext (fun z : _123419 => @lem6185848 _123419 op x y z)). Qed.
Lemma lem6185850 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6185851 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term438 _123419 op x y) = (term438 _123419 op x y).
Proof. exact (MK_COMB (@lem6185850 _123419) (@lem6185849 _123419 op x y)). Qed.
Lemma lem6185852 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term439 _123419 op x) = (term439 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6185851 _123419 op x y)). Qed.
Lemma lem6185853 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6185854 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term440 _123419 op x) = (term440 _123419 op x).
Proof. exact (MK_COMB (@lem6185853 _123419) (@lem6185852 _123419 op x)). Qed.
Lemma lem6185855 {_123419 : Type'} (op : type1400 _123419) : (term441 _123419 op) = (term441 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6185854 _123419 op x)). Qed.
Lemma lem6185856 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6185857 {_123419 : Type'} (op : type1400 _123419) : (term442 _123419 op) = (term442 _123419 op).
Proof. exact (MK_COMB (@lem6185856 _123419) (@lem6185855 _123419 op)). Qed.
Lemma lem6185858 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6185859 {_123419 : Type'} (op : type1400 _123419) : (term443 _123419 op) = (term443 _123419 op).
Proof. exact (MK_COMB (@lem6185858) (@lem6185857 _123419 op)). Qed.
Lemma lem6185860 {_123419 : Type'} (op : type1400 _123419) : (term444 _123419 op) = (term444 _123419 op).
Proof. exact (MK_COMB (@lem6185859 _123419 op) (@lem6185847 _123419 op)). Qed.
Lemma lem6185861 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : ((op x y) = (op y x)) = ((op x y) = (op y x)).
Proof. exact (eq_refl ((op x y) = (op y x))). Qed.
Lemma lem6185862 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term445 _123419 op x) = (term445 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6185861 _123419 op y x)). Qed.
Lemma lem6185863 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6185864 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term446 _123419 op x) = (term446 _123419 op x).
Proof. exact (MK_COMB (@lem6185863 _123419) (@lem6185862 _123419 op x)). Qed.
Lemma lem6185865 {_123419 : Type'} (op : type1400 _123419) : (term447 _123419 op) = (term447 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6185864 _123419 op x)). Qed.
Lemma lem6185866 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6185867 {_123419 : Type'} (op : type1400 _123419) : (term448 _123419 op) = (term448 _123419 op).
Proof. exact (MK_COMB (@lem6185866 _123419) (@lem6185865 _123419 op)). Qed.
Lemma lem6185868 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6185869 {_123419 : Type'} (op : type1400 _123419) : (term449 _123419 op) = (term449 _123419 op).
Proof. exact (MK_COMB (@lem6185868) (@lem6185867 _123419 op)). Qed.
Lemma lem6185870 {_123419 : Type'} (op : type1400 _123419) : (term450 _123419 op) = (term450 _123419 op).
Proof. exact (MK_COMB (@lem6185869 _123419 op) (@lem6185860 _123419 op)). Qed.
Lemma lem6185873 {_123419 : Type'} (op : type1400 _123419) : (term451 _123419 op) = (term451 _123419 op).
Proof. exact (eq_refl (term451 _123419 op)). Qed.
Lemma lem6185874 {_123419 : Type'} (op : type1400 _123419) : ((@monoidal _123419 op) = (term450 _123419 op)) = ((@monoidal _123419 op) = (term450 _123419 op)).
Proof. exact (MK_COMB (@lem6185873 _123419 op) (@lem6185870 _123419 op)). Qed.
Lemma lem6185875 {_123419 : Type'} : (term452 _123419) = (term452 _123419).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6185874 _123419 op)). Qed.
Lemma lem6185876 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6185877 {_123419 : Type'} : (term382 _123419) = (term382 _123419).
Proof. exact (MK_COMB (@lem6185876 _123419) (@lem6185875 _123419)). Qed.
Lemma lem6185878 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6185879 {_123419 : Type'} : (term390 _123419) = (term390 _123419).
Proof. exact (MK_COMB (@lem6185878) (@lem6185877 _123419)). Qed.
Lemma lem6185880 {_123419 : Type'} : (term392 _123419) = (term392 _123419).
Proof. exact (MK_COMB (@lem6185879 _123419) (@lem6185843)). Qed.
Lemma lem6185885 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : (term393 _123419 op f) = (term393 _123419 op f).
Proof. exact (eq_refl (term393 _123419 op f)). Qed.
Lemma lem6185886 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : (term395 _123419 op f) = (term395 _123419 op f).
Proof. exact (MK_COMB (@lem6185885 _123419 op f) (@lem6185880 _123419)). Qed.
Lemma lem6185889 (m : nat) : (term217 m) = (term217 m).
Proof. exact (eq_refl (term217 m)). Qed.
Lemma lem6185890 {_123419 : Type'} (m : nat) (op : type1400 _123419) (f : nat -> _123419) : (term397 _123419 m op f) = (term397 _123419 m op f).
Proof. exact (MK_COMB (@lem6185889 m) (@lem6185886 _123419 op f)). Qed.
Lemma lem6185893 {_123419 : Type'} (op : type1400 _123419) : (term196 _123419 op) = (term196 _123419 op).
Proof. exact (eq_refl (term196 _123419 op)). Qed.
Lemma lem6185894 {_123419 : Type'} (m : nat) (op : type1400 _123419) (f : nat -> _123419) : (term398 _123419 m op f) = (term398 _123419 m op f).
Proof. exact (MK_COMB (@lem6185893 _123419 op) (@lem6185890 _123419 m op f)). Qed.
Lemma lem6185895 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : (term400 _123419 op f) = (term400 _123419 op f).
Proof. exact (fun_ext (fun m : nat => @lem6185894 _123419 m op f)). Qed.
Lemma lem6185896 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6185897 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : (term402 _123419 op f) = (term402 _123419 op f).
Proof. exact (MK_COMB (@lem6185896) (@lem6185895 _123419 op f)). Qed.
Lemma lem6185898 {_123419 : Type'} (f : nat -> _123419) : (term404 _123419 f) = (term404 _123419 f).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6185897 _123419 op f)). Qed.
Lemma lem6185899 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6185900 {_123419 : Type'} (f : nat -> _123419) : (term406 _123419 f) = (term406 _123419 f).
Proof. exact (MK_COMB (@lem6185899 _123419) (@lem6185898 _123419 f)). Qed.
Lemma lem6185901 {_123419 : Type'} : (term408 _123419) = (term408 _123419).
Proof. exact (fun_ext (fun f : nat -> _123419 => @lem6185900 _123419 f)). Qed.
Lemma lem6185902 {_123419 : Type'} : (@all (nat -> _123419)) = (@all (nat -> _123419)).
Proof. exact (eq_refl (@all (nat -> _123419))). Qed.
Lemma lem6185903 {_123419 : Type'} : (term410 _123419) = (term410 _123419).
Proof. exact (MK_COMB (@lem6185902 _123419) (@lem6185901 _123419)). Qed.
Lemma lem6186024 {_123419 : Type'} : (term409 _123419) = (term410 _123419).
Proof. exact (TRANS (@lem6185807 _123419) (@lem6185903 _123419)). Qed.
Lemma lem6186025 {_123419 : Type'} : (term410 _123419) = (term409 _123419).
Proof. exact (SYM (@lem6186024 _123419)). Qed.
Lemma lem6186029 {_123419 : Type'} (h1 : term382 _123419) : term382 _123419.
Proof. exact (h1). Qed.
Lemma lem6186030 (h1 : term383) : term383.
Proof. exact (h1). Qed.
Lemma lem6186036 {_123419 : Type'} (op : type1400 _123419) (h1 : @monoidal _123419 op) : @monoidal _123419 op.
Proof. exact (h1). Qed.
Lemma lem6186048 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (h1 : term381 _123419 op f) : term381 _123419 op f.
Proof. exact (h1). Qed.
Lemma lem6186052 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : ((op x y) = (op y x)) = ((op x y) = (op y x)).
Proof. exact (eq_refl ((op x y) = (op y x))). Qed.
Lemma lem6186053 {_123419 : Type'} (P : _123419 -> Prop) : (term453 _123419 P) = (term454 _123419 P).
Proof. exact (@lem18392 _123419 P). Qed.
Lemma lem6186054 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term455 _123419 op x) = (term456 _123419 op x).
Proof. exact (@lem6186053 _123419 (term445 _123419 op x)). Qed.
Lemma lem6186055 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (term457 _123419 op x y) = ((op x y) = (op y x)).
Proof. exact (eq_refl (term457 _123419 op x y)). Qed.
Lemma lem6186056 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6186058 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (term458 _123419 op x y) = (term459 _123419 op y x).
Proof. exact (MK_COMB (@lem6186056) (@lem6186055 _123419 op y x)). Qed.
Lemma lem6186059 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term460 _123419 op x) = (term461 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6186058 _123419 op y x)). Qed.
Lemma lem6186060 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186061 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term456 _123419 op x) = (term462 _123419 op x).
Proof. exact (MK_COMB (@lem6186060 _123419) (@lem6186059 _123419 op x)). Qed.
Lemma lem6186062 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term455 _123419 op x) = (term462 _123419 op x).
Proof. exact (TRANS (@lem6186054 _123419 op x) (@lem6186061 _123419 op x)). Qed.
Lemma lem6186063 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term445 _123419 op x) = (term445 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6186052 _123419 op y x)). Qed.
Lemma lem6186064 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6186065 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term446 _123419 op x) = (term446 _123419 op x).
Proof. exact (MK_COMB (@lem6186064 _123419) (@lem6186063 _123419 op x)). Qed.
Lemma lem6186066 {_123419 : Type'} (P : _123419 -> Prop) : (term453 _123419 P) = (term454 _123419 P).
Proof. exact (@lem18392 _123419 P). Qed.
Lemma lem6186067 {_123419 : Type'} (op : type1400 _123419) : (term463 _123419 op) = (term464 _123419 op).
Proof. exact (@lem6186066 _123419 (term447 _123419 op)). Qed.
Lemma lem6186068 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term465 _123419 op x) = (term446 _123419 op x).
Proof. exact (eq_refl (term465 _123419 op x)). Qed.
Lemma lem6186069 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6186070 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term466 _123419 op x) = (term455 _123419 op x).
Proof. exact (MK_COMB (@lem6186069) (@lem6186068 _123419 op x)). Qed.
Lemma lem6186071 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term466 _123419 op x) = (term462 _123419 op x).
Proof. exact (TRANS (@lem6186070 _123419 op x) (@lem6186062 _123419 op x)). Qed.
Lemma lem6186072 {_123419 : Type'} (op : type1400 _123419) : (term467 _123419 op) = (term468 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6186071 _123419 op x)). Qed.
Lemma lem6186073 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186074 {_123419 : Type'} (op : type1400 _123419) : (term464 _123419 op) = (term469 _123419 op).
Proof. exact (MK_COMB (@lem6186073 _123419) (@lem6186072 _123419 op)). Qed.
Lemma lem6186075 {_123419 : Type'} (op : type1400 _123419) : (term463 _123419 op) = (term469 _123419 op).
Proof. exact (TRANS (@lem6186067 _123419 op) (@lem6186074 _123419 op)). Qed.
Lemma lem6186076 {_123419 : Type'} (op : type1400 _123419) : (term447 _123419 op) = (term447 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6186065 _123419 op x)). Qed.
Lemma lem6186077 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6186078 {_123419 : Type'} (op : type1400 _123419) : (term448 _123419 op) = (term448 _123419 op).
Proof. exact (MK_COMB (@lem6186077 _123419) (@lem6186076 _123419 op)). Qed.
Lemma lem6186080 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : ((term435 _123419 x op y z) = (term436 _123419 op x y z)) = ((term435 _123419 x op y z) = (term436 _123419 op x y z)).
Proof. exact (eq_refl ((term435 _123419 x op y z) = (term436 _123419 op x y z))). Qed.
Lemma lem6186081 {_123419 : Type'} (P : _123419 -> Prop) : (term453 _123419 P) = (term454 _123419 P).
Proof. exact (@lem18392 _123419 P). Qed.
Lemma lem6186082 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term470 _123419 op x y) = (term471 _123419 op x y).
Proof. exact (@lem6186081 _123419 (term437 _123419 op x y)). Qed.
Lemma lem6186083 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : (term472 _123419 op x y z) = ((term435 _123419 x op y z) = (term436 _123419 op x y z)).
Proof. exact (eq_refl (term472 _123419 op x y z)). Qed.
Lemma lem6186084 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6186086 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : (term473 _123419 op x y z) = (term474 _123419 op x y z).
Proof. exact (MK_COMB (@lem6186084) (@lem6186083 _123419 op x y z)). Qed.
Lemma lem6186087 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term475 _123419 op x y) = (term476 _123419 op x y).
Proof. exact (fun_ext (fun z : _123419 => @lem6186086 _123419 op x y z)). Qed.
Lemma lem6186088 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186089 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term471 _123419 op x y) = (term477 _123419 op x y).
Proof. exact (MK_COMB (@lem6186088 _123419) (@lem6186087 _123419 op x y)). Qed.
Lemma lem6186090 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term470 _123419 op x y) = (term477 _123419 op x y).
Proof. exact (TRANS (@lem6186082 _123419 op x y) (@lem6186089 _123419 op x y)). Qed.
Lemma lem6186091 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term437 _123419 op x y) = (term437 _123419 op x y).
Proof. exact (fun_ext (fun z : _123419 => @lem6186080 _123419 op x y z)). Qed.
Lemma lem6186092 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6186093 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term438 _123419 op x y) = (term438 _123419 op x y).
Proof. exact (MK_COMB (@lem6186092 _123419) (@lem6186091 _123419 op x y)). Qed.
Lemma lem6186094 {_123419 : Type'} (P : _123419 -> Prop) : (term453 _123419 P) = (term454 _123419 P).
Proof. exact (@lem18392 _123419 P). Qed.
Lemma lem6186095 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term478 _123419 op x) = (term479 _123419 op x).
Proof. exact (@lem6186094 _123419 (term439 _123419 op x)). Qed.
Lemma lem6186096 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term480 _123419 op x y) = (term438 _123419 op x y).
Proof. exact (eq_refl (term480 _123419 op x y)). Qed.
Lemma lem6186097 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6186098 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term481 _123419 op x y) = (term470 _123419 op x y).
Proof. exact (MK_COMB (@lem6186097) (@lem6186096 _123419 op x y)). Qed.
Lemma lem6186099 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term481 _123419 op x y) = (term477 _123419 op x y).
Proof. exact (TRANS (@lem6186098 _123419 op x y) (@lem6186090 _123419 op x y)). Qed.
Lemma lem6186100 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term482 _123419 op x) = (term483 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6186099 _123419 op x y)). Qed.
Lemma lem6186101 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186102 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term479 _123419 op x) = (term484 _123419 op x).
Proof. exact (MK_COMB (@lem6186101 _123419) (@lem6186100 _123419 op x)). Qed.
Lemma lem6186103 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term478 _123419 op x) = (term484 _123419 op x).
Proof. exact (TRANS (@lem6186095 _123419 op x) (@lem6186102 _123419 op x)). Qed.
Lemma lem6186104 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term439 _123419 op x) = (term439 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6186093 _123419 op x y)). Qed.
Lemma lem6186105 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6186106 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term440 _123419 op x) = (term440 _123419 op x).
Proof. exact (MK_COMB (@lem6186105 _123419) (@lem6186104 _123419 op x)). Qed.
Lemma lem6186107 {_123419 : Type'} (P : _123419 -> Prop) : (term453 _123419 P) = (term454 _123419 P).
Proof. exact (@lem18392 _123419 P). Qed.
Lemma lem6186108 {_123419 : Type'} (op : type1400 _123419) : (term485 _123419 op) = (term486 _123419 op).
Proof. exact (@lem6186107 _123419 (term441 _123419 op)). Qed.
Lemma lem6186109 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term487 _123419 op x) = (term440 _123419 op x).
Proof. exact (eq_refl (term487 _123419 op x)). Qed.
Lemma lem6186110 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6186111 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term488 _123419 op x) = (term478 _123419 op x).
Proof. exact (MK_COMB (@lem6186110) (@lem6186109 _123419 op x)). Qed.
Lemma lem6186112 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term488 _123419 op x) = (term484 _123419 op x).
Proof. exact (TRANS (@lem6186111 _123419 op x) (@lem6186103 _123419 op x)). Qed.
Lemma lem6186113 {_123419 : Type'} (op : type1400 _123419) : (term489 _123419 op) = (term490 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6186112 _123419 op x)). Qed.
Lemma lem6186114 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186115 {_123419 : Type'} (op : type1400 _123419) : (term486 _123419 op) = (term491 _123419 op).
Proof. exact (MK_COMB (@lem6186114 _123419) (@lem6186113 _123419 op)). Qed.
Lemma lem6186116 {_123419 : Type'} (op : type1400 _123419) : (term485 _123419 op) = (term491 _123419 op).
Proof. exact (TRANS (@lem6186108 _123419 op) (@lem6186115 _123419 op)). Qed.
Lemma lem6186117 {_123419 : Type'} (op : type1400 _123419) : (term441 _123419 op) = (term441 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6186106 _123419 op x)). Qed.
Lemma lem6186118 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6186119 {_123419 : Type'} (op : type1400 _123419) : (term442 _123419 op) = (term442 _123419 op).
Proof. exact (MK_COMB (@lem6186118 _123419) (@lem6186117 _123419 op)). Qed.
Lemma lem6186121 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : ((term432 _123419 op x) = x) = ((term432 _123419 op x) = x).
Proof. exact (eq_refl ((term432 _123419 op x) = x)). Qed.
Lemma lem6186122 {_123419 : Type'} (P : _123419 -> Prop) : (term453 _123419 P) = (term454 _123419 P).
Proof. exact (@lem18392 _123419 P). Qed.
Lemma lem6186123 {_123419 : Type'} (op : type1400 _123419) : (term492 _123419 op) = (term493 _123419 op).
Proof. exact (@lem6186122 _123419 (term433 _123419 op)). Qed.
Lemma lem6186124 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term494 _123419 op x) = ((term432 _123419 op x) = x).
Proof. exact (eq_refl (term494 _123419 op x)). Qed.
Lemma lem6186125 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6186127 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term495 _123419 op x) = (term496 _123419 op x).
Proof. exact (MK_COMB (@lem6186125) (@lem6186124 _123419 op x)). Qed.
Lemma lem6186128 {_123419 : Type'} (op : type1400 _123419) : (term497 _123419 op) = (term498 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6186127 _123419 op x)). Qed.
Lemma lem6186129 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186130 {_123419 : Type'} (op : type1400 _123419) : (term493 _123419 op) = (term499 _123419 op).
Proof. exact (MK_COMB (@lem6186129 _123419) (@lem6186128 _123419 op)). Qed.
Lemma lem6186131 {_123419 : Type'} (op : type1400 _123419) : (term492 _123419 op) = (term499 _123419 op).
Proof. exact (TRANS (@lem6186123 _123419 op) (@lem6186130 _123419 op)). Qed.
Lemma lem6186132 {_123419 : Type'} (op : type1400 _123419) : (term433 _123419 op) = (term433 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6186121 _123419 op x)). Qed.
Lemma lem6186133 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6186134 {_123419 : Type'} (op : type1400 _123419) : (term434 _123419 op) = (term434 _123419 op).
Proof. exact (MK_COMB (@lem6186133 _123419) (@lem6186132 _123419 op)). Qed.
Lemma lem6186135 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6186136 {_123419 : Type'} (op : type1400 _123419) : (term500 _123419 op) = (term501 _123419 op).
Proof. exact (MK_COMB (@lem6186135) (@lem6186116 _123419 op)). Qed.
Lemma lem6186137 {_123419 : Type'} (op : type1400 _123419) : (term502 _123419 op) = (term503 _123419 op).
Proof. exact (MK_COMB (@lem6186136 _123419 op) (@lem6186131 _123419 op)). Qed.
Lemma lem6186138 {_123419 : Type'} (op : type1400 _123419) : (term504 _123419 op) = (term502 _123419 op).
Proof. exact (@lem17045 (term442 _123419 op) (term434 _123419 op)). Qed.
Lemma lem6186139 {_123419 : Type'} (op : type1400 _123419) : (term504 _123419 op) = (term503 _123419 op).
Proof. exact (TRANS (@lem6186138 _123419 op) (@lem6186137 _123419 op)). Qed.
Lemma lem6186140 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6186141 {_123419 : Type'} (op : type1400 _123419) : (term443 _123419 op) = (term443 _123419 op).
Proof. exact (MK_COMB (@lem6186140) (@lem6186119 _123419 op)). Qed.
Lemma lem6186142 {_123419 : Type'} (op : type1400 _123419) : (term444 _123419 op) = (term444 _123419 op).
Proof. exact (MK_COMB (@lem6186141 _123419 op) (@lem6186134 _123419 op)). Qed.
Lemma lem6186143 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6186144 {_123419 : Type'} (op : type1400 _123419) : (term505 _123419 op) = (term506 _123419 op).
Proof. exact (MK_COMB (@lem6186143) (@lem6186075 _123419 op)). Qed.
Lemma lem6186145 {_123419 : Type'} (op : type1400 _123419) : (term507 _123419 op) = (term508 _123419 op).
Proof. exact (MK_COMB (@lem6186144 _123419 op) (@lem6186139 _123419 op)). Qed.
Lemma lem6186146 {_123419 : Type'} (op : type1400 _123419) : (term509 _123419 op) = (term507 _123419 op).
Proof. exact (@lem17045 (term448 _123419 op) (term444 _123419 op)). Qed.
Lemma lem6186147 {_123419 : Type'} (op : type1400 _123419) : (term509 _123419 op) = (term508 _123419 op).
Proof. exact (TRANS (@lem6186146 _123419 op) (@lem6186145 _123419 op)). Qed.
Lemma lem6186148 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6186149 {_123419 : Type'} (op : type1400 _123419) : (term449 _123419 op) = (term449 _123419 op).
Proof. exact (MK_COMB (@lem6186148) (@lem6186078 _123419 op)). Qed.
Lemma lem6186150 {_123419 : Type'} (op : type1400 _123419) : (term450 _123419 op) = (term450 _123419 op).
Proof. exact (MK_COMB (@lem6186149 _123419 op) (@lem6186142 _123419 op)). Qed.
Lemma lem6186152 {_123419 : Type'} (op : type1400 _123419) : (term510 _123419 op) = (term510 _123419 op).
Proof. exact (eq_refl (term510 _123419 op)). Qed.
Lemma lem6186153 {_123419 : Type'} (op : type1400 _123419) : (term511 _123419 op) = (term511 _123419 op).
Proof. exact (MK_COMB (@lem6186152 _123419 op) (@lem6186150 _123419 op)). Qed.
Lemma lem6186155 {_123419 : Type'} (op : type1400 _123419) : (term512 _123419 op) = (term512 _123419 op).
Proof. exact (eq_refl (term512 _123419 op)). Qed.
Lemma lem6186156 {_123419 : Type'} (op : type1400 _123419) : (term513 _123419 op) = (term514 _123419 op).
Proof. exact (MK_COMB (@lem6186155 _123419 op) (@lem6186147 _123419 op)). Qed.
Lemma lem6186157 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6186158 {_123419 : Type'} (op : type1400 _123419) : (term515 _123419 op) = (term516 _123419 op).
Proof. exact (MK_COMB (@lem6186157) (@lem6186156 _123419 op)). Qed.
Lemma lem6186159 {_123419 : Type'} (op : type1400 _123419) : (term517 _123419 op) = (term518 _123419 op).
Proof. exact (MK_COMB (@lem6186158 _123419 op) (@lem6186153 _123419 op)). Qed.
Lemma lem6186160 {_123419 : Type'} (op : type1400 _123419) : ((@monoidal _123419 op) = (term450 _123419 op)) = (term517 _123419 op).
Proof. exact (@lem17784 (@monoidal _123419 op) (term450 _123419 op)). Qed.
Lemma lem6186161 {_123419 : Type'} (op : type1400 _123419) : ((@monoidal _123419 op) = (term450 _123419 op)) = (term518 _123419 op).
Proof. exact (TRANS (@lem6186160 _123419 op) (@lem6186159 _123419 op)). Qed.
Lemma lem6186162 {_123419 : Type'} : (term452 _123419) = (term519 _123419).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6186161 _123419 op)). Qed.
Lemma lem6186163 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6186164 {_123419 : Type'} : (term382 _123419) = (term520 _123419).
Proof. exact (MK_COMB (@lem6186163 _123419) (@lem6186162 _123419)). Qed.
Lemma lem6186166 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term521 A P Q) = (term522 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6186167 {_123419 : Type'} (P : type403 _123419) (Q : type403 _123419) : (term523 _123419 P Q) = (term524 _123419 P Q).
Proof. exact (@lem6186166 (type1400 _123419) P Q). Qed.
Lemma lem6186168 {_123419 : Type'} : (term525 _123419) = (term526 _123419).
Proof. exact (@lem6186167 _123419 (term527 _123419) (term528 _123419)). Qed.
Lemma lem6186169 {_123419 : Type'} (op : type1400 _123419) : (term529 _123419 op) = (term514 _123419 op).
Proof. exact (eq_refl (term529 _123419 op)). Qed.
Lemma lem6186170 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6186171 {_123419 : Type'} (op : type1400 _123419) : (term530 _123419 op) = (term516 _123419 op).
Proof. exact (MK_COMB (@lem6186170) (@lem6186169 _123419 op)). Qed.
Lemma lem6186172 {_123419 : Type'} (op : type1400 _123419) : (term531 _123419 op) = (term511 _123419 op).
Proof. exact (eq_refl (term531 _123419 op)). Qed.
Lemma lem6186173 {_123419 : Type'} (op : type1400 _123419) : (term532 _123419 op) = (term518 _123419 op).
Proof. exact (MK_COMB (@lem6186171 _123419 op) (@lem6186172 _123419 op)). Qed.
Lemma lem6186174 {_123419 : Type'} : (term533 _123419) = (term519 _123419).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6186173 _123419 op)). Qed.
Lemma lem6186175 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6186176 {_123419 : Type'} : (term525 _123419) = (term520 _123419).
Proof. exact (MK_COMB (@lem6186175 _123419) (@lem6186174 _123419)). Qed.
Lemma lem6186177 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6186178 {_123419 : Type'} : (term534 _123419) = (term535 _123419).
Proof. exact (MK_COMB (@lem6186177) (@lem6186176 _123419)). Qed.
Lemma lem6186179 {_123419 : Type'} (op : type1400 _123419) : (term529 _123419 op) = (term514 _123419 op).
Proof. exact (eq_refl (term529 _123419 op)). Qed.
Lemma lem6186180 {_123419 : Type'} : (term536 _123419) = (term527 _123419).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6186179 _123419 op)). Qed.
Lemma lem6186181 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6186182 {_123419 : Type'} : (term537 _123419) = (term538 _123419).
Proof. exact (MK_COMB (@lem6186181 _123419) (@lem6186180 _123419)). Qed.
Lemma lem6186183 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6186184 {_123419 : Type'} : (term539 _123419) = (term540 _123419).
Proof. exact (MK_COMB (@lem6186183) (@lem6186182 _123419)). Qed.
Lemma lem6186185 {_123419 : Type'} (op : type1400 _123419) : (term531 _123419 op) = (term511 _123419 op).
Proof. exact (eq_refl (term531 _123419 op)). Qed.
Lemma lem6186186 {_123419 : Type'} : (term541 _123419) = (term528 _123419).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6186185 _123419 op)). Qed.
Lemma lem6186187 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6186188 {_123419 : Type'} : (term542 _123419) = (term543 _123419).
Proof. exact (MK_COMB (@lem6186187 _123419) (@lem6186186 _123419)). Qed.
Lemma lem6186189 {_123419 : Type'} : (term526 _123419) = (term544 _123419).
Proof. exact (MK_COMB (@lem6186184 _123419) (@lem6186188 _123419)). Qed.
Lemma lem6186190 {_123419 : Type'} : ((term525 _123419) = (term526 _123419)) = ((term520 _123419) = (term544 _123419)).
Proof. exact (MK_COMB (@lem6186178 _123419) (@lem6186189 _123419)). Qed.
Lemma lem6186191 {_123419 : Type'} : (term520 _123419) = (term544 _123419).
Proof. exact (EQ_MP (@lem6186190 _123419) (@lem6186168 _123419)). Qed.
Lemma lem6186317 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term545 A P Q) = (term546 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6186318 {_123419 : Type'} (P : _123419 -> Prop) (Q : _123419 -> Prop) : (term545 _123419 P Q) = (term546 _123419 P Q).
Proof. exact (@lem6186317 _123419 P Q). Qed.
Lemma lem6186319 {_123419 : Type'} (op : type1400 _123419) : (term547 _123419 op) = (term548 _123419 op).
Proof. exact (@lem6186318 _123419 (term490 _123419 op) (term498 _123419 op)). Qed.
Lemma lem6186320 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term549 _123419 op x) = (term484 _123419 op x).
Proof. exact (eq_refl (term549 _123419 op x)). Qed.
Lemma lem6186321 {_123419 : Type'} (op : type1400 _123419) : (term550 _123419 op) = (term490 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6186320 _123419 op x)). Qed.
Lemma lem6186322 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186323 {_123419 : Type'} (op : type1400 _123419) : (term551 _123419 op) = (term491 _123419 op).
Proof. exact (MK_COMB (@lem6186322 _123419) (@lem6186321 _123419 op)). Qed.
Lemma lem6186324 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6186325 {_123419 : Type'} (op : type1400 _123419) : (term552 _123419 op) = (term501 _123419 op).
Proof. exact (MK_COMB (@lem6186324) (@lem6186323 _123419 op)). Qed.
Lemma lem6186326 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term553 _123419 op x) = (term496 _123419 op x).
Proof. exact (eq_refl (term553 _123419 op x)). Qed.
Lemma lem6186327 {_123419 : Type'} (op : type1400 _123419) : (term554 _123419 op) = (term498 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6186326 _123419 op x)). Qed.
Lemma lem6186328 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186329 {_123419 : Type'} (op : type1400 _123419) : (term555 _123419 op) = (term499 _123419 op).
Proof. exact (MK_COMB (@lem6186328 _123419) (@lem6186327 _123419 op)). Qed.
Lemma lem6186330 {_123419 : Type'} (op : type1400 _123419) : (term547 _123419 op) = (term503 _123419 op).
Proof. exact (MK_COMB (@lem6186325 _123419 op) (@lem6186329 _123419 op)). Qed.
Lemma lem6186331 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6186332 {_123419 : Type'} (op : type1400 _123419) : (term556 _123419 op) = (term557 _123419 op).
Proof. exact (MK_COMB (@lem6186331) (@lem6186330 _123419 op)). Qed.
Lemma lem6186333 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term549 _123419 op x) = (term484 _123419 op x).
Proof. exact (eq_refl (term549 _123419 op x)). Qed.
Lemma lem6186334 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6186335 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term558 _123419 op x) = (term559 _123419 op x).
Proof. exact (MK_COMB (@lem6186334) (@lem6186333 _123419 op x)). Qed.
Lemma lem6186336 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term553 _123419 op x) = (term496 _123419 op x).
Proof. exact (eq_refl (term553 _123419 op x)). Qed.
Lemma lem6186337 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term560 _123419 op x) = (term561 _123419 op x).
Proof. exact (MK_COMB (@lem6186335 _123419 op x) (@lem6186336 _123419 op x)). Qed.
Lemma lem6186338 {_123419 : Type'} (op : type1400 _123419) : (term562 _123419 op) = (term563 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6186337 _123419 op x)). Qed.
Lemma lem6186339 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186340 {_123419 : Type'} (op : type1400 _123419) : (term548 _123419 op) = (term564 _123419 op).
Proof. exact (MK_COMB (@lem6186339 _123419) (@lem6186338 _123419 op)). Qed.
Lemma lem6186341 {_123419 : Type'} (op : type1400 _123419) : ((term547 _123419 op) = (term548 _123419 op)) = ((term503 _123419 op) = (term564 _123419 op)).
Proof. exact (MK_COMB (@lem6186332 _123419 op) (@lem6186340 _123419 op)). Qed.
Lemma lem6186342 {_123419 : Type'} (op : type1400 _123419) : (term503 _123419 op) = (term564 _123419 op).
Proof. exact (EQ_MP (@lem6186341 _123419 op) (@lem6186319 _123419 op)). Qed.
Lemma lem6186344 {A : Type'} (P : A -> Prop) (Q : Prop) : (term565 A P Q) = (term566 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6186345 {_123419 : Type'} (P : _123419 -> Prop) (Q : Prop) : (term565 _123419 P Q) = (term566 _123419 P Q).
Proof. exact (@lem6186344 _123419 P Q). Qed.
Lemma lem6186346 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term567 _123419 op x) = (term568 _123419 op x).
Proof. exact (@lem6186345 _123419 (term483 _123419 op x) (term496 _123419 op x)). Qed.
Lemma lem6186347 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term569 _123419 op x y) = (term477 _123419 op x y).
Proof. exact (eq_refl (term569 _123419 op x y)). Qed.
Lemma lem6186348 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term570 _123419 op x) = (term483 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6186347 _123419 op x y)). Qed.
Lemma lem6186349 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186350 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term571 _123419 op x) = (term484 _123419 op x).
Proof. exact (MK_COMB (@lem6186349 _123419) (@lem6186348 _123419 op x)). Qed.
Lemma lem6186351 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6186352 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term572 _123419 op x) = (term559 _123419 op x).
Proof. exact (MK_COMB (@lem6186351) (@lem6186350 _123419 op x)). Qed.
Lemma lem6186353 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term496 _123419 op x) = (term496 _123419 op x).
Proof. exact (eq_refl (term496 _123419 op x)). Qed.
Lemma lem6186354 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term567 _123419 op x) = (term561 _123419 op x).
Proof. exact (MK_COMB (@lem6186352 _123419 op x) (@lem6186353 _123419 op x)). Qed.
Lemma lem6186355 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6186356 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term573 _123419 op x) = (term574 _123419 op x).
Proof. exact (MK_COMB (@lem6186355) (@lem6186354 _123419 op x)). Qed.
Lemma lem6186357 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term569 _123419 op x y) = (term477 _123419 op x y).
Proof. exact (eq_refl (term569 _123419 op x y)). Qed.
Lemma lem6186358 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6186359 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term575 _123419 op x y) = (term576 _123419 op x y).
Proof. exact (MK_COMB (@lem6186358) (@lem6186357 _123419 op x y)). Qed.
Lemma lem6186360 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term496 _123419 op x) = (term496 _123419 op x).
Proof. exact (eq_refl (term496 _123419 op x)). Qed.
Lemma lem6186361 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term577 _123419 y op x) = (term578 _123419 y op x).
Proof. exact (MK_COMB (@lem6186359 _123419 op x y) (@lem6186360 _123419 op x)). Qed.
Lemma lem6186362 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term579 _123419 op x) = (term580 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6186361 _123419 y op x)). Qed.
Lemma lem6186363 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186364 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term568 _123419 op x) = (term581 _123419 op x).
Proof. exact (MK_COMB (@lem6186363 _123419) (@lem6186362 _123419 op x)). Qed.
Lemma lem6186365 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : ((term567 _123419 op x) = (term568 _123419 op x)) = ((term561 _123419 op x) = (term581 _123419 op x)).
Proof. exact (MK_COMB (@lem6186356 _123419 op x) (@lem6186364 _123419 op x)). Qed.
Lemma lem6186366 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term561 _123419 op x) = (term581 _123419 op x).
Proof. exact (EQ_MP (@lem6186365 _123419 op x) (@lem6186346 _123419 op x)). Qed.
Lemma lem6186368 {A : Type'} (P : A -> Prop) (Q : Prop) : (term565 A P Q) = (term566 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6186369 {_123419 : Type'} (P : _123419 -> Prop) (Q : Prop) : (term565 _123419 P Q) = (term566 _123419 P Q).
Proof. exact (@lem6186368 _123419 P Q). Qed.
Lemma lem6186370 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term582 _123419 y op x) = (term583 _123419 y op x).
Proof. exact (@lem6186369 _123419 (term476 _123419 op x y) (term496 _123419 op x)). Qed.
Lemma lem6186371 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : (term584 _123419 op x y z) = (term474 _123419 op x y z).
Proof. exact (eq_refl (term584 _123419 op x y z)). Qed.
Lemma lem6186372 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term585 _123419 op x y) = (term476 _123419 op x y).
Proof. exact (fun_ext (fun z : _123419 => @lem6186371 _123419 op x y z)). Qed.
Lemma lem6186373 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186374 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term586 _123419 op x y) = (term477 _123419 op x y).
Proof. exact (MK_COMB (@lem6186373 _123419) (@lem6186372 _123419 op x y)). Qed.
Lemma lem6186375 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6186376 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term587 _123419 op x y) = (term576 _123419 op x y).
Proof. exact (MK_COMB (@lem6186375) (@lem6186374 _123419 op x y)). Qed.
Lemma lem6186377 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term496 _123419 op x) = (term496 _123419 op x).
Proof. exact (eq_refl (term496 _123419 op x)). Qed.
Lemma lem6186378 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term582 _123419 y op x) = (term578 _123419 y op x).
Proof. exact (MK_COMB (@lem6186376 _123419 op x y) (@lem6186377 _123419 op x)). Qed.
Lemma lem6186379 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6186380 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term588 _123419 y op x) = (term589 _123419 y op x).
Proof. exact (MK_COMB (@lem6186379) (@lem6186378 _123419 y op x)). Qed.
Lemma lem6186381 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : (term584 _123419 op x y z) = (term474 _123419 op x y z).
Proof. exact (eq_refl (term584 _123419 op x y z)). Qed.
Lemma lem6186382 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6186383 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : (term590 _123419 op x y z) = (term591 _123419 op x y z).
Proof. exact (MK_COMB (@lem6186382) (@lem6186381 _123419 op x y z)). Qed.
Lemma lem6186384 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term496 _123419 op x) = (term496 _123419 op x).
Proof. exact (eq_refl (term496 _123419 op x)). Qed.
Lemma lem6186385 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term592 _123419 y z op x) = (term593 _123419 y z op x).
Proof. exact (MK_COMB (@lem6186383 _123419 op x y z) (@lem6186384 _123419 op x)). Qed.
Lemma lem6186386 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term594 _123419 y op x) = (term595 _123419 y op x).
Proof. exact (fun_ext (fun z : _123419 => @lem6186385 _123419 y z op x)). Qed.
Lemma lem6186387 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186388 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term583 _123419 y op x) = (term596 _123419 y op x).
Proof. exact (MK_COMB (@lem6186387 _123419) (@lem6186386 _123419 y op x)). Qed.
Lemma lem6186389 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : ((term582 _123419 y op x) = (term583 _123419 y op x)) = ((term578 _123419 y op x) = (term596 _123419 y op x)).
Proof. exact (MK_COMB (@lem6186380 _123419 y op x) (@lem6186388 _123419 y op x)). Qed.
Lemma lem6186390 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term578 _123419 y op x) = (term596 _123419 y op x).
Proof. exact (EQ_MP (@lem6186389 _123419 y op x) (@lem6186370 _123419 y op x)). Qed.
Lemma lem6186391 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term580 _123419 op x) = (term597 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6186390 _123419 y op x)). Qed.
Lemma lem6186392 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186393 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term581 _123419 op x) = (term598 _123419 op x).
Proof. exact (MK_COMB (@lem6186392 _123419) (@lem6186391 _123419 op x)). Qed.
Lemma lem6186394 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term561 _123419 op x) = (term598 _123419 op x).
Proof. exact (TRANS (@lem6186366 _123419 op x) (@lem6186393 _123419 op x)). Qed.
Lemma lem6186395 {_123419 : Type'} (op : type1400 _123419) : (term563 _123419 op) = (term599 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6186394 _123419 op x)). Qed.
Lemma lem6186396 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186397 {_123419 : Type'} (op : type1400 _123419) : (term564 _123419 op) = (term600 _123419 op).
Proof. exact (MK_COMB (@lem6186396 _123419) (@lem6186395 _123419 op)). Qed.
Lemma lem6186398 {_123419 : Type'} (op : type1400 _123419) : (term503 _123419 op) = (term600 _123419 op).
Proof. exact (TRANS (@lem6186342 _123419 op) (@lem6186397 _123419 op)). Qed.
Lemma lem6186399 {_123419 : Type'} (op : type1400 _123419) : (term506 _123419 op) = (term506 _123419 op).
Proof. exact (eq_refl (term506 _123419 op)). Qed.
Lemma lem6186400 {_123419 : Type'} (op : type1400 _123419) : (term508 _123419 op) = (term601 _123419 op).
Proof. exact (MK_COMB (@lem6186399 _123419 op) (@lem6186398 _123419 op)). Qed.
Lemma lem6186402 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term545 A P Q) = (term546 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6186403 {_123419 : Type'} (P : _123419 -> Prop) (Q : _123419 -> Prop) : (term545 _123419 P Q) = (term546 _123419 P Q).
Proof. exact (@lem6186402 _123419 P Q). Qed.
Lemma lem6186404 {_123419 : Type'} (op : type1400 _123419) : (term602 _123419 op) = (term603 _123419 op).
Proof. exact (@lem6186403 _123419 (term468 _123419 op) (term599 _123419 op)). Qed.
Lemma lem6186405 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term604 _123419 op x) = (term462 _123419 op x).
Proof. exact (eq_refl (term604 _123419 op x)). Qed.
Lemma lem6186406 {_123419 : Type'} (op : type1400 _123419) : (term605 _123419 op) = (term468 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6186405 _123419 op x)). Qed.
Lemma lem6186407 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186408 {_123419 : Type'} (op : type1400 _123419) : (term606 _123419 op) = (term469 _123419 op).
Proof. exact (MK_COMB (@lem6186407 _123419) (@lem6186406 _123419 op)). Qed.
Lemma lem6186409 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6186410 {_123419 : Type'} (op : type1400 _123419) : (term607 _123419 op) = (term506 _123419 op).
Proof. exact (MK_COMB (@lem6186409) (@lem6186408 _123419 op)). Qed.
Lemma lem6186411 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term608 _123419 op x) = (term598 _123419 op x).
Proof. exact (eq_refl (term608 _123419 op x)). Qed.
Lemma lem6186412 {_123419 : Type'} (op : type1400 _123419) : (term609 _123419 op) = (term599 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6186411 _123419 op x)). Qed.
Lemma lem6186413 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186414 {_123419 : Type'} (op : type1400 _123419) : (term610 _123419 op) = (term600 _123419 op).
Proof. exact (MK_COMB (@lem6186413 _123419) (@lem6186412 _123419 op)). Qed.
Lemma lem6186415 {_123419 : Type'} (op : type1400 _123419) : (term602 _123419 op) = (term601 _123419 op).
Proof. exact (MK_COMB (@lem6186410 _123419 op) (@lem6186414 _123419 op)). Qed.
Lemma lem6186416 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6186417 {_123419 : Type'} (op : type1400 _123419) : (term611 _123419 op) = (term612 _123419 op).
Proof. exact (MK_COMB (@lem6186416) (@lem6186415 _123419 op)). Qed.
Lemma lem6186418 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term604 _123419 op x) = (term462 _123419 op x).
Proof. exact (eq_refl (term604 _123419 op x)). Qed.
Lemma lem6186419 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6186420 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term613 _123419 op x) = (term614 _123419 op x).
Proof. exact (MK_COMB (@lem6186419) (@lem6186418 _123419 op x)). Qed.
Lemma lem6186421 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term608 _123419 op x) = (term598 _123419 op x).
Proof. exact (eq_refl (term608 _123419 op x)). Qed.
Lemma lem6186422 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term615 _123419 op x) = (term616 _123419 op x).
Proof. exact (MK_COMB (@lem6186420 _123419 op x) (@lem6186421 _123419 op x)). Qed.
Lemma lem6186423 {_123419 : Type'} (op : type1400 _123419) : (term617 _123419 op) = (term618 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6186422 _123419 op x)). Qed.
Lemma lem6186424 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186425 {_123419 : Type'} (op : type1400 _123419) : (term603 _123419 op) = (term619 _123419 op).
Proof. exact (MK_COMB (@lem6186424 _123419) (@lem6186423 _123419 op)). Qed.
Lemma lem6186426 {_123419 : Type'} (op : type1400 _123419) : ((term602 _123419 op) = (term603 _123419 op)) = ((term601 _123419 op) = (term619 _123419 op)).
Proof. exact (MK_COMB (@lem6186417 _123419 op) (@lem6186425 _123419 op)). Qed.
Lemma lem6186427 {_123419 : Type'} (op : type1400 _123419) : (term601 _123419 op) = (term619 _123419 op).
Proof. exact (EQ_MP (@lem6186426 _123419 op) (@lem6186404 _123419 op)). Qed.
Lemma lem6186429 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term545 A P Q) = (term546 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6186430 {_123419 : Type'} (P : _123419 -> Prop) (Q : _123419 -> Prop) : (term545 _123419 P Q) = (term546 _123419 P Q).
Proof. exact (@lem6186429 _123419 P Q). Qed.
Lemma lem6186431 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term620 _123419 op x) = (term621 _123419 op x).
Proof. exact (@lem6186430 _123419 (term461 _123419 op x) (term597 _123419 op x)). Qed.
Lemma lem6186432 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (term622 _123419 op x y) = (term459 _123419 op y x).
Proof. exact (eq_refl (term622 _123419 op x y)). Qed.
Lemma lem6186433 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term623 _123419 op x) = (term461 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6186432 _123419 op y x)). Qed.
Lemma lem6186434 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186435 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term624 _123419 op x) = (term462 _123419 op x).
Proof. exact (MK_COMB (@lem6186434 _123419) (@lem6186433 _123419 op x)). Qed.
Lemma lem6186436 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6186437 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term625 _123419 op x) = (term614 _123419 op x).
Proof. exact (MK_COMB (@lem6186436) (@lem6186435 _123419 op x)). Qed.
Lemma lem6186438 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term626 _123419 op x y) = (term596 _123419 y op x).
Proof. exact (eq_refl (term626 _123419 op x y)). Qed.
Lemma lem6186439 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term627 _123419 op x) = (term597 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6186438 _123419 y op x)). Qed.
Lemma lem6186440 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186441 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term628 _123419 op x) = (term598 _123419 op x).
Proof. exact (MK_COMB (@lem6186440 _123419) (@lem6186439 _123419 op x)). Qed.
Lemma lem6186442 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term620 _123419 op x) = (term616 _123419 op x).
Proof. exact (MK_COMB (@lem6186437 _123419 op x) (@lem6186441 _123419 op x)). Qed.
Lemma lem6186443 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6186444 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term629 _123419 op x) = (term630 _123419 op x).
Proof. exact (MK_COMB (@lem6186443) (@lem6186442 _123419 op x)). Qed.
Lemma lem6186445 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (term622 _123419 op x y) = (term459 _123419 op y x).
Proof. exact (eq_refl (term622 _123419 op x y)). Qed.
Lemma lem6186446 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6186447 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (term631 _123419 op x y) = (term632 _123419 op y x).
Proof. exact (MK_COMB (@lem6186446) (@lem6186445 _123419 op y x)). Qed.
Lemma lem6186448 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term626 _123419 op x y) = (term596 _123419 y op x).
Proof. exact (eq_refl (term626 _123419 op x y)). Qed.
Lemma lem6186449 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term633 _123419 op x y) = (term634 _123419 y op x).
Proof. exact (MK_COMB (@lem6186447 _123419 op y x) (@lem6186448 _123419 y op x)). Qed.
Lemma lem6186450 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term635 _123419 op x) = (term636 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6186449 _123419 y op x)). Qed.
Lemma lem6186451 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186452 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term621 _123419 op x) = (term637 _123419 op x).
Proof. exact (MK_COMB (@lem6186451 _123419) (@lem6186450 _123419 op x)). Qed.
Lemma lem6186453 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : ((term620 _123419 op x) = (term621 _123419 op x)) = ((term616 _123419 op x) = (term637 _123419 op x)).
Proof. exact (MK_COMB (@lem6186444 _123419 op x) (@lem6186452 _123419 op x)). Qed.
Lemma lem6186454 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term616 _123419 op x) = (term637 _123419 op x).
Proof. exact (EQ_MP (@lem6186453 _123419 op x) (@lem6186431 _123419 op x)). Qed.
Lemma lem6186456 {A : Type'} (P : Prop) (Q : A -> Prop) : (term638 A P Q) = (term639 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6186457 {_123419 : Type'} (P : Prop) (Q : _123419 -> Prop) : (term638 _123419 P Q) = (term639 _123419 P Q).
Proof. exact (@lem6186456 _123419 P Q). Qed.
Lemma lem6186458 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term640 _123419 y op x) = (term641 _123419 y op x).
Proof. exact (@lem6186457 _123419 (term459 _123419 op y x) (term595 _123419 y op x)). Qed.
Lemma lem6186459 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term642 _123419 y op x z) = (term593 _123419 y z op x).
Proof. exact (eq_refl (term642 _123419 y op x z)). Qed.
Lemma lem6186460 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term643 _123419 y op x) = (term595 _123419 y op x).
Proof. exact (fun_ext (fun z : _123419 => @lem6186459 _123419 y z op x)). Qed.
Lemma lem6186461 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186462 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term644 _123419 y op x) = (term596 _123419 y op x).
Proof. exact (MK_COMB (@lem6186461 _123419) (@lem6186460 _123419 y op x)). Qed.
Lemma lem6186463 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (term632 _123419 op y x) = (term632 _123419 op y x).
Proof. exact (eq_refl (term632 _123419 op y x)). Qed.
Lemma lem6186464 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term640 _123419 y op x) = (term634 _123419 y op x).
Proof. exact (MK_COMB (@lem6186463 _123419 op y x) (@lem6186462 _123419 y op x)). Qed.
Lemma lem6186465 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6186466 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term645 _123419 y op x) = (term646 _123419 y op x).
Proof. exact (MK_COMB (@lem6186465) (@lem6186464 _123419 y op x)). Qed.
Lemma lem6186467 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term642 _123419 y op x z) = (term593 _123419 y z op x).
Proof. exact (eq_refl (term642 _123419 y op x z)). Qed.
Lemma lem6186468 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (term632 _123419 op y x) = (term632 _123419 op y x).
Proof. exact (eq_refl (term632 _123419 op y x)). Qed.
Lemma lem6186469 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term647 _123419 y op x z) = (term648 _123419 y z op x).
Proof. exact (MK_COMB (@lem6186468 _123419 op y x) (@lem6186467 _123419 y z op x)). Qed.
Lemma lem6186470 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term649 _123419 y op x) = (term650 _123419 y op x).
Proof. exact (fun_ext (fun z : _123419 => @lem6186469 _123419 y z op x)). Qed.
Lemma lem6186471 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186472 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term641 _123419 y op x) = (term651 _123419 y op x).
Proof. exact (MK_COMB (@lem6186471 _123419) (@lem6186470 _123419 y op x)). Qed.
Lemma lem6186473 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : ((term640 _123419 y op x) = (term641 _123419 y op x)) = ((term634 _123419 y op x) = (term651 _123419 y op x)).
Proof. exact (MK_COMB (@lem6186466 _123419 y op x) (@lem6186472 _123419 y op x)). Qed.
Lemma lem6186474 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term634 _123419 y op x) = (term651 _123419 y op x).
Proof. exact (EQ_MP (@lem6186473 _123419 y op x) (@lem6186458 _123419 y op x)). Qed.
Lemma lem6186475 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term636 _123419 op x) = (term652 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6186474 _123419 y op x)). Qed.
Lemma lem6186476 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186477 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term637 _123419 op x) = (term653 _123419 op x).
Proof. exact (MK_COMB (@lem6186476 _123419) (@lem6186475 _123419 op x)). Qed.
Lemma lem6186478 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term616 _123419 op x) = (term653 _123419 op x).
Proof. exact (TRANS (@lem6186454 _123419 op x) (@lem6186477 _123419 op x)). Qed.
Lemma lem6186479 {_123419 : Type'} (op : type1400 _123419) : (term618 _123419 op) = (term654 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6186478 _123419 op x)). Qed.
Lemma lem6186480 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186481 {_123419 : Type'} (op : type1400 _123419) : (term619 _123419 op) = (term655 _123419 op).
Proof. exact (MK_COMB (@lem6186480 _123419) (@lem6186479 _123419 op)). Qed.
Lemma lem6186482 {_123419 : Type'} (op : type1400 _123419) : (term601 _123419 op) = (term655 _123419 op).
Proof. exact (TRANS (@lem6186427 _123419 op) (@lem6186481 _123419 op)). Qed.
Lemma lem6186483 {_123419 : Type'} (op : type1400 _123419) : (term508 _123419 op) = (term655 _123419 op).
Proof. exact (TRANS (@lem6186400 _123419 op) (@lem6186482 _123419 op)). Qed.
Lemma lem6186484 {_123419 : Type'} (op : type1400 _123419) : (term512 _123419 op) = (term512 _123419 op).
Proof. exact (eq_refl (term512 _123419 op)). Qed.
Lemma lem6186485 {_123419 : Type'} (op : type1400 _123419) : (term514 _123419 op) = (term656 _123419 op).
Proof. exact (MK_COMB (@lem6186484 _123419 op) (@lem6186483 _123419 op)). Qed.
Lemma lem6186487 {A : Type'} (P : Prop) (Q : A -> Prop) : (term638 A P Q) = (term639 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6186488 {_123419 : Type'} (P : Prop) (Q : _123419 -> Prop) : (term638 _123419 P Q) = (term639 _123419 P Q).
Proof. exact (@lem6186487 _123419 P Q). Qed.
Lemma lem6186489 {_123419 : Type'} (op : type1400 _123419) : (term657 _123419 op) = (term658 _123419 op).
Proof. exact (@lem6186488 _123419 (@monoidal _123419 op) (term654 _123419 op)). Qed.
Lemma lem6186490 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term659 _123419 op x) = (term653 _123419 op x).
Proof. exact (eq_refl (term659 _123419 op x)). Qed.
Lemma lem6186491 {_123419 : Type'} (op : type1400 _123419) : (term660 _123419 op) = (term654 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6186490 _123419 op x)). Qed.
Lemma lem6186492 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186493 {_123419 : Type'} (op : type1400 _123419) : (term661 _123419 op) = (term655 _123419 op).
Proof. exact (MK_COMB (@lem6186492 _123419) (@lem6186491 _123419 op)). Qed.
Lemma lem6186494 {_123419 : Type'} (op : type1400 _123419) : (term512 _123419 op) = (term512 _123419 op).
Proof. exact (eq_refl (term512 _123419 op)). Qed.
Lemma lem6186495 {_123419 : Type'} (op : type1400 _123419) : (term657 _123419 op) = (term656 _123419 op).
Proof. exact (MK_COMB (@lem6186494 _123419 op) (@lem6186493 _123419 op)). Qed.
Lemma lem6186496 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6186497 {_123419 : Type'} (op : type1400 _123419) : (term662 _123419 op) = (term663 _123419 op).
Proof. exact (MK_COMB (@lem6186496) (@lem6186495 _123419 op)). Qed.
Lemma lem6186498 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term659 _123419 op x) = (term653 _123419 op x).
Proof. exact (eq_refl (term659 _123419 op x)). Qed.
Lemma lem6186499 {_123419 : Type'} (op : type1400 _123419) : (term512 _123419 op) = (term512 _123419 op).
Proof. exact (eq_refl (term512 _123419 op)). Qed.
Lemma lem6186500 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term664 _123419 op x) = (term665 _123419 op x).
Proof. exact (MK_COMB (@lem6186499 _123419 op) (@lem6186498 _123419 op x)). Qed.
Lemma lem6186501 {_123419 : Type'} (op : type1400 _123419) : (term666 _123419 op) = (term667 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6186500 _123419 op x)). Qed.
Lemma lem6186502 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186503 {_123419 : Type'} (op : type1400 _123419) : (term658 _123419 op) = (term668 _123419 op).
Proof. exact (MK_COMB (@lem6186502 _123419) (@lem6186501 _123419 op)). Qed.
Lemma lem6186504 {_123419 : Type'} (op : type1400 _123419) : ((term657 _123419 op) = (term658 _123419 op)) = ((term656 _123419 op) = (term668 _123419 op)).
Proof. exact (MK_COMB (@lem6186497 _123419 op) (@lem6186503 _123419 op)). Qed.
Lemma lem6186505 {_123419 : Type'} (op : type1400 _123419) : (term656 _123419 op) = (term668 _123419 op).
Proof. exact (EQ_MP (@lem6186504 _123419 op) (@lem6186489 _123419 op)). Qed.
Lemma lem6186507 {A : Type'} (P : Prop) (Q : A -> Prop) : (term638 A P Q) = (term639 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6186508 {_123419 : Type'} (P : Prop) (Q : _123419 -> Prop) : (term638 _123419 P Q) = (term639 _123419 P Q).
Proof. exact (@lem6186507 _123419 P Q). Qed.
Lemma lem6186509 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term669 _123419 op x) = (term670 _123419 op x).
Proof. exact (@lem6186508 _123419 (@monoidal _123419 op) (term652 _123419 op x)). Qed.
Lemma lem6186510 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term671 _123419 op x y) = (term651 _123419 y op x).
Proof. exact (eq_refl (term671 _123419 op x y)). Qed.
Lemma lem6186511 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term672 _123419 op x) = (term652 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6186510 _123419 y op x)). Qed.
Lemma lem6186512 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186513 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term673 _123419 op x) = (term653 _123419 op x).
Proof. exact (MK_COMB (@lem6186512 _123419) (@lem6186511 _123419 op x)). Qed.
Lemma lem6186514 {_123419 : Type'} (op : type1400 _123419) : (term512 _123419 op) = (term512 _123419 op).
Proof. exact (eq_refl (term512 _123419 op)). Qed.
Lemma lem6186515 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term669 _123419 op x) = (term665 _123419 op x).
Proof. exact (MK_COMB (@lem6186514 _123419 op) (@lem6186513 _123419 op x)). Qed.
Lemma lem6186516 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6186517 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term674 _123419 op x) = (term675 _123419 op x).
Proof. exact (MK_COMB (@lem6186516) (@lem6186515 _123419 op x)). Qed.
Lemma lem6186518 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term671 _123419 op x y) = (term651 _123419 y op x).
Proof. exact (eq_refl (term671 _123419 op x y)). Qed.
Lemma lem6186519 {_123419 : Type'} (op : type1400 _123419) : (term512 _123419 op) = (term512 _123419 op).
Proof. exact (eq_refl (term512 _123419 op)). Qed.
Lemma lem6186520 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term676 _123419 op x y) = (term677 _123419 y op x).
Proof. exact (MK_COMB (@lem6186519 _123419 op) (@lem6186518 _123419 y op x)). Qed.
Lemma lem6186521 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term678 _123419 op x) = (term679 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6186520 _123419 y op x)). Qed.
Lemma lem6186522 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186523 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term670 _123419 op x) = (term680 _123419 op x).
Proof. exact (MK_COMB (@lem6186522 _123419) (@lem6186521 _123419 op x)). Qed.
Lemma lem6186524 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : ((term669 _123419 op x) = (term670 _123419 op x)) = ((term665 _123419 op x) = (term680 _123419 op x)).
Proof. exact (MK_COMB (@lem6186517 _123419 op x) (@lem6186523 _123419 op x)). Qed.
Lemma lem6186525 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term665 _123419 op x) = (term680 _123419 op x).
Proof. exact (EQ_MP (@lem6186524 _123419 op x) (@lem6186509 _123419 op x)). Qed.
Lemma lem6186527 {A : Type'} (P : Prop) (Q : A -> Prop) : (term638 A P Q) = (term639 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6186528 {_123419 : Type'} (P : Prop) (Q : _123419 -> Prop) : (term638 _123419 P Q) = (term639 _123419 P Q).
Proof. exact (@lem6186527 _123419 P Q). Qed.
Lemma lem6186529 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term681 _123419 y op x) = (term682 _123419 y op x).
Proof. exact (@lem6186528 _123419 (@monoidal _123419 op) (term650 _123419 y op x)). Qed.
Lemma lem6186530 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term683 _123419 y op x z) = (term648 _123419 y z op x).
Proof. exact (eq_refl (term683 _123419 y op x z)). Qed.
Lemma lem6186531 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term684 _123419 y op x) = (term650 _123419 y op x).
Proof. exact (fun_ext (fun z : _123419 => @lem6186530 _123419 y z op x)). Qed.
Lemma lem6186532 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186533 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term685 _123419 y op x) = (term651 _123419 y op x).
Proof. exact (MK_COMB (@lem6186532 _123419) (@lem6186531 _123419 y op x)). Qed.
Lemma lem6186534 {_123419 : Type'} (op : type1400 _123419) : (term512 _123419 op) = (term512 _123419 op).
Proof. exact (eq_refl (term512 _123419 op)). Qed.
Lemma lem6186535 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term681 _123419 y op x) = (term677 _123419 y op x).
Proof. exact (MK_COMB (@lem6186534 _123419 op) (@lem6186533 _123419 y op x)). Qed.
Lemma lem6186536 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6186537 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term686 _123419 y op x) = (term687 _123419 y op x).
Proof. exact (MK_COMB (@lem6186536) (@lem6186535 _123419 y op x)). Qed.
Lemma lem6186538 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term683 _123419 y op x z) = (term648 _123419 y z op x).
Proof. exact (eq_refl (term683 _123419 y op x z)). Qed.
Lemma lem6186539 {_123419 : Type'} (op : type1400 _123419) : (term512 _123419 op) = (term512 _123419 op).
Proof. exact (eq_refl (term512 _123419 op)). Qed.
Lemma lem6186540 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term688 _123419 y op x z) = (term689 _123419 y z op x).
Proof. exact (MK_COMB (@lem6186539 _123419 op) (@lem6186538 _123419 y z op x)). Qed.
Lemma lem6186541 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term690 _123419 y op x) = (term691 _123419 y op x).
Proof. exact (fun_ext (fun z : _123419 => @lem6186540 _123419 y z op x)). Qed.
Lemma lem6186542 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186543 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term682 _123419 y op x) = (term692 _123419 y op x).
Proof. exact (MK_COMB (@lem6186542 _123419) (@lem6186541 _123419 y op x)). Qed.
Lemma lem6186544 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : ((term681 _123419 y op x) = (term682 _123419 y op x)) = ((term677 _123419 y op x) = (term692 _123419 y op x)).
Proof. exact (MK_COMB (@lem6186537 _123419 y op x) (@lem6186543 _123419 y op x)). Qed.
Lemma lem6186545 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term677 _123419 y op x) = (term692 _123419 y op x).
Proof. exact (EQ_MP (@lem6186544 _123419 y op x) (@lem6186529 _123419 y op x)). Qed.
Lemma lem6186546 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term679 _123419 op x) = (term693 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6186545 _123419 y op x)). Qed.
Lemma lem6186547 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186548 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term680 _123419 op x) = (term694 _123419 op x).
Proof. exact (MK_COMB (@lem6186547 _123419) (@lem6186546 _123419 op x)). Qed.
Lemma lem6186549 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term665 _123419 op x) = (term694 _123419 op x).
Proof. exact (TRANS (@lem6186525 _123419 op x) (@lem6186548 _123419 op x)). Qed.
Lemma lem6186550 {_123419 : Type'} (op : type1400 _123419) : (term667 _123419 op) = (term695 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6186549 _123419 op x)). Qed.
Lemma lem6186551 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186552 {_123419 : Type'} (op : type1400 _123419) : (term668 _123419 op) = (term696 _123419 op).
Proof. exact (MK_COMB (@lem6186551 _123419) (@lem6186550 _123419 op)). Qed.
Lemma lem6186553 {_123419 : Type'} (op : type1400 _123419) : (term656 _123419 op) = (term696 _123419 op).
Proof. exact (TRANS (@lem6186505 _123419 op) (@lem6186552 _123419 op)). Qed.
Lemma lem6186554 {_123419 : Type'} (op : type1400 _123419) : (term514 _123419 op) = (term696 _123419 op).
Proof. exact (TRANS (@lem6186485 _123419 op) (@lem6186553 _123419 op)). Qed.
Lemma lem6186555 {_123419 : Type'} : (term527 _123419) = (term697 _123419).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6186554 _123419 op)). Qed.
Lemma lem6186556 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6186557 {_123419 : Type'} : (term538 _123419) = (term698 _123419).
Proof. exact (MK_COMB (@lem6186556 _123419) (@lem6186555 _123419)). Qed.
Lemma lem6186559 {A B : Type'} (P : type1413 A B) : (term699 A B P) = (term700 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6186560 {_123419 : Type'} (P : type401 _123419) : (term701 _123419 P) = (term702 _123419 P).
Proof. exact (@lem6186559 (type1400 _123419) _123419 P). Qed.
Lemma lem6186561 {_123419 : Type'} : (term703 _123419) = (term704 _123419).
Proof. exact (@lem6186560 _123419 (term705 _123419)). Qed.
Lemma lem6186562 {_123419 : Type'} (op : type1400 _123419) : (term706 _123419 op) = (term695 _123419 op).
Proof. exact (eq_refl (term706 _123419 op)). Qed.
Lemma lem6186563 {_123419 : Type'} (x : _123419) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6186564 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term707 _123419 op x) = (term708 _123419 op x).
Proof. exact (MK_COMB (@lem6186562 _123419 op) (@lem6186563 _123419 x)). Qed.
Lemma lem6186565 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term708 _123419 op x) = (term694 _123419 op x).
Proof. exact (eq_refl (term708 _123419 op x)). Qed.
Lemma lem6186566 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term707 _123419 op x) = (term694 _123419 op x).
Proof. exact (TRANS (@lem6186564 _123419 op x) (@lem6186565 _123419 op x)). Qed.
Lemma lem6186567 {_123419 : Type'} (op : type1400 _123419) : (term709 _123419 op) = (term695 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6186566 _123419 op x)). Qed.
Lemma lem6186568 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186569 {_123419 : Type'} (op : type1400 _123419) : (term710 _123419 op) = (term696 _123419 op).
Proof. exact (MK_COMB (@lem6186568 _123419) (@lem6186567 _123419 op)). Qed.
Lemma lem6186570 {_123419 : Type'} : (term711 _123419) = (term697 _123419).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6186569 _123419 op)). Qed.
Lemma lem6186571 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6186572 {_123419 : Type'} : (term703 _123419) = (term698 _123419).
Proof. exact (MK_COMB (@lem6186571 _123419) (@lem6186570 _123419)). Qed.
Lemma lem6186573 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6186574 {_123419 : Type'} : (term712 _123419) = (term713 _123419).
Proof. exact (MK_COMB (@lem6186573) (@lem6186572 _123419)). Qed.
Lemma lem6186575 {_123419 : Type'} (op : type1400 _123419) : (term706 _123419 op) = (term695 _123419 op).
Proof. exact (eq_refl (term706 _123419 op)). Qed.
Lemma lem6186576 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (x op) = (x op).
Proof. exact (eq_refl (x op)). Qed.
Lemma lem6186577 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (term714 _123419 x op) = (term715 _123419 x op).
Proof. exact (MK_COMB (@lem6186575 _123419 op) (@lem6186576 _123419 x op)). Qed.
Lemma lem6186578 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (term715 _123419 x op) = (term716 _123419 x op).
Proof. exact (eq_refl (term715 _123419 x op)). Qed.
Lemma lem6186579 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (term714 _123419 x op) = (term716 _123419 x op).
Proof. exact (TRANS (@lem6186577 _123419 x op) (@lem6186578 _123419 x op)). Qed.
Lemma lem6186580 {_123419 : Type'} (x : type402 _123419) : (term717 _123419 x) = (term718 _123419 x).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6186579 _123419 x op)). Qed.
Lemma lem6186581 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6186582 {_123419 : Type'} (x : type402 _123419) : (term719 _123419 x) = (term720 _123419 x).
Proof. exact (MK_COMB (@lem6186581 _123419) (@lem6186580 _123419 x)). Qed.
Lemma lem6186583 {_123419 : Type'} : (term721 _123419) = (term722 _123419).
Proof. exact (fun_ext (fun x : type402 _123419 => @lem6186582 _123419 x)). Qed.
Lemma lem6186584 {_123419 : Type'} : (@ex ((_123419 -> _123419 -> _123419) -> _123419)) = (@ex ((_123419 -> _123419 -> _123419) -> _123419)).
Proof. exact (eq_refl (@ex ((_123419 -> _123419 -> _123419) -> _123419))). Qed.
Lemma lem6186585 {_123419 : Type'} : (term704 _123419) = (term723 _123419).
Proof. exact (MK_COMB (@lem6186584 _123419) (@lem6186583 _123419)). Qed.
Lemma lem6186586 {_123419 : Type'} : ((term703 _123419) = (term704 _123419)) = ((term698 _123419) = (term723 _123419)).
Proof. exact (MK_COMB (@lem6186574 _123419) (@lem6186585 _123419)). Qed.
Lemma lem6186587 {_123419 : Type'} : (term698 _123419) = (term723 _123419).
Proof. exact (EQ_MP (@lem6186586 _123419) (@lem6186561 _123419)). Qed.
Lemma lem6186589 {A B : Type'} (P : type1413 A B) : (term699 A B P) = (term700 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6186590 {_123419 : Type'} (P : type401 _123419) : (term701 _123419 P) = (term702 _123419 P).
Proof. exact (@lem6186589 (type1400 _123419) _123419 P). Qed.
Lemma lem6186591 {_123419 : Type'} (x : type402 _123419) : (term724 _123419 x) = (term725 _123419 x).
Proof. exact (@lem6186590 _123419 (term726 _123419 x)). Qed.
Lemma lem6186592 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (term727 _123419 x op) = (term728 _123419 x op).
Proof. exact (eq_refl (term727 _123419 x op)). Qed.
Lemma lem6186593 {_123419 : Type'} (y : _123419) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6186594 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) (y : _123419) : (term729 _123419 x op y) = (term730 _123419 x op y).
Proof. exact (MK_COMB (@lem6186592 _123419 x op) (@lem6186593 _123419 y)). Qed.
Lemma lem6186595 {_123419 : Type'} (y : _123419) (x : type402 _123419) (op : type1400 _123419) : (term730 _123419 x op y) = (term731 _123419 y x op).
Proof. exact (eq_refl (term730 _123419 x op y)). Qed.
Lemma lem6186596 {_123419 : Type'} (y : _123419) (x : type402 _123419) (op : type1400 _123419) : (term729 _123419 x op y) = (term731 _123419 y x op).
Proof. exact (TRANS (@lem6186594 _123419 x op y) (@lem6186595 _123419 y x op)). Qed.
Lemma lem6186597 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (term732 _123419 x op) = (term728 _123419 x op).
Proof. exact (fun_ext (fun y : _123419 => @lem6186596 _123419 y x op)). Qed.
Lemma lem6186598 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186599 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (term733 _123419 x op) = (term716 _123419 x op).
Proof. exact (MK_COMB (@lem6186598 _123419) (@lem6186597 _123419 x op)). Qed.
Lemma lem6186600 {_123419 : Type'} (x : type402 _123419) : (term734 _123419 x) = (term718 _123419 x).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6186599 _123419 x op)). Qed.
Lemma lem6186601 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6186602 {_123419 : Type'} (x : type402 _123419) : (term724 _123419 x) = (term720 _123419 x).
Proof. exact (MK_COMB (@lem6186601 _123419) (@lem6186600 _123419 x)). Qed.
Lemma lem6186603 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6186604 {_123419 : Type'} (x : type402 _123419) : (term735 _123419 x) = (term736 _123419 x).
Proof. exact (MK_COMB (@lem6186603) (@lem6186602 _123419 x)). Qed.
Lemma lem6186605 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (term727 _123419 x op) = (term728 _123419 x op).
Proof. exact (eq_refl (term727 _123419 x op)). Qed.
Lemma lem6186606 {_123419 : Type'} (y : type402 _123419) (op : type1400 _123419) : (y op) = (y op).
Proof. exact (eq_refl (y op)). Qed.
Lemma lem6186607 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (op : type1400 _123419) : (term737 _123419 x y op) = (term738 _123419 x y op).
Proof. exact (MK_COMB (@lem6186605 _123419 x op) (@lem6186606 _123419 y op)). Qed.
Lemma lem6186608 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) (op : type1400 _123419) : (term738 _123419 x y op) = (term739 _123419 y x op).
Proof. exact (eq_refl (term738 _123419 x y op)). Qed.
Lemma lem6186609 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) (op : type1400 _123419) : (term737 _123419 x y op) = (term739 _123419 y x op).
Proof. exact (TRANS (@lem6186607 _123419 x y op) (@lem6186608 _123419 y x op)). Qed.
Lemma lem6186610 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term740 _123419 x y) = (term741 _123419 y x).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6186609 _123419 y x op)). Qed.
Lemma lem6186611 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6186612 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term742 _123419 x y) = (term743 _123419 y x).
Proof. exact (MK_COMB (@lem6186611 _123419) (@lem6186610 _123419 y x)). Qed.
Lemma lem6186613 {_123419 : Type'} (x : type402 _123419) : (term744 _123419 x) = (term745 _123419 x).
Proof. exact (fun_ext (fun y : type402 _123419 => @lem6186612 _123419 y x)). Qed.
Lemma lem6186614 {_123419 : Type'} : (@ex ((_123419 -> _123419 -> _123419) -> _123419)) = (@ex ((_123419 -> _123419 -> _123419) -> _123419)).
Proof. exact (eq_refl (@ex ((_123419 -> _123419 -> _123419) -> _123419))). Qed.
Lemma lem6186615 {_123419 : Type'} (x : type402 _123419) : (term725 _123419 x) = (term746 _123419 x).
Proof. exact (MK_COMB (@lem6186614 _123419) (@lem6186613 _123419 x)). Qed.
Lemma lem6186616 {_123419 : Type'} (x : type402 _123419) : ((term724 _123419 x) = (term725 _123419 x)) = ((term720 _123419 x) = (term746 _123419 x)).
Proof. exact (MK_COMB (@lem6186604 _123419 x) (@lem6186615 _123419 x)). Qed.
Lemma lem6186617 {_123419 : Type'} (x : type402 _123419) : (term720 _123419 x) = (term746 _123419 x).
Proof. exact (EQ_MP (@lem6186616 _123419 x) (@lem6186591 _123419 x)). Qed.
Lemma lem6186619 {A B : Type'} (P : type1413 A B) : (term699 A B P) = (term700 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6186620 {_123419 : Type'} (P : type401 _123419) : (term701 _123419 P) = (term702 _123419 P).
Proof. exact (@lem6186619 (type1400 _123419) _123419 P). Qed.
Lemma lem6186621 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term747 _123419 y x) = (term748 _123419 y x).
Proof. exact (@lem6186620 _123419 (term749 _123419 y x)). Qed.
Lemma lem6186622 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) (op : type1400 _123419) : (term750 _123419 y x op) = (term751 _123419 y x op).
Proof. exact (eq_refl (term750 _123419 y x op)). Qed.
Lemma lem6186623 {_123419 : Type'} (z : _123419) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem6186624 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) (op : type1400 _123419) (z : _123419) : (term752 _123419 y x op z) = (term753 _123419 y x op z).
Proof. exact (MK_COMB (@lem6186622 _123419 y x op) (@lem6186623 _123419 z)). Qed.
Lemma lem6186625 {_123419 : Type'} (y : type402 _123419) (z : _123419) (x : type402 _123419) (op : type1400 _123419) : (term753 _123419 y x op z) = (term754 _123419 y z x op).
Proof. exact (eq_refl (term753 _123419 y x op z)). Qed.
Lemma lem6186626 {_123419 : Type'} (y : type402 _123419) (z : _123419) (x : type402 _123419) (op : type1400 _123419) : (term752 _123419 y x op z) = (term754 _123419 y z x op).
Proof. exact (TRANS (@lem6186624 _123419 y x op z) (@lem6186625 _123419 y z x op)). Qed.
Lemma lem6186627 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) (op : type1400 _123419) : (term755 _123419 y x op) = (term751 _123419 y x op).
Proof. exact (fun_ext (fun z : _123419 => @lem6186626 _123419 y z x op)). Qed.
Lemma lem6186628 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6186629 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) (op : type1400 _123419) : (term756 _123419 y x op) = (term739 _123419 y x op).
Proof. exact (MK_COMB (@lem6186628 _123419) (@lem6186627 _123419 y x op)). Qed.
Lemma lem6186630 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term757 _123419 y x) = (term741 _123419 y x).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6186629 _123419 y x op)). Qed.
Lemma lem6186631 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6186632 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term747 _123419 y x) = (term743 _123419 y x).
Proof. exact (MK_COMB (@lem6186631 _123419) (@lem6186630 _123419 y x)). Qed.
Lemma lem6186633 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6186634 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term758 _123419 y x) = (term759 _123419 y x).
Proof. exact (MK_COMB (@lem6186633) (@lem6186632 _123419 y x)). Qed.
Lemma lem6186635 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) (op : type1400 _123419) : (term750 _123419 y x op) = (term751 _123419 y x op).
Proof. exact (eq_refl (term750 _123419 y x op)). Qed.
Lemma lem6186636 {_123419 : Type'} (z : type402 _123419) (op : type1400 _123419) : (z op) = (z op).
Proof. exact (eq_refl (z op)). Qed.
Lemma lem6186637 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) (z : type402 _123419) (op : type1400 _123419) : (term760 _123419 y x z op) = (term761 _123419 y x z op).
Proof. exact (MK_COMB (@lem6186635 _123419 y x op) (@lem6186636 _123419 z op)). Qed.
Lemma lem6186638 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (op : type1400 _123419) : (term761 _123419 y x z op) = (term762 _123419 y z x op).
Proof. exact (eq_refl (term761 _123419 y x z op)). Qed.
Lemma lem6186639 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (op : type1400 _123419) : (term760 _123419 y x z op) = (term762 _123419 y z x op).
Proof. exact (TRANS (@lem6186637 _123419 y x z op) (@lem6186638 _123419 y z x op)). Qed.
Lemma lem6186640 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) : (term763 _123419 y x z) = (term764 _123419 y z x).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6186639 _123419 y z x op)). Qed.
Lemma lem6186641 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6186642 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) : (term765 _123419 y x z) = (term766 _123419 y z x).
Proof. exact (MK_COMB (@lem6186641 _123419) (@lem6186640 _123419 y z x)). Qed.
Lemma lem6186643 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term767 _123419 y x) = (term768 _123419 y x).
Proof. exact (fun_ext (fun z : type402 _123419 => @lem6186642 _123419 y z x)). Qed.
Lemma lem6186644 {_123419 : Type'} : (@ex ((_123419 -> _123419 -> _123419) -> _123419)) = (@ex ((_123419 -> _123419 -> _123419) -> _123419)).
Proof. exact (eq_refl (@ex ((_123419 -> _123419 -> _123419) -> _123419))). Qed.
Lemma lem6186645 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term748 _123419 y x) = (term769 _123419 y x).
Proof. exact (MK_COMB (@lem6186644 _123419) (@lem6186643 _123419 y x)). Qed.
Lemma lem6186646 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : ((term747 _123419 y x) = (term748 _123419 y x)) = ((term743 _123419 y x) = (term769 _123419 y x)).
Proof. exact (MK_COMB (@lem6186634 _123419 y x) (@lem6186645 _123419 y x)). Qed.
Lemma lem6186647 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term743 _123419 y x) = (term769 _123419 y x).
Proof. exact (EQ_MP (@lem6186646 _123419 y x) (@lem6186621 _123419 y x)). Qed.
Lemma lem6186648 {_123419 : Type'} (x : type402 _123419) : (term745 _123419 x) = (term770 _123419 x).
Proof. exact (fun_ext (fun y : type402 _123419 => @lem6186647 _123419 y x)). Qed.
Lemma lem6186649 {_123419 : Type'} : (@ex ((_123419 -> _123419 -> _123419) -> _123419)) = (@ex ((_123419 -> _123419 -> _123419) -> _123419)).
Proof. exact (eq_refl (@ex ((_123419 -> _123419 -> _123419) -> _123419))). Qed.
Lemma lem6186650 {_123419 : Type'} (x : type402 _123419) : (term746 _123419 x) = (term771 _123419 x).
Proof. exact (MK_COMB (@lem6186649 _123419) (@lem6186648 _123419 x)). Qed.
Lemma lem6186651 {_123419 : Type'} (x : type402 _123419) : (term720 _123419 x) = (term771 _123419 x).
Proof. exact (TRANS (@lem6186617 _123419 x) (@lem6186650 _123419 x)). Qed.
Lemma lem6186652 {_123419 : Type'} : (term722 _123419) = (term772 _123419).
Proof. exact (fun_ext (fun x : type402 _123419 => @lem6186651 _123419 x)). Qed.
Lemma lem6186653 {_123419 : Type'} : (@ex ((_123419 -> _123419 -> _123419) -> _123419)) = (@ex ((_123419 -> _123419 -> _123419) -> _123419)).
Proof. exact (eq_refl (@ex ((_123419 -> _123419 -> _123419) -> _123419))). Qed.
Lemma lem6186654 {_123419 : Type'} : (term723 _123419) = (term773 _123419).
Proof. exact (MK_COMB (@lem6186653 _123419) (@lem6186652 _123419)). Qed.
Lemma lem6186655 {_123419 : Type'} : (term698 _123419) = (term773 _123419).
Proof. exact (TRANS (@lem6186587 _123419) (@lem6186654 _123419)). Qed.
Lemma lem6186656 {_123419 : Type'} : (term538 _123419) = (term773 _123419).
Proof. exact (TRANS (@lem6186557 _123419) (@lem6186655 _123419)). Qed.
Lemma lem6186657 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6186658 {_123419 : Type'} : (term540 _123419) = (term774 _123419).
Proof. exact (MK_COMB (@lem6186657) (@lem6186656 _123419)). Qed.
Lemma lem6186659 {_123419 : Type'} : (term543 _123419) = (term543 _123419).
Proof. exact (eq_refl (term543 _123419)). Qed.
Lemma lem6186660 {_123419 : Type'} : (term544 _123419) = (term775 _123419).
Proof. exact (MK_COMB (@lem6186658 _123419) (@lem6186659 _123419)). Qed.
Lemma lem6186662 {A : Type'} (P : A -> Prop) (Q : Prop) : (term776 A P Q) = (term777 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6186663 {_123419 : Type'} (P : type82 _123419) (Q : Prop) : (term778 _123419 P Q) = (term779 _123419 P Q).
Proof. exact (@lem6186662 (type402 _123419) P Q). Qed.
Lemma lem6186664 {_123419 : Type'} : (term780 _123419) = (term781 _123419).
Proof. exact (@lem6186663 _123419 (term772 _123419) (term543 _123419)). Qed.
Lemma lem6186665 {_123419 : Type'} (x : type402 _123419) : (term782 _123419 x) = (term771 _123419 x).
Proof. exact (eq_refl (term782 _123419 x)). Qed.
Lemma lem6186666 {_123419 : Type'} : (term783 _123419) = (term772 _123419).
Proof. exact (fun_ext (fun x : type402 _123419 => @lem6186665 _123419 x)). Qed.
Lemma lem6186667 {_123419 : Type'} : (@ex ((_123419 -> _123419 -> _123419) -> _123419)) = (@ex ((_123419 -> _123419 -> _123419) -> _123419)).
Proof. exact (eq_refl (@ex ((_123419 -> _123419 -> _123419) -> _123419))). Qed.
Lemma lem6186668 {_123419 : Type'} : (term784 _123419) = (term773 _123419).
Proof. exact (MK_COMB (@lem6186667 _123419) (@lem6186666 _123419)). Qed.
Lemma lem6186669 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6186670 {_123419 : Type'} : (term785 _123419) = (term774 _123419).
Proof. exact (MK_COMB (@lem6186669) (@lem6186668 _123419)). Qed.
Lemma lem6186671 {_123419 : Type'} : (term543 _123419) = (term543 _123419).
Proof. exact (eq_refl (term543 _123419)). Qed.
Lemma lem6186672 {_123419 : Type'} : (term780 _123419) = (term775 _123419).
Proof. exact (MK_COMB (@lem6186670 _123419) (@lem6186671 _123419)). Qed.
Lemma lem6186673 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6186674 {_123419 : Type'} : (term786 _123419) = (term787 _123419).
Proof. exact (MK_COMB (@lem6186673) (@lem6186672 _123419)). Qed.
Lemma lem6186675 {_123419 : Type'} (x : type402 _123419) : (term782 _123419 x) = (term771 _123419 x).
Proof. exact (eq_refl (term782 _123419 x)). Qed.
Lemma lem6186676 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6186677 {_123419 : Type'} (x : type402 _123419) : (term788 _123419 x) = (term789 _123419 x).
Proof. exact (MK_COMB (@lem6186676) (@lem6186675 _123419 x)). Qed.
Lemma lem6186678 {_123419 : Type'} : (term543 _123419) = (term543 _123419).
Proof. exact (eq_refl (term543 _123419)). Qed.
Lemma lem6186679 {_123419 : Type'} (x : type402 _123419) : (term790 _123419 x) = (term791 _123419 x).
Proof. exact (MK_COMB (@lem6186677 _123419 x) (@lem6186678 _123419)). Qed.
Lemma lem6186680 {_123419 : Type'} : (term792 _123419) = (term793 _123419).
Proof. exact (fun_ext (fun x : type402 _123419 => @lem6186679 _123419 x)). Qed.
Lemma lem6186681 {_123419 : Type'} : (@ex ((_123419 -> _123419 -> _123419) -> _123419)) = (@ex ((_123419 -> _123419 -> _123419) -> _123419)).
Proof. exact (eq_refl (@ex ((_123419 -> _123419 -> _123419) -> _123419))). Qed.
Lemma lem6186682 {_123419 : Type'} : (term781 _123419) = (term794 _123419).
Proof. exact (MK_COMB (@lem6186681 _123419) (@lem6186680 _123419)). Qed.
Lemma lem6186683 {_123419 : Type'} : ((term780 _123419) = (term781 _123419)) = ((term775 _123419) = (term794 _123419)).
Proof. exact (MK_COMB (@lem6186674 _123419) (@lem6186682 _123419)). Qed.
Lemma lem6186684 {_123419 : Type'} : (term775 _123419) = (term794 _123419).
Proof. exact (EQ_MP (@lem6186683 _123419) (@lem6186664 _123419)). Qed.
Lemma lem6186686 {A : Type'} (P : A -> Prop) (Q : Prop) : (term776 A P Q) = (term777 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6186687 {_123419 : Type'} (P : type82 _123419) (Q : Prop) : (term778 _123419 P Q) = (term779 _123419 P Q).
Proof. exact (@lem6186686 (type402 _123419) P Q). Qed.
Lemma lem6186688 {_123419 : Type'} (x : type402 _123419) : (term795 _123419 x) = (term796 _123419 x).
Proof. exact (@lem6186687 _123419 (term770 _123419 x) (term543 _123419)). Qed.
Lemma lem6186689 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term797 _123419 x y) = (term769 _123419 y x).
Proof. exact (eq_refl (term797 _123419 x y)). Qed.
Lemma lem6186690 {_123419 : Type'} (x : type402 _123419) : (term798 _123419 x) = (term770 _123419 x).
Proof. exact (fun_ext (fun y : type402 _123419 => @lem6186689 _123419 y x)). Qed.
Lemma lem6186691 {_123419 : Type'} : (@ex ((_123419 -> _123419 -> _123419) -> _123419)) = (@ex ((_123419 -> _123419 -> _123419) -> _123419)).
Proof. exact (eq_refl (@ex ((_123419 -> _123419 -> _123419) -> _123419))). Qed.
Lemma lem6186692 {_123419 : Type'} (x : type402 _123419) : (term799 _123419 x) = (term771 _123419 x).
Proof. exact (MK_COMB (@lem6186691 _123419) (@lem6186690 _123419 x)). Qed.
Lemma lem6186693 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6186694 {_123419 : Type'} (x : type402 _123419) : (term800 _123419 x) = (term789 _123419 x).
Proof. exact (MK_COMB (@lem6186693) (@lem6186692 _123419 x)). Qed.
Lemma lem6186695 {_123419 : Type'} : (term543 _123419) = (term543 _123419).
Proof. exact (eq_refl (term543 _123419)). Qed.
Lemma lem6186696 {_123419 : Type'} (x : type402 _123419) : (term795 _123419 x) = (term791 _123419 x).
Proof. exact (MK_COMB (@lem6186694 _123419 x) (@lem6186695 _123419)). Qed.
Lemma lem6186697 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6186698 {_123419 : Type'} (x : type402 _123419) : (term801 _123419 x) = (term802 _123419 x).
Proof. exact (MK_COMB (@lem6186697) (@lem6186696 _123419 x)). Qed.
Lemma lem6186699 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term797 _123419 x y) = (term769 _123419 y x).
Proof. exact (eq_refl (term797 _123419 x y)). Qed.
Lemma lem6186700 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6186701 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term803 _123419 x y) = (term804 _123419 y x).
Proof. exact (MK_COMB (@lem6186700) (@lem6186699 _123419 y x)). Qed.
Lemma lem6186702 {_123419 : Type'} : (term543 _123419) = (term543 _123419).
Proof. exact (eq_refl (term543 _123419)). Qed.
Lemma lem6186703 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term805 _123419 x y) = (term806 _123419 y x).
Proof. exact (MK_COMB (@lem6186701 _123419 y x) (@lem6186702 _123419)). Qed.
Lemma lem6186704 {_123419 : Type'} (x : type402 _123419) : (term807 _123419 x) = (term808 _123419 x).
Proof. exact (fun_ext (fun y : type402 _123419 => @lem6186703 _123419 y x)). Qed.
Lemma lem6186705 {_123419 : Type'} : (@ex ((_123419 -> _123419 -> _123419) -> _123419)) = (@ex ((_123419 -> _123419 -> _123419) -> _123419)).
Proof. exact (eq_refl (@ex ((_123419 -> _123419 -> _123419) -> _123419))). Qed.
Lemma lem6186706 {_123419 : Type'} (x : type402 _123419) : (term796 _123419 x) = (term809 _123419 x).
Proof. exact (MK_COMB (@lem6186705 _123419) (@lem6186704 _123419 x)). Qed.
Lemma lem6186707 {_123419 : Type'} (x : type402 _123419) : ((term795 _123419 x) = (term796 _123419 x)) = ((term791 _123419 x) = (term809 _123419 x)).
Proof. exact (MK_COMB (@lem6186698 _123419 x) (@lem6186706 _123419 x)). Qed.
Lemma lem6186708 {_123419 : Type'} (x : type402 _123419) : (term791 _123419 x) = (term809 _123419 x).
Proof. exact (EQ_MP (@lem6186707 _123419 x) (@lem6186688 _123419 x)). Qed.
Lemma lem6186710 {A : Type'} (P : A -> Prop) (Q : Prop) : (term776 A P Q) = (term777 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6186711 {_123419 : Type'} (P : type82 _123419) (Q : Prop) : (term778 _123419 P Q) = (term779 _123419 P Q).
Proof. exact (@lem6186710 (type402 _123419) P Q). Qed.
Lemma lem6186712 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term810 _123419 y x) = (term811 _123419 y x).
Proof. exact (@lem6186711 _123419 (term768 _123419 y x) (term543 _123419)). Qed.
Lemma lem6186713 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) : (term812 _123419 y x z) = (term766 _123419 y z x).
Proof. exact (eq_refl (term812 _123419 y x z)). Qed.
Lemma lem6186714 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term813 _123419 y x) = (term768 _123419 y x).
Proof. exact (fun_ext (fun z : type402 _123419 => @lem6186713 _123419 y z x)). Qed.
Lemma lem6186715 {_123419 : Type'} : (@ex ((_123419 -> _123419 -> _123419) -> _123419)) = (@ex ((_123419 -> _123419 -> _123419) -> _123419)).
Proof. exact (eq_refl (@ex ((_123419 -> _123419 -> _123419) -> _123419))). Qed.
Lemma lem6186716 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term814 _123419 y x) = (term769 _123419 y x).
Proof. exact (MK_COMB (@lem6186715 _123419) (@lem6186714 _123419 y x)). Qed.
Lemma lem6186717 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6186718 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term815 _123419 y x) = (term804 _123419 y x).
Proof. exact (MK_COMB (@lem6186717) (@lem6186716 _123419 y x)). Qed.
Lemma lem6186719 {_123419 : Type'} : (term543 _123419) = (term543 _123419).
Proof. exact (eq_refl (term543 _123419)). Qed.
Lemma lem6186720 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term810 _123419 y x) = (term806 _123419 y x).
Proof. exact (MK_COMB (@lem6186718 _123419 y x) (@lem6186719 _123419)). Qed.
Lemma lem6186721 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6186722 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term816 _123419 y x) = (term817 _123419 y x).
Proof. exact (MK_COMB (@lem6186721) (@lem6186720 _123419 y x)). Qed.
Lemma lem6186723 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) : (term812 _123419 y x z) = (term766 _123419 y z x).
Proof. exact (eq_refl (term812 _123419 y x z)). Qed.
Lemma lem6186724 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6186725 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) : (term818 _123419 y x z) = (term819 _123419 y z x).
Proof. exact (MK_COMB (@lem6186724) (@lem6186723 _123419 y z x)). Qed.
Lemma lem6186726 {_123419 : Type'} : (term543 _123419) = (term543 _123419).
Proof. exact (eq_refl (term543 _123419)). Qed.
Lemma lem6186727 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) : (term820 _123419 y x z) = (term821 _123419 y z x).
Proof. exact (MK_COMB (@lem6186725 _123419 y z x) (@lem6186726 _123419)). Qed.
Lemma lem6186728 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term822 _123419 y x) = (term823 _123419 y x).
Proof. exact (fun_ext (fun z : type402 _123419 => @lem6186727 _123419 y z x)). Qed.
Lemma lem6186729 {_123419 : Type'} : (@ex ((_123419 -> _123419 -> _123419) -> _123419)) = (@ex ((_123419 -> _123419 -> _123419) -> _123419)).
Proof. exact (eq_refl (@ex ((_123419 -> _123419 -> _123419) -> _123419))). Qed.
Lemma lem6186730 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term811 _123419 y x) = (term824 _123419 y x).
Proof. exact (MK_COMB (@lem6186729 _123419) (@lem6186728 _123419 y x)). Qed.
Lemma lem6186731 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : ((term810 _123419 y x) = (term811 _123419 y x)) = ((term806 _123419 y x) = (term824 _123419 y x)).
Proof. exact (MK_COMB (@lem6186722 _123419 y x) (@lem6186730 _123419 y x)). Qed.
Lemma lem6186732 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term806 _123419 y x) = (term824 _123419 y x).
Proof. exact (EQ_MP (@lem6186731 _123419 y x) (@lem6186712 _123419 y x)). Qed.
Lemma lem6186733 {_123419 : Type'} (x : type402 _123419) : (term808 _123419 x) = (term825 _123419 x).
Proof. exact (fun_ext (fun y : type402 _123419 => @lem6186732 _123419 y x)). Qed.
Lemma lem6186734 {_123419 : Type'} : (@ex ((_123419 -> _123419 -> _123419) -> _123419)) = (@ex ((_123419 -> _123419 -> _123419) -> _123419)).
Proof. exact (eq_refl (@ex ((_123419 -> _123419 -> _123419) -> _123419))). Qed.
Lemma lem6186735 {_123419 : Type'} (x : type402 _123419) : (term809 _123419 x) = (term826 _123419 x).
Proof. exact (MK_COMB (@lem6186734 _123419) (@lem6186733 _123419 x)). Qed.
Lemma lem6186736 {_123419 : Type'} (x : type402 _123419) : (term791 _123419 x) = (term826 _123419 x).
Proof. exact (TRANS (@lem6186708 _123419 x) (@lem6186735 _123419 x)). Qed.
Lemma lem6186737 {_123419 : Type'} : (term793 _123419) = (term827 _123419).
Proof. exact (fun_ext (fun x : type402 _123419 => @lem6186736 _123419 x)). Qed.
Lemma lem6186738 {_123419 : Type'} : (@ex ((_123419 -> _123419 -> _123419) -> _123419)) = (@ex ((_123419 -> _123419 -> _123419) -> _123419)).
Proof. exact (eq_refl (@ex ((_123419 -> _123419 -> _123419) -> _123419))). Qed.
Lemma lem6186739 {_123419 : Type'} : (term794 _123419) = (term828 _123419).
Proof. exact (MK_COMB (@lem6186738 _123419) (@lem6186737 _123419)). Qed.
Lemma lem6186740 {_123419 : Type'} : (term775 _123419) = (term828 _123419).
Proof. exact (TRANS (@lem6186684 _123419) (@lem6186739 _123419)). Qed.
Lemma lem6186741 {_123419 : Type'} : (term544 _123419) = (term828 _123419).
Proof. exact (TRANS (@lem6186660 _123419) (@lem6186740 _123419)). Qed.
Lemma lem6186742 {_123419 : Type'} : (term520 _123419) = (term828 _123419).
Proof. exact (TRANS (@lem6186191 _123419) (@lem6186741 _123419)). Qed.
Lemma lem6186743 {_123419 : Type'} : (term382 _123419) = (term828 _123419).
Proof. exact (TRANS (@lem6186164 _123419) (@lem6186742 _123419)). Qed.
Lemma lem6186744 {_123419 : Type'} (h1 : term382 _123419) : term828 _123419.
Proof. exact (EQ_MP (@lem6186743 _123419) (@lem6186029 _123419 h1)). Qed.
Lemma lem6186748 (op : type1606) (y : nat) (x : nat) : ((op x y) = (op y x)) = ((op x y) = (op y x)).
Proof. exact (eq_refl ((op x y) = (op y x))). Qed.
Lemma lem6186749 (P : nat -> Prop) : (term829 P) = (term830 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem6186750 (op : type1606) (x : nat) : (term831 op x) = (term832 op x).
Proof. exact (@lem6186749 (term424 op x)). Qed.
Lemma lem6186751 (op : type1606) (y : nat) (x : nat) : (term833 op x y) = ((op x y) = (op y x)).
Proof. exact (eq_refl (term833 op x y)). Qed.
Lemma lem6186752 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6186754 (op : type1606) (y : nat) (x : nat) : (term834 op x y) = (term835 op y x).
Proof. exact (MK_COMB (@lem6186752) (@lem6186751 op y x)). Qed.
Lemma lem6186755 (op : type1606) (x : nat) : (term836 op x) = (term837 op x).
Proof. exact (fun_ext (fun y : nat => @lem6186754 op y x)). Qed.
Lemma lem6186756 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6186757 (op : type1606) (x : nat) : (term832 op x) = (term838 op x).
Proof. exact (MK_COMB (@lem6186756) (@lem6186755 op x)). Qed.
Lemma lem6186758 (op : type1606) (x : nat) : (term831 op x) = (term838 op x).
Proof. exact (TRANS (@lem6186750 op x) (@lem6186757 op x)). Qed.
Lemma lem6186759 (op : type1606) (x : nat) : (term424 op x) = (term424 op x).
Proof. exact (fun_ext (fun y : nat => @lem6186748 op y x)). Qed.
Lemma lem6186760 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6186761 (op : type1606) (x : nat) : (term425 op x) = (term425 op x).
Proof. exact (MK_COMB (@lem6186760) (@lem6186759 op x)). Qed.
Lemma lem6186762 (P : nat -> Prop) : (term829 P) = (term830 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem6186763 (op : type1606) : (term839 op) = (term840 op).
Proof. exact (@lem6186762 (term426 op)). Qed.
Lemma lem6186764 (op : type1606) (x : nat) : (term841 op x) = (term425 op x).
Proof. exact (eq_refl (term841 op x)). Qed.
Lemma lem6186765 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6186766 (op : type1606) (x : nat) : (term842 op x) = (term831 op x).
Proof. exact (MK_COMB (@lem6186765) (@lem6186764 op x)). Qed.
Lemma lem6186767 (op : type1606) (x : nat) : (term842 op x) = (term838 op x).
Proof. exact (TRANS (@lem6186766 op x) (@lem6186758 op x)). Qed.
Lemma lem6186768 (op : type1606) : (term843 op) = (term844 op).
Proof. exact (fun_ext (fun x : nat => @lem6186767 op x)). Qed.
Lemma lem6186769 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6186770 (op : type1606) : (term840 op) = (term845 op).
Proof. exact (MK_COMB (@lem6186769) (@lem6186768 op)). Qed.
Lemma lem6186771 (op : type1606) : (term839 op) = (term845 op).
Proof. exact (TRANS (@lem6186763 op) (@lem6186770 op)). Qed.
Lemma lem6186772 (op : type1606) : (term426 op) = (term426 op).
Proof. exact (fun_ext (fun x : nat => @lem6186761 op x)). Qed.
Lemma lem6186773 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6186774 (op : type1606) : (term427 op) = (term427 op).
Proof. exact (MK_COMB (@lem6186773) (@lem6186772 op)). Qed.
Lemma lem6186776 (op : type1606) (x : nat) (y : nat) (z : nat) : ((term414 x op y z) = (term415 op x y z)) = ((term414 x op y z) = (term415 op x y z)).
Proof. exact (eq_refl ((term414 x op y z) = (term415 op x y z))). Qed.
Lemma lem6186777 (P : nat -> Prop) : (term829 P) = (term830 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem6186778 (op : type1606) (x : nat) (y : nat) : (term846 op x y) = (term847 op x y).
Proof. exact (@lem6186777 (term416 op x y)). Qed.
Lemma lem6186779 (op : type1606) (x : nat) (y : nat) (z : nat) : (term848 op x y z) = ((term414 x op y z) = (term415 op x y z)).
Proof. exact (eq_refl (term848 op x y z)). Qed.
Lemma lem6186780 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6186782 (op : type1606) (x : nat) (y : nat) (z : nat) : (term849 op x y z) = (term850 op x y z).
Proof. exact (MK_COMB (@lem6186780) (@lem6186779 op x y z)). Qed.
Lemma lem6186783 (op : type1606) (x : nat) (y : nat) : (term851 op x y) = (term852 op x y).
Proof. exact (fun_ext (fun z : nat => @lem6186782 op x y z)). Qed.
Lemma lem6186784 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6186785 (op : type1606) (x : nat) (y : nat) : (term847 op x y) = (term853 op x y).
Proof. exact (MK_COMB (@lem6186784) (@lem6186783 op x y)). Qed.
Lemma lem6186786 (op : type1606) (x : nat) (y : nat) : (term846 op x y) = (term853 op x y).
Proof. exact (TRANS (@lem6186778 op x y) (@lem6186785 op x y)). Qed.
Lemma lem6186787 (op : type1606) (x : nat) (y : nat) : (term416 op x y) = (term416 op x y).
Proof. exact (fun_ext (fun z : nat => @lem6186776 op x y z)). Qed.
Lemma lem6186788 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6186789 (op : type1606) (x : nat) (y : nat) : (term417 op x y) = (term417 op x y).
Proof. exact (MK_COMB (@lem6186788) (@lem6186787 op x y)). Qed.
Lemma lem6186790 (P : nat -> Prop) : (term829 P) = (term830 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem6186791 (op : type1606) (x : nat) : (term854 op x) = (term855 op x).
Proof. exact (@lem6186790 (term418 op x)). Qed.
Lemma lem6186792 (op : type1606) (x : nat) (y : nat) : (term856 op x y) = (term417 op x y).
Proof. exact (eq_refl (term856 op x y)). Qed.
Lemma lem6186793 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6186794 (op : type1606) (x : nat) (y : nat) : (term857 op x y) = (term846 op x y).
Proof. exact (MK_COMB (@lem6186793) (@lem6186792 op x y)). Qed.
Lemma lem6186795 (op : type1606) (x : nat) (y : nat) : (term857 op x y) = (term853 op x y).
Proof. exact (TRANS (@lem6186794 op x y) (@lem6186786 op x y)). Qed.
Lemma lem6186796 (op : type1606) (x : nat) : (term858 op x) = (term859 op x).
Proof. exact (fun_ext (fun y : nat => @lem6186795 op x y)). Qed.
Lemma lem6186797 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6186798 (op : type1606) (x : nat) : (term855 op x) = (term860 op x).
Proof. exact (MK_COMB (@lem6186797) (@lem6186796 op x)). Qed.
Lemma lem6186799 (op : type1606) (x : nat) : (term854 op x) = (term860 op x).
Proof. exact (TRANS (@lem6186791 op x) (@lem6186798 op x)). Qed.
Lemma lem6186800 (op : type1606) (x : nat) : (term418 op x) = (term418 op x).
Proof. exact (fun_ext (fun y : nat => @lem6186789 op x y)). Qed.
Lemma lem6186801 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6186802 (op : type1606) (x : nat) : (term419 op x) = (term419 op x).
Proof. exact (MK_COMB (@lem6186801) (@lem6186800 op x)). Qed.
Lemma lem6186803 (P : nat -> Prop) : (term829 P) = (term830 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem6186804 (op : type1606) : (term861 op) = (term862 op).
Proof. exact (@lem6186803 (term420 op)). Qed.
Lemma lem6186805 (op : type1606) (x : nat) : (term863 op x) = (term419 op x).
Proof. exact (eq_refl (term863 op x)). Qed.
Lemma lem6186806 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6186807 (op : type1606) (x : nat) : (term864 op x) = (term854 op x).
Proof. exact (MK_COMB (@lem6186806) (@lem6186805 op x)). Qed.
Lemma lem6186808 (op : type1606) (x : nat) : (term864 op x) = (term860 op x).
Proof. exact (TRANS (@lem6186807 op x) (@lem6186799 op x)). Qed.
Lemma lem6186809 (op : type1606) : (term865 op) = (term866 op).
Proof. exact (fun_ext (fun x : nat => @lem6186808 op x)). Qed.
Lemma lem6186810 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6186811 (op : type1606) : (term862 op) = (term867 op).
Proof. exact (MK_COMB (@lem6186810) (@lem6186809 op)). Qed.
Lemma lem6186812 (op : type1606) : (term861 op) = (term867 op).
Proof. exact (TRANS (@lem6186804 op) (@lem6186811 op)). Qed.
Lemma lem6186813 (op : type1606) : (term420 op) = (term420 op).
Proof. exact (fun_ext (fun x : nat => @lem6186802 op x)). Qed.
Lemma lem6186814 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6186815 (op : type1606) : (term421 op) = (term421 op).
Proof. exact (MK_COMB (@lem6186814) (@lem6186813 op)). Qed.
Lemma lem6186817 (op : type1606) (x : nat) : ((term411 op x) = x) = ((term411 op x) = x).
Proof. exact (eq_refl ((term411 op x) = x)). Qed.
Lemma lem6186818 (P : nat -> Prop) : (term829 P) = (term830 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem6186819 (op : type1606) : (term868 op) = (term869 op).
Proof. exact (@lem6186818 (term412 op)). Qed.
Lemma lem6186820 (op : type1606) (x : nat) : (term870 op x) = ((term411 op x) = x).
Proof. exact (eq_refl (term870 op x)). Qed.
Lemma lem6186821 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6186823 (op : type1606) (x : nat) : (term871 op x) = (term872 op x).
Proof. exact (MK_COMB (@lem6186821) (@lem6186820 op x)). Qed.
Lemma lem6186824 (op : type1606) : (term873 op) = (term874 op).
Proof. exact (fun_ext (fun x : nat => @lem6186823 op x)). Qed.
Lemma lem6186825 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6186826 (op : type1606) : (term869 op) = (term875 op).
Proof. exact (MK_COMB (@lem6186825) (@lem6186824 op)). Qed.
Lemma lem6186827 (op : type1606) : (term868 op) = (term875 op).
Proof. exact (TRANS (@lem6186819 op) (@lem6186826 op)). Qed.
Lemma lem6186828 (op : type1606) : (term412 op) = (term412 op).
Proof. exact (fun_ext (fun x : nat => @lem6186817 op x)). Qed.
Lemma lem6186829 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6186830 (op : type1606) : (term413 op) = (term413 op).
Proof. exact (MK_COMB (@lem6186829) (@lem6186828 op)). Qed.
Lemma lem6186831 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6186832 (op : type1606) : (term876 op) = (term877 op).
Proof. exact (MK_COMB (@lem6186831) (@lem6186812 op)). Qed.
Lemma lem6186833 (op : type1606) : (term878 op) = (term879 op).
Proof. exact (MK_COMB (@lem6186832 op) (@lem6186827 op)). Qed.
Lemma lem6186834 (op : type1606) : (term880 op) = (term878 op).
Proof. exact (@lem17045 (term421 op) (term413 op)). Qed.
Lemma lem6186835 (op : type1606) : (term880 op) = (term879 op).
Proof. exact (TRANS (@lem6186834 op) (@lem6186833 op)). Qed.
Lemma lem6186836 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6186837 (op : type1606) : (term422 op) = (term422 op).
Proof. exact (MK_COMB (@lem6186836) (@lem6186815 op)). Qed.
Lemma lem6186838 (op : type1606) : (term423 op) = (term423 op).
Proof. exact (MK_COMB (@lem6186837 op) (@lem6186830 op)). Qed.
Lemma lem6186839 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6186840 (op : type1606) : (term881 op) = (term882 op).
Proof. exact (MK_COMB (@lem6186839) (@lem6186771 op)). Qed.
Lemma lem6186841 (op : type1606) : (term883 op) = (term884 op).
Proof. exact (MK_COMB (@lem6186840 op) (@lem6186835 op)). Qed.
Lemma lem6186842 (op : type1606) : (term885 op) = (term883 op).
Proof. exact (@lem17045 (term427 op) (term423 op)). Qed.
Lemma lem6186843 (op : type1606) : (term885 op) = (term884 op).
Proof. exact (TRANS (@lem6186842 op) (@lem6186841 op)). Qed.
Lemma lem6186844 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6186845 (op : type1606) : (term428 op) = (term428 op).
Proof. exact (MK_COMB (@lem6186844) (@lem6186774 op)). Qed.
Lemma lem6186846 (op : type1606) : (term429 op) = (term429 op).
Proof. exact (MK_COMB (@lem6186845 op) (@lem6186838 op)). Qed.
Lemma lem6186848 (op : type1606) : (term886 op) = (term886 op).
Proof. exact (eq_refl (term886 op)). Qed.
Lemma lem6186849 (op : type1606) : (term887 op) = (term887 op).
Proof. exact (MK_COMB (@lem6186848 op) (@lem6186846 op)). Qed.
Lemma lem6186851 (op : type1606) : (term888 op) = (term888 op).
Proof. exact (eq_refl (term888 op)). Qed.
Lemma lem6186852 (op : type1606) : (term889 op) = (term890 op).
Proof. exact (MK_COMB (@lem6186851 op) (@lem6186843 op)). Qed.
Lemma lem6186853 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6186854 (op : type1606) : (term891 op) = (term892 op).
Proof. exact (MK_COMB (@lem6186853) (@lem6186852 op)). Qed.
Lemma lem6186855 (op : type1606) : (term893 op) = (term894 op).
Proof. exact (MK_COMB (@lem6186854 op) (@lem6186849 op)). Qed.
Lemma lem6186856 (op : type1606) : ((@monoidal nat op) = (term429 op)) = (term893 op).
Proof. exact (@lem17784 (@monoidal nat op) (term429 op)). Qed.
Lemma lem6186857 (op : type1606) : ((@monoidal nat op) = (term429 op)) = (term894 op).
Proof. exact (TRANS (@lem6186856 op) (@lem6186855 op)). Qed.
Lemma lem6186858 : term431 = term895.
Proof. exact (fun_ext (fun op : type1606 => @lem6186857 op)). Qed.
Lemma lem6186859 : (@all (nat -> nat -> nat)) = (@all (nat -> nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat -> nat))). Qed.
Lemma lem6186860 : term383 = term896.
Proof. exact (MK_COMB (@lem6186859) (@lem6186858)). Qed.
Lemma lem6186862 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term521 A P Q) = (term522 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6186863 (P : type961) (Q : type961) : (term897 P Q) = (term898 P Q).
Proof. exact (@lem6186862 type1606 P Q). Qed.
Lemma lem6186864 : term899 = term900.
Proof. exact (@lem6186863 term901 term902). Qed.
Lemma lem6186865 (op : type1606) : (term903 op) = (term890 op).
Proof. exact (eq_refl (term903 op)). Qed.
Lemma lem6186866 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6186867 (op : type1606) : (term904 op) = (term892 op).
Proof. exact (MK_COMB (@lem6186866) (@lem6186865 op)). Qed.
Lemma lem6186868 (op : type1606) : (term905 op) = (term887 op).
Proof. exact (eq_refl (term905 op)). Qed.
Lemma lem6186869 (op : type1606) : (term906 op) = (term894 op).
Proof. exact (MK_COMB (@lem6186867 op) (@lem6186868 op)). Qed.
Lemma lem6186870 : term907 = term895.
Proof. exact (fun_ext (fun op : type1606 => @lem6186869 op)). Qed.
Lemma lem6186871 : (@all (nat -> nat -> nat)) = (@all (nat -> nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat -> nat))). Qed.
Lemma lem6186872 : term899 = term896.
Proof. exact (MK_COMB (@lem6186871) (@lem6186870)). Qed.
Lemma lem6186873 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6186874 : term908 = term909.
Proof. exact (MK_COMB (@lem6186873) (@lem6186872)). Qed.
Lemma lem6186875 (op : type1606) : (term903 op) = (term890 op).
Proof. exact (eq_refl (term903 op)). Qed.
Lemma lem6186876 : term910 = term901.
Proof. exact (fun_ext (fun op : type1606 => @lem6186875 op)). Qed.
Lemma lem6186877 : (@all (nat -> nat -> nat)) = (@all (nat -> nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat -> nat))). Qed.
Lemma lem6186878 : term911 = term912.
Proof. exact (MK_COMB (@lem6186877) (@lem6186876)). Qed.
Lemma lem6186879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6186880 : term913 = term914.
Proof. exact (MK_COMB (@lem6186879) (@lem6186878)). Qed.
Lemma lem6186881 (op : type1606) : (term905 op) = (term887 op).
Proof. exact (eq_refl (term905 op)). Qed.
Lemma lem6186882 : term915 = term902.
Proof. exact (fun_ext (fun op : type1606 => @lem6186881 op)). Qed.
Lemma lem6186883 : (@all (nat -> nat -> nat)) = (@all (nat -> nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat -> nat))). Qed.
Lemma lem6186884 : term916 = term917.
Proof. exact (MK_COMB (@lem6186883) (@lem6186882)). Qed.
Lemma lem6186885 : term900 = term918.
Proof. exact (MK_COMB (@lem6186880) (@lem6186884)). Qed.
Lemma lem6186886 : (term899 = term900) = (term896 = term918).
Proof. exact (MK_COMB (@lem6186874) (@lem6186885)). Qed.
Lemma lem6186887 : term896 = term918.
Proof. exact (EQ_MP (@lem6186886) (@lem6186864)). Qed.
Lemma lem6187013 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term545 A P Q) = (term546 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6187014 (P : nat -> Prop) (Q : nat -> Prop) : (term919 P Q) = (term920 P Q).
Proof. exact (@lem6187013 nat P Q). Qed.
Lemma lem6187015 (op : type1606) : (term921 op) = (term922 op).
Proof. exact (@lem6187014 (term866 op) (term874 op)). Qed.
Lemma lem6187016 (op : type1606) (x : nat) : (term923 op x) = (term860 op x).
Proof. exact (eq_refl (term923 op x)). Qed.
Lemma lem6187017 (op : type1606) : (term924 op) = (term866 op).
Proof. exact (fun_ext (fun x : nat => @lem6187016 op x)). Qed.
Lemma lem6187018 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187019 (op : type1606) : (term925 op) = (term867 op).
Proof. exact (MK_COMB (@lem6187018) (@lem6187017 op)). Qed.
Lemma lem6187020 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6187021 (op : type1606) : (term926 op) = (term877 op).
Proof. exact (MK_COMB (@lem6187020) (@lem6187019 op)). Qed.
Lemma lem6187022 (op : type1606) (x : nat) : (term927 op x) = (term872 op x).
Proof. exact (eq_refl (term927 op x)). Qed.
Lemma lem6187023 (op : type1606) : (term928 op) = (term874 op).
Proof. exact (fun_ext (fun x : nat => @lem6187022 op x)). Qed.
Lemma lem6187024 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187025 (op : type1606) : (term929 op) = (term875 op).
Proof. exact (MK_COMB (@lem6187024) (@lem6187023 op)). Qed.
Lemma lem6187026 (op : type1606) : (term921 op) = (term879 op).
Proof. exact (MK_COMB (@lem6187021 op) (@lem6187025 op)). Qed.
Lemma lem6187027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6187028 (op : type1606) : (term930 op) = (term931 op).
Proof. exact (MK_COMB (@lem6187027) (@lem6187026 op)). Qed.
Lemma lem6187029 (op : type1606) (x : nat) : (term923 op x) = (term860 op x).
Proof. exact (eq_refl (term923 op x)). Qed.
Lemma lem6187030 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6187031 (op : type1606) (x : nat) : (term932 op x) = (term933 op x).
Proof. exact (MK_COMB (@lem6187030) (@lem6187029 op x)). Qed.
Lemma lem6187032 (op : type1606) (x : nat) : (term927 op x) = (term872 op x).
Proof. exact (eq_refl (term927 op x)). Qed.
Lemma lem6187033 (op : type1606) (x : nat) : (term934 op x) = (term935 op x).
Proof. exact (MK_COMB (@lem6187031 op x) (@lem6187032 op x)). Qed.
Lemma lem6187034 (op : type1606) : (term936 op) = (term937 op).
Proof. exact (fun_ext (fun x : nat => @lem6187033 op x)). Qed.
Lemma lem6187035 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187036 (op : type1606) : (term922 op) = (term938 op).
Proof. exact (MK_COMB (@lem6187035) (@lem6187034 op)). Qed.
Lemma lem6187037 (op : type1606) : ((term921 op) = (term922 op)) = ((term879 op) = (term938 op)).
Proof. exact (MK_COMB (@lem6187028 op) (@lem6187036 op)). Qed.
Lemma lem6187038 (op : type1606) : (term879 op) = (term938 op).
Proof. exact (EQ_MP (@lem6187037 op) (@lem6187015 op)). Qed.
Lemma lem6187040 {A : Type'} (P : A -> Prop) (Q : Prop) : (term565 A P Q) = (term566 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6187041 (P : nat -> Prop) (Q : Prop) : (term939 P Q) = (term940 P Q).
Proof. exact (@lem6187040 nat P Q). Qed.
Lemma lem6187042 (op : type1606) (x : nat) : (term941 op x) = (term942 op x).
Proof. exact (@lem6187041 (term859 op x) (term872 op x)). Qed.
Lemma lem6187043 (op : type1606) (x : nat) (y : nat) : (term943 op x y) = (term853 op x y).
Proof. exact (eq_refl (term943 op x y)). Qed.
Lemma lem6187044 (op : type1606) (x : nat) : (term944 op x) = (term859 op x).
Proof. exact (fun_ext (fun y : nat => @lem6187043 op x y)). Qed.
Lemma lem6187045 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187046 (op : type1606) (x : nat) : (term945 op x) = (term860 op x).
Proof. exact (MK_COMB (@lem6187045) (@lem6187044 op x)). Qed.
Lemma lem6187047 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6187048 (op : type1606) (x : nat) : (term946 op x) = (term933 op x).
Proof. exact (MK_COMB (@lem6187047) (@lem6187046 op x)). Qed.
Lemma lem6187049 (op : type1606) (x : nat) : (term872 op x) = (term872 op x).
Proof. exact (eq_refl (term872 op x)). Qed.
Lemma lem6187050 (op : type1606) (x : nat) : (term941 op x) = (term935 op x).
Proof. exact (MK_COMB (@lem6187048 op x) (@lem6187049 op x)). Qed.
Lemma lem6187051 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6187052 (op : type1606) (x : nat) : (term947 op x) = (term948 op x).
Proof. exact (MK_COMB (@lem6187051) (@lem6187050 op x)). Qed.
Lemma lem6187053 (op : type1606) (x : nat) (y : nat) : (term943 op x y) = (term853 op x y).
Proof. exact (eq_refl (term943 op x y)). Qed.
Lemma lem6187054 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6187055 (op : type1606) (x : nat) (y : nat) : (term949 op x y) = (term950 op x y).
Proof. exact (MK_COMB (@lem6187054) (@lem6187053 op x y)). Qed.
Lemma lem6187056 (op : type1606) (x : nat) : (term872 op x) = (term872 op x).
Proof. exact (eq_refl (term872 op x)). Qed.
Lemma lem6187057 (y : nat) (op : type1606) (x : nat) : (term951 y op x) = (term952 y op x).
Proof. exact (MK_COMB (@lem6187055 op x y) (@lem6187056 op x)). Qed.
Lemma lem6187058 (op : type1606) (x : nat) : (term953 op x) = (term954 op x).
Proof. exact (fun_ext (fun y : nat => @lem6187057 y op x)). Qed.
Lemma lem6187059 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187060 (op : type1606) (x : nat) : (term942 op x) = (term955 op x).
Proof. exact (MK_COMB (@lem6187059) (@lem6187058 op x)). Qed.
Lemma lem6187061 (op : type1606) (x : nat) : ((term941 op x) = (term942 op x)) = ((term935 op x) = (term955 op x)).
Proof. exact (MK_COMB (@lem6187052 op x) (@lem6187060 op x)). Qed.
Lemma lem6187062 (op : type1606) (x : nat) : (term935 op x) = (term955 op x).
Proof. exact (EQ_MP (@lem6187061 op x) (@lem6187042 op x)). Qed.
Lemma lem6187064 {A : Type'} (P : A -> Prop) (Q : Prop) : (term565 A P Q) = (term566 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6187065 (P : nat -> Prop) (Q : Prop) : (term939 P Q) = (term940 P Q).
Proof. exact (@lem6187064 nat P Q). Qed.
Lemma lem6187066 (y : nat) (op : type1606) (x : nat) : (term956 y op x) = (term957 y op x).
Proof. exact (@lem6187065 (term852 op x y) (term872 op x)). Qed.
Lemma lem6187067 (op : type1606) (x : nat) (y : nat) (z : nat) : (term958 op x y z) = (term850 op x y z).
Proof. exact (eq_refl (term958 op x y z)). Qed.
Lemma lem6187068 (op : type1606) (x : nat) (y : nat) : (term959 op x y) = (term852 op x y).
Proof. exact (fun_ext (fun z : nat => @lem6187067 op x y z)). Qed.
Lemma lem6187069 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187070 (op : type1606) (x : nat) (y : nat) : (term960 op x y) = (term853 op x y).
Proof. exact (MK_COMB (@lem6187069) (@lem6187068 op x y)). Qed.
Lemma lem6187071 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6187072 (op : type1606) (x : nat) (y : nat) : (term961 op x y) = (term950 op x y).
Proof. exact (MK_COMB (@lem6187071) (@lem6187070 op x y)). Qed.
Lemma lem6187073 (op : type1606) (x : nat) : (term872 op x) = (term872 op x).
Proof. exact (eq_refl (term872 op x)). Qed.
Lemma lem6187074 (y : nat) (op : type1606) (x : nat) : (term956 y op x) = (term952 y op x).
Proof. exact (MK_COMB (@lem6187072 op x y) (@lem6187073 op x)). Qed.
Lemma lem6187075 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6187076 (y : nat) (op : type1606) (x : nat) : (term962 y op x) = (term963 y op x).
Proof. exact (MK_COMB (@lem6187075) (@lem6187074 y op x)). Qed.
Lemma lem6187077 (op : type1606) (x : nat) (y : nat) (z : nat) : (term958 op x y z) = (term850 op x y z).
Proof. exact (eq_refl (term958 op x y z)). Qed.
Lemma lem6187078 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6187079 (op : type1606) (x : nat) (y : nat) (z : nat) : (term964 op x y z) = (term965 op x y z).
Proof. exact (MK_COMB (@lem6187078) (@lem6187077 op x y z)). Qed.
Lemma lem6187080 (op : type1606) (x : nat) : (term872 op x) = (term872 op x).
Proof. exact (eq_refl (term872 op x)). Qed.
Lemma lem6187081 (y : nat) (z : nat) (op : type1606) (x : nat) : (term966 y z op x) = (term967 y z op x).
Proof. exact (MK_COMB (@lem6187079 op x y z) (@lem6187080 op x)). Qed.
Lemma lem6187082 (y : nat) (op : type1606) (x : nat) : (term968 y op x) = (term969 y op x).
Proof. exact (fun_ext (fun z : nat => @lem6187081 y z op x)). Qed.
Lemma lem6187083 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187084 (y : nat) (op : type1606) (x : nat) : (term957 y op x) = (term970 y op x).
Proof. exact (MK_COMB (@lem6187083) (@lem6187082 y op x)). Qed.
Lemma lem6187085 (y : nat) (op : type1606) (x : nat) : ((term956 y op x) = (term957 y op x)) = ((term952 y op x) = (term970 y op x)).
Proof. exact (MK_COMB (@lem6187076 y op x) (@lem6187084 y op x)). Qed.
Lemma lem6187086 (y : nat) (op : type1606) (x : nat) : (term952 y op x) = (term970 y op x).
Proof. exact (EQ_MP (@lem6187085 y op x) (@lem6187066 y op x)). Qed.
Lemma lem6187087 (op : type1606) (x : nat) : (term954 op x) = (term971 op x).
Proof. exact (fun_ext (fun y : nat => @lem6187086 y op x)). Qed.
Lemma lem6187088 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187089 (op : type1606) (x : nat) : (term955 op x) = (term972 op x).
Proof. exact (MK_COMB (@lem6187088) (@lem6187087 op x)). Qed.
Lemma lem6187090 (op : type1606) (x : nat) : (term935 op x) = (term972 op x).
Proof. exact (TRANS (@lem6187062 op x) (@lem6187089 op x)). Qed.
Lemma lem6187091 (op : type1606) : (term937 op) = (term973 op).
Proof. exact (fun_ext (fun x : nat => @lem6187090 op x)). Qed.
Lemma lem6187092 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187093 (op : type1606) : (term938 op) = (term974 op).
Proof. exact (MK_COMB (@lem6187092) (@lem6187091 op)). Qed.
Lemma lem6187094 (op : type1606) : (term879 op) = (term974 op).
Proof. exact (TRANS (@lem6187038 op) (@lem6187093 op)). Qed.
Lemma lem6187095 (op : type1606) : (term882 op) = (term882 op).
Proof. exact (eq_refl (term882 op)). Qed.
Lemma lem6187096 (op : type1606) : (term884 op) = (term975 op).
Proof. exact (MK_COMB (@lem6187095 op) (@lem6187094 op)). Qed.
Lemma lem6187098 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term545 A P Q) = (term546 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6187099 (P : nat -> Prop) (Q : nat -> Prop) : (term919 P Q) = (term920 P Q).
Proof. exact (@lem6187098 nat P Q). Qed.
Lemma lem6187100 (op : type1606) : (term976 op) = (term977 op).
Proof. exact (@lem6187099 (term844 op) (term973 op)). Qed.
Lemma lem6187101 (op : type1606) (x : nat) : (term978 op x) = (term838 op x).
Proof. exact (eq_refl (term978 op x)). Qed.
Lemma lem6187102 (op : type1606) : (term979 op) = (term844 op).
Proof. exact (fun_ext (fun x : nat => @lem6187101 op x)). Qed.
Lemma lem6187103 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187104 (op : type1606) : (term980 op) = (term845 op).
Proof. exact (MK_COMB (@lem6187103) (@lem6187102 op)). Qed.
Lemma lem6187105 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6187106 (op : type1606) : (term981 op) = (term882 op).
Proof. exact (MK_COMB (@lem6187105) (@lem6187104 op)). Qed.
Lemma lem6187107 (op : type1606) (x : nat) : (term982 op x) = (term972 op x).
Proof. exact (eq_refl (term982 op x)). Qed.
Lemma lem6187108 (op : type1606) : (term983 op) = (term973 op).
Proof. exact (fun_ext (fun x : nat => @lem6187107 op x)). Qed.
Lemma lem6187109 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187110 (op : type1606) : (term984 op) = (term974 op).
Proof. exact (MK_COMB (@lem6187109) (@lem6187108 op)). Qed.
Lemma lem6187111 (op : type1606) : (term976 op) = (term975 op).
Proof. exact (MK_COMB (@lem6187106 op) (@lem6187110 op)). Qed.
Lemma lem6187112 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6187113 (op : type1606) : (term985 op) = (term986 op).
Proof. exact (MK_COMB (@lem6187112) (@lem6187111 op)). Qed.
Lemma lem6187114 (op : type1606) (x : nat) : (term978 op x) = (term838 op x).
Proof. exact (eq_refl (term978 op x)). Qed.
Lemma lem6187115 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6187116 (op : type1606) (x : nat) : (term987 op x) = (term988 op x).
Proof. exact (MK_COMB (@lem6187115) (@lem6187114 op x)). Qed.
Lemma lem6187117 (op : type1606) (x : nat) : (term982 op x) = (term972 op x).
Proof. exact (eq_refl (term982 op x)). Qed.
Lemma lem6187118 (op : type1606) (x : nat) : (term989 op x) = (term990 op x).
Proof. exact (MK_COMB (@lem6187116 op x) (@lem6187117 op x)). Qed.
Lemma lem6187119 (op : type1606) : (term991 op) = (term992 op).
Proof. exact (fun_ext (fun x : nat => @lem6187118 op x)). Qed.
Lemma lem6187120 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187121 (op : type1606) : (term977 op) = (term993 op).
Proof. exact (MK_COMB (@lem6187120) (@lem6187119 op)). Qed.
Lemma lem6187122 (op : type1606) : ((term976 op) = (term977 op)) = ((term975 op) = (term993 op)).
Proof. exact (MK_COMB (@lem6187113 op) (@lem6187121 op)). Qed.
Lemma lem6187123 (op : type1606) : (term975 op) = (term993 op).
Proof. exact (EQ_MP (@lem6187122 op) (@lem6187100 op)). Qed.
Lemma lem6187125 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term545 A P Q) = (term546 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6187126 (P : nat -> Prop) (Q : nat -> Prop) : (term919 P Q) = (term920 P Q).
Proof. exact (@lem6187125 nat P Q). Qed.
Lemma lem6187127 (op : type1606) (x : nat) : (term994 op x) = (term995 op x).
Proof. exact (@lem6187126 (term837 op x) (term971 op x)). Qed.
Lemma lem6187128 (op : type1606) (y : nat) (x : nat) : (term996 op x y) = (term835 op y x).
Proof. exact (eq_refl (term996 op x y)). Qed.
Lemma lem6187129 (op : type1606) (x : nat) : (term997 op x) = (term837 op x).
Proof. exact (fun_ext (fun y : nat => @lem6187128 op y x)). Qed.
Lemma lem6187130 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187131 (op : type1606) (x : nat) : (term998 op x) = (term838 op x).
Proof. exact (MK_COMB (@lem6187130) (@lem6187129 op x)). Qed.
Lemma lem6187132 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6187133 (op : type1606) (x : nat) : (term999 op x) = (term988 op x).
Proof. exact (MK_COMB (@lem6187132) (@lem6187131 op x)). Qed.
Lemma lem6187134 (y : nat) (op : type1606) (x : nat) : (term1000 op x y) = (term970 y op x).
Proof. exact (eq_refl (term1000 op x y)). Qed.
Lemma lem6187135 (op : type1606) (x : nat) : (term1001 op x) = (term971 op x).
Proof. exact (fun_ext (fun y : nat => @lem6187134 y op x)). Qed.
Lemma lem6187136 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187137 (op : type1606) (x : nat) : (term1002 op x) = (term972 op x).
Proof. exact (MK_COMB (@lem6187136) (@lem6187135 op x)). Qed.
Lemma lem6187138 (op : type1606) (x : nat) : (term994 op x) = (term990 op x).
Proof. exact (MK_COMB (@lem6187133 op x) (@lem6187137 op x)). Qed.
Lemma lem6187139 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6187140 (op : type1606) (x : nat) : (term1003 op x) = (term1004 op x).
Proof. exact (MK_COMB (@lem6187139) (@lem6187138 op x)). Qed.
Lemma lem6187141 (op : type1606) (y : nat) (x : nat) : (term996 op x y) = (term835 op y x).
Proof. exact (eq_refl (term996 op x y)). Qed.
Lemma lem6187142 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6187143 (op : type1606) (y : nat) (x : nat) : (term1005 op x y) = (term1006 op y x).
Proof. exact (MK_COMB (@lem6187142) (@lem6187141 op y x)). Qed.
Lemma lem6187144 (y : nat) (op : type1606) (x : nat) : (term1000 op x y) = (term970 y op x).
Proof. exact (eq_refl (term1000 op x y)). Qed.
Lemma lem6187145 (y : nat) (op : type1606) (x : nat) : (term1007 op x y) = (term1008 y op x).
Proof. exact (MK_COMB (@lem6187143 op y x) (@lem6187144 y op x)). Qed.
Lemma lem6187146 (op : type1606) (x : nat) : (term1009 op x) = (term1010 op x).
Proof. exact (fun_ext (fun y : nat => @lem6187145 y op x)). Qed.
Lemma lem6187147 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187148 (op : type1606) (x : nat) : (term995 op x) = (term1011 op x).
Proof. exact (MK_COMB (@lem6187147) (@lem6187146 op x)). Qed.
Lemma lem6187149 (op : type1606) (x : nat) : ((term994 op x) = (term995 op x)) = ((term990 op x) = (term1011 op x)).
Proof. exact (MK_COMB (@lem6187140 op x) (@lem6187148 op x)). Qed.
Lemma lem6187150 (op : type1606) (x : nat) : (term990 op x) = (term1011 op x).
Proof. exact (EQ_MP (@lem6187149 op x) (@lem6187127 op x)). Qed.
Lemma lem6187152 {A : Type'} (P : Prop) (Q : A -> Prop) : (term638 A P Q) = (term639 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6187153 (P : Prop) (Q : nat -> Prop) : (term1012 P Q) = (term1013 P Q).
Proof. exact (@lem6187152 nat P Q). Qed.
Lemma lem6187154 (y : nat) (op : type1606) (x : nat) : (term1014 y op x) = (term1015 y op x).
Proof. exact (@lem6187153 (term835 op y x) (term969 y op x)). Qed.
Lemma lem6187155 (y : nat) (z : nat) (op : type1606) (x : nat) : (term1016 y op x z) = (term967 y z op x).
Proof. exact (eq_refl (term1016 y op x z)). Qed.
Lemma lem6187156 (y : nat) (op : type1606) (x : nat) : (term1017 y op x) = (term969 y op x).
Proof. exact (fun_ext (fun z : nat => @lem6187155 y z op x)). Qed.
Lemma lem6187157 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187158 (y : nat) (op : type1606) (x : nat) : (term1018 y op x) = (term970 y op x).
Proof. exact (MK_COMB (@lem6187157) (@lem6187156 y op x)). Qed.
Lemma lem6187159 (op : type1606) (y : nat) (x : nat) : (term1006 op y x) = (term1006 op y x).
Proof. exact (eq_refl (term1006 op y x)). Qed.
Lemma lem6187160 (y : nat) (op : type1606) (x : nat) : (term1014 y op x) = (term1008 y op x).
Proof. exact (MK_COMB (@lem6187159 op y x) (@lem6187158 y op x)). Qed.
Lemma lem6187161 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6187162 (y : nat) (op : type1606) (x : nat) : (term1019 y op x) = (term1020 y op x).
Proof. exact (MK_COMB (@lem6187161) (@lem6187160 y op x)). Qed.
Lemma lem6187163 (y : nat) (z : nat) (op : type1606) (x : nat) : (term1016 y op x z) = (term967 y z op x).
Proof. exact (eq_refl (term1016 y op x z)). Qed.
Lemma lem6187164 (op : type1606) (y : nat) (x : nat) : (term1006 op y x) = (term1006 op y x).
Proof. exact (eq_refl (term1006 op y x)). Qed.
Lemma lem6187165 (y : nat) (z : nat) (op : type1606) (x : nat) : (term1021 y op x z) = (term1022 y z op x).
Proof. exact (MK_COMB (@lem6187164 op y x) (@lem6187163 y z op x)). Qed.
Lemma lem6187166 (y : nat) (op : type1606) (x : nat) : (term1023 y op x) = (term1024 y op x).
Proof. exact (fun_ext (fun z : nat => @lem6187165 y z op x)). Qed.
Lemma lem6187167 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187168 (y : nat) (op : type1606) (x : nat) : (term1015 y op x) = (term1025 y op x).
Proof. exact (MK_COMB (@lem6187167) (@lem6187166 y op x)). Qed.
Lemma lem6187169 (y : nat) (op : type1606) (x : nat) : ((term1014 y op x) = (term1015 y op x)) = ((term1008 y op x) = (term1025 y op x)).
Proof. exact (MK_COMB (@lem6187162 y op x) (@lem6187168 y op x)). Qed.
Lemma lem6187170 (y : nat) (op : type1606) (x : nat) : (term1008 y op x) = (term1025 y op x).
Proof. exact (EQ_MP (@lem6187169 y op x) (@lem6187154 y op x)). Qed.
Lemma lem6187171 (op : type1606) (x : nat) : (term1010 op x) = (term1026 op x).
Proof. exact (fun_ext (fun y : nat => @lem6187170 y op x)). Qed.
Lemma lem6187172 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187173 (op : type1606) (x : nat) : (term1011 op x) = (term1027 op x).
Proof. exact (MK_COMB (@lem6187172) (@lem6187171 op x)). Qed.
Lemma lem6187174 (op : type1606) (x : nat) : (term990 op x) = (term1027 op x).
Proof. exact (TRANS (@lem6187150 op x) (@lem6187173 op x)). Qed.
Lemma lem6187175 (op : type1606) : (term992 op) = (term1028 op).
Proof. exact (fun_ext (fun x : nat => @lem6187174 op x)). Qed.
Lemma lem6187176 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187177 (op : type1606) : (term993 op) = (term1029 op).
Proof. exact (MK_COMB (@lem6187176) (@lem6187175 op)). Qed.
Lemma lem6187178 (op : type1606) : (term975 op) = (term1029 op).
Proof. exact (TRANS (@lem6187123 op) (@lem6187177 op)). Qed.
Lemma lem6187179 (op : type1606) : (term884 op) = (term1029 op).
Proof. exact (TRANS (@lem6187096 op) (@lem6187178 op)). Qed.
Lemma lem6187180 (op : type1606) : (term888 op) = (term888 op).
Proof. exact (eq_refl (term888 op)). Qed.
Lemma lem6187181 (op : type1606) : (term890 op) = (term1030 op).
Proof. exact (MK_COMB (@lem6187180 op) (@lem6187179 op)). Qed.
Lemma lem6187183 {A : Type'} (P : Prop) (Q : A -> Prop) : (term638 A P Q) = (term639 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6187184 (P : Prop) (Q : nat -> Prop) : (term1012 P Q) = (term1013 P Q).
Proof. exact (@lem6187183 nat P Q). Qed.
Lemma lem6187185 (op : type1606) : (term1031 op) = (term1032 op).
Proof. exact (@lem6187184 (@monoidal nat op) (term1028 op)). Qed.
Lemma lem6187186 (op : type1606) (x : nat) : (term1033 op x) = (term1027 op x).
Proof. exact (eq_refl (term1033 op x)). Qed.
Lemma lem6187187 (op : type1606) : (term1034 op) = (term1028 op).
Proof. exact (fun_ext (fun x : nat => @lem6187186 op x)). Qed.
Lemma lem6187188 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187189 (op : type1606) : (term1035 op) = (term1029 op).
Proof. exact (MK_COMB (@lem6187188) (@lem6187187 op)). Qed.
Lemma lem6187190 (op : type1606) : (term888 op) = (term888 op).
Proof. exact (eq_refl (term888 op)). Qed.
Lemma lem6187191 (op : type1606) : (term1031 op) = (term1030 op).
Proof. exact (MK_COMB (@lem6187190 op) (@lem6187189 op)). Qed.
Lemma lem6187192 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6187193 (op : type1606) : (term1036 op) = (term1037 op).
Proof. exact (MK_COMB (@lem6187192) (@lem6187191 op)). Qed.
Lemma lem6187194 (op : type1606) (x : nat) : (term1033 op x) = (term1027 op x).
Proof. exact (eq_refl (term1033 op x)). Qed.
Lemma lem6187195 (op : type1606) : (term888 op) = (term888 op).
Proof. exact (eq_refl (term888 op)). Qed.
Lemma lem6187196 (op : type1606) (x : nat) : (term1038 op x) = (term1039 op x).
Proof. exact (MK_COMB (@lem6187195 op) (@lem6187194 op x)). Qed.
Lemma lem6187197 (op : type1606) : (term1040 op) = (term1041 op).
Proof. exact (fun_ext (fun x : nat => @lem6187196 op x)). Qed.
Lemma lem6187198 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187199 (op : type1606) : (term1032 op) = (term1042 op).
Proof. exact (MK_COMB (@lem6187198) (@lem6187197 op)). Qed.
Lemma lem6187200 (op : type1606) : ((term1031 op) = (term1032 op)) = ((term1030 op) = (term1042 op)).
Proof. exact (MK_COMB (@lem6187193 op) (@lem6187199 op)). Qed.
Lemma lem6187201 (op : type1606) : (term1030 op) = (term1042 op).
Proof. exact (EQ_MP (@lem6187200 op) (@lem6187185 op)). Qed.
Lemma lem6187203 {A : Type'} (P : Prop) (Q : A -> Prop) : (term638 A P Q) = (term639 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6187204 (P : Prop) (Q : nat -> Prop) : (term1012 P Q) = (term1013 P Q).
Proof. exact (@lem6187203 nat P Q). Qed.
Lemma lem6187205 (op : type1606) (x : nat) : (term1043 op x) = (term1044 op x).
Proof. exact (@lem6187204 (@monoidal nat op) (term1026 op x)). Qed.
Lemma lem6187206 (y : nat) (op : type1606) (x : nat) : (term1045 op x y) = (term1025 y op x).
Proof. exact (eq_refl (term1045 op x y)). Qed.
Lemma lem6187207 (op : type1606) (x : nat) : (term1046 op x) = (term1026 op x).
Proof. exact (fun_ext (fun y : nat => @lem6187206 y op x)). Qed.
Lemma lem6187208 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187209 (op : type1606) (x : nat) : (term1047 op x) = (term1027 op x).
Proof. exact (MK_COMB (@lem6187208) (@lem6187207 op x)). Qed.
Lemma lem6187210 (op : type1606) : (term888 op) = (term888 op).
Proof. exact (eq_refl (term888 op)). Qed.
Lemma lem6187211 (op : type1606) (x : nat) : (term1043 op x) = (term1039 op x).
Proof. exact (MK_COMB (@lem6187210 op) (@lem6187209 op x)). Qed.
Lemma lem6187212 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6187213 (op : type1606) (x : nat) : (term1048 op x) = (term1049 op x).
Proof. exact (MK_COMB (@lem6187212) (@lem6187211 op x)). Qed.
Lemma lem6187214 (y : nat) (op : type1606) (x : nat) : (term1045 op x y) = (term1025 y op x).
Proof. exact (eq_refl (term1045 op x y)). Qed.
Lemma lem6187215 (op : type1606) : (term888 op) = (term888 op).
Proof. exact (eq_refl (term888 op)). Qed.
Lemma lem6187216 (y : nat) (op : type1606) (x : nat) : (term1050 op x y) = (term1051 y op x).
Proof. exact (MK_COMB (@lem6187215 op) (@lem6187214 y op x)). Qed.
Lemma lem6187217 (op : type1606) (x : nat) : (term1052 op x) = (term1053 op x).
Proof. exact (fun_ext (fun y : nat => @lem6187216 y op x)). Qed.
Lemma lem6187218 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187219 (op : type1606) (x : nat) : (term1044 op x) = (term1054 op x).
Proof. exact (MK_COMB (@lem6187218) (@lem6187217 op x)). Qed.
Lemma lem6187220 (op : type1606) (x : nat) : ((term1043 op x) = (term1044 op x)) = ((term1039 op x) = (term1054 op x)).
Proof. exact (MK_COMB (@lem6187213 op x) (@lem6187219 op x)). Qed.
Lemma lem6187221 (op : type1606) (x : nat) : (term1039 op x) = (term1054 op x).
Proof. exact (EQ_MP (@lem6187220 op x) (@lem6187205 op x)). Qed.
Lemma lem6187223 {A : Type'} (P : Prop) (Q : A -> Prop) : (term638 A P Q) = (term639 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6187224 (P : Prop) (Q : nat -> Prop) : (term1012 P Q) = (term1013 P Q).
Proof. exact (@lem6187223 nat P Q). Qed.
Lemma lem6187225 (y : nat) (op : type1606) (x : nat) : (term1055 y op x) = (term1056 y op x).
Proof. exact (@lem6187224 (@monoidal nat op) (term1024 y op x)). Qed.
Lemma lem6187226 (y : nat) (z : nat) (op : type1606) (x : nat) : (term1057 y op x z) = (term1022 y z op x).
Proof. exact (eq_refl (term1057 y op x z)). Qed.
Lemma lem6187227 (y : nat) (op : type1606) (x : nat) : (term1058 y op x) = (term1024 y op x).
Proof. exact (fun_ext (fun z : nat => @lem6187226 y z op x)). Qed.
Lemma lem6187228 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187229 (y : nat) (op : type1606) (x : nat) : (term1059 y op x) = (term1025 y op x).
Proof. exact (MK_COMB (@lem6187228) (@lem6187227 y op x)). Qed.
Lemma lem6187230 (op : type1606) : (term888 op) = (term888 op).
Proof. exact (eq_refl (term888 op)). Qed.
Lemma lem6187231 (y : nat) (op : type1606) (x : nat) : (term1055 y op x) = (term1051 y op x).
Proof. exact (MK_COMB (@lem6187230 op) (@lem6187229 y op x)). Qed.
Lemma lem6187232 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6187233 (y : nat) (op : type1606) (x : nat) : (term1060 y op x) = (term1061 y op x).
Proof. exact (MK_COMB (@lem6187232) (@lem6187231 y op x)). Qed.
Lemma lem6187234 (y : nat) (z : nat) (op : type1606) (x : nat) : (term1057 y op x z) = (term1022 y z op x).
Proof. exact (eq_refl (term1057 y op x z)). Qed.
Lemma lem6187235 (op : type1606) : (term888 op) = (term888 op).
Proof. exact (eq_refl (term888 op)). Qed.
Lemma lem6187236 (y : nat) (z : nat) (op : type1606) (x : nat) : (term1062 y op x z) = (term1063 y z op x).
Proof. exact (MK_COMB (@lem6187235 op) (@lem6187234 y z op x)). Qed.
Lemma lem6187237 (y : nat) (op : type1606) (x : nat) : (term1064 y op x) = (term1065 y op x).
Proof. exact (fun_ext (fun z : nat => @lem6187236 y z op x)). Qed.
Lemma lem6187238 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187239 (y : nat) (op : type1606) (x : nat) : (term1056 y op x) = (term1066 y op x).
Proof. exact (MK_COMB (@lem6187238) (@lem6187237 y op x)). Qed.
Lemma lem6187240 (y : nat) (op : type1606) (x : nat) : ((term1055 y op x) = (term1056 y op x)) = ((term1051 y op x) = (term1066 y op x)).
Proof. exact (MK_COMB (@lem6187233 y op x) (@lem6187239 y op x)). Qed.
Lemma lem6187241 (y : nat) (op : type1606) (x : nat) : (term1051 y op x) = (term1066 y op x).
Proof. exact (EQ_MP (@lem6187240 y op x) (@lem6187225 y op x)). Qed.
Lemma lem6187242 (op : type1606) (x : nat) : (term1053 op x) = (term1067 op x).
Proof. exact (fun_ext (fun y : nat => @lem6187241 y op x)). Qed.
Lemma lem6187243 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187244 (op : type1606) (x : nat) : (term1054 op x) = (term1068 op x).
Proof. exact (MK_COMB (@lem6187243) (@lem6187242 op x)). Qed.
Lemma lem6187245 (op : type1606) (x : nat) : (term1039 op x) = (term1068 op x).
Proof. exact (TRANS (@lem6187221 op x) (@lem6187244 op x)). Qed.
Lemma lem6187246 (op : type1606) : (term1041 op) = (term1069 op).
Proof. exact (fun_ext (fun x : nat => @lem6187245 op x)). Qed.
Lemma lem6187247 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187248 (op : type1606) : (term1042 op) = (term1070 op).
Proof. exact (MK_COMB (@lem6187247) (@lem6187246 op)). Qed.
Lemma lem6187249 (op : type1606) : (term1030 op) = (term1070 op).
Proof. exact (TRANS (@lem6187201 op) (@lem6187248 op)). Qed.
Lemma lem6187250 (op : type1606) : (term890 op) = (term1070 op).
Proof. exact (TRANS (@lem6187181 op) (@lem6187249 op)). Qed.
Lemma lem6187251 : term901 = term1071.
Proof. exact (fun_ext (fun op : type1606 => @lem6187250 op)). Qed.
Lemma lem6187252 : (@all (nat -> nat -> nat)) = (@all (nat -> nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat -> nat))). Qed.
Lemma lem6187253 : term912 = term1072.
Proof. exact (MK_COMB (@lem6187252) (@lem6187251)). Qed.
Lemma lem6187255 {A B : Type'} (P : type1413 A B) : (term699 A B P) = (term700 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6187256 (P : type960) : (term1073 P) = (term1074 P).
Proof. exact (@lem6187255 type1606 nat P). Qed.
Lemma lem6187257 : term1075 = term1076.
Proof. exact (@lem6187256 term1077). Qed.
Lemma lem6187258 (op : type1606) : (term1078 op) = (term1069 op).
Proof. exact (eq_refl (term1078 op)). Qed.
Lemma lem6187259 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6187260 (op : type1606) (x : nat) : (term1079 op x) = (term1080 op x).
Proof. exact (MK_COMB (@lem6187258 op) (@lem6187259 x)). Qed.
Lemma lem6187261 (op : type1606) (x : nat) : (term1080 op x) = (term1068 op x).
Proof. exact (eq_refl (term1080 op x)). Qed.
Lemma lem6187262 (op : type1606) (x : nat) : (term1079 op x) = (term1068 op x).
Proof. exact (TRANS (@lem6187260 op x) (@lem6187261 op x)). Qed.
Lemma lem6187263 (op : type1606) : (term1081 op) = (term1069 op).
Proof. exact (fun_ext (fun x : nat => @lem6187262 op x)). Qed.
Lemma lem6187264 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187265 (op : type1606) : (term1082 op) = (term1070 op).
Proof. exact (MK_COMB (@lem6187264) (@lem6187263 op)). Qed.
Lemma lem6187266 : term1083 = term1071.
Proof. exact (fun_ext (fun op : type1606 => @lem6187265 op)). Qed.
Lemma lem6187267 : (@all (nat -> nat -> nat)) = (@all (nat -> nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat -> nat))). Qed.
Lemma lem6187268 : term1075 = term1072.
Proof. exact (MK_COMB (@lem6187267) (@lem6187266)). Qed.
Lemma lem6187269 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6187270 : term1084 = term1085.
Proof. exact (MK_COMB (@lem6187269) (@lem6187268)). Qed.
Lemma lem6187271 (op : type1606) : (term1078 op) = (term1069 op).
Proof. exact (eq_refl (term1078 op)). Qed.
Lemma lem6187272 (x : type962) (op : type1606) : (x op) = (x op).
Proof. exact (eq_refl (x op)). Qed.
Lemma lem6187273 (x : type962) (op : type1606) : (term1086 x op) = (term1087 x op).
Proof. exact (MK_COMB (@lem6187271 op) (@lem6187272 x op)). Qed.
Lemma lem6187274 (x : type962) (op : type1606) : (term1087 x op) = (term1088 x op).
Proof. exact (eq_refl (term1087 x op)). Qed.
Lemma lem6187275 (x : type962) (op : type1606) : (term1086 x op) = (term1088 x op).
Proof. exact (TRANS (@lem6187273 x op) (@lem6187274 x op)). Qed.
Lemma lem6187276 (x : type962) : (term1089 x) = (term1090 x).
Proof. exact (fun_ext (fun op : type1606 => @lem6187275 x op)). Qed.
Lemma lem6187277 : (@all (nat -> nat -> nat)) = (@all (nat -> nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat -> nat))). Qed.
Lemma lem6187278 (x : type962) : (term1091 x) = (term1092 x).
Proof. exact (MK_COMB (@lem6187277) (@lem6187276 x)). Qed.
Lemma lem6187279 : term1093 = term1094.
Proof. exact (fun_ext (fun x : type962 => @lem6187278 x)). Qed.
Lemma lem6187280 : (@ex ((nat -> nat -> nat) -> nat)) = (@ex ((nat -> nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> nat -> nat) -> nat))). Qed.
Lemma lem6187281 : term1076 = term1095.
Proof. exact (MK_COMB (@lem6187280) (@lem6187279)). Qed.
Lemma lem6187282 : (term1075 = term1076) = (term1072 = term1095).
Proof. exact (MK_COMB (@lem6187270) (@lem6187281)). Qed.
Lemma lem6187283 : term1072 = term1095.
Proof. exact (EQ_MP (@lem6187282) (@lem6187257)). Qed.
Lemma lem6187285 {A B : Type'} (P : type1413 A B) : (term699 A B P) = (term700 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6187286 (P : type960) : (term1073 P) = (term1074 P).
Proof. exact (@lem6187285 type1606 nat P). Qed.
Lemma lem6187287 (x : type962) : (term1096 x) = (term1097 x).
Proof. exact (@lem6187286 (term1098 x)). Qed.
Lemma lem6187288 (x : type962) (op : type1606) : (term1099 x op) = (term1100 x op).
Proof. exact (eq_refl (term1099 x op)). Qed.
Lemma lem6187289 (y : nat) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6187290 (x : type962) (op : type1606) (y : nat) : (term1101 x op y) = (term1102 x op y).
Proof. exact (MK_COMB (@lem6187288 x op) (@lem6187289 y)). Qed.
Lemma lem6187291 (y : nat) (x : type962) (op : type1606) : (term1102 x op y) = (term1103 y x op).
Proof. exact (eq_refl (term1102 x op y)). Qed.
Lemma lem6187292 (y : nat) (x : type962) (op : type1606) : (term1101 x op y) = (term1103 y x op).
Proof. exact (TRANS (@lem6187290 x op y) (@lem6187291 y x op)). Qed.
Lemma lem6187293 (x : type962) (op : type1606) : (term1104 x op) = (term1100 x op).
Proof. exact (fun_ext (fun y : nat => @lem6187292 y x op)). Qed.
Lemma lem6187294 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187295 (x : type962) (op : type1606) : (term1105 x op) = (term1088 x op).
Proof. exact (MK_COMB (@lem6187294) (@lem6187293 x op)). Qed.
Lemma lem6187296 (x : type962) : (term1106 x) = (term1090 x).
Proof. exact (fun_ext (fun op : type1606 => @lem6187295 x op)). Qed.
Lemma lem6187297 : (@all (nat -> nat -> nat)) = (@all (nat -> nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat -> nat))). Qed.
Lemma lem6187298 (x : type962) : (term1096 x) = (term1092 x).
Proof. exact (MK_COMB (@lem6187297) (@lem6187296 x)). Qed.
Lemma lem6187299 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6187300 (x : type962) : (term1107 x) = (term1108 x).
Proof. exact (MK_COMB (@lem6187299) (@lem6187298 x)). Qed.
Lemma lem6187301 (x : type962) (op : type1606) : (term1099 x op) = (term1100 x op).
Proof. exact (eq_refl (term1099 x op)). Qed.
Lemma lem6187302 (y : type962) (op : type1606) : (y op) = (y op).
Proof. exact (eq_refl (y op)). Qed.
Lemma lem6187303 (x : type962) (y : type962) (op : type1606) : (term1109 x y op) = (term1110 x y op).
Proof. exact (MK_COMB (@lem6187301 x op) (@lem6187302 y op)). Qed.
Lemma lem6187304 (y : type962) (x : type962) (op : type1606) : (term1110 x y op) = (term1111 y x op).
Proof. exact (eq_refl (term1110 x y op)). Qed.
Lemma lem6187305 (y : type962) (x : type962) (op : type1606) : (term1109 x y op) = (term1111 y x op).
Proof. exact (TRANS (@lem6187303 x y op) (@lem6187304 y x op)). Qed.
Lemma lem6187306 (y : type962) (x : type962) : (term1112 x y) = (term1113 y x).
Proof. exact (fun_ext (fun op : type1606 => @lem6187305 y x op)). Qed.
Lemma lem6187307 : (@all (nat -> nat -> nat)) = (@all (nat -> nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat -> nat))). Qed.
Lemma lem6187308 (y : type962) (x : type962) : (term1114 x y) = (term1115 y x).
Proof. exact (MK_COMB (@lem6187307) (@lem6187306 y x)). Qed.
Lemma lem6187309 (x : type962) : (term1116 x) = (term1117 x).
Proof. exact (fun_ext (fun y : type962 => @lem6187308 y x)). Qed.
Lemma lem6187310 : (@ex ((nat -> nat -> nat) -> nat)) = (@ex ((nat -> nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> nat -> nat) -> nat))). Qed.
Lemma lem6187311 (x : type962) : (term1097 x) = (term1118 x).
Proof. exact (MK_COMB (@lem6187310) (@lem6187309 x)). Qed.
Lemma lem6187312 (x : type962) : ((term1096 x) = (term1097 x)) = ((term1092 x) = (term1118 x)).
Proof. exact (MK_COMB (@lem6187300 x) (@lem6187311 x)). Qed.
Lemma lem6187313 (x : type962) : (term1092 x) = (term1118 x).
Proof. exact (EQ_MP (@lem6187312 x) (@lem6187287 x)). Qed.
Lemma lem6187315 {A B : Type'} (P : type1413 A B) : (term699 A B P) = (term700 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6187316 (P : type960) : (term1073 P) = (term1074 P).
Proof. exact (@lem6187315 type1606 nat P). Qed.
Lemma lem6187317 (y : type962) (x : type962) : (term1119 y x) = (term1120 y x).
Proof. exact (@lem6187316 (term1121 y x)). Qed.
Lemma lem6187318 (y : type962) (x : type962) (op : type1606) : (term1122 y x op) = (term1123 y x op).
Proof. exact (eq_refl (term1122 y x op)). Qed.
Lemma lem6187319 (z : nat) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem6187320 (y : type962) (x : type962) (op : type1606) (z : nat) : (term1124 y x op z) = (term1125 y x op z).
Proof. exact (MK_COMB (@lem6187318 y x op) (@lem6187319 z)). Qed.
Lemma lem6187321 (y : type962) (z : nat) (x : type962) (op : type1606) : (term1125 y x op z) = (term1126 y z x op).
Proof. exact (eq_refl (term1125 y x op z)). Qed.
Lemma lem6187322 (y : type962) (z : nat) (x : type962) (op : type1606) : (term1124 y x op z) = (term1126 y z x op).
Proof. exact (TRANS (@lem6187320 y x op z) (@lem6187321 y z x op)). Qed.
Lemma lem6187323 (y : type962) (x : type962) (op : type1606) : (term1127 y x op) = (term1123 y x op).
Proof. exact (fun_ext (fun z : nat => @lem6187322 y z x op)). Qed.
Lemma lem6187324 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6187325 (y : type962) (x : type962) (op : type1606) : (term1128 y x op) = (term1111 y x op).
Proof. exact (MK_COMB (@lem6187324) (@lem6187323 y x op)). Qed.
Lemma lem6187326 (y : type962) (x : type962) : (term1129 y x) = (term1113 y x).
Proof. exact (fun_ext (fun op : type1606 => @lem6187325 y x op)). Qed.
Lemma lem6187327 : (@all (nat -> nat -> nat)) = (@all (nat -> nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat -> nat))). Qed.
Lemma lem6187328 (y : type962) (x : type962) : (term1119 y x) = (term1115 y x).
Proof. exact (MK_COMB (@lem6187327) (@lem6187326 y x)). Qed.
Lemma lem6187329 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6187330 (y : type962) (x : type962) : (term1130 y x) = (term1131 y x).
Proof. exact (MK_COMB (@lem6187329) (@lem6187328 y x)). Qed.
Lemma lem6187331 (y : type962) (x : type962) (op : type1606) : (term1122 y x op) = (term1123 y x op).
Proof. exact (eq_refl (term1122 y x op)). Qed.
Lemma lem6187332 (z : type962) (op : type1606) : (z op) = (z op).
Proof. exact (eq_refl (z op)). Qed.
Lemma lem6187333 (y : type962) (x : type962) (z : type962) (op : type1606) : (term1132 y x z op) = (term1133 y x z op).
Proof. exact (MK_COMB (@lem6187331 y x op) (@lem6187332 z op)). Qed.
Lemma lem6187334 (y : type962) (z : type962) (x : type962) (op : type1606) : (term1133 y x z op) = (term1134 y z x op).
Proof. exact (eq_refl (term1133 y x z op)). Qed.
Lemma lem6187335 (y : type962) (z : type962) (x : type962) (op : type1606) : (term1132 y x z op) = (term1134 y z x op).
Proof. exact (TRANS (@lem6187333 y x z op) (@lem6187334 y z x op)). Qed.
Lemma lem6187336 (y : type962) (z : type962) (x : type962) : (term1135 y x z) = (term1136 y z x).
Proof. exact (fun_ext (fun op : type1606 => @lem6187335 y z x op)). Qed.
Lemma lem6187337 : (@all (nat -> nat -> nat)) = (@all (nat -> nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat -> nat))). Qed.
Lemma lem6187338 (y : type962) (z : type962) (x : type962) : (term1137 y x z) = (term1138 y z x).
Proof. exact (MK_COMB (@lem6187337) (@lem6187336 y z x)). Qed.
Lemma lem6187339 (y : type962) (x : type962) : (term1139 y x) = (term1140 y x).
Proof. exact (fun_ext (fun z : type962 => @lem6187338 y z x)). Qed.
Lemma lem6187340 : (@ex ((nat -> nat -> nat) -> nat)) = (@ex ((nat -> nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> nat -> nat) -> nat))). Qed.
Lemma lem6187341 (y : type962) (x : type962) : (term1120 y x) = (term1141 y x).
Proof. exact (MK_COMB (@lem6187340) (@lem6187339 y x)). Qed.
Lemma lem6187342 (y : type962) (x : type962) : ((term1119 y x) = (term1120 y x)) = ((term1115 y x) = (term1141 y x)).
Proof. exact (MK_COMB (@lem6187330 y x) (@lem6187341 y x)). Qed.
Lemma lem6187343 (y : type962) (x : type962) : (term1115 y x) = (term1141 y x).
Proof. exact (EQ_MP (@lem6187342 y x) (@lem6187317 y x)). Qed.
Lemma lem6187344 (x : type962) : (term1117 x) = (term1142 x).
Proof. exact (fun_ext (fun y : type962 => @lem6187343 y x)). Qed.
Lemma lem6187345 : (@ex ((nat -> nat -> nat) -> nat)) = (@ex ((nat -> nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> nat -> nat) -> nat))). Qed.
Lemma lem6187346 (x : type962) : (term1118 x) = (term1143 x).
Proof. exact (MK_COMB (@lem6187345) (@lem6187344 x)). Qed.
Lemma lem6187347 (x : type962) : (term1092 x) = (term1143 x).
Proof. exact (TRANS (@lem6187313 x) (@lem6187346 x)). Qed.
Lemma lem6187348 : term1094 = term1144.
Proof. exact (fun_ext (fun x : type962 => @lem6187347 x)). Qed.
Lemma lem6187349 : (@ex ((nat -> nat -> nat) -> nat)) = (@ex ((nat -> nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> nat -> nat) -> nat))). Qed.
Lemma lem6187350 : term1095 = term1145.
Proof. exact (MK_COMB (@lem6187349) (@lem6187348)). Qed.
Lemma lem6187351 : term1072 = term1145.
Proof. exact (TRANS (@lem6187283) (@lem6187350)). Qed.
Lemma lem6187352 : term912 = term1145.
Proof. exact (TRANS (@lem6187253) (@lem6187351)). Qed.
Lemma lem6187353 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6187354 : term914 = term1146.
Proof. exact (MK_COMB (@lem6187353) (@lem6187352)). Qed.
Lemma lem6187355 : term917 = term917.
Proof. exact (eq_refl term917). Qed.
Lemma lem6187356 : term918 = term1147.
Proof. exact (MK_COMB (@lem6187354) (@lem6187355)). Qed.
Lemma lem6187358 {A : Type'} (P : A -> Prop) (Q : Prop) : (term776 A P Q) = (term777 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6187359 (P : type243) (Q : Prop) : (term1148 P Q) = (term1149 P Q).
Proof. exact (@lem6187358 type962 P Q). Qed.
Lemma lem6187360 : term1150 = term1151.
Proof. exact (@lem6187359 term1144 term917). Qed.
Lemma lem6187361 (x : type962) : (term1152 x) = (term1143 x).
Proof. exact (eq_refl (term1152 x)). Qed.
Lemma lem6187362 : term1153 = term1144.
Proof. exact (fun_ext (fun x : type962 => @lem6187361 x)). Qed.
Lemma lem6187363 : (@ex ((nat -> nat -> nat) -> nat)) = (@ex ((nat -> nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> nat -> nat) -> nat))). Qed.
Lemma lem6187364 : term1154 = term1145.
Proof. exact (MK_COMB (@lem6187363) (@lem6187362)). Qed.
Lemma lem6187365 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6187366 : term1155 = term1146.
Proof. exact (MK_COMB (@lem6187365) (@lem6187364)). Qed.
Lemma lem6187367 : term917 = term917.
Proof. exact (eq_refl term917). Qed.
Lemma lem6187368 : term1150 = term1147.
Proof. exact (MK_COMB (@lem6187366) (@lem6187367)). Qed.
Lemma lem6187369 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6187370 : term1156 = term1157.
Proof. exact (MK_COMB (@lem6187369) (@lem6187368)). Qed.
Lemma lem6187371 (x : type962) : (term1152 x) = (term1143 x).
Proof. exact (eq_refl (term1152 x)). Qed.
Lemma lem6187372 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6187373 (x : type962) : (term1158 x) = (term1159 x).
Proof. exact (MK_COMB (@lem6187372) (@lem6187371 x)). Qed.
Lemma lem6187374 : term917 = term917.
Proof. exact (eq_refl term917). Qed.
Lemma lem6187375 (x : type962) : (term1160 x) = (term1161 x).
Proof. exact (MK_COMB (@lem6187373 x) (@lem6187374)). Qed.
Lemma lem6187376 : term1162 = term1163.
Proof. exact (fun_ext (fun x : type962 => @lem6187375 x)). Qed.
Lemma lem6187377 : (@ex ((nat -> nat -> nat) -> nat)) = (@ex ((nat -> nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> nat -> nat) -> nat))). Qed.
Lemma lem6187378 : term1151 = term1164.
Proof. exact (MK_COMB (@lem6187377) (@lem6187376)). Qed.
Lemma lem6187379 : (term1150 = term1151) = (term1147 = term1164).
Proof. exact (MK_COMB (@lem6187370) (@lem6187378)). Qed.
Lemma lem6187380 : term1147 = term1164.
Proof. exact (EQ_MP (@lem6187379) (@lem6187360)). Qed.
Lemma lem6187382 {A : Type'} (P : A -> Prop) (Q : Prop) : (term776 A P Q) = (term777 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6187383 (P : type243) (Q : Prop) : (term1148 P Q) = (term1149 P Q).
Proof. exact (@lem6187382 type962 P Q). Qed.
Lemma lem6187384 (x : type962) : (term1165 x) = (term1166 x).
Proof. exact (@lem6187383 (term1142 x) term917). Qed.
Lemma lem6187385 (y : type962) (x : type962) : (term1167 x y) = (term1141 y x).
Proof. exact (eq_refl (term1167 x y)). Qed.
Lemma lem6187386 (x : type962) : (term1168 x) = (term1142 x).
Proof. exact (fun_ext (fun y : type962 => @lem6187385 y x)). Qed.
Lemma lem6187387 : (@ex ((nat -> nat -> nat) -> nat)) = (@ex ((nat -> nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> nat -> nat) -> nat))). Qed.
Lemma lem6187388 (x : type962) : (term1169 x) = (term1143 x).
Proof. exact (MK_COMB (@lem6187387) (@lem6187386 x)). Qed.
Lemma lem6187389 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6187390 (x : type962) : (term1170 x) = (term1159 x).
Proof. exact (MK_COMB (@lem6187389) (@lem6187388 x)). Qed.
Lemma lem6187391 : term917 = term917.
Proof. exact (eq_refl term917). Qed.
Lemma lem6187392 (x : type962) : (term1165 x) = (term1161 x).
Proof. exact (MK_COMB (@lem6187390 x) (@lem6187391)). Qed.
Lemma lem6187393 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6187394 (x : type962) : (term1171 x) = (term1172 x).
Proof. exact (MK_COMB (@lem6187393) (@lem6187392 x)). Qed.
Lemma lem6187395 (y : type962) (x : type962) : (term1167 x y) = (term1141 y x).
Proof. exact (eq_refl (term1167 x y)). Qed.
Lemma lem6187396 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6187397 (y : type962) (x : type962) : (term1173 x y) = (term1174 y x).
Proof. exact (MK_COMB (@lem6187396) (@lem6187395 y x)). Qed.
Lemma lem6187398 : term917 = term917.
Proof. exact (eq_refl term917). Qed.
Lemma lem6187399 (y : type962) (x : type962) : (term1175 x y) = (term1176 y x).
Proof. exact (MK_COMB (@lem6187397 y x) (@lem6187398)). Qed.
Lemma lem6187400 (x : type962) : (term1177 x) = (term1178 x).
Proof. exact (fun_ext (fun y : type962 => @lem6187399 y x)). Qed.
Lemma lem6187401 : (@ex ((nat -> nat -> nat) -> nat)) = (@ex ((nat -> nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> nat -> nat) -> nat))). Qed.
Lemma lem6187402 (x : type962) : (term1166 x) = (term1179 x).
Proof. exact (MK_COMB (@lem6187401) (@lem6187400 x)). Qed.
Lemma lem6187403 (x : type962) : ((term1165 x) = (term1166 x)) = ((term1161 x) = (term1179 x)).
Proof. exact (MK_COMB (@lem6187394 x) (@lem6187402 x)). Qed.
Lemma lem6187404 (x : type962) : (term1161 x) = (term1179 x).
Proof. exact (EQ_MP (@lem6187403 x) (@lem6187384 x)). Qed.
Lemma lem6187406 {A : Type'} (P : A -> Prop) (Q : Prop) : (term776 A P Q) = (term777 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6187407 (P : type243) (Q : Prop) : (term1148 P Q) = (term1149 P Q).
Proof. exact (@lem6187406 type962 P Q). Qed.
Lemma lem6187408 (y : type962) (x : type962) : (term1180 y x) = (term1181 y x).
Proof. exact (@lem6187407 (term1140 y x) term917). Qed.
Lemma lem6187409 (y : type962) (z : type962) (x : type962) : (term1182 y x z) = (term1138 y z x).
Proof. exact (eq_refl (term1182 y x z)). Qed.
Lemma lem6187410 (y : type962) (x : type962) : (term1183 y x) = (term1140 y x).
Proof. exact (fun_ext (fun z : type962 => @lem6187409 y z x)). Qed.
Lemma lem6187411 : (@ex ((nat -> nat -> nat) -> nat)) = (@ex ((nat -> nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> nat -> nat) -> nat))). Qed.
Lemma lem6187412 (y : type962) (x : type962) : (term1184 y x) = (term1141 y x).
Proof. exact (MK_COMB (@lem6187411) (@lem6187410 y x)). Qed.
Lemma lem6187413 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6187414 (y : type962) (x : type962) : (term1185 y x) = (term1174 y x).
Proof. exact (MK_COMB (@lem6187413) (@lem6187412 y x)). Qed.
Lemma lem6187415 : term917 = term917.
Proof. exact (eq_refl term917). Qed.
Lemma lem6187416 (y : type962) (x : type962) : (term1180 y x) = (term1176 y x).
Proof. exact (MK_COMB (@lem6187414 y x) (@lem6187415)). Qed.
Lemma lem6187417 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6187418 (y : type962) (x : type962) : (term1186 y x) = (term1187 y x).
Proof. exact (MK_COMB (@lem6187417) (@lem6187416 y x)). Qed.
Lemma lem6187419 (y : type962) (z : type962) (x : type962) : (term1182 y x z) = (term1138 y z x).
Proof. exact (eq_refl (term1182 y x z)). Qed.
Lemma lem6187420 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6187421 (y : type962) (z : type962) (x : type962) : (term1188 y x z) = (term1189 y z x).
Proof. exact (MK_COMB (@lem6187420) (@lem6187419 y z x)). Qed.
Lemma lem6187422 : term917 = term917.
Proof. exact (eq_refl term917). Qed.
Lemma lem6187423 (y : type962) (z : type962) (x : type962) : (term1190 y x z) = (term1191 y z x).
Proof. exact (MK_COMB (@lem6187421 y z x) (@lem6187422)). Qed.
Lemma lem6187424 (y : type962) (x : type962) : (term1192 y x) = (term1193 y x).
Proof. exact (fun_ext (fun z : type962 => @lem6187423 y z x)). Qed.
Lemma lem6187425 : (@ex ((nat -> nat -> nat) -> nat)) = (@ex ((nat -> nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> nat -> nat) -> nat))). Qed.
Lemma lem6187426 (y : type962) (x : type962) : (term1181 y x) = (term1194 y x).
Proof. exact (MK_COMB (@lem6187425) (@lem6187424 y x)). Qed.
Lemma lem6187427 (y : type962) (x : type962) : ((term1180 y x) = (term1181 y x)) = ((term1176 y x) = (term1194 y x)).
Proof. exact (MK_COMB (@lem6187418 y x) (@lem6187426 y x)). Qed.
Lemma lem6187428 (y : type962) (x : type962) : (term1176 y x) = (term1194 y x).
Proof. exact (EQ_MP (@lem6187427 y x) (@lem6187408 y x)). Qed.
Lemma lem6187429 (x : type962) : (term1178 x) = (term1195 x).
Proof. exact (fun_ext (fun y : type962 => @lem6187428 y x)). Qed.
Lemma lem6187430 : (@ex ((nat -> nat -> nat) -> nat)) = (@ex ((nat -> nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> nat -> nat) -> nat))). Qed.
Lemma lem6187431 (x : type962) : (term1179 x) = (term1196 x).
Proof. exact (MK_COMB (@lem6187430) (@lem6187429 x)). Qed.
Lemma lem6187432 (x : type962) : (term1161 x) = (term1196 x).
Proof. exact (TRANS (@lem6187404 x) (@lem6187431 x)). Qed.
Lemma lem6187433 : term1163 = term1197.
Proof. exact (fun_ext (fun x : type962 => @lem6187432 x)). Qed.
Lemma lem6187434 : (@ex ((nat -> nat -> nat) -> nat)) = (@ex ((nat -> nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> nat -> nat) -> nat))). Qed.
Lemma lem6187435 : term1164 = term1198.
Proof. exact (MK_COMB (@lem6187434) (@lem6187433)). Qed.
Lemma lem6187436 : term1147 = term1198.
Proof. exact (TRANS (@lem6187380) (@lem6187435)). Qed.
Lemma lem6187437 : term918 = term1198.
Proof. exact (TRANS (@lem6187356) (@lem6187436)). Qed.
Lemma lem6187438 : term896 = term1198.
Proof. exact (TRANS (@lem6186887) (@lem6187437)). Qed.
Lemma lem6187439 : term383 = term1198.
Proof. exact (TRANS (@lem6186860) (@lem6187438)). Qed.
Lemma lem6187440 (h1 : term383) : term1198.
Proof. exact (EQ_MP (@lem6187439) (@lem6186030 h1)). Qed.
Lemma lem6187441 (x : type962) (h1 : term1196 x) : term1196 x.
Proof. exact (h1). Qed.
Lemma lem6187442 (y : type962) (x : type962) (h1 : term1194 y x) : term1194 y x.
Proof. exact (h1). Qed.
Lemma lem6187444 {_123419 : Type'} (x' : type402 _123419) (h1 : term826 _123419 x') : term826 _123419 x'.
Proof. exact (h1). Qed.
Lemma lem6187445 {_123419 : Type'} (y' : type402 _123419) (x' : type402 _123419) (h1 : term824 _123419 y' x') : term824 _123419 y' x'.
Proof. exact (h1). Qed.
Lemma lem6187446 {_123419 : Type'} (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : term821 _123419 y' z' x') : term821 _123419 y' z' x'.
Proof. exact (h1). Qed.
Lemma lem6187451 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6187452 {_123419 : Type'} (f : type403 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> Prop) f x).
Proof. exact (@lem6187451 (type1400 _123419) Prop f x). Qed.
Lemma lem6187454 {_123419 : Type'} (op : type1400 _123419) : (@monoidal _123419 op) = (@I ((_123419 -> _123419 -> _123419) -> Prop) (@monoidal _123419) op).
Proof. exact (@lem6187452 _123419 (@monoidal _123419) op). Qed.
Lemma lem6187469 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6187470 {_123419 : Type'} : (@eq _123419) = (@eq _123419).
Proof. exact (eq_refl (@eq _123419)). Qed.
Lemma lem6187471 {_123419 : Type'} (op : type1400 _123419) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6187472 {_123419 : Type'} (f : nat -> _123419) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6187477 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6187478 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem6187477 nat nat f x). Qed.
Lemma lem6187480 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem6187478 NUMERAL 0). Qed.
Lemma lem6187481 {_123419 : Type'} (f : nat -> _123419) : (term327 _123419 f) = (term1199 _123419 f).
Proof. exact (MK_COMB (@lem6187472 _123419 f) (@lem6187480)). Qed.
Lemma lem6187483 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6187484 {_123419 : Type'} (f : nat -> _123419) (x : nat) : (f x) = (@I (nat -> _123419) f x).
Proof. exact (@lem6187483 nat _123419 f x). Qed.
Lemma lem6187485 {_123419 : Type'} (f : nat -> _123419) : (term1199 _123419 f) = (term1200 _123419 f).
Proof. exact (@lem6187484 _123419 f (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem6187486 {_123419 : Type'} (f : nat -> _123419) : (term327 _123419 f) = (term1200 _123419 f).
Proof. exact (TRANS (@lem6187481 _123419 f) (@lem6187485 _123419 f)). Qed.
Lemma lem6187491 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6187492 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6187491 (type1400 _123419) _123419 f x). Qed.
Lemma lem6187494 {_123419 : Type'} (op : type1400 _123419) : (@neutral _123419 op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) (@neutral _123419) op).
Proof. exact (@lem6187492 _123419 (@neutral _123419) op). Qed.
Lemma lem6187495 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : (term319 _123419 op f) = (term1201 _123419 op f).
Proof. exact (MK_COMB (@lem6187471 _123419 op) (@lem6187486 _123419 f)). Qed.
Lemma lem6187496 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : (term320 _123419 f op) = (term1202 _123419 f op).
Proof. exact (MK_COMB (@lem6187495 _123419 op f) (@lem6187494 _123419 op)). Qed.
Lemma lem6187498 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6187499 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6187498 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6187500 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : (term1201 _123419 op f) = (term1203 _123419 op f).
Proof. exact (@lem6187499 _123419 op (term1200 _123419 f)). Qed.
Lemma lem6187501 {_123419 : Type'} (op : type1400 _123419) : (@I ((_123419 -> _123419 -> _123419) -> _123419) (@neutral _123419) op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) (@neutral _123419) op).
Proof. exact (eq_refl (@I ((_123419 -> _123419 -> _123419) -> _123419) (@neutral _123419) op)). Qed.
Lemma lem6187502 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : (term1202 _123419 f op) = (term1204 _123419 f op).
Proof. exact (MK_COMB (@lem6187500 _123419 op f) (@lem6187501 _123419 op)). Qed.
Lemma lem6187504 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6187505 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6187504 _123419 _123419 f x). Qed.
Lemma lem6187506 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : (term1204 _123419 f op) = (term1205 _123419 f op).
Proof. exact (@lem6187505 _123419 (term1203 _123419 op f) (@I ((_123419 -> _123419 -> _123419) -> _123419) (@neutral _123419) op)). Qed.
Lemma lem6187507 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : (term1202 _123419 f op) = (term1205 _123419 f op).
Proof. exact (TRANS (@lem6187502 _123419 f op) (@lem6187506 _123419 f op)). Qed.
Lemma lem6187508 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : (term320 _123419 f op) = (term1205 _123419 f op).
Proof. exact (TRANS (@lem6187496 _123419 f op) (@lem6187507 _123419 f op)). Qed.
Lemma lem6187509 {_123419 : Type'} (f : nat -> _123419) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6187514 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6187515 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem6187514 nat nat f x). Qed.
Lemma lem6187517 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem6187515 NUMERAL 0). Qed.
Lemma lem6187518 {_123419 : Type'} (f : nat -> _123419) : (term327 _123419 f) = (term1199 _123419 f).
Proof. exact (MK_COMB (@lem6187509 _123419 f) (@lem6187517)). Qed.
Lemma lem6187520 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6187521 {_123419 : Type'} (f : nat -> _123419) (x : nat) : (f x) = (@I (nat -> _123419) f x).
Proof. exact (@lem6187520 nat _123419 f x). Qed.
Lemma lem6187522 {_123419 : Type'} (f : nat -> _123419) : (term1199 _123419 f) = (term1200 _123419 f).
Proof. exact (@lem6187521 _123419 f (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem6187523 {_123419 : Type'} (f : nat -> _123419) : (term327 _123419 f) = (term1200 _123419 f).
Proof. exact (TRANS (@lem6187518 _123419 f) (@lem6187522 _123419 f)). Qed.
Lemma lem6187524 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : (term373 _123419 f op) = (term1206 _123419 f op).
Proof. exact (MK_COMB (@lem6187470 _123419) (@lem6187508 _123419 f op)). Qed.
Lemma lem6187525 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : ((term320 _123419 f op) = (term327 _123419 f)) = ((term1205 _123419 f op) = (term1200 _123419 f)).
Proof. exact (MK_COMB (@lem6187524 _123419 f op) (@lem6187523 _123419 f)). Qed.
Lemma lem6187526 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : (term381 _123419 op f) = (term1207 _123419 op f).
Proof. exact (MK_COMB (@lem6187469) (@lem6187525 _123419 op f)). Qed.
Lemma lem6187950 {_123419 : Type'} : (@eq _123419) = (@eq _123419).
Proof. exact (eq_refl (@eq _123419)). Qed.
Lemma lem6187951 {_123419 : Type'} (op : type1400 _123419) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6187956 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6187957 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6187956 (type1400 _123419) _123419 f x). Qed.
Lemma lem6187959 {_123419 : Type'} (op : type1400 _123419) : (@neutral _123419 op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) (@neutral _123419) op).
Proof. exact (@lem6187957 _123419 (@neutral _123419) op). Qed.
Lemma lem6187960 {_123419 : Type'} (x : _123419) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6187961 {_123419 : Type'} (op : type1400 _123419) : (term1208 _123419 op) = (term1209 _123419 op).
Proof. exact (MK_COMB (@lem6187951 _123419 op) (@lem6187959 _123419 op)). Qed.
Lemma lem6187962 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term432 _123419 op x) = (term1210 _123419 op x).
Proof. exact (MK_COMB (@lem6187961 _123419 op) (@lem6187960 _123419 x)). Qed.
Lemma lem6187964 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6187965 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6187964 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6187966 {_123419 : Type'} (op : type1400 _123419) : (term1209 _123419 op) = (term1211 _123419 op).
Proof. exact (@lem6187965 _123419 op (@I ((_123419 -> _123419 -> _123419) -> _123419) (@neutral _123419) op)). Qed.
Lemma lem6187967 {_123419 : Type'} (x : _123419) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6187968 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1210 _123419 op x) = (term1212 _123419 op x).
Proof. exact (MK_COMB (@lem6187966 _123419 op) (@lem6187967 _123419 x)). Qed.
Lemma lem6187970 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6187971 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6187970 _123419 _123419 f x). Qed.
Lemma lem6187972 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1212 _123419 op x) = (term1213 _123419 op x).
Proof. exact (@lem6187971 _123419 (term1211 _123419 op) x). Qed.
Lemma lem6187973 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1210 _123419 op x) = (term1213 _123419 op x).
Proof. exact (TRANS (@lem6187968 _123419 op x) (@lem6187972 _123419 op x)). Qed.
Lemma lem6187974 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term432 _123419 op x) = (term1213 _123419 op x).
Proof. exact (TRANS (@lem6187962 _123419 op x) (@lem6187973 _123419 op x)). Qed.
Lemma lem6187975 {_123419 : Type'} (x : _123419) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6187976 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1214 _123419 op x) = (term1215 _123419 op x).
Proof. exact (MK_COMB (@lem6187950 _123419) (@lem6187974 _123419 op x)). Qed.
Lemma lem6187977 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : ((term432 _123419 op x) = x) = ((term1213 _123419 op x) = x).
Proof. exact (MK_COMB (@lem6187976 _123419 op x) (@lem6187975 _123419 x)). Qed.
Lemma lem6187978 {_123419 : Type'} (op : type1400 _123419) : (term433 _123419 op) = (term1216 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6187977 _123419 op x)). Qed.
Lemma lem6187979 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6187980 {_123419 : Type'} (op : type1400 _123419) : (term434 _123419 op) = (term1217 _123419 op).
Proof. exact (MK_COMB (@lem6187979 _123419) (@lem6187978 _123419 op)). Qed.
Lemma lem6187981 {_123419 : Type'} : (@eq _123419) = (@eq _123419).
Proof. exact (eq_refl (@eq _123419)). Qed.
Lemma lem6187990 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6187991 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6187990 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6187992 {_123419 : Type'} (op : type1400 _123419) (y : _123419) : (op y) = (@I (_123419 -> _123419 -> _123419) op y).
Proof. exact (@lem6187991 _123419 op y). Qed.
Lemma lem6187993 {_123419 : Type'} (z : _123419) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem6187994 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (z : _123419) : (op y z) = (@I (_123419 -> _123419 -> _123419) op y z).
Proof. exact (MK_COMB (@lem6187992 _123419 op y) (@lem6187993 _123419 z)). Qed.
Lemma lem6187996 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6187997 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6187996 _123419 _123419 f x). Qed.
Lemma lem6187998 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (z : _123419) : (@I (_123419 -> _123419 -> _123419) op y z) = (term1218 _123419 op y z).
Proof. exact (@lem6187997 _123419 (@I (_123419 -> _123419 -> _123419) op y) z). Qed.
Lemma lem6188000 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (z : _123419) : (op y z) = (term1218 _123419 op y z).
Proof. exact (TRANS (@lem6187994 _123419 op y z) (@lem6187998 _123419 op y z)). Qed.
Lemma lem6188001 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (op x) = (op x).
Proof. exact (eq_refl (op x)). Qed.
Lemma lem6188002 {_123419 : Type'} (x : _123419) (op : type1400 _123419) (y : _123419) (z : _123419) : (term435 _123419 x op y z) = (term1219 _123419 x op y z).
Proof. exact (MK_COMB (@lem6188001 _123419 op x) (@lem6188000 _123419 op y z)). Qed.
Lemma lem6188004 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188005 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6188004 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6188006 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (op x) = (@I (_123419 -> _123419 -> _123419) op x).
Proof. exact (@lem6188005 _123419 op x). Qed.
Lemma lem6188007 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (z : _123419) : (term1218 _123419 op y z) = (term1218 _123419 op y z).
Proof. exact (eq_refl (term1218 _123419 op y z)). Qed.
Lemma lem6188008 {_123419 : Type'} (x : _123419) (op : type1400 _123419) (y : _123419) (z : _123419) : (term1219 _123419 x op y z) = (term1220 _123419 x op y z).
Proof. exact (MK_COMB (@lem6188006 _123419 op x) (@lem6188007 _123419 op y z)). Qed.
Lemma lem6188010 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188011 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6188010 _123419 _123419 f x). Qed.
Lemma lem6188012 {_123419 : Type'} (x : _123419) (op : type1400 _123419) (y : _123419) (z : _123419) : (term1220 _123419 x op y z) = (term1221 _123419 x op y z).
Proof. exact (@lem6188011 _123419 (@I (_123419 -> _123419 -> _123419) op x) (term1218 _123419 op y z)). Qed.
Lemma lem6188013 {_123419 : Type'} (x : _123419) (op : type1400 _123419) (y : _123419) (z : _123419) : (term1219 _123419 x op y z) = (term1221 _123419 x op y z).
Proof. exact (TRANS (@lem6188008 _123419 x op y z) (@lem6188012 _123419 x op y z)). Qed.
Lemma lem6188014 {_123419 : Type'} (x : _123419) (op : type1400 _123419) (y : _123419) (z : _123419) : (term435 _123419 x op y z) = (term1221 _123419 x op y z).
Proof. exact (TRANS (@lem6188002 _123419 x op y z) (@lem6188013 _123419 x op y z)). Qed.
Lemma lem6188015 {_123419 : Type'} (op : type1400 _123419) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6188022 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188023 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6188022 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6188024 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (op x) = (@I (_123419 -> _123419 -> _123419) op x).
Proof. exact (@lem6188023 _123419 op x). Qed.
Lemma lem6188025 {_123419 : Type'} (y : _123419) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6188026 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (op x y) = (@I (_123419 -> _123419 -> _123419) op x y).
Proof. exact (MK_COMB (@lem6188024 _123419 op x) (@lem6188025 _123419 y)). Qed.
Lemma lem6188028 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188029 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6188028 _123419 _123419 f x). Qed.
Lemma lem6188030 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (@I (_123419 -> _123419 -> _123419) op x y) = (term1218 _123419 op x y).
Proof. exact (@lem6188029 _123419 (@I (_123419 -> _123419 -> _123419) op x) y). Qed.
Lemma lem6188032 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (op x y) = (term1218 _123419 op x y).
Proof. exact (TRANS (@lem6188026 _123419 op x y) (@lem6188030 _123419 op x y)). Qed.
Lemma lem6188033 {_123419 : Type'} (z : _123419) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem6188034 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term1222 _123419 op x y) = (term1223 _123419 op x y).
Proof. exact (MK_COMB (@lem6188015 _123419 op) (@lem6188032 _123419 op x y)). Qed.
Lemma lem6188035 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : (term436 _123419 op x y z) = (term1224 _123419 op x y z).
Proof. exact (MK_COMB (@lem6188034 _123419 op x y) (@lem6188033 _123419 z)). Qed.
Lemma lem6188037 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188038 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6188037 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6188039 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term1223 _123419 op x y) = (term1225 _123419 op x y).
Proof. exact (@lem6188038 _123419 op (term1218 _123419 op x y)). Qed.
Lemma lem6188040 {_123419 : Type'} (z : _123419) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem6188041 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : (term1224 _123419 op x y z) = (term1226 _123419 op x y z).
Proof. exact (MK_COMB (@lem6188039 _123419 op x y) (@lem6188040 _123419 z)). Qed.
Lemma lem6188043 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188044 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6188043 _123419 _123419 f x). Qed.
Lemma lem6188045 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : (term1226 _123419 op x y z) = (term1227 _123419 op x y z).
Proof. exact (@lem6188044 _123419 (term1225 _123419 op x y) z). Qed.
Lemma lem6188046 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : (term1224 _123419 op x y z) = (term1227 _123419 op x y z).
Proof. exact (TRANS (@lem6188041 _123419 op x y z) (@lem6188045 _123419 op x y z)). Qed.
Lemma lem6188047 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : (term436 _123419 op x y z) = (term1227 _123419 op x y z).
Proof. exact (TRANS (@lem6188035 _123419 op x y z) (@lem6188046 _123419 op x y z)). Qed.
Lemma lem6188048 {_123419 : Type'} (x : _123419) (op : type1400 _123419) (y : _123419) (z : _123419) : (term1228 _123419 x op y z) = (term1229 _123419 x op y z).
Proof. exact (MK_COMB (@lem6187981 _123419) (@lem6188014 _123419 x op y z)). Qed.
Lemma lem6188049 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : ((term435 _123419 x op y z) = (term436 _123419 op x y z)) = ((term1221 _123419 x op y z) = (term1227 _123419 op x y z)).
Proof. exact (MK_COMB (@lem6188048 _123419 x op y z) (@lem6188047 _123419 op x y z)). Qed.
Lemma lem6188050 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term437 _123419 op x y) = (term1230 _123419 op x y).
Proof. exact (fun_ext (fun z : _123419 => @lem6188049 _123419 op x y z)). Qed.
Lemma lem6188051 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188052 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term438 _123419 op x y) = (term1231 _123419 op x y).
Proof. exact (MK_COMB (@lem6188051 _123419) (@lem6188050 _123419 op x y)). Qed.
Lemma lem6188053 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term439 _123419 op x) = (term1232 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6188052 _123419 op x y)). Qed.
Lemma lem6188054 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188055 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term440 _123419 op x) = (term1233 _123419 op x).
Proof. exact (MK_COMB (@lem6188054 _123419) (@lem6188053 _123419 op x)). Qed.
Lemma lem6188056 {_123419 : Type'} (op : type1400 _123419) : (term441 _123419 op) = (term1234 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6188055 _123419 op x)). Qed.
Lemma lem6188057 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188058 {_123419 : Type'} (op : type1400 _123419) : (term442 _123419 op) = (term1235 _123419 op).
Proof. exact (MK_COMB (@lem6188057 _123419) (@lem6188056 _123419 op)). Qed.
Lemma lem6188059 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6188060 {_123419 : Type'} (op : type1400 _123419) : (term443 _123419 op) = (term1236 _123419 op).
Proof. exact (MK_COMB (@lem6188059) (@lem6188058 _123419 op)). Qed.
Lemma lem6188061 {_123419 : Type'} (op : type1400 _123419) : (term444 _123419 op) = (term1237 _123419 op).
Proof. exact (MK_COMB (@lem6188060 _123419 op) (@lem6187980 _123419 op)). Qed.
Lemma lem6188062 {_123419 : Type'} : (@eq _123419) = (@eq _123419).
Proof. exact (eq_refl (@eq _123419)). Qed.
Lemma lem6188069 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188070 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6188069 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6188071 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (op x) = (@I (_123419 -> _123419 -> _123419) op x).
Proof. exact (@lem6188070 _123419 op x). Qed.
Lemma lem6188072 {_123419 : Type'} (y : _123419) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6188073 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (op x y) = (@I (_123419 -> _123419 -> _123419) op x y).
Proof. exact (MK_COMB (@lem6188071 _123419 op x) (@lem6188072 _123419 y)). Qed.
Lemma lem6188075 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188076 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6188075 _123419 _123419 f x). Qed.
Lemma lem6188077 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (@I (_123419 -> _123419 -> _123419) op x y) = (term1218 _123419 op x y).
Proof. exact (@lem6188076 _123419 (@I (_123419 -> _123419 -> _123419) op x) y). Qed.
Lemma lem6188079 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (op x y) = (term1218 _123419 op x y).
Proof. exact (TRANS (@lem6188073 _123419 op x y) (@lem6188077 _123419 op x y)). Qed.
Lemma lem6188086 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188087 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6188086 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6188088 {_123419 : Type'} (op : type1400 _123419) (y : _123419) : (op y) = (@I (_123419 -> _123419 -> _123419) op y).
Proof. exact (@lem6188087 _123419 op y). Qed.
Lemma lem6188089 {_123419 : Type'} (x : _123419) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6188090 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (op y x) = (@I (_123419 -> _123419 -> _123419) op y x).
Proof. exact (MK_COMB (@lem6188088 _123419 op y) (@lem6188089 _123419 x)). Qed.
Lemma lem6188092 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188093 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6188092 _123419 _123419 f x). Qed.
Lemma lem6188094 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (@I (_123419 -> _123419 -> _123419) op y x) = (term1218 _123419 op y x).
Proof. exact (@lem6188093 _123419 (@I (_123419 -> _123419 -> _123419) op y) x). Qed.
Lemma lem6188096 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (op y x) = (term1218 _123419 op y x).
Proof. exact (TRANS (@lem6188090 _123419 op y x) (@lem6188094 _123419 op y x)). Qed.
Lemma lem6188097 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term1238 _123419 op x y) = (term1239 _123419 op x y).
Proof. exact (MK_COMB (@lem6188062 _123419) (@lem6188079 _123419 op x y)). Qed.
Lemma lem6188098 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : ((op x y) = (op y x)) = ((term1218 _123419 op x y) = (term1218 _123419 op y x)).
Proof. exact (MK_COMB (@lem6188097 _123419 op x y) (@lem6188096 _123419 op y x)). Qed.
Lemma lem6188099 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term445 _123419 op x) = (term1240 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6188098 _123419 op y x)). Qed.
Lemma lem6188100 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188101 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term446 _123419 op x) = (term1241 _123419 op x).
Proof. exact (MK_COMB (@lem6188100 _123419) (@lem6188099 _123419 op x)). Qed.
Lemma lem6188102 {_123419 : Type'} (op : type1400 _123419) : (term447 _123419 op) = (term1242 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6188101 _123419 op x)). Qed.
Lemma lem6188103 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188104 {_123419 : Type'} (op : type1400 _123419) : (term448 _123419 op) = (term1243 _123419 op).
Proof. exact (MK_COMB (@lem6188103 _123419) (@lem6188102 _123419 op)). Qed.
Lemma lem6188105 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6188106 {_123419 : Type'} (op : type1400 _123419) : (term449 _123419 op) = (term1244 _123419 op).
Proof. exact (MK_COMB (@lem6188105) (@lem6188104 _123419 op)). Qed.
Lemma lem6188107 {_123419 : Type'} (op : type1400 _123419) : (term450 _123419 op) = (term1245 _123419 op).
Proof. exact (MK_COMB (@lem6188106 _123419 op) (@lem6188061 _123419 op)). Qed.
Lemma lem6188108 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6188113 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188114 {_123419 : Type'} (f : type403 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> Prop) f x).
Proof. exact (@lem6188113 (type1400 _123419) Prop f x). Qed.
Lemma lem6188116 {_123419 : Type'} (op : type1400 _123419) : (@monoidal _123419 op) = (@I ((_123419 -> _123419 -> _123419) -> Prop) (@monoidal _123419) op).
Proof. exact (@lem6188114 _123419 (@monoidal _123419) op). Qed.
Lemma lem6188117 {_123419 : Type'} (op : type1400 _123419) : (term1246 _123419 op) = (term1247 _123419 op).
Proof. exact (MK_COMB (@lem6188108) (@lem6188116 _123419 op)). Qed.
Lemma lem6188118 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6188119 {_123419 : Type'} (op : type1400 _123419) : (term510 _123419 op) = (term1248 _123419 op).
Proof. exact (MK_COMB (@lem6188118) (@lem6188117 _123419 op)). Qed.
Lemma lem6188120 {_123419 : Type'} (op : type1400 _123419) : (term511 _123419 op) = (term1249 _123419 op).
Proof. exact (MK_COMB (@lem6188119 _123419 op) (@lem6188107 _123419 op)). Qed.
Lemma lem6188121 {_123419 : Type'} : (term528 _123419) = (term1250 _123419).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6188120 _123419 op)). Qed.
Lemma lem6188122 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6188123 {_123419 : Type'} : (term543 _123419) = (term1251 _123419).
Proof. exact (MK_COMB (@lem6188122 _123419) (@lem6188121 _123419)). Qed.
Lemma lem6188124 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6188125 {_123419 : Type'} : (@eq _123419) = (@eq _123419).
Proof. exact (eq_refl (@eq _123419)). Qed.
Lemma lem6188126 {_123419 : Type'} (op : type1400 _123419) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6188131 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188132 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6188131 (type1400 _123419) _123419 f x). Qed.
Lemma lem6188134 {_123419 : Type'} (op : type1400 _123419) : (@neutral _123419 op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) (@neutral _123419) op).
Proof. exact (@lem6188132 _123419 (@neutral _123419) op). Qed.
Lemma lem6188139 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188140 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6188139 (type1400 _123419) _123419 f x). Qed.
Lemma lem6188142 {_123419 : Type'} (x' : type402 _123419) (op : type1400 _123419) : (x' op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) x' op).
Proof. exact (@lem6188140 _123419 x' op). Qed.
Lemma lem6188143 {_123419 : Type'} (op : type1400 _123419) : (term1208 _123419 op) = (term1209 _123419 op).
Proof. exact (MK_COMB (@lem6188126 _123419 op) (@lem6188134 _123419 op)). Qed.
Lemma lem6188144 {_123419 : Type'} (x' : type402 _123419) (op : type1400 _123419) : (term1252 _123419 x' op) = (term1253 _123419 x' op).
Proof. exact (MK_COMB (@lem6188143 _123419 op) (@lem6188142 _123419 x' op)). Qed.
Lemma lem6188146 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188147 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6188146 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6188148 {_123419 : Type'} (op : type1400 _123419) : (term1209 _123419 op) = (term1211 _123419 op).
Proof. exact (@lem6188147 _123419 op (@I ((_123419 -> _123419 -> _123419) -> _123419) (@neutral _123419) op)). Qed.
Lemma lem6188149 {_123419 : Type'} (x' : type402 _123419) (op : type1400 _123419) : (@I ((_123419 -> _123419 -> _123419) -> _123419) x' op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) x' op).
Proof. exact (eq_refl (@I ((_123419 -> _123419 -> _123419) -> _123419) x' op)). Qed.
Lemma lem6188150 {_123419 : Type'} (x' : type402 _123419) (op : type1400 _123419) : (term1253 _123419 x' op) = (term1254 _123419 x' op).
Proof. exact (MK_COMB (@lem6188148 _123419 op) (@lem6188149 _123419 x' op)). Qed.
Lemma lem6188152 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188153 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6188152 _123419 _123419 f x). Qed.
Lemma lem6188154 {_123419 : Type'} (x' : type402 _123419) (op : type1400 _123419) : (term1254 _123419 x' op) = (term1255 _123419 x' op).
Proof. exact (@lem6188153 _123419 (term1211 _123419 op) (@I ((_123419 -> _123419 -> _123419) -> _123419) x' op)). Qed.
Lemma lem6188155 {_123419 : Type'} (x' : type402 _123419) (op : type1400 _123419) : (term1253 _123419 x' op) = (term1255 _123419 x' op).
Proof. exact (TRANS (@lem6188150 _123419 x' op) (@lem6188154 _123419 x' op)). Qed.
Lemma lem6188156 {_123419 : Type'} (x' : type402 _123419) (op : type1400 _123419) : (term1252 _123419 x' op) = (term1255 _123419 x' op).
Proof. exact (TRANS (@lem6188144 _123419 x' op) (@lem6188155 _123419 x' op)). Qed.
Lemma lem6188161 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188162 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6188161 (type1400 _123419) _123419 f x). Qed.
Lemma lem6188164 {_123419 : Type'} (x' : type402 _123419) (op : type1400 _123419) : (x' op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) x' op).
Proof. exact (@lem6188162 _123419 x' op). Qed.
Lemma lem6188165 {_123419 : Type'} (x' : type402 _123419) (op : type1400 _123419) : (term1256 _123419 x' op) = (term1257 _123419 x' op).
Proof. exact (MK_COMB (@lem6188125 _123419) (@lem6188156 _123419 x' op)). Qed.
Lemma lem6188166 {_123419 : Type'} (x' : type402 _123419) (op : type1400 _123419) : ((term1252 _123419 x' op) = (x' op)) = ((term1255 _123419 x' op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) x' op)).
Proof. exact (MK_COMB (@lem6188165 _123419 x' op) (@lem6188164 _123419 x' op)). Qed.
Lemma lem6188167 {_123419 : Type'} (x' : type402 _123419) (op : type1400 _123419) : (term1258 _123419 x' op) = (term1259 _123419 x' op).
Proof. exact (MK_COMB (@lem6188124) (@lem6188166 _123419 x' op)). Qed.
Lemma lem6188168 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6188169 {_123419 : Type'} : (@eq _123419) = (@eq _123419).
Proof. exact (eq_refl (@eq _123419)). Qed.
Lemma lem6188170 {_123419 : Type'} (op : type1400 _123419) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6188175 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188176 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6188175 (type1400 _123419) _123419 f x). Qed.
Lemma lem6188178 {_123419 : Type'} (x' : type402 _123419) (op : type1400 _123419) : (x' op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) x' op).
Proof. exact (@lem6188176 _123419 x' op). Qed.
Lemma lem6188179 {_123419 : Type'} (op : type1400 _123419) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6188184 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188185 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6188184 (type1400 _123419) _123419 f x). Qed.
Lemma lem6188187 {_123419 : Type'} (y' : type402 _123419) (op : type1400 _123419) : (y' op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) y' op).
Proof. exact (@lem6188185 _123419 y' op). Qed.
Lemma lem6188192 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188193 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6188192 (type1400 _123419) _123419 f x). Qed.
Lemma lem6188195 {_123419 : Type'} (z' : type402 _123419) (op : type1400 _123419) : (z' op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) z' op).
Proof. exact (@lem6188193 _123419 z' op). Qed.
Lemma lem6188196 {_123419 : Type'} (y' : type402 _123419) (op : type1400 _123419) : (term1260 _123419 y' op) = (term1261 _123419 y' op).
Proof. exact (MK_COMB (@lem6188179 _123419 op) (@lem6188187 _123419 y' op)). Qed.
Lemma lem6188197 {_123419 : Type'} (y' : type402 _123419) (z' : type402 _123419) (op : type1400 _123419) : (term1262 _123419 y' z' op) = (term1263 _123419 y' z' op).
Proof. exact (MK_COMB (@lem6188196 _123419 y' op) (@lem6188195 _123419 z' op)). Qed.
Lemma lem6188199 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188200 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6188199 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6188201 {_123419 : Type'} (y' : type402 _123419) (op : type1400 _123419) : (term1261 _123419 y' op) = (term1264 _123419 y' op).
Proof. exact (@lem6188200 _123419 op (@I ((_123419 -> _123419 -> _123419) -> _123419) y' op)). Qed.
Lemma lem6188202 {_123419 : Type'} (z' : type402 _123419) (op : type1400 _123419) : (@I ((_123419 -> _123419 -> _123419) -> _123419) z' op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) z' op).
Proof. exact (eq_refl (@I ((_123419 -> _123419 -> _123419) -> _123419) z' op)). Qed.
Lemma lem6188203 {_123419 : Type'} (y' : type402 _123419) (z' : type402 _123419) (op : type1400 _123419) : (term1263 _123419 y' z' op) = (term1265 _123419 y' z' op).
Proof. exact (MK_COMB (@lem6188201 _123419 y' op) (@lem6188202 _123419 z' op)). Qed.
Lemma lem6188205 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188206 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6188205 _123419 _123419 f x). Qed.
Lemma lem6188207 {_123419 : Type'} (y' : type402 _123419) (z' : type402 _123419) (op : type1400 _123419) : (term1265 _123419 y' z' op) = (term1266 _123419 y' z' op).
Proof. exact (@lem6188206 _123419 (term1264 _123419 y' op) (@I ((_123419 -> _123419 -> _123419) -> _123419) z' op)). Qed.
Lemma lem6188208 {_123419 : Type'} (y' : type402 _123419) (z' : type402 _123419) (op : type1400 _123419) : (term1263 _123419 y' z' op) = (term1266 _123419 y' z' op).
Proof. exact (TRANS (@lem6188203 _123419 y' z' op) (@lem6188207 _123419 y' z' op)). Qed.
Lemma lem6188209 {_123419 : Type'} (y' : type402 _123419) (z' : type402 _123419) (op : type1400 _123419) : (term1262 _123419 y' z' op) = (term1266 _123419 y' z' op).
Proof. exact (TRANS (@lem6188197 _123419 y' z' op) (@lem6188208 _123419 y' z' op)). Qed.
Lemma lem6188210 {_123419 : Type'} (x' : type402 _123419) (op : type1400 _123419) : (term1260 _123419 x' op) = (term1261 _123419 x' op).
Proof. exact (MK_COMB (@lem6188170 _123419 op) (@lem6188178 _123419 x' op)). Qed.
Lemma lem6188211 {_123419 : Type'} (x' : type402 _123419) (y' : type402 _123419) (z' : type402 _123419) (op : type1400 _123419) : (term1267 _123419 x' y' z' op) = (term1268 _123419 x' y' z' op).
Proof. exact (MK_COMB (@lem6188210 _123419 x' op) (@lem6188209 _123419 y' z' op)). Qed.
Lemma lem6188213 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188214 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6188213 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6188215 {_123419 : Type'} (x' : type402 _123419) (op : type1400 _123419) : (term1261 _123419 x' op) = (term1264 _123419 x' op).
Proof. exact (@lem6188214 _123419 op (@I ((_123419 -> _123419 -> _123419) -> _123419) x' op)). Qed.
Lemma lem6188216 {_123419 : Type'} (y' : type402 _123419) (z' : type402 _123419) (op : type1400 _123419) : (term1266 _123419 y' z' op) = (term1266 _123419 y' z' op).
Proof. exact (eq_refl (term1266 _123419 y' z' op)). Qed.
Lemma lem6188217 {_123419 : Type'} (x' : type402 _123419) (y' : type402 _123419) (z' : type402 _123419) (op : type1400 _123419) : (term1268 _123419 x' y' z' op) = (term1269 _123419 x' y' z' op).
Proof. exact (MK_COMB (@lem6188215 _123419 x' op) (@lem6188216 _123419 y' z' op)). Qed.
Lemma lem6188219 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188220 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6188219 _123419 _123419 f x). Qed.
Lemma lem6188221 {_123419 : Type'} (x' : type402 _123419) (y' : type402 _123419) (z' : type402 _123419) (op : type1400 _123419) : (term1269 _123419 x' y' z' op) = (term1270 _123419 x' y' z' op).
Proof. exact (@lem6188220 _123419 (term1264 _123419 x' op) (term1266 _123419 y' z' op)). Qed.
Lemma lem6188222 {_123419 : Type'} (x' : type402 _123419) (y' : type402 _123419) (z' : type402 _123419) (op : type1400 _123419) : (term1268 _123419 x' y' z' op) = (term1270 _123419 x' y' z' op).
Proof. exact (TRANS (@lem6188217 _123419 x' y' z' op) (@lem6188221 _123419 x' y' z' op)). Qed.
Lemma lem6188223 {_123419 : Type'} (x' : type402 _123419) (y' : type402 _123419) (z' : type402 _123419) (op : type1400 _123419) : (term1267 _123419 x' y' z' op) = (term1270 _123419 x' y' z' op).
Proof. exact (TRANS (@lem6188211 _123419 x' y' z' op) (@lem6188222 _123419 x' y' z' op)). Qed.
Lemma lem6188224 {_123419 : Type'} (op : type1400 _123419) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6188225 {_123419 : Type'} (op : type1400 _123419) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6188230 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188231 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6188230 (type1400 _123419) _123419 f x). Qed.
Lemma lem6188233 {_123419 : Type'} (x' : type402 _123419) (op : type1400 _123419) : (x' op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) x' op).
Proof. exact (@lem6188231 _123419 x' op). Qed.
Lemma lem6188238 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188239 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6188238 (type1400 _123419) _123419 f x). Qed.
Lemma lem6188241 {_123419 : Type'} (y' : type402 _123419) (op : type1400 _123419) : (y' op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) y' op).
Proof. exact (@lem6188239 _123419 y' op). Qed.
Lemma lem6188242 {_123419 : Type'} (x' : type402 _123419) (op : type1400 _123419) : (term1260 _123419 x' op) = (term1261 _123419 x' op).
Proof. exact (MK_COMB (@lem6188225 _123419 op) (@lem6188233 _123419 x' op)). Qed.
Lemma lem6188243 {_123419 : Type'} (x' : type402 _123419) (y' : type402 _123419) (op : type1400 _123419) : (term1262 _123419 x' y' op) = (term1263 _123419 x' y' op).
Proof. exact (MK_COMB (@lem6188242 _123419 x' op) (@lem6188241 _123419 y' op)). Qed.
Lemma lem6188245 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188246 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6188245 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6188247 {_123419 : Type'} (x' : type402 _123419) (op : type1400 _123419) : (term1261 _123419 x' op) = (term1264 _123419 x' op).
Proof. exact (@lem6188246 _123419 op (@I ((_123419 -> _123419 -> _123419) -> _123419) x' op)). Qed.
Lemma lem6188248 {_123419 : Type'} (y' : type402 _123419) (op : type1400 _123419) : (@I ((_123419 -> _123419 -> _123419) -> _123419) y' op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) y' op).
Proof. exact (eq_refl (@I ((_123419 -> _123419 -> _123419) -> _123419) y' op)). Qed.
Lemma lem6188249 {_123419 : Type'} (x' : type402 _123419) (y' : type402 _123419) (op : type1400 _123419) : (term1263 _123419 x' y' op) = (term1265 _123419 x' y' op).
Proof. exact (MK_COMB (@lem6188247 _123419 x' op) (@lem6188248 _123419 y' op)). Qed.
Lemma lem6188251 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188252 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6188251 _123419 _123419 f x). Qed.
Lemma lem6188253 {_123419 : Type'} (x' : type402 _123419) (y' : type402 _123419) (op : type1400 _123419) : (term1265 _123419 x' y' op) = (term1266 _123419 x' y' op).
Proof. exact (@lem6188252 _123419 (term1264 _123419 x' op) (@I ((_123419 -> _123419 -> _123419) -> _123419) y' op)). Qed.
Lemma lem6188254 {_123419 : Type'} (x' : type402 _123419) (y' : type402 _123419) (op : type1400 _123419) : (term1263 _123419 x' y' op) = (term1266 _123419 x' y' op).
Proof. exact (TRANS (@lem6188249 _123419 x' y' op) (@lem6188253 _123419 x' y' op)). Qed.
Lemma lem6188255 {_123419 : Type'} (x' : type402 _123419) (y' : type402 _123419) (op : type1400 _123419) : (term1262 _123419 x' y' op) = (term1266 _123419 x' y' op).
Proof. exact (TRANS (@lem6188243 _123419 x' y' op) (@lem6188254 _123419 x' y' op)). Qed.
Lemma lem6188260 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188261 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6188260 (type1400 _123419) _123419 f x). Qed.
Lemma lem6188263 {_123419 : Type'} (z' : type402 _123419) (op : type1400 _123419) : (z' op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) z' op).
Proof. exact (@lem6188261 _123419 z' op). Qed.
Lemma lem6188264 {_123419 : Type'} (x' : type402 _123419) (y' : type402 _123419) (op : type1400 _123419) : (term1271 _123419 x' y' op) = (term1272 _123419 x' y' op).
Proof. exact (MK_COMB (@lem6188224 _123419 op) (@lem6188255 _123419 x' y' op)). Qed.
Lemma lem6188265 {_123419 : Type'} (x' : type402 _123419) (y' : type402 _123419) (z' : type402 _123419) (op : type1400 _123419) : (term1273 _123419 x' y' z' op) = (term1274 _123419 x' y' z' op).
Proof. exact (MK_COMB (@lem6188264 _123419 x' y' op) (@lem6188263 _123419 z' op)). Qed.
Lemma lem6188267 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188268 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6188267 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6188269 {_123419 : Type'} (x' : type402 _123419) (y' : type402 _123419) (op : type1400 _123419) : (term1272 _123419 x' y' op) = (term1275 _123419 x' y' op).
Proof. exact (@lem6188268 _123419 op (term1266 _123419 x' y' op)). Qed.
Lemma lem6188270 {_123419 : Type'} (z' : type402 _123419) (op : type1400 _123419) : (@I ((_123419 -> _123419 -> _123419) -> _123419) z' op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) z' op).
Proof. exact (eq_refl (@I ((_123419 -> _123419 -> _123419) -> _123419) z' op)). Qed.
Lemma lem6188271 {_123419 : Type'} (x' : type402 _123419) (y' : type402 _123419) (z' : type402 _123419) (op : type1400 _123419) : (term1274 _123419 x' y' z' op) = (term1276 _123419 x' y' z' op).
Proof. exact (MK_COMB (@lem6188269 _123419 x' y' op) (@lem6188270 _123419 z' op)). Qed.
Lemma lem6188273 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188274 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6188273 _123419 _123419 f x). Qed.
Lemma lem6188275 {_123419 : Type'} (x' : type402 _123419) (y' : type402 _123419) (z' : type402 _123419) (op : type1400 _123419) : (term1276 _123419 x' y' z' op) = (term1277 _123419 x' y' z' op).
Proof. exact (@lem6188274 _123419 (term1275 _123419 x' y' op) (@I ((_123419 -> _123419 -> _123419) -> _123419) z' op)). Qed.
Lemma lem6188276 {_123419 : Type'} (x' : type402 _123419) (y' : type402 _123419) (z' : type402 _123419) (op : type1400 _123419) : (term1274 _123419 x' y' z' op) = (term1277 _123419 x' y' z' op).
Proof. exact (TRANS (@lem6188271 _123419 x' y' z' op) (@lem6188275 _123419 x' y' z' op)). Qed.
Lemma lem6188277 {_123419 : Type'} (x' : type402 _123419) (y' : type402 _123419) (z' : type402 _123419) (op : type1400 _123419) : (term1273 _123419 x' y' z' op) = (term1277 _123419 x' y' z' op).
Proof. exact (TRANS (@lem6188265 _123419 x' y' z' op) (@lem6188276 _123419 x' y' z' op)). Qed.
Lemma lem6188278 {_123419 : Type'} (x' : type402 _123419) (y' : type402 _123419) (z' : type402 _123419) (op : type1400 _123419) : (term1278 _123419 x' y' z' op) = (term1279 _123419 x' y' z' op).
Proof. exact (MK_COMB (@lem6188169 _123419) (@lem6188223 _123419 x' y' z' op)). Qed.
Lemma lem6188279 {_123419 : Type'} (x' : type402 _123419) (y' : type402 _123419) (z' : type402 _123419) (op : type1400 _123419) : ((term1267 _123419 x' y' z' op) = (term1273 _123419 x' y' z' op)) = ((term1270 _123419 x' y' z' op) = (term1277 _123419 x' y' z' op)).
Proof. exact (MK_COMB (@lem6188278 _123419 x' y' z' op) (@lem6188277 _123419 x' y' z' op)). Qed.
Lemma lem6188280 {_123419 : Type'} (x' : type402 _123419) (y' : type402 _123419) (z' : type402 _123419) (op : type1400 _123419) : (term1280 _123419 x' y' z' op) = (term1281 _123419 x' y' z' op).
Proof. exact (MK_COMB (@lem6188168) (@lem6188279 _123419 x' y' z' op)). Qed.
Lemma lem6188281 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6188282 {_123419 : Type'} (x' : type402 _123419) (y' : type402 _123419) (z' : type402 _123419) (op : type1400 _123419) : (term1282 _123419 x' y' z' op) = (term1283 _123419 x' y' z' op).
Proof. exact (MK_COMB (@lem6188281) (@lem6188280 _123419 x' y' z' op)). Qed.
Lemma lem6188283 {_123419 : Type'} (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (op : type1400 _123419) : (term1284 _123419 y' z' x' op) = (term1285 _123419 y' z' x' op).
Proof. exact (MK_COMB (@lem6188282 _123419 x' y' z' op) (@lem6188167 _123419 x' op)). Qed.
Lemma lem6188284 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6188285 {_123419 : Type'} : (@eq _123419) = (@eq _123419).
Proof. exact (eq_refl (@eq _123419)). Qed.
Lemma lem6188286 {_123419 : Type'} (op : type1400 _123419) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6188291 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188292 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6188291 (type1400 _123419) _123419 f x). Qed.
Lemma lem6188294 {_123419 : Type'} (x' : type402 _123419) (op : type1400 _123419) : (x' op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) x' op).
Proof. exact (@lem6188292 _123419 x' op). Qed.
Lemma lem6188299 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188300 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6188299 (type1400 _123419) _123419 f x). Qed.
Lemma lem6188302 {_123419 : Type'} (y' : type402 _123419) (op : type1400 _123419) : (y' op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) y' op).
Proof. exact (@lem6188300 _123419 y' op). Qed.
Lemma lem6188303 {_123419 : Type'} (x' : type402 _123419) (op : type1400 _123419) : (term1260 _123419 x' op) = (term1261 _123419 x' op).
Proof. exact (MK_COMB (@lem6188286 _123419 op) (@lem6188294 _123419 x' op)). Qed.
Lemma lem6188304 {_123419 : Type'} (x' : type402 _123419) (y' : type402 _123419) (op : type1400 _123419) : (term1262 _123419 x' y' op) = (term1263 _123419 x' y' op).
Proof. exact (MK_COMB (@lem6188303 _123419 x' op) (@lem6188302 _123419 y' op)). Qed.
Lemma lem6188306 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188307 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6188306 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6188308 {_123419 : Type'} (x' : type402 _123419) (op : type1400 _123419) : (term1261 _123419 x' op) = (term1264 _123419 x' op).
Proof. exact (@lem6188307 _123419 op (@I ((_123419 -> _123419 -> _123419) -> _123419) x' op)). Qed.
Lemma lem6188309 {_123419 : Type'} (y' : type402 _123419) (op : type1400 _123419) : (@I ((_123419 -> _123419 -> _123419) -> _123419) y' op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) y' op).
Proof. exact (eq_refl (@I ((_123419 -> _123419 -> _123419) -> _123419) y' op)). Qed.
Lemma lem6188310 {_123419 : Type'} (x' : type402 _123419) (y' : type402 _123419) (op : type1400 _123419) : (term1263 _123419 x' y' op) = (term1265 _123419 x' y' op).
Proof. exact (MK_COMB (@lem6188308 _123419 x' op) (@lem6188309 _123419 y' op)). Qed.
Lemma lem6188312 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188313 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6188312 _123419 _123419 f x). Qed.
Lemma lem6188314 {_123419 : Type'} (x' : type402 _123419) (y' : type402 _123419) (op : type1400 _123419) : (term1265 _123419 x' y' op) = (term1266 _123419 x' y' op).
Proof. exact (@lem6188313 _123419 (term1264 _123419 x' op) (@I ((_123419 -> _123419 -> _123419) -> _123419) y' op)). Qed.
Lemma lem6188315 {_123419 : Type'} (x' : type402 _123419) (y' : type402 _123419) (op : type1400 _123419) : (term1263 _123419 x' y' op) = (term1266 _123419 x' y' op).
Proof. exact (TRANS (@lem6188310 _123419 x' y' op) (@lem6188314 _123419 x' y' op)). Qed.
Lemma lem6188316 {_123419 : Type'} (x' : type402 _123419) (y' : type402 _123419) (op : type1400 _123419) : (term1262 _123419 x' y' op) = (term1266 _123419 x' y' op).
Proof. exact (TRANS (@lem6188304 _123419 x' y' op) (@lem6188315 _123419 x' y' op)). Qed.
Lemma lem6188317 {_123419 : Type'} (op : type1400 _123419) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6188322 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188323 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6188322 (type1400 _123419) _123419 f x). Qed.
Lemma lem6188325 {_123419 : Type'} (y' : type402 _123419) (op : type1400 _123419) : (y' op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) y' op).
Proof. exact (@lem6188323 _123419 y' op). Qed.
Lemma lem6188330 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188331 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6188330 (type1400 _123419) _123419 f x). Qed.
Lemma lem6188333 {_123419 : Type'} (x' : type402 _123419) (op : type1400 _123419) : (x' op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) x' op).
Proof. exact (@lem6188331 _123419 x' op). Qed.
Lemma lem6188334 {_123419 : Type'} (y' : type402 _123419) (op : type1400 _123419) : (term1260 _123419 y' op) = (term1261 _123419 y' op).
Proof. exact (MK_COMB (@lem6188317 _123419 op) (@lem6188325 _123419 y' op)). Qed.
Lemma lem6188335 {_123419 : Type'} (y' : type402 _123419) (x' : type402 _123419) (op : type1400 _123419) : (term1262 _123419 y' x' op) = (term1263 _123419 y' x' op).
Proof. exact (MK_COMB (@lem6188334 _123419 y' op) (@lem6188333 _123419 x' op)). Qed.
Lemma lem6188337 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188338 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6188337 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6188339 {_123419 : Type'} (y' : type402 _123419) (op : type1400 _123419) : (term1261 _123419 y' op) = (term1264 _123419 y' op).
Proof. exact (@lem6188338 _123419 op (@I ((_123419 -> _123419 -> _123419) -> _123419) y' op)). Qed.
Lemma lem6188340 {_123419 : Type'} (x' : type402 _123419) (op : type1400 _123419) : (@I ((_123419 -> _123419 -> _123419) -> _123419) x' op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) x' op).
Proof. exact (eq_refl (@I ((_123419 -> _123419 -> _123419) -> _123419) x' op)). Qed.
Lemma lem6188341 {_123419 : Type'} (y' : type402 _123419) (x' : type402 _123419) (op : type1400 _123419) : (term1263 _123419 y' x' op) = (term1265 _123419 y' x' op).
Proof. exact (MK_COMB (@lem6188339 _123419 y' op) (@lem6188340 _123419 x' op)). Qed.
Lemma lem6188343 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188344 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6188343 _123419 _123419 f x). Qed.
Lemma lem6188345 {_123419 : Type'} (y' : type402 _123419) (x' : type402 _123419) (op : type1400 _123419) : (term1265 _123419 y' x' op) = (term1266 _123419 y' x' op).
Proof. exact (@lem6188344 _123419 (term1264 _123419 y' op) (@I ((_123419 -> _123419 -> _123419) -> _123419) x' op)). Qed.
Lemma lem6188346 {_123419 : Type'} (y' : type402 _123419) (x' : type402 _123419) (op : type1400 _123419) : (term1263 _123419 y' x' op) = (term1266 _123419 y' x' op).
Proof. exact (TRANS (@lem6188341 _123419 y' x' op) (@lem6188345 _123419 y' x' op)). Qed.
Lemma lem6188347 {_123419 : Type'} (y' : type402 _123419) (x' : type402 _123419) (op : type1400 _123419) : (term1262 _123419 y' x' op) = (term1266 _123419 y' x' op).
Proof. exact (TRANS (@lem6188335 _123419 y' x' op) (@lem6188346 _123419 y' x' op)). Qed.
Lemma lem6188348 {_123419 : Type'} (x' : type402 _123419) (y' : type402 _123419) (op : type1400 _123419) : (term1286 _123419 x' y' op) = (term1287 _123419 x' y' op).
Proof. exact (MK_COMB (@lem6188285 _123419) (@lem6188316 _123419 x' y' op)). Qed.
Lemma lem6188349 {_123419 : Type'} (y' : type402 _123419) (x' : type402 _123419) (op : type1400 _123419) : ((term1262 _123419 x' y' op) = (term1262 _123419 y' x' op)) = ((term1266 _123419 x' y' op) = (term1266 _123419 y' x' op)).
Proof. exact (MK_COMB (@lem6188348 _123419 x' y' op) (@lem6188347 _123419 y' x' op)). Qed.
Lemma lem6188350 {_123419 : Type'} (y' : type402 _123419) (x' : type402 _123419) (op : type1400 _123419) : (term1288 _123419 y' x' op) = (term1289 _123419 y' x' op).
Proof. exact (MK_COMB (@lem6188284) (@lem6188349 _123419 y' x' op)). Qed.
Lemma lem6188351 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6188352 {_123419 : Type'} (y' : type402 _123419) (x' : type402 _123419) (op : type1400 _123419) : (term1290 _123419 y' x' op) = (term1291 _123419 y' x' op).
Proof. exact (MK_COMB (@lem6188351) (@lem6188350 _123419 y' x' op)). Qed.
Lemma lem6188353 {_123419 : Type'} (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (op : type1400 _123419) : (term1292 _123419 y' z' x' op) = (term1293 _123419 y' z' x' op).
Proof. exact (MK_COMB (@lem6188352 _123419 y' x' op) (@lem6188283 _123419 y' z' x' op)). Qed.
Lemma lem6188358 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6188359 {_123419 : Type'} (f : type403 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> Prop) f x).
Proof. exact (@lem6188358 (type1400 _123419) Prop f x). Qed.
Lemma lem6188361 {_123419 : Type'} (op : type1400 _123419) : (@monoidal _123419 op) = (@I ((_123419 -> _123419 -> _123419) -> Prop) (@monoidal _123419) op).
Proof. exact (@lem6188359 _123419 (@monoidal _123419) op). Qed.
Lemma lem6188362 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6188363 {_123419 : Type'} (op : type1400 _123419) : (term512 _123419 op) = (term1294 _123419 op).
Proof. exact (MK_COMB (@lem6188362) (@lem6188361 _123419 op)). Qed.
Lemma lem6188364 {_123419 : Type'} (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (op : type1400 _123419) : (term762 _123419 y' z' x' op) = (term1295 _123419 y' z' x' op).
Proof. exact (MK_COMB (@lem6188363 _123419 op) (@lem6188353 _123419 y' z' x' op)). Qed.
Lemma lem6188365 {_123419 : Type'} (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) : (term764 _123419 y' z' x') = (term1296 _123419 y' z' x').
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6188364 _123419 y' z' x' op)). Qed.
Lemma lem6188366 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6188367 {_123419 : Type'} (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) : (term766 _123419 y' z' x') = (term1297 _123419 y' z' x').
Proof. exact (MK_COMB (@lem6188366 _123419) (@lem6188365 _123419 y' z' x')). Qed.
Lemma lem6188368 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6188369 {_123419 : Type'} (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) : (term819 _123419 y' z' x') = (term1298 _123419 y' z' x').
Proof. exact (MK_COMB (@lem6188368) (@lem6188367 _123419 y' z' x')). Qed.
Lemma lem6188370 {_123419 : Type'} (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) : (term821 _123419 y' z' x') = (term1299 _123419 y' z' x').
Proof. exact (MK_COMB (@lem6188369 _123419 y' z' x') (@lem6188123 _123419)). Qed.
Lemma lem6188371 {_123419 : Type'} (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : term821 _123419 y' z' x') : term1299 _123419 y' z' x'.
Proof. exact (EQ_MP (@lem6188370 _123419 y' z' x') (@lem6187446 _123419 y' z' x' h1)). Qed.
Lemma lem6188372 {_123419 : Type'} (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : term821 _123419 y' z' x') : term1251 _123419.
Proof. exact (proj2 (@lem6188371 _123419 y' z' x' h1)). Qed.
Lemma lem6188414 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term522 A P Q) = (term521 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6188415 {_123419 : Type'} (P : _123419 -> Prop) (Q : _123419 -> Prop) : (term522 _123419 P Q) = (term521 _123419 P Q).
Proof. exact (@lem6188414 _123419 P Q). Qed.
Lemma lem6188416 {_123419 : Type'} (op : type1400 _123419) : (term1300 _123419 op) = (term1301 _123419 op).
Proof. exact (@lem6188415 _123419 (term1234 _123419 op) (term1216 _123419 op)). Qed.
Lemma lem6188417 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1302 _123419 op x) = (term1233 _123419 op x).
Proof. exact (eq_refl (term1302 _123419 op x)). Qed.
Lemma lem6188418 {_123419 : Type'} (op : type1400 _123419) : (term1303 _123419 op) = (term1234 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6188417 _123419 op x)). Qed.
Lemma lem6188419 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188420 {_123419 : Type'} (op : type1400 _123419) : (term1304 _123419 op) = (term1235 _123419 op).
Proof. exact (MK_COMB (@lem6188419 _123419) (@lem6188418 _123419 op)). Qed.
Lemma lem6188421 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6188422 {_123419 : Type'} (op : type1400 _123419) : (term1305 _123419 op) = (term1236 _123419 op).
Proof. exact (MK_COMB (@lem6188421) (@lem6188420 _123419 op)). Qed.
Lemma lem6188423 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1306 _123419 op x) = ((term1213 _123419 op x) = x).
Proof. exact (eq_refl (term1306 _123419 op x)). Qed.
Lemma lem6188424 {_123419 : Type'} (op : type1400 _123419) : (term1307 _123419 op) = (term1216 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6188423 _123419 op x)). Qed.
Lemma lem6188425 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188426 {_123419 : Type'} (op : type1400 _123419) : (term1308 _123419 op) = (term1217 _123419 op).
Proof. exact (MK_COMB (@lem6188425 _123419) (@lem6188424 _123419 op)). Qed.
Lemma lem6188427 {_123419 : Type'} (op : type1400 _123419) : (term1300 _123419 op) = (term1237 _123419 op).
Proof. exact (MK_COMB (@lem6188422 _123419 op) (@lem6188426 _123419 op)). Qed.
Lemma lem6188428 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6188429 {_123419 : Type'} (op : type1400 _123419) : (term1309 _123419 op) = (term1310 _123419 op).
Proof. exact (MK_COMB (@lem6188428) (@lem6188427 _123419 op)). Qed.
Lemma lem6188430 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1302 _123419 op x) = (term1233 _123419 op x).
Proof. exact (eq_refl (term1302 _123419 op x)). Qed.
Lemma lem6188431 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6188432 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1311 _123419 op x) = (term1312 _123419 op x).
Proof. exact (MK_COMB (@lem6188431) (@lem6188430 _123419 op x)). Qed.
Lemma lem6188433 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1306 _123419 op x) = ((term1213 _123419 op x) = x).
Proof. exact (eq_refl (term1306 _123419 op x)). Qed.
Lemma lem6188434 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1313 _123419 op x) = (term1314 _123419 op x).
Proof. exact (MK_COMB (@lem6188432 _123419 op x) (@lem6188433 _123419 op x)). Qed.
Lemma lem6188435 {_123419 : Type'} (op : type1400 _123419) : (term1315 _123419 op) = (term1316 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6188434 _123419 op x)). Qed.
Lemma lem6188436 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188437 {_123419 : Type'} (op : type1400 _123419) : (term1301 _123419 op) = (term1317 _123419 op).
Proof. exact (MK_COMB (@lem6188436 _123419) (@lem6188435 _123419 op)). Qed.
Lemma lem6188438 {_123419 : Type'} (op : type1400 _123419) : ((term1300 _123419 op) = (term1301 _123419 op)) = ((term1237 _123419 op) = (term1317 _123419 op)).
Proof. exact (MK_COMB (@lem6188429 _123419 op) (@lem6188437 _123419 op)). Qed.
Lemma lem6188439 {_123419 : Type'} (op : type1400 _123419) : (term1237 _123419 op) = (term1317 _123419 op).
Proof. exact (EQ_MP (@lem6188438 _123419 op) (@lem6188416 _123419 op)). Qed.
Lemma lem6188441 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1318 A P Q) = (term1319 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem6188442 {_123419 : Type'} (P : _123419 -> Prop) (Q : Prop) : (term1318 _123419 P Q) = (term1319 _123419 P Q).
Proof. exact (@lem6188441 _123419 P Q). Qed.
Lemma lem6188443 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1320 _123419 op x) = (term1321 _123419 op x).
Proof. exact (@lem6188442 _123419 (term1232 _123419 op x) ((term1213 _123419 op x) = x)). Qed.
Lemma lem6188444 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term1322 _123419 op x y) = (term1231 _123419 op x y).
Proof. exact (eq_refl (term1322 _123419 op x y)). Qed.
Lemma lem6188445 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1323 _123419 op x) = (term1232 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6188444 _123419 op x y)). Qed.
Lemma lem6188446 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188447 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1324 _123419 op x) = (term1233 _123419 op x).
Proof. exact (MK_COMB (@lem6188446 _123419) (@lem6188445 _123419 op x)). Qed.
Lemma lem6188448 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6188449 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1325 _123419 op x) = (term1312 _123419 op x).
Proof. exact (MK_COMB (@lem6188448) (@lem6188447 _123419 op x)). Qed.
Lemma lem6188450 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : ((term1213 _123419 op x) = x) = ((term1213 _123419 op x) = x).
Proof. exact (eq_refl ((term1213 _123419 op x) = x)). Qed.
Lemma lem6188451 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1320 _123419 op x) = (term1314 _123419 op x).
Proof. exact (MK_COMB (@lem6188449 _123419 op x) (@lem6188450 _123419 op x)). Qed.
Lemma lem6188452 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6188453 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1326 _123419 op x) = (term1327 _123419 op x).
Proof. exact (MK_COMB (@lem6188452) (@lem6188451 _123419 op x)). Qed.
Lemma lem6188454 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term1322 _123419 op x y) = (term1231 _123419 op x y).
Proof. exact (eq_refl (term1322 _123419 op x y)). Qed.
Lemma lem6188455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6188456 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term1328 _123419 op x y) = (term1329 _123419 op x y).
Proof. exact (MK_COMB (@lem6188455) (@lem6188454 _123419 op x y)). Qed.
Lemma lem6188457 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : ((term1213 _123419 op x) = x) = ((term1213 _123419 op x) = x).
Proof. exact (eq_refl ((term1213 _123419 op x) = x)). Qed.
Lemma lem6188458 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1330 _123419 y op x) = (term1331 _123419 y op x).
Proof. exact (MK_COMB (@lem6188456 _123419 op x y) (@lem6188457 _123419 op x)). Qed.
Lemma lem6188459 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1332 _123419 op x) = (term1333 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6188458 _123419 y op x)). Qed.
Lemma lem6188460 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188461 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1321 _123419 op x) = (term1334 _123419 op x).
Proof. exact (MK_COMB (@lem6188460 _123419) (@lem6188459 _123419 op x)). Qed.
Lemma lem6188462 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : ((term1320 _123419 op x) = (term1321 _123419 op x)) = ((term1314 _123419 op x) = (term1334 _123419 op x)).
Proof. exact (MK_COMB (@lem6188453 _123419 op x) (@lem6188461 _123419 op x)). Qed.
Lemma lem6188463 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1314 _123419 op x) = (term1334 _123419 op x).
Proof. exact (EQ_MP (@lem6188462 _123419 op x) (@lem6188443 _123419 op x)). Qed.
Lemma lem6188465 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1318 A P Q) = (term1319 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem6188466 {_123419 : Type'} (P : _123419 -> Prop) (Q : Prop) : (term1318 _123419 P Q) = (term1319 _123419 P Q).
Proof. exact (@lem6188465 _123419 P Q). Qed.
Lemma lem6188467 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1335 _123419 y op x) = (term1336 _123419 y op x).
Proof. exact (@lem6188466 _123419 (term1230 _123419 op x y) ((term1213 _123419 op x) = x)). Qed.
Lemma lem6188468 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : (term1337 _123419 op x y z) = ((term1221 _123419 x op y z) = (term1227 _123419 op x y z)).
Proof. exact (eq_refl (term1337 _123419 op x y z)). Qed.
Lemma lem6188469 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term1338 _123419 op x y) = (term1230 _123419 op x y).
Proof. exact (fun_ext (fun z : _123419 => @lem6188468 _123419 op x y z)). Qed.
Lemma lem6188470 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188471 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term1339 _123419 op x y) = (term1231 _123419 op x y).
Proof. exact (MK_COMB (@lem6188470 _123419) (@lem6188469 _123419 op x y)). Qed.
Lemma lem6188472 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6188473 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term1340 _123419 op x y) = (term1329 _123419 op x y).
Proof. exact (MK_COMB (@lem6188472) (@lem6188471 _123419 op x y)). Qed.
Lemma lem6188474 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : ((term1213 _123419 op x) = x) = ((term1213 _123419 op x) = x).
Proof. exact (eq_refl ((term1213 _123419 op x) = x)). Qed.
Lemma lem6188475 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1335 _123419 y op x) = (term1331 _123419 y op x).
Proof. exact (MK_COMB (@lem6188473 _123419 op x y) (@lem6188474 _123419 op x)). Qed.
Lemma lem6188476 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6188477 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1341 _123419 y op x) = (term1342 _123419 y op x).
Proof. exact (MK_COMB (@lem6188476) (@lem6188475 _123419 y op x)). Qed.
Lemma lem6188478 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : (term1337 _123419 op x y z) = ((term1221 _123419 x op y z) = (term1227 _123419 op x y z)).
Proof. exact (eq_refl (term1337 _123419 op x y z)). Qed.
Lemma lem6188479 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6188480 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : (term1343 _123419 op x y z) = (term1344 _123419 op x y z).
Proof. exact (MK_COMB (@lem6188479) (@lem6188478 _123419 op x y z)). Qed.
Lemma lem6188481 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : ((term1213 _123419 op x) = x) = ((term1213 _123419 op x) = x).
Proof. exact (eq_refl ((term1213 _123419 op x) = x)). Qed.
Lemma lem6188482 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term1345 _123419 y z op x) = (term1346 _123419 y z op x).
Proof. exact (MK_COMB (@lem6188480 _123419 op x y z) (@lem6188481 _123419 op x)). Qed.
Lemma lem6188483 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1347 _123419 y op x) = (term1348 _123419 y op x).
Proof. exact (fun_ext (fun z : _123419 => @lem6188482 _123419 y z op x)). Qed.
Lemma lem6188484 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188485 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1336 _123419 y op x) = (term1349 _123419 y op x).
Proof. exact (MK_COMB (@lem6188484 _123419) (@lem6188483 _123419 y op x)). Qed.
Lemma lem6188486 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : ((term1335 _123419 y op x) = (term1336 _123419 y op x)) = ((term1331 _123419 y op x) = (term1349 _123419 y op x)).
Proof. exact (MK_COMB (@lem6188477 _123419 y op x) (@lem6188485 _123419 y op x)). Qed.
Lemma lem6188487 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1331 _123419 y op x) = (term1349 _123419 y op x).
Proof. exact (EQ_MP (@lem6188486 _123419 y op x) (@lem6188467 _123419 y op x)). Qed.
Lemma lem6188488 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1333 _123419 op x) = (term1350 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6188487 _123419 y op x)). Qed.
Lemma lem6188489 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188490 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1334 _123419 op x) = (term1351 _123419 op x).
Proof. exact (MK_COMB (@lem6188489 _123419) (@lem6188488 _123419 op x)). Qed.
Lemma lem6188491 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1314 _123419 op x) = (term1351 _123419 op x).
Proof. exact (TRANS (@lem6188463 _123419 op x) (@lem6188490 _123419 op x)). Qed.
Lemma lem6188492 {_123419 : Type'} (op : type1400 _123419) : (term1316 _123419 op) = (term1352 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6188491 _123419 op x)). Qed.
Lemma lem6188493 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188494 {_123419 : Type'} (op : type1400 _123419) : (term1317 _123419 op) = (term1353 _123419 op).
Proof. exact (MK_COMB (@lem6188493 _123419) (@lem6188492 _123419 op)). Qed.
Lemma lem6188495 {_123419 : Type'} (op : type1400 _123419) : (term1237 _123419 op) = (term1353 _123419 op).
Proof. exact (TRANS (@lem6188439 _123419 op) (@lem6188494 _123419 op)). Qed.
Lemma lem6188496 {_123419 : Type'} (op : type1400 _123419) : (term1244 _123419 op) = (term1244 _123419 op).
Proof. exact (eq_refl (term1244 _123419 op)). Qed.
Lemma lem6188497 {_123419 : Type'} (op : type1400 _123419) : (term1245 _123419 op) = (term1354 _123419 op).
Proof. exact (MK_COMB (@lem6188496 _123419 op) (@lem6188495 _123419 op)). Qed.
Lemma lem6188499 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term522 A P Q) = (term521 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6188500 {_123419 : Type'} (P : _123419 -> Prop) (Q : _123419 -> Prop) : (term522 _123419 P Q) = (term521 _123419 P Q).
Proof. exact (@lem6188499 _123419 P Q). Qed.
Lemma lem6188501 {_123419 : Type'} (op : type1400 _123419) : (term1355 _123419 op) = (term1356 _123419 op).
Proof. exact (@lem6188500 _123419 (term1242 _123419 op) (term1352 _123419 op)). Qed.
Lemma lem6188502 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1357 _123419 op x) = (term1241 _123419 op x).
Proof. exact (eq_refl (term1357 _123419 op x)). Qed.
Lemma lem6188503 {_123419 : Type'} (op : type1400 _123419) : (term1358 _123419 op) = (term1242 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6188502 _123419 op x)). Qed.
Lemma lem6188504 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188505 {_123419 : Type'} (op : type1400 _123419) : (term1359 _123419 op) = (term1243 _123419 op).
Proof. exact (MK_COMB (@lem6188504 _123419) (@lem6188503 _123419 op)). Qed.
Lemma lem6188506 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6188507 {_123419 : Type'} (op : type1400 _123419) : (term1360 _123419 op) = (term1244 _123419 op).
Proof. exact (MK_COMB (@lem6188506) (@lem6188505 _123419 op)). Qed.
Lemma lem6188508 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1361 _123419 op x) = (term1351 _123419 op x).
Proof. exact (eq_refl (term1361 _123419 op x)). Qed.
Lemma lem6188509 {_123419 : Type'} (op : type1400 _123419) : (term1362 _123419 op) = (term1352 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6188508 _123419 op x)). Qed.
Lemma lem6188510 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188511 {_123419 : Type'} (op : type1400 _123419) : (term1363 _123419 op) = (term1353 _123419 op).
Proof. exact (MK_COMB (@lem6188510 _123419) (@lem6188509 _123419 op)). Qed.
Lemma lem6188512 {_123419 : Type'} (op : type1400 _123419) : (term1355 _123419 op) = (term1354 _123419 op).
Proof. exact (MK_COMB (@lem6188507 _123419 op) (@lem6188511 _123419 op)). Qed.
Lemma lem6188513 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6188514 {_123419 : Type'} (op : type1400 _123419) : (term1364 _123419 op) = (term1365 _123419 op).
Proof. exact (MK_COMB (@lem6188513) (@lem6188512 _123419 op)). Qed.
Lemma lem6188515 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1357 _123419 op x) = (term1241 _123419 op x).
Proof. exact (eq_refl (term1357 _123419 op x)). Qed.
Lemma lem6188516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6188517 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1366 _123419 op x) = (term1367 _123419 op x).
Proof. exact (MK_COMB (@lem6188516) (@lem6188515 _123419 op x)). Qed.
Lemma lem6188518 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1361 _123419 op x) = (term1351 _123419 op x).
Proof. exact (eq_refl (term1361 _123419 op x)). Qed.
Lemma lem6188519 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1368 _123419 op x) = (term1369 _123419 op x).
Proof. exact (MK_COMB (@lem6188517 _123419 op x) (@lem6188518 _123419 op x)). Qed.
Lemma lem6188520 {_123419 : Type'} (op : type1400 _123419) : (term1370 _123419 op) = (term1371 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6188519 _123419 op x)). Qed.
Lemma lem6188521 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188522 {_123419 : Type'} (op : type1400 _123419) : (term1356 _123419 op) = (term1372 _123419 op).
Proof. exact (MK_COMB (@lem6188521 _123419) (@lem6188520 _123419 op)). Qed.
Lemma lem6188523 {_123419 : Type'} (op : type1400 _123419) : ((term1355 _123419 op) = (term1356 _123419 op)) = ((term1354 _123419 op) = (term1372 _123419 op)).
Proof. exact (MK_COMB (@lem6188514 _123419 op) (@lem6188522 _123419 op)). Qed.
Lemma lem6188524 {_123419 : Type'} (op : type1400 _123419) : (term1354 _123419 op) = (term1372 _123419 op).
Proof. exact (EQ_MP (@lem6188523 _123419 op) (@lem6188501 _123419 op)). Qed.
Lemma lem6188526 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term522 A P Q) = (term521 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6188527 {_123419 : Type'} (P : _123419 -> Prop) (Q : _123419 -> Prop) : (term522 _123419 P Q) = (term521 _123419 P Q).
Proof. exact (@lem6188526 _123419 P Q). Qed.
Lemma lem6188528 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1373 _123419 op x) = (term1374 _123419 op x).
Proof. exact (@lem6188527 _123419 (term1240 _123419 op x) (term1350 _123419 op x)). Qed.
Lemma lem6188529 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (term1375 _123419 op x y) = ((term1218 _123419 op x y) = (term1218 _123419 op y x)).
Proof. exact (eq_refl (term1375 _123419 op x y)). Qed.
Lemma lem6188530 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1376 _123419 op x) = (term1240 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6188529 _123419 op y x)). Qed.
Lemma lem6188531 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188532 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1377 _123419 op x) = (term1241 _123419 op x).
Proof. exact (MK_COMB (@lem6188531 _123419) (@lem6188530 _123419 op x)). Qed.
Lemma lem6188533 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6188534 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1378 _123419 op x) = (term1367 _123419 op x).
Proof. exact (MK_COMB (@lem6188533) (@lem6188532 _123419 op x)). Qed.
Lemma lem6188535 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1379 _123419 op x y) = (term1349 _123419 y op x).
Proof. exact (eq_refl (term1379 _123419 op x y)). Qed.
Lemma lem6188536 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1380 _123419 op x) = (term1350 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6188535 _123419 y op x)). Qed.
Lemma lem6188537 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188538 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1381 _123419 op x) = (term1351 _123419 op x).
Proof. exact (MK_COMB (@lem6188537 _123419) (@lem6188536 _123419 op x)). Qed.
Lemma lem6188539 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1373 _123419 op x) = (term1369 _123419 op x).
Proof. exact (MK_COMB (@lem6188534 _123419 op x) (@lem6188538 _123419 op x)). Qed.
Lemma lem6188540 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6188541 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1382 _123419 op x) = (term1383 _123419 op x).
Proof. exact (MK_COMB (@lem6188540) (@lem6188539 _123419 op x)). Qed.
Lemma lem6188542 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (term1375 _123419 op x y) = ((term1218 _123419 op x y) = (term1218 _123419 op y x)).
Proof. exact (eq_refl (term1375 _123419 op x y)). Qed.
Lemma lem6188543 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6188544 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (term1384 _123419 op x y) = (term1385 _123419 op y x).
Proof. exact (MK_COMB (@lem6188543) (@lem6188542 _123419 op y x)). Qed.
Lemma lem6188545 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1379 _123419 op x y) = (term1349 _123419 y op x).
Proof. exact (eq_refl (term1379 _123419 op x y)). Qed.
Lemma lem6188546 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1386 _123419 op x y) = (term1387 _123419 y op x).
Proof. exact (MK_COMB (@lem6188544 _123419 op y x) (@lem6188545 _123419 y op x)). Qed.
Lemma lem6188547 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1388 _123419 op x) = (term1389 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6188546 _123419 y op x)). Qed.
Lemma lem6188548 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188549 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1374 _123419 op x) = (term1390 _123419 op x).
Proof. exact (MK_COMB (@lem6188548 _123419) (@lem6188547 _123419 op x)). Qed.
Lemma lem6188550 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : ((term1373 _123419 op x) = (term1374 _123419 op x)) = ((term1369 _123419 op x) = (term1390 _123419 op x)).
Proof. exact (MK_COMB (@lem6188541 _123419 op x) (@lem6188549 _123419 op x)). Qed.
Lemma lem6188551 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1369 _123419 op x) = (term1390 _123419 op x).
Proof. exact (EQ_MP (@lem6188550 _123419 op x) (@lem6188528 _123419 op x)). Qed.
Lemma lem6188553 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1391 A P Q) = (term1392 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem6188554 {_123419 : Type'} (P : Prop) (Q : _123419 -> Prop) : (term1391 _123419 P Q) = (term1392 _123419 P Q).
Proof. exact (@lem6188553 _123419 P Q). Qed.
Lemma lem6188555 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1393 _123419 y op x) = (term1394 _123419 y op x).
Proof. exact (@lem6188554 _123419 ((term1218 _123419 op x y) = (term1218 _123419 op y x)) (term1348 _123419 y op x)). Qed.
Lemma lem6188556 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term1395 _123419 y op x z) = (term1346 _123419 y z op x).
Proof. exact (eq_refl (term1395 _123419 y op x z)). Qed.
Lemma lem6188557 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1396 _123419 y op x) = (term1348 _123419 y op x).
Proof. exact (fun_ext (fun z : _123419 => @lem6188556 _123419 y z op x)). Qed.
Lemma lem6188558 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188559 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1397 _123419 y op x) = (term1349 _123419 y op x).
Proof. exact (MK_COMB (@lem6188558 _123419) (@lem6188557 _123419 y op x)). Qed.
Lemma lem6188560 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (term1385 _123419 op y x) = (term1385 _123419 op y x).
Proof. exact (eq_refl (term1385 _123419 op y x)). Qed.
Lemma lem6188561 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1393 _123419 y op x) = (term1387 _123419 y op x).
Proof. exact (MK_COMB (@lem6188560 _123419 op y x) (@lem6188559 _123419 y op x)). Qed.
Lemma lem6188562 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6188563 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1398 _123419 y op x) = (term1399 _123419 y op x).
Proof. exact (MK_COMB (@lem6188562) (@lem6188561 _123419 y op x)). Qed.
Lemma lem6188564 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term1395 _123419 y op x z) = (term1346 _123419 y z op x).
Proof. exact (eq_refl (term1395 _123419 y op x z)). Qed.
Lemma lem6188565 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (term1385 _123419 op y x) = (term1385 _123419 op y x).
Proof. exact (eq_refl (term1385 _123419 op y x)). Qed.
Lemma lem6188566 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term1400 _123419 y op x z) = (term1401 _123419 y z op x).
Proof. exact (MK_COMB (@lem6188565 _123419 op y x) (@lem6188564 _123419 y z op x)). Qed.
Lemma lem6188567 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1402 _123419 y op x) = (term1403 _123419 y op x).
Proof. exact (fun_ext (fun z : _123419 => @lem6188566 _123419 y z op x)). Qed.
Lemma lem6188568 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188569 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1394 _123419 y op x) = (term1404 _123419 y op x).
Proof. exact (MK_COMB (@lem6188568 _123419) (@lem6188567 _123419 y op x)). Qed.
Lemma lem6188570 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : ((term1393 _123419 y op x) = (term1394 _123419 y op x)) = ((term1387 _123419 y op x) = (term1404 _123419 y op x)).
Proof. exact (MK_COMB (@lem6188563 _123419 y op x) (@lem6188569 _123419 y op x)). Qed.
Lemma lem6188571 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1387 _123419 y op x) = (term1404 _123419 y op x).
Proof. exact (EQ_MP (@lem6188570 _123419 y op x) (@lem6188555 _123419 y op x)). Qed.
Lemma lem6188572 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1389 _123419 op x) = (term1405 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6188571 _123419 y op x)). Qed.
Lemma lem6188573 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188574 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1390 _123419 op x) = (term1406 _123419 op x).
Proof. exact (MK_COMB (@lem6188573 _123419) (@lem6188572 _123419 op x)). Qed.
Lemma lem6188575 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1369 _123419 op x) = (term1406 _123419 op x).
Proof. exact (TRANS (@lem6188551 _123419 op x) (@lem6188574 _123419 op x)). Qed.
Lemma lem6188576 {_123419 : Type'} (op : type1400 _123419) : (term1371 _123419 op) = (term1407 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6188575 _123419 op x)). Qed.
Lemma lem6188577 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188578 {_123419 : Type'} (op : type1400 _123419) : (term1372 _123419 op) = (term1408 _123419 op).
Proof. exact (MK_COMB (@lem6188577 _123419) (@lem6188576 _123419 op)). Qed.
Lemma lem6188579 {_123419 : Type'} (op : type1400 _123419) : (term1354 _123419 op) = (term1408 _123419 op).
Proof. exact (TRANS (@lem6188524 _123419 op) (@lem6188578 _123419 op)). Qed.
Lemma lem6188580 {_123419 : Type'} (op : type1400 _123419) : (term1245 _123419 op) = (term1408 _123419 op).
Proof. exact (TRANS (@lem6188497 _123419 op) (@lem6188579 _123419 op)). Qed.
Lemma lem6188581 {_123419 : Type'} (op : type1400 _123419) : (term1248 _123419 op) = (term1248 _123419 op).
Proof. exact (eq_refl (term1248 _123419 op)). Qed.
Lemma lem6188582 {_123419 : Type'} (op : type1400 _123419) : (term1249 _123419 op) = (term1409 _123419 op).
Proof. exact (MK_COMB (@lem6188581 _123419 op) (@lem6188580 _123419 op)). Qed.
Lemma lem6188584 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1410 A P Q) = (term1411 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem6188585 {_123419 : Type'} (P : Prop) (Q : _123419 -> Prop) : (term1410 _123419 P Q) = (term1411 _123419 P Q).
Proof. exact (@lem6188584 _123419 P Q). Qed.
Lemma lem6188586 {_123419 : Type'} (op : type1400 _123419) : (term1412 _123419 op) = (term1413 _123419 op).
Proof. exact (@lem6188585 _123419 (term1247 _123419 op) (term1407 _123419 op)). Qed.
Lemma lem6188587 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1414 _123419 op x) = (term1406 _123419 op x).
Proof. exact (eq_refl (term1414 _123419 op x)). Qed.
Lemma lem6188588 {_123419 : Type'} (op : type1400 _123419) : (term1415 _123419 op) = (term1407 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6188587 _123419 op x)). Qed.
Lemma lem6188589 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188590 {_123419 : Type'} (op : type1400 _123419) : (term1416 _123419 op) = (term1408 _123419 op).
Proof. exact (MK_COMB (@lem6188589 _123419) (@lem6188588 _123419 op)). Qed.
Lemma lem6188591 {_123419 : Type'} (op : type1400 _123419) : (term1248 _123419 op) = (term1248 _123419 op).
Proof. exact (eq_refl (term1248 _123419 op)). Qed.
Lemma lem6188592 {_123419 : Type'} (op : type1400 _123419) : (term1412 _123419 op) = (term1409 _123419 op).
Proof. exact (MK_COMB (@lem6188591 _123419 op) (@lem6188590 _123419 op)). Qed.
Lemma lem6188593 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6188594 {_123419 : Type'} (op : type1400 _123419) : (term1417 _123419 op) = (term1418 _123419 op).
Proof. exact (MK_COMB (@lem6188593) (@lem6188592 _123419 op)). Qed.
Lemma lem6188595 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1414 _123419 op x) = (term1406 _123419 op x).
Proof. exact (eq_refl (term1414 _123419 op x)). Qed.
Lemma lem6188596 {_123419 : Type'} (op : type1400 _123419) : (term1248 _123419 op) = (term1248 _123419 op).
Proof. exact (eq_refl (term1248 _123419 op)). Qed.
Lemma lem6188597 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1419 _123419 op x) = (term1420 _123419 op x).
Proof. exact (MK_COMB (@lem6188596 _123419 op) (@lem6188595 _123419 op x)). Qed.
Lemma lem6188598 {_123419 : Type'} (op : type1400 _123419) : (term1421 _123419 op) = (term1422 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6188597 _123419 op x)). Qed.
Lemma lem6188599 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188600 {_123419 : Type'} (op : type1400 _123419) : (term1413 _123419 op) = (term1423 _123419 op).
Proof. exact (MK_COMB (@lem6188599 _123419) (@lem6188598 _123419 op)). Qed.
Lemma lem6188601 {_123419 : Type'} (op : type1400 _123419) : ((term1412 _123419 op) = (term1413 _123419 op)) = ((term1409 _123419 op) = (term1423 _123419 op)).
Proof. exact (MK_COMB (@lem6188594 _123419 op) (@lem6188600 _123419 op)). Qed.
Lemma lem6188602 {_123419 : Type'} (op : type1400 _123419) : (term1409 _123419 op) = (term1423 _123419 op).
Proof. exact (EQ_MP (@lem6188601 _123419 op) (@lem6188586 _123419 op)). Qed.
Lemma lem6188604 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1410 A P Q) = (term1411 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem6188605 {_123419 : Type'} (P : Prop) (Q : _123419 -> Prop) : (term1410 _123419 P Q) = (term1411 _123419 P Q).
Proof. exact (@lem6188604 _123419 P Q). Qed.
Lemma lem6188606 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1424 _123419 op x) = (term1425 _123419 op x).
Proof. exact (@lem6188605 _123419 (term1247 _123419 op) (term1405 _123419 op x)). Qed.
Lemma lem6188607 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1426 _123419 op x y) = (term1404 _123419 y op x).
Proof. exact (eq_refl (term1426 _123419 op x y)). Qed.
Lemma lem6188608 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1427 _123419 op x) = (term1405 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6188607 _123419 y op x)). Qed.
Lemma lem6188609 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188610 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1428 _123419 op x) = (term1406 _123419 op x).
Proof. exact (MK_COMB (@lem6188609 _123419) (@lem6188608 _123419 op x)). Qed.
Lemma lem6188611 {_123419 : Type'} (op : type1400 _123419) : (term1248 _123419 op) = (term1248 _123419 op).
Proof. exact (eq_refl (term1248 _123419 op)). Qed.
Lemma lem6188612 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1424 _123419 op x) = (term1420 _123419 op x).
Proof. exact (MK_COMB (@lem6188611 _123419 op) (@lem6188610 _123419 op x)). Qed.
Lemma lem6188613 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6188614 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1429 _123419 op x) = (term1430 _123419 op x).
Proof. exact (MK_COMB (@lem6188613) (@lem6188612 _123419 op x)). Qed.
Lemma lem6188615 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1426 _123419 op x y) = (term1404 _123419 y op x).
Proof. exact (eq_refl (term1426 _123419 op x y)). Qed.
Lemma lem6188616 {_123419 : Type'} (op : type1400 _123419) : (term1248 _123419 op) = (term1248 _123419 op).
Proof. exact (eq_refl (term1248 _123419 op)). Qed.
Lemma lem6188617 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1431 _123419 op x y) = (term1432 _123419 y op x).
Proof. exact (MK_COMB (@lem6188616 _123419 op) (@lem6188615 _123419 y op x)). Qed.
Lemma lem6188618 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1433 _123419 op x) = (term1434 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6188617 _123419 y op x)). Qed.
Lemma lem6188619 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188620 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1425 _123419 op x) = (term1435 _123419 op x).
Proof. exact (MK_COMB (@lem6188619 _123419) (@lem6188618 _123419 op x)). Qed.
Lemma lem6188621 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : ((term1424 _123419 op x) = (term1425 _123419 op x)) = ((term1420 _123419 op x) = (term1435 _123419 op x)).
Proof. exact (MK_COMB (@lem6188614 _123419 op x) (@lem6188620 _123419 op x)). Qed.
Lemma lem6188622 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1420 _123419 op x) = (term1435 _123419 op x).
Proof. exact (EQ_MP (@lem6188621 _123419 op x) (@lem6188606 _123419 op x)). Qed.
Lemma lem6188624 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1410 A P Q) = (term1411 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem6188625 {_123419 : Type'} (P : Prop) (Q : _123419 -> Prop) : (term1410 _123419 P Q) = (term1411 _123419 P Q).
Proof. exact (@lem6188624 _123419 P Q). Qed.
Lemma lem6188626 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1436 _123419 y op x) = (term1437 _123419 y op x).
Proof. exact (@lem6188625 _123419 (term1247 _123419 op) (term1403 _123419 y op x)). Qed.
Lemma lem6188627 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term1438 _123419 y op x z) = (term1401 _123419 y z op x).
Proof. exact (eq_refl (term1438 _123419 y op x z)). Qed.
Lemma lem6188628 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1439 _123419 y op x) = (term1403 _123419 y op x).
Proof. exact (fun_ext (fun z : _123419 => @lem6188627 _123419 y z op x)). Qed.
Lemma lem6188629 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188630 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1440 _123419 y op x) = (term1404 _123419 y op x).
Proof. exact (MK_COMB (@lem6188629 _123419) (@lem6188628 _123419 y op x)). Qed.
Lemma lem6188631 {_123419 : Type'} (op : type1400 _123419) : (term1248 _123419 op) = (term1248 _123419 op).
Proof. exact (eq_refl (term1248 _123419 op)). Qed.
Lemma lem6188632 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1436 _123419 y op x) = (term1432 _123419 y op x).
Proof. exact (MK_COMB (@lem6188631 _123419 op) (@lem6188630 _123419 y op x)). Qed.
Lemma lem6188633 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6188634 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1441 _123419 y op x) = (term1442 _123419 y op x).
Proof. exact (MK_COMB (@lem6188633) (@lem6188632 _123419 y op x)). Qed.
Lemma lem6188635 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term1438 _123419 y op x z) = (term1401 _123419 y z op x).
Proof. exact (eq_refl (term1438 _123419 y op x z)). Qed.
Lemma lem6188636 {_123419 : Type'} (op : type1400 _123419) : (term1248 _123419 op) = (term1248 _123419 op).
Proof. exact (eq_refl (term1248 _123419 op)). Qed.
Lemma lem6188637 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term1443 _123419 y op x z) = (term1444 _123419 y z op x).
Proof. exact (MK_COMB (@lem6188636 _123419 op) (@lem6188635 _123419 y z op x)). Qed.
Lemma lem6188638 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1445 _123419 y op x) = (term1446 _123419 y op x).
Proof. exact (fun_ext (fun z : _123419 => @lem6188637 _123419 y z op x)). Qed.
Lemma lem6188639 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188640 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1437 _123419 y op x) = (term1447 _123419 y op x).
Proof. exact (MK_COMB (@lem6188639 _123419) (@lem6188638 _123419 y op x)). Qed.
Lemma lem6188641 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : ((term1436 _123419 y op x) = (term1437 _123419 y op x)) = ((term1432 _123419 y op x) = (term1447 _123419 y op x)).
Proof. exact (MK_COMB (@lem6188634 _123419 y op x) (@lem6188640 _123419 y op x)). Qed.
Lemma lem6188642 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1432 _123419 y op x) = (term1447 _123419 y op x).
Proof. exact (EQ_MP (@lem6188641 _123419 y op x) (@lem6188626 _123419 y op x)). Qed.
Lemma lem6188643 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1434 _123419 op x) = (term1448 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6188642 _123419 y op x)). Qed.
Lemma lem6188644 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188645 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1435 _123419 op x) = (term1449 _123419 op x).
Proof. exact (MK_COMB (@lem6188644 _123419) (@lem6188643 _123419 op x)). Qed.
Lemma lem6188646 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1420 _123419 op x) = (term1449 _123419 op x).
Proof. exact (TRANS (@lem6188622 _123419 op x) (@lem6188645 _123419 op x)). Qed.
Lemma lem6188647 {_123419 : Type'} (op : type1400 _123419) : (term1422 _123419 op) = (term1450 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6188646 _123419 op x)). Qed.
Lemma lem6188648 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188649 {_123419 : Type'} (op : type1400 _123419) : (term1423 _123419 op) = (term1451 _123419 op).
Proof. exact (MK_COMB (@lem6188648 _123419) (@lem6188647 _123419 op)). Qed.
Lemma lem6188650 {_123419 : Type'} (op : type1400 _123419) : (term1409 _123419 op) = (term1451 _123419 op).
Proof. exact (TRANS (@lem6188602 _123419 op) (@lem6188649 _123419 op)). Qed.
Lemma lem6188651 {_123419 : Type'} (op : type1400 _123419) : (term1249 _123419 op) = (term1451 _123419 op).
Proof. exact (TRANS (@lem6188582 _123419 op) (@lem6188650 _123419 op)). Qed.
Lemma lem6188652 {_123419 : Type'} : (term1250 _123419) = (term1452 _123419).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6188651 _123419 op)). Qed.
Lemma lem6188653 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6188654 {_123419 : Type'} : (term1251 _123419) = (term1453 _123419).
Proof. exact (MK_COMB (@lem6188653 _123419) (@lem6188652 _123419)). Qed.
Lemma lem6188668 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term1444 _123419 y z op x) = (term1454 _123419 y z op x).
Proof. exact (@lem19490 ((term1218 _123419 op x y) = (term1218 _123419 op y x)) (term1247 _123419 op) (term1346 _123419 y z op x)). Qed.
Lemma lem6188675 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term1455 _123419 y z op x) = (term1456 _123419 y z op x).
Proof. exact (@lem19490 ((term1221 _123419 x op y z) = (term1227 _123419 op x y z)) (term1247 _123419 op) ((term1213 _123419 op x) = x)). Qed.
Lemma lem6188678 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (term1457 _123419 op y x) = (term1457 _123419 op y x).
Proof. exact (eq_refl (term1457 _123419 op y x)). Qed.
Lemma lem6188679 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term1454 _123419 y z op x) = (term1458 _123419 y z op x).
Proof. exact (MK_COMB (@lem6188678 _123419 op y x) (@lem6188675 _123419 y z op x)). Qed.
Lemma lem6188681 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term1444 _123419 y z op x) = (term1458 _123419 y z op x).
Proof. exact (TRANS (@lem6188668 _123419 y z op x) (@lem6188679 _123419 y z op x)). Qed.
Lemma lem6188682 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1446 _123419 y op x) = (term1459 _123419 y op x).
Proof. exact (fun_ext (fun z : _123419 => @lem6188681 _123419 y z op x)). Qed.
Lemma lem6188683 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188684 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1447 _123419 y op x) = (term1460 _123419 y op x).
Proof. exact (MK_COMB (@lem6188683 _123419) (@lem6188682 _123419 y op x)). Qed.
Lemma lem6188685 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1448 _123419 op x) = (term1461 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6188684 _123419 y op x)). Qed.
Lemma lem6188686 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188687 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1449 _123419 op x) = (term1462 _123419 op x).
Proof. exact (MK_COMB (@lem6188686 _123419) (@lem6188685 _123419 op x)). Qed.
Lemma lem6188688 {_123419 : Type'} (op : type1400 _123419) : (term1450 _123419 op) = (term1463 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6188687 _123419 op x)). Qed.
Lemma lem6188689 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6188690 {_123419 : Type'} (op : type1400 _123419) : (term1451 _123419 op) = (term1464 _123419 op).
Proof. exact (MK_COMB (@lem6188689 _123419) (@lem6188688 _123419 op)). Qed.
Lemma lem6188691 {_123419 : Type'} : (term1452 _123419) = (term1465 _123419).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6188690 _123419 op)). Qed.
Lemma lem6188692 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6188693 {_123419 : Type'} : (term1453 _123419) = (term1466 _123419).
Proof. exact (MK_COMB (@lem6188692 _123419) (@lem6188691 _123419)). Qed.
Lemma lem6188694 {_123419 : Type'} : (term1251 _123419) = (term1466 _123419).
Proof. exact (TRANS (@lem6188654 _123419) (@lem6188693 _123419)). Qed.
Lemma lem6188695 {_123419 : Type'} (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : term821 _123419 y' z' x') : term1466 _123419.
Proof. exact (EQ_MP (@lem6188694 _123419) (@lem6188372 _123419 y' z' x' h1)). Qed.
Lemma lem6189007 {_123419 : Type'} (_78781 : type1400 _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : term821 _123419 y' z' x') : term1467 _123419 _78781.
Proof. exact (@lem6188695 _123419 y' z' x' h1 _78781). Qed.
Lemma lem6189008 {_123419 : Type'} (_78781 : type1400 _123419) : (term1467 _123419 _78781) = (term1464 _123419 _78781).
Proof. exact (eq_refl (term1467 _123419 _78781)). Qed.
Lemma lem6189009 {_123419 : Type'} (_78781 : type1400 _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : term821 _123419 y' z' x') : term1464 _123419 _78781.
Proof. exact (EQ_MP (@lem6189008 _123419 _78781) (@lem6189007 _123419 _78781 y' z' x' h1)). Qed.
Lemma lem6189010 {_123419 : Type'} (_78781 : type1400 _123419) (_78782 : _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : term821 _123419 y' z' x') : term1468 _123419 _78781 _78782.
Proof. exact (@lem6189009 _123419 _78781 y' z' x' h1 _78782). Qed.
Lemma lem6189011 {_123419 : Type'} (_78781 : type1400 _123419) (_78782 : _123419) : (term1468 _123419 _78781 _78782) = (term1462 _123419 _78781 _78782).
Proof. exact (eq_refl (term1468 _123419 _78781 _78782)). Qed.
Lemma lem6189012 {_123419 : Type'} (_78781 : type1400 _123419) (_78782 : _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : term821 _123419 y' z' x') : term1462 _123419 _78781 _78782.
Proof. exact (EQ_MP (@lem6189011 _123419 _78781 _78782) (@lem6189010 _123419 _78781 _78782 y' z' x' h1)). Qed.
Lemma lem6189013 {_123419 : Type'} (_78781 : type1400 _123419) (_78782 : _123419) (_78783 : _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : term821 _123419 y' z' x') : term1469 _123419 _78781 _78782 _78783.
Proof. exact (@lem6189012 _123419 _78781 _78782 y' z' x' h1 _78783). Qed.
Lemma lem6189014 {_123419 : Type'} (_78783 : _123419) (_78781 : type1400 _123419) (_78782 : _123419) : (term1469 _123419 _78781 _78782 _78783) = (term1460 _123419 _78783 _78781 _78782).
Proof. exact (eq_refl (term1469 _123419 _78781 _78782 _78783)). Qed.
Lemma lem6189015 {_123419 : Type'} (_78783 : _123419) (_78781 : type1400 _123419) (_78782 : _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : term821 _123419 y' z' x') : term1460 _123419 _78783 _78781 _78782.
Proof. exact (EQ_MP (@lem6189014 _123419 _78783 _78781 _78782) (@lem6189013 _123419 _78781 _78782 _78783 y' z' x' h1)). Qed.
Lemma lem6189016 {_123419 : Type'} (_78783 : _123419) (_78781 : type1400 _123419) (_78782 : _123419) (_78784 : _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : term821 _123419 y' z' x') : term1470 _123419 _78783 _78781 _78782 _78784.
Proof. exact (@lem6189015 _123419 _78783 _78781 _78782 y' z' x' h1 _78784). Qed.
Lemma lem6189017 {_123419 : Type'} (_78783 : _123419) (_78784 : _123419) (_78781 : type1400 _123419) (_78782 : _123419) : (term1470 _123419 _78783 _78781 _78782 _78784) = (term1458 _123419 _78783 _78784 _78781 _78782).
Proof. exact (eq_refl (term1470 _123419 _78783 _78781 _78782 _78784)). Qed.
Lemma lem6189018 {_123419 : Type'} (_78783 : _123419) (_78784 : _123419) (_78781 : type1400 _123419) (_78782 : _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : term821 _123419 y' z' x') : term1458 _123419 _78783 _78784 _78781 _78782.
Proof. exact (EQ_MP (@lem6189017 _123419 _78783 _78784 _78781 _78782) (@lem6189016 _123419 _78783 _78781 _78782 _78784 y' z' x' h1)). Qed.
Lemma lem6189038 {_123419 : Type'} (_78783 : _123419) (_78784 : _123419) (_78781 : type1400 _123419) (_78782 : _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : term821 _123419 y' z' x') : term1456 _123419 _78783 _78784 _78781 _78782.
Proof. exact (proj2 (@lem6189018 _123419 _78783 _78784 _78781 _78782 y' z' x' h1)). Qed.
Lemma lem6189153 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (h1 : term381 _123419 op f) : term1207 _123419 op f.
Proof. exact (EQ_MP (@lem6187526 _123419 op f) (@lem6186048 _123419 op f h1)). Qed.
Lemma lem6189237 {_123419 : Type'} (_78781 : type1400 _123419) (_78783 : _123419) (_78782 : _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : term821 _123419 y' z' x') : term1471 _123419 _78781 _78783 _78782.
Proof. exact (proj1 (@lem6189018 _123419 _78783 (@el _123419) _78781 _78782 y' z' x' h1)). Qed.
Lemma lem6189265 {_123419 : Type'} (_78781 : type1400 _123419) (_78782 : _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : term821 _123419 y' z' x') : term1472 _123419 _78781 _78782.
Proof. exact (proj2 (@lem6189038 _123419 (@el _123419) (@el _123419) _78781 _78782 y' z' x' h1)). Qed.
Lemma lem6189410 {_123419 : Type'} (x : _123419) (y : _123419) (z : _123419) : term1473 _123419 x y z.
Proof. exact (@lem21385 _123419 x y z). Qed.
Lemma lem6189432 {_123419 : Type'} (op : type1400 _123419) (h1 : @monoidal _123419 op) : @I ((_123419 -> _123419 -> _123419) -> Prop) (@monoidal _123419) op.
Proof. exact (EQ_MP (@lem6187454 _123419 op) (@lem6186036 _123419 op h1)). Qed.
Lemma lem6189433 {_123419 : Type'} (op : type1400 _123419) (h1 : @monoidal _123419 op) : term1474 _123419 op.
Proof. exact (fun h0 : term1247 _123419 op => @lem6189432 _123419 op h1). Qed.
Lemma lem6189435 (p : Prop) : (term1475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6189436 {_123419 : Type'} (op : type1400 _123419) : (term1474 _123419 op) = (@I ((_123419 -> _123419 -> _123419) -> Prop) (@monoidal _123419) op).
Proof. exact (@lem6189435 (@I ((_123419 -> _123419 -> _123419) -> Prop) (@monoidal _123419) op)). Qed.
Lemma lem6189437 {_123419 : Type'} (op : type1400 _123419) (h1 : @monoidal _123419 op) : @I ((_123419 -> _123419 -> _123419) -> Prop) (@monoidal _123419) op.
Proof. exact (EQ_MP (@lem6189436 _123419 op) (@lem6189433 _123419 op h1)). Qed.
Lemma lem6189443 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6189444 {_123419 : Type'} (_78783 : _123419) (_78782 : _123419) (_78781 : type1400 _123419) : (term1471 _123419 _78781 _78783 _78782) = (term1476 _123419 _78783 _78782 _78781).
Proof. exact (@lem6189443 ((term1218 _123419 _78781 _78782 _78783) = (term1218 _123419 _78781 _78783 _78782)) (term1247 _123419 _78781)). Qed.
Lemma lem6189452 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6189453 {_123419 : Type'} (_78783 : _123419) (_78782 : _123419) (_78781 : type1400 _123419) : (term1477 _123419 _78781 _78783 _78782) = (term1478 _123419 _78783 _78782 _78781).
Proof. exact (MK_COMB (@lem6189452) (@lem6189444 _123419 _78783 _78782 _78781)). Qed.
Lemma lem6189461 {_123419 : Type'} (_78783 : _123419) (_78782 : _123419) (_78781 : type1400 _123419) : (term1476 _123419 _78783 _78782 _78781) = (term1476 _123419 _78783 _78782 _78781).
Proof. exact (eq_refl (term1476 _123419 _78783 _78782 _78781)). Qed.
Lemma lem6189462 {_123419 : Type'} (_78783 : _123419) (_78782 : _123419) (_78781 : type1400 _123419) : ((term1471 _123419 _78781 _78783 _78782) = (term1476 _123419 _78783 _78782 _78781)) = ((term1476 _123419 _78783 _78782 _78781) = (term1476 _123419 _78783 _78782 _78781)).
Proof. exact (MK_COMB (@lem6189453 _123419 _78783 _78782 _78781) (@lem6189461 _123419 _78783 _78782 _78781)). Qed.
Lemma lem6189464 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6189465 (x : Prop) : (x = x) = True.
Proof. exact (@lem6189464 Prop x). Qed.
Lemma lem6189466 {_123419 : Type'} (_78783 : _123419) (_78782 : _123419) (_78781 : type1400 _123419) : ((term1476 _123419 _78783 _78782 _78781) = (term1476 _123419 _78783 _78782 _78781)) = True.
Proof. exact (@lem6189465 (term1476 _123419 _78783 _78782 _78781)). Qed.
Lemma lem6189467 {_123419 : Type'} (_78783 : _123419) (_78782 : _123419) (_78781 : type1400 _123419) : ((term1471 _123419 _78781 _78783 _78782) = (term1476 _123419 _78783 _78782 _78781)) = True.
Proof. exact (TRANS (@lem6189462 _123419 _78783 _78782 _78781) (@lem6189466 _123419 _78783 _78782 _78781)). Qed.
Lemma lem6189468 {_123419 : Type'} (_78783 : _123419) (_78782 : _123419) (_78781 : type1400 _123419) : True = ((term1471 _123419 _78781 _78783 _78782) = (term1476 _123419 _78783 _78782 _78781)).
Proof. exact (SYM (@lem6189467 _123419 _78783 _78782 _78781)). Qed.
Lemma lem6189469 {_123419 : Type'} (_78783 : _123419) (_78782 : _123419) (_78781 : type1400 _123419) : (term1471 _123419 _78781 _78783 _78782) = (term1476 _123419 _78783 _78782 _78781).
Proof. exact (EQ_MP (@lem6189468 _123419 _78783 _78782 _78781) (@lem0)). Qed.
Lemma lem6189470 {_123419 : Type'} (_78783 : _123419) (_78782 : _123419) (_78781 : type1400 _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : term821 _123419 y' z' x') : term1476 _123419 _78783 _78782 _78781.
Proof. exact (EQ_MP (@lem6189469 _123419 _78783 _78782 _78781) (@lem6189237 _123419 _78781 _78783 _78782 y' z' x' h1)). Qed.
Lemma lem6189472 (b : Prop) (a : Prop) : (a \/ b) = (term1479 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6189473 {_123419 : Type'} (_78781 : type1400 _123419) (_78783 : _123419) (_78782 : _123419) : (term1476 _123419 _78783 _78782 _78781) = (term1480 _123419 _78781 _78783 _78782).
Proof. exact (@lem6189472 (term1247 _123419 _78781) ((term1218 _123419 _78781 _78782 _78783) = (term1218 _123419 _78781 _78783 _78782))). Qed.
Lemma lem6189475 (a : Prop) : (term55 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6189476 {_123419 : Type'} (_78781 : type1400 _123419) : (term1481 _123419 _78781) = (@I ((_123419 -> _123419 -> _123419) -> Prop) (@monoidal _123419) _78781).
Proof. exact (@lem6189475 (@I ((_123419 -> _123419 -> _123419) -> Prop) (@monoidal _123419) _78781)). Qed.
Lemma lem6189477 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6189478 {_123419 : Type'} (_78781 : type1400 _123419) : (term1482 _123419 _78781) = (term1483 _123419 _78781).
Proof. exact (MK_COMB (@lem6189477) (@lem6189476 _123419 _78781)). Qed.
Lemma lem6189479 {_123419 : Type'} (_78781 : type1400 _123419) (_78783 : _123419) (_78782 : _123419) : ((term1218 _123419 _78781 _78782 _78783) = (term1218 _123419 _78781 _78783 _78782)) = ((term1218 _123419 _78781 _78782 _78783) = (term1218 _123419 _78781 _78783 _78782)).
Proof. exact (eq_refl ((term1218 _123419 _78781 _78782 _78783) = (term1218 _123419 _78781 _78783 _78782))). Qed.
Lemma lem6189480 {_123419 : Type'} (_78781 : type1400 _123419) (_78783 : _123419) (_78782 : _123419) : (term1480 _123419 _78781 _78783 _78782) = (term1484 _123419 _78781 _78783 _78782).
Proof. exact (MK_COMB (@lem6189478 _123419 _78781) (@lem6189479 _123419 _78781 _78783 _78782)). Qed.
Lemma lem6189481 {_123419 : Type'} (_78781 : type1400 _123419) (_78783 : _123419) (_78782 : _123419) : (term1476 _123419 _78783 _78782 _78781) = (term1484 _123419 _78781 _78783 _78782).
Proof. exact (TRANS (@lem6189473 _123419 _78781 _78783 _78782) (@lem6189480 _123419 _78781 _78783 _78782)). Qed.
Lemma lem6189484 {_123419 : Type'} (_78781 : type1400 _123419) (_78783 : _123419) (_78782 : _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : term821 _123419 y' z' x') : term1484 _123419 _78781 _78783 _78782.
Proof. exact (EQ_MP (@lem6189481 _123419 _78781 _78783 _78782) (@lem6189470 _123419 _78783 _78782 _78781 y' z' x' h1)). Qed.
Lemma lem6189485 {_123419 : Type'} (_78781 : type1400 _123419) (_78783 : _123419) (_78782 : _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : term821 _123419 y' z' x') : term1484 _123419 _78781 _78783 _78782.
Proof. exact (@lem6189484 _123419 _78781 _78783 _78782 y' z' x' h1). Qed.
Lemma lem6189486 {_123419 : Type'} (op : type1400 _123419) (_78783 : _123419) (_78782 : _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : term821 _123419 y' z' x') : term1484 _123419 op _78783 _78782.
Proof. exact (@lem6189485 _123419 op _78783 _78782 y' z' x' h1). Qed.
Lemma lem6189489 {_123419 : Type'} (_78783 : _123419) (_78782 : _123419) (op : type1400 _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : @monoidal _123419 op) (h2 : term821 _123419 y' z' x') : (term1218 _123419 op _78782 _78783) = (term1218 _123419 op _78783 _78782).
Proof. exact (@lem6189486 _123419 op _78783 _78782 y' z' x' h2 (@lem6189437 _123419 op h1)). Qed.
Lemma lem6189490 {_123419 : Type'} (_78783 : _123419) (_78782 : _123419) (op : type1400 _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : @monoidal _123419 op) (h2 : term821 _123419 y' z' x') : (term1218 _123419 op _78782 _78783) = (term1218 _123419 op _78783 _78782).
Proof. exact (@lem6189489 _123419 _78783 _78782 op y' z' x' h1 h2). Qed.
Lemma lem6189491 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : @monoidal _123419 op) (h2 : term821 _123419 y' z' x') : (term1485 _123419 op f) = (term1205 _123419 f op).
Proof. exact (@lem6189490 _123419 (term1200 _123419 f) (@I ((_123419 -> _123419 -> _123419) -> _123419) (@neutral _123419) op) op y' z' x' h1 h2). Qed.
Lemma lem6189492 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : @monoidal _123419 op) (h2 : term821 _123419 y' z' x') : term1486 _123419 f op.
Proof. exact (fun h0 : term1487 _123419 f op => @lem6189491 _123419 f op y' z' x' h1 h2). Qed.
Lemma lem6189494 (p : Prop) : (term1475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6189495 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : (term1486 _123419 f op) = ((term1485 _123419 op f) = (term1205 _123419 f op)).
Proof. exact (@lem6189494 ((term1485 _123419 op f) = (term1205 _123419 f op))). Qed.
Lemma lem6189496 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : @monoidal _123419 op) (h2 : term821 _123419 y' z' x') : (term1485 _123419 op f) = (term1205 _123419 f op).
Proof. exact (EQ_MP (@lem6189495 _123419 f op) (@lem6189492 _123419 f op y' z' x' h1 h2)). Qed.
Lemma lem6189498 {_123419 : Type'} (op : type1400 _123419) (h1 : @monoidal _123419 op) : @I ((_123419 -> _123419 -> _123419) -> Prop) (@monoidal _123419) op.
Proof. exact (EQ_MP (@lem6187454 _123419 op) (@lem6186036 _123419 op h1)). Qed.
Lemma lem6189499 {_123419 : Type'} (op : type1400 _123419) (h1 : @monoidal _123419 op) : term1474 _123419 op.
Proof. exact (fun h0 : term1247 _123419 op => @lem6189498 _123419 op h1). Qed.
Lemma lem6189501 (p : Prop) : (term1475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6189502 {_123419 : Type'} (op : type1400 _123419) : (term1474 _123419 op) = (@I ((_123419 -> _123419 -> _123419) -> Prop) (@monoidal _123419) op).
Proof. exact (@lem6189501 (@I ((_123419 -> _123419 -> _123419) -> Prop) (@monoidal _123419) op)). Qed.
Lemma lem6189503 {_123419 : Type'} (op : type1400 _123419) (h1 : @monoidal _123419 op) : @I ((_123419 -> _123419 -> _123419) -> Prop) (@monoidal _123419) op.
Proof. exact (EQ_MP (@lem6189502 _123419 op) (@lem6189499 _123419 op h1)). Qed.
Lemma lem6189509 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6189510 {_123419 : Type'} (_78782 : _123419) (_78781 : type1400 _123419) : (term1472 _123419 _78781 _78782) = (term1488 _123419 _78782 _78781).
Proof. exact (@lem6189509 ((term1213 _123419 _78781 _78782) = _78782) (term1247 _123419 _78781)). Qed.
Lemma lem6189518 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6189519 {_123419 : Type'} (_78782 : _123419) (_78781 : type1400 _123419) : (term1489 _123419 _78781 _78782) = (term1490 _123419 _78782 _78781).
Proof. exact (MK_COMB (@lem6189518) (@lem6189510 _123419 _78782 _78781)). Qed.
Lemma lem6189527 {_123419 : Type'} (_78782 : _123419) (_78781 : type1400 _123419) : (term1488 _123419 _78782 _78781) = (term1488 _123419 _78782 _78781).
Proof. exact (eq_refl (term1488 _123419 _78782 _78781)). Qed.
Lemma lem6189528 {_123419 : Type'} (_78782 : _123419) (_78781 : type1400 _123419) : ((term1472 _123419 _78781 _78782) = (term1488 _123419 _78782 _78781)) = ((term1488 _123419 _78782 _78781) = (term1488 _123419 _78782 _78781)).
Proof. exact (MK_COMB (@lem6189519 _123419 _78782 _78781) (@lem6189527 _123419 _78782 _78781)). Qed.
Lemma lem6189530 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6189531 (x : Prop) : (x = x) = True.
Proof. exact (@lem6189530 Prop x). Qed.
Lemma lem6189532 {_123419 : Type'} (_78782 : _123419) (_78781 : type1400 _123419) : ((term1488 _123419 _78782 _78781) = (term1488 _123419 _78782 _78781)) = True.
Proof. exact (@lem6189531 (term1488 _123419 _78782 _78781)). Qed.
Lemma lem6189533 {_123419 : Type'} (_78782 : _123419) (_78781 : type1400 _123419) : ((term1472 _123419 _78781 _78782) = (term1488 _123419 _78782 _78781)) = True.
Proof. exact (TRANS (@lem6189528 _123419 _78782 _78781) (@lem6189532 _123419 _78782 _78781)). Qed.
Lemma lem6189534 {_123419 : Type'} (_78782 : _123419) (_78781 : type1400 _123419) : True = ((term1472 _123419 _78781 _78782) = (term1488 _123419 _78782 _78781)).
Proof. exact (SYM (@lem6189533 _123419 _78782 _78781)). Qed.
Lemma lem6189535 {_123419 : Type'} (_78782 : _123419) (_78781 : type1400 _123419) : (term1472 _123419 _78781 _78782) = (term1488 _123419 _78782 _78781).
Proof. exact (EQ_MP (@lem6189534 _123419 _78782 _78781) (@lem0)). Qed.
Lemma lem6189536 {_123419 : Type'} (_78782 : _123419) (_78781 : type1400 _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : term821 _123419 y' z' x') : term1488 _123419 _78782 _78781.
Proof. exact (EQ_MP (@lem6189535 _123419 _78782 _78781) (@lem6189265 _123419 _78781 _78782 y' z' x' h1)). Qed.
Lemma lem6189538 (b : Prop) (a : Prop) : (a \/ b) = (term1479 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6189539 {_123419 : Type'} (_78781 : type1400 _123419) (_78782 : _123419) : (term1488 _123419 _78782 _78781) = (term1491 _123419 _78781 _78782).
Proof. exact (@lem6189538 (term1247 _123419 _78781) ((term1213 _123419 _78781 _78782) = _78782)). Qed.
Lemma lem6189541 (a : Prop) : (term55 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6189542 {_123419 : Type'} (_78781 : type1400 _123419) : (term1481 _123419 _78781) = (@I ((_123419 -> _123419 -> _123419) -> Prop) (@monoidal _123419) _78781).
Proof. exact (@lem6189541 (@I ((_123419 -> _123419 -> _123419) -> Prop) (@monoidal _123419) _78781)). Qed.
Lemma lem6189543 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6189544 {_123419 : Type'} (_78781 : type1400 _123419) : (term1482 _123419 _78781) = (term1483 _123419 _78781).
Proof. exact (MK_COMB (@lem6189543) (@lem6189542 _123419 _78781)). Qed.
Lemma lem6189545 {_123419 : Type'} (_78781 : type1400 _123419) (_78782 : _123419) : ((term1213 _123419 _78781 _78782) = _78782) = ((term1213 _123419 _78781 _78782) = _78782).
Proof. exact (eq_refl ((term1213 _123419 _78781 _78782) = _78782)). Qed.
Lemma lem6189546 {_123419 : Type'} (_78781 : type1400 _123419) (_78782 : _123419) : (term1491 _123419 _78781 _78782) = (term1492 _123419 _78781 _78782).
Proof. exact (MK_COMB (@lem6189544 _123419 _78781) (@lem6189545 _123419 _78781 _78782)). Qed.
Lemma lem6189547 {_123419 : Type'} (_78781 : type1400 _123419) (_78782 : _123419) : (term1488 _123419 _78782 _78781) = (term1492 _123419 _78781 _78782).
Proof. exact (TRANS (@lem6189539 _123419 _78781 _78782) (@lem6189546 _123419 _78781 _78782)). Qed.
Lemma lem6189550 {_123419 : Type'} (_78781 : type1400 _123419) (_78782 : _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : term821 _123419 y' z' x') : term1492 _123419 _78781 _78782.
Proof. exact (EQ_MP (@lem6189547 _123419 _78781 _78782) (@lem6189536 _123419 _78782 _78781 y' z' x' h1)). Qed.
Lemma lem6189551 {_123419 : Type'} (_78781 : type1400 _123419) (_78782 : _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : term821 _123419 y' z' x') : term1492 _123419 _78781 _78782.
Proof. exact (@lem6189550 _123419 _78781 _78782 y' z' x' h1). Qed.
Lemma lem6189552 {_123419 : Type'} (op : type1400 _123419) (_78782 : _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : term821 _123419 y' z' x') : term1492 _123419 op _78782.
Proof. exact (@lem6189551 _123419 op _78782 y' z' x' h1). Qed.
Lemma lem6189555 {_123419 : Type'} (_78782 : _123419) (op : type1400 _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : @monoidal _123419 op) (h2 : term821 _123419 y' z' x') : (term1213 _123419 op _78782) = _78782.
Proof. exact (@lem6189552 _123419 op _78782 y' z' x' h2 (@lem6189503 _123419 op h1)). Qed.
Lemma lem6189556 {_123419 : Type'} (_78782 : _123419) (op : type1400 _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : @monoidal _123419 op) (h2 : term821 _123419 y' z' x') : (term1213 _123419 op _78782) = _78782.
Proof. exact (@lem6189555 _123419 _78782 op y' z' x' h1 h2). Qed.
Lemma lem6189557 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : @monoidal _123419 op) (h2 : term821 _123419 y' z' x') : (term1485 _123419 op f) = (term1200 _123419 f).
Proof. exact (@lem6189556 _123419 (term1200 _123419 f) op y' z' x' h1 h2). Qed.
Lemma lem6189558 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : @monoidal _123419 op) (h2 : term821 _123419 y' z' x') : term1493 _123419 op f.
Proof. exact (fun h0 : term1494 _123419 op f => @lem6189557 _123419 f op y' z' x' h1 h2). Qed.
Lemma lem6189560 (p : Prop) : (term1475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6189561 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : (term1493 _123419 op f) = ((term1485 _123419 op f) = (term1200 _123419 f)).
Proof. exact (@lem6189560 ((term1485 _123419 op f) = (term1200 _123419 f))). Qed.
Lemma lem6189562 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : @monoidal _123419 op) (h2 : term821 _123419 y' z' x') : (term1485 _123419 op f) = (term1200 _123419 f).
Proof. exact (EQ_MP (@lem6189561 _123419 op f) (@lem6189558 _123419 f op y' z' x' h1 h2)). Qed.
Lemma lem6189580 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6189581 {_123419 : Type'} (y : _123419) (x : _123419) (z : _123419) : (term1495 _123419 x y z) = (term1496 _123419 y x z).
Proof. exact (@lem6189580 (y = z) (term1497 _123419 x z)). Qed.
Lemma lem6189591 {_123419 : Type'} (x : _123419) (y : _123419) : (term1498 _123419 x y) = (term1498 _123419 x y).
Proof. exact (eq_refl (term1498 _123419 x y)). Qed.
Lemma lem6189592 {_123419 : Type'} (y : _123419) (x : _123419) (z : _123419) : (term1473 _123419 x y z) = (term1499 _123419 y x z).
Proof. exact (MK_COMB (@lem6189591 _123419 x y) (@lem6189581 _123419 y x z)). Qed.
Lemma lem6189596 (q : Prop) (p : Prop) (r : Prop) : (term1500 p q r) = (term1500 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6189597 {_123419 : Type'} (y : _123419) (x : _123419) (z : _123419) : (term1499 _123419 y x z) = (term1501 _123419 y x z).
Proof. exact (@lem6189596 (y = z) (term1497 _123419 x y) (term1497 _123419 x z)). Qed.
Lemma lem6189619 {_123419 : Type'} (y : _123419) (x : _123419) (z : _123419) : (term1473 _123419 x y z) = (term1501 _123419 y x z).
Proof. exact (TRANS (@lem6189592 _123419 y x z) (@lem6189597 _123419 y x z)). Qed.
Lemma lem6189620 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6189621 {_123419 : Type'} (y : _123419) (x : _123419) (z : _123419) : (term1502 _123419 x y z) = (term1503 _123419 y x z).
Proof. exact (MK_COMB (@lem6189620) (@lem6189619 _123419 y x z)). Qed.
Lemma lem6189643 {_123419 : Type'} (y : _123419) (x : _123419) (z : _123419) : (term1501 _123419 y x z) = (term1501 _123419 y x z).
Proof. exact (eq_refl (term1501 _123419 y x z)). Qed.
Lemma lem6189644 {_123419 : Type'} (y : _123419) (x : _123419) (z : _123419) : ((term1473 _123419 x y z) = (term1501 _123419 y x z)) = ((term1501 _123419 y x z) = (term1501 _123419 y x z)).
Proof. exact (MK_COMB (@lem6189621 _123419 y x z) (@lem6189643 _123419 y x z)). Qed.
Lemma lem6189646 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6189647 (x : Prop) : (x = x) = True.
Proof. exact (@lem6189646 Prop x). Qed.
Lemma lem6189648 {_123419 : Type'} (y : _123419) (x : _123419) (z : _123419) : ((term1501 _123419 y x z) = (term1501 _123419 y x z)) = True.
Proof. exact (@lem6189647 (term1501 _123419 y x z)). Qed.
Lemma lem6189649 {_123419 : Type'} (y : _123419) (x : _123419) (z : _123419) : ((term1473 _123419 x y z) = (term1501 _123419 y x z)) = True.
Proof. exact (TRANS (@lem6189644 _123419 y x z) (@lem6189648 _123419 y x z)). Qed.
Lemma lem6189650 {_123419 : Type'} (y : _123419) (x : _123419) (z : _123419) : True = ((term1473 _123419 x y z) = (term1501 _123419 y x z)).
Proof. exact (SYM (@lem6189649 _123419 y x z)). Qed.
Lemma lem6189651 {_123419 : Type'} (y : _123419) (x : _123419) (z : _123419) : (term1473 _123419 x y z) = (term1501 _123419 y x z).
Proof. exact (EQ_MP (@lem6189650 _123419 y x z) (@lem0)). Qed.
Lemma lem6189652 {_123419 : Type'} (y : _123419) (x : _123419) (z : _123419) : term1501 _123419 y x z.
Proof. exact (EQ_MP (@lem6189651 _123419 y x z) (@lem6189410 _123419 x y z)). Qed.
Lemma lem6189654 (b : Prop) (a : Prop) : (a \/ b) = (term1479 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6189655 {_123419 : Type'} (x : _123419) (y : _123419) (z : _123419) : (term1501 _123419 y x z) = (term1504 _123419 x y z).
Proof. exact (@lem6189654 (term1505 _123419 y x z) (y = z)). Qed.
Lemma lem6189657 (a : Prop) (b : Prop) : (term1506 a b) = (term1507 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6189658 {_123419 : Type'} (y : _123419) (x : _123419) (z : _123419) : (term1508 _123419 y x z) = (term1509 _123419 y x z).
Proof. exact (@lem6189657 (term1497 _123419 x y) (term1497 _123419 x z)). Qed.
Lemma lem6189660 (a : Prop) : (term55 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6189661 {_123419 : Type'} (x : _123419) (y : _123419) : (term1510 _123419 x y) = (x = y).
Proof. exact (@lem6189660 (x = y)). Qed.
Lemma lem6189662 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6189663 {_123419 : Type'} (x : _123419) (y : _123419) : (term1511 _123419 x y) = (term1512 _123419 x y).
Proof. exact (MK_COMB (@lem6189662) (@lem6189661 _123419 x y)). Qed.
Lemma lem6189665 (a : Prop) : (term55 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6189666 {_123419 : Type'} (x : _123419) (z : _123419) : (term1510 _123419 x z) = (x = z).
Proof. exact (@lem6189665 (x = z)). Qed.
Lemma lem6189667 {_123419 : Type'} (y : _123419) (x : _123419) (z : _123419) : (term1509 _123419 y x z) = (term1513 _123419 y x z).
Proof. exact (MK_COMB (@lem6189663 _123419 x y) (@lem6189666 _123419 x z)). Qed.
Lemma lem6189668 {_123419 : Type'} (y : _123419) (x : _123419) (z : _123419) : (term1508 _123419 y x z) = (term1513 _123419 y x z).
Proof. exact (TRANS (@lem6189658 _123419 y x z) (@lem6189667 _123419 y x z)). Qed.
Lemma lem6189669 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6189670 {_123419 : Type'} (y : _123419) (x : _123419) (z : _123419) : (term1514 _123419 y x z) = (term1515 _123419 y x z).
Proof. exact (MK_COMB (@lem6189669) (@lem6189668 _123419 y x z)). Qed.
Lemma lem6189671 {_123419 : Type'} (y : _123419) (z : _123419) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem6189672 {_123419 : Type'} (x : _123419) (y : _123419) (z : _123419) : (term1504 _123419 x y z) = (term1516 _123419 x y z).
Proof. exact (MK_COMB (@lem6189670 _123419 y x z) (@lem6189671 _123419 y z)). Qed.
Lemma lem6189673 {_123419 : Type'} (x : _123419) (y : _123419) (z : _123419) : (term1501 _123419 y x z) = (term1516 _123419 x y z).
Proof. exact (TRANS (@lem6189655 _123419 x y z) (@lem6189672 _123419 x y z)). Qed.
Lemma lem6189675 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : @monoidal _123419 op) (h2 : term821 _123419 y' z' x') : term1517 _123419 op f.
Proof. exact (conj (@lem6189496 _123419 f op y' z' x' h1 h2) (@lem6189562 _123419 f op y' z' x' h1 h2)). Qed.
Lemma lem6189677 {_123419 : Type'} (x : _123419) (y : _123419) (z : _123419) : term1516 _123419 x y z.
Proof. exact (EQ_MP (@lem6189673 _123419 x y z) (@lem6189652 _123419 y x z)). Qed.
Lemma lem6189678 {_123419 : Type'} (x : _123419) (y : _123419) (z : _123419) : term1516 _123419 x y z.
Proof. exact (@lem6189677 _123419 x y z). Qed.
Lemma lem6189679 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : term1518 _123419 op f.
Proof. exact (@lem6189678 _123419 (term1485 _123419 op f) (term1205 _123419 f op) (term1200 _123419 f)). Qed.
Lemma lem6189682 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : @monoidal _123419 op) (h2 : term821 _123419 y' z' x') : (term1205 _123419 f op) = (term1200 _123419 f).
Proof. exact (@lem6189679 _123419 op f (@lem6189675 _123419 f op y' z' x' h1 h2)). Qed.
Lemma lem6189683 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : @monoidal _123419 op) (h2 : term821 _123419 y' z' x') : (term1205 _123419 f op) = (term1200 _123419 f).
Proof. exact (@lem6189682 _123419 f op y' z' x' h1 h2). Qed.
Lemma lem6189684 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : @monoidal _123419 op) (h2 : term821 _123419 y' z' x') : term1519 _123419 op f.
Proof. exact (fun h0 : term1207 _123419 op f => @lem6189683 _123419 f op y' z' x' h1 h2). Qed.
Lemma lem6189686 (p : Prop) : (term1475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6189687 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : (term1519 _123419 op f) = ((term1205 _123419 f op) = (term1200 _123419 f)).
Proof. exact (@lem6189686 ((term1205 _123419 f op) = (term1200 _123419 f))). Qed.
Lemma lem6189688 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : @monoidal _123419 op) (h2 : term821 _123419 y' z' x') : (term1205 _123419 f op) = (term1200 _123419 f).
Proof. exact (EQ_MP (@lem6189687 _123419 op f) (@lem6189684 _123419 f op y' z' x' h1 h2)). Qed.
Lemma lem6189691 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6189693 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : (term1207 _123419 op f) = (term1520 _123419 op f).
Proof. exact (@lem6189691 ((term1205 _123419 f op) = (term1200 _123419 f))). Qed.
Lemma lem6189696 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (h1 : term381 _123419 op f) : term1520 _123419 op f.
Proof. exact (EQ_MP (@lem6189693 _123419 op f) (@lem6189153 _123419 op f h1)). Qed.
Lemma lem6189699 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : @monoidal _123419 op) (h2 : term381 _123419 op f) (h3 : term821 _123419 y' z' x') : False.
Proof. exact (@lem6189696 _123419 op f h2 (@lem6189688 _123419 f op y' z' x' h1 h3)). Qed.
Lemma lem6189700 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : @monoidal _123419 op) (h2 : term381 _123419 op f) (h3 : term821 _123419 y' z' x') : term1521.
Proof. exact (fun h0 : ~ False => @lem6189699 _123419 op f y' z' x' h1 h2 h3). Qed.
Lemma lem6189702 (p : Prop) : (term1475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6189703 : term1521 = False.
Proof. exact (@lem6189702 False). Qed.
Lemma lem6189705 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (y' : type402 _123419) (z' : type402 _123419) (x' : type402 _123419) (h1 : @monoidal _123419 op) (h2 : term381 _123419 op f) (h3 : term821 _123419 y' z' x') : False.
Proof. exact (EQ_MP (@lem6189703) (@lem6189700 _123419 op f y' z' x' h1 h2 h3)). Qed.
Lemma lem6189706 {_123419 : Type'} (y' : type402 _123419) (x' : type402 _123419) (op : type1400 _123419) (f : nat -> _123419) (h1 : term824 _123419 y' x') (h2 : @monoidal _123419 op) (h3 : term381 _123419 op f) : False.
Proof. exact (ex_elim (@lem6187445 _123419 y' x' h1) (fun z' : type402 _123419 => fun h0 : term823 _123419 y' x' z' => @lem6189705 _123419 op f y' z' x' h2 h3 h0)). Qed.
Lemma lem6189707 {_123419 : Type'} (x' : type402 _123419) (op : type1400 _123419) (f : nat -> _123419) (h1 : term826 _123419 x') (h2 : @monoidal _123419 op) (h3 : term381 _123419 op f) : False.
Proof. exact (ex_elim (@lem6187444 _123419 x' h1) (fun y' : type402 _123419 => fun h0 : term825 _123419 x' y' => @lem6189706 _123419 y' x' op f h0 h2 h3)). Qed.
Lemma lem6189708 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (h1 : term382 _123419) (h2 : @monoidal _123419 op) (h3 : term381 _123419 op f) : False.
Proof. exact (ex_elim (@lem6186744 _123419 h1) (fun x' : type402 _123419 => fun h0 : term827 _123419 x' => @lem6189707 _123419 x' op f h0 h2 h3)). Qed.
Lemma lem6189709 {_123419 : Type'} (y : type962) (x : type962) (op : type1400 _123419) (f : nat -> _123419) (h1 : term382 _123419) (h2 : term1194 y x) (h3 : @monoidal _123419 op) (h4 : term381 _123419 op f) : False.
Proof. exact (ex_elim (@lem6187442 y x h2) (fun z : type962 => fun h0 : term1193 y x z => @lem6189708 _123419 op f h1 h3 h4)). Qed.
Lemma lem6189710 {_123419 : Type'} (x : type962) (op : type1400 _123419) (f : nat -> _123419) (h1 : term382 _123419) (h2 : term1196 x) (h3 : @monoidal _123419 op) (h4 : term381 _123419 op f) : False.
Proof. exact (ex_elim (@lem6187441 x h2) (fun y : type962 => fun h0 : term1195 x y => @lem6189709 _123419 y x op f h1 h0 h3 h4)). Qed.
Lemma lem6189711 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (h1 : term382 _123419) (h2 : term383) (h3 : @monoidal _123419 op) (h4 : term381 _123419 op f) : False.
Proof. exact (ex_elim (@lem6187440 h2) (fun x : type962 => fun h0 : term1197 x => @lem6189710 _123419 x op f h1 h0 h3 h4)). Qed.
Lemma lem6189712 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (h1 : term382 _123419) (h2 : term383) (h3 : @monoidal _123419 op) (h4 : term381 _123419 op f) : (term381 _123419 op f) = False.
Proof. exact (prop_ext (fun h5 : term381 _123419 op f => @lem6189711 _123419 op f h1 h2 h3 h4) (fun h5 : False => @lem6186048 _123419 op f h4)). Qed.
Lemma lem6189713 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (h1 : term382 _123419) (h2 : term383) (h3 : @monoidal _123419 op) (h4 : term381 _123419 op f) : False.
Proof. exact (EQ_MP (@lem6189712 _123419 op f h1 h2 h3 h4) (@lem6186048 _123419 op f h4)). Qed.
Lemma lem6189714 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (h1 : term382 _123419) (h2 : term383) (h3 : @monoidal _123419 op) (h4 : term381 _123419 op f) : (@monoidal _123419 op) = False.
Proof. exact (prop_ext (fun h5 : @monoidal _123419 op => @lem6189713 _123419 op f h1 h2 h3 h4) (fun h5 : False => @lem6186036 _123419 op h3)). Qed.
Lemma lem6189715 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (h1 : term382 _123419) (h2 : term383) (h3 : @monoidal _123419 op) (h4 : term381 _123419 op f) : False.
Proof. exact (EQ_MP (@lem6189714 _123419 op f h1 h2 h3 h4) (@lem6186036 _123419 op h3)). Qed.
Lemma lem6189716 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (h1 : term382 _123419) (h2 : @monoidal _123419 op) (h3 : term381 _123419 op f) : term388.
Proof. exact (fun h0 : term383 => @lem6189715 _123419 op f h1 h0 h2 h3). Qed.
Lemma lem6189717 : term388 = term389.
Proof. exact (@lem69 term383). Qed.
Lemma lem6189718 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (h1 : term382 _123419) (h2 : @monoidal _123419 op) (h3 : term381 _123419 op f) : term389.
Proof. exact (EQ_MP (@lem6189717) (@lem6189716 _123419 op f h1 h2 h3)). Qed.
Lemma lem6189719 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (h1 : @monoidal _123419 op) (h2 : term381 _123419 op f) : term392 _123419.
Proof. exact (fun h0 : term382 _123419 => @lem6189718 _123419 op f h0 h1 h2). Qed.
Lemma lem6189720 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : term395 _123419 op f.
Proof. exact (fun h0 : term381 _123419 op f => @lem6189719 _123419 op f h1 h0). Qed.
Lemma lem6189721 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : term397 _123419 m op f.
Proof. exact (fun h0 : m = (NUMERAL 0) => @lem6189720 _123419 f op h1). Qed.
Lemma lem6189722 {_123419 : Type'} (m : nat) (op : type1400 _123419) (f : nat -> _123419) : term398 _123419 m op f.
Proof. exact (fun h0 : @monoidal _123419 op => @lem6189721 _123419 m f op h0). Qed.
Lemma lem6189727 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : term402 _123419 op f.
Proof. exact (fun m : nat => @lem6189722 _123419 m op f). Qed.
Lemma lem6189732 {_123419 : Type'} (f : nat -> _123419) : term406 _123419 f.
Proof. exact (fun op : type1400 _123419 => @lem6189727 _123419 op f). Qed.
Lemma lem6189737 {_123419 : Type'} : term410 _123419.
Proof. exact (fun f : nat -> _123419 => @lem6189732 _123419 f). Qed.
Lemma lem6189738 {_123419 : Type'} : term409 _123419.
Proof. exact (EQ_MP (@lem6186025 _123419) (@lem6189737 _123419)). Qed.
Lemma lem6189739 {_123419 : Type'} (f : nat -> _123419) : term1522 _123419 f.
Proof. exact (@lem6189738 _123419 f). Qed.
Lemma lem6189740 {_123419 : Type'} (f : nat -> _123419) : (term1522 _123419 f) = (term405 _123419 f).
Proof. exact (eq_refl (term1522 _123419 f)). Qed.
Lemma lem6189741 {_123419 : Type'} (f : nat -> _123419) : term405 _123419 f.
Proof. exact (EQ_MP (@lem6189740 _123419 f) (@lem6189739 _123419 f)). Qed.
Lemma lem6189742 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : term1523 _123419 f op.
Proof. exact (@lem6189741 _123419 f op). Qed.
Lemma lem6189743 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : (term1523 _123419 f op) = (term401 _123419 op f).
Proof. exact (eq_refl (term1523 _123419 f op)). Qed.
Lemma lem6189744 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : term401 _123419 op f.
Proof. exact (EQ_MP (@lem6189743 _123419 op f) (@lem6189742 _123419 f op)). Qed.
Lemma lem6189745 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (m : nat) : term1524 _123419 op f m.
Proof. exact (@lem6189744 _123419 op f m). Qed.
Lemma lem6189746 {_123419 : Type'} (m : nat) (op : type1400 _123419) (f : nat -> _123419) : (term1524 _123419 op f m) = (term384 _123419 m op f).
Proof. exact (eq_refl (term1524 _123419 op f m)). Qed.
Lemma lem6189747 {_123419 : Type'} (m : nat) (op : type1400 _123419) (f : nat -> _123419) : term384 _123419 m op f.
Proof. exact (EQ_MP (@lem6189746 _123419 m op f) (@lem6189745 _123419 op f m)). Qed.
Lemma lem6189749 {_123419 : Type'} (m : nat) (op : type1400 _123419) (f : nat -> _123419) : term384 _123419 m op f.
Proof. exact (@lem6185679 _123419 m op f (@lem6189747 _123419 m op f)). Qed.
Lemma lem6189750 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : term396 _123419 m op f.
Proof. exact (@lem6189749 _123419 m op f (@lem6184862 _123419 op h1)). Qed.
Lemma lem6189751 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (h1 : @monoidal _123419 op) (h2 : m = (NUMERAL 0)) : term394 _123419 op f.
Proof. exact (@lem6189750 _123419 m f op h1 (@lem6184881 m h2)). Qed.
Lemma lem6189752 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (m : nat) (h1 : @monoidal _123419 op) (h2 : term381 _123419 op f) (h3 : m = (NUMERAL 0)) : term391 _123419.
Proof. exact (@lem6189751 _123419 f op m h1 h3 (@lem6185659 _123419 op f h2)). Qed.
Lemma lem6189753 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (m : nat) (h1 : @monoidal _123419 op) (h2 : term381 _123419 op f) (h3 : m = (NUMERAL 0)) : term388.
Proof. exact (@lem6189752 _123419 op f m h1 h2 h3 (@lem6185660 _123419)). Qed.
Lemma lem6189754 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (m : nat) (h1 : @monoidal _123419 op) (h2 : term381 _123419 op f) (h3 : m = (NUMERAL 0)) : False.
Proof. exact (@lem6189753 _123419 op f m h1 h2 h3 (@lem6185661)). Qed.
Lemma lem6189755 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (m : nat) (h1 : @monoidal _123419 op) (h2 : term381 _123419 op f) (h3 : m = (NUMERAL 0)) : (term381 _123419 op f) = False.
Proof. exact (prop_ext (fun h4 : term381 _123419 op f => @lem6189754 _123419 op f m h1 h2 h3) (fun h4 : False => @lem6185659 _123419 op f h2)). Qed.
Lemma lem6189756 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (m : nat) (h1 : @monoidal _123419 op) (h2 : term381 _123419 op f) (h3 : m = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem6189755 _123419 op f m h1 h2 h3) (@lem6185659 _123419 op f h2)). Qed.
Lemma lem6189757 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (h1 : @monoidal _123419 op) (h2 : m = (NUMERAL 0)) : term380 _123419 op f.
Proof. exact (fun h0 : term381 _123419 op f => @lem6189756 _123419 op f m h1 h0 h2). Qed.
Lemma lem6189758 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (h1 : @monoidal _123419 op) (h2 : m = (NUMERAL 0)) : (term320 _123419 f op) = (term327 _123419 f).
Proof. exact (EQ_MP (@lem6185658 _123419 op f) (@lem6189757 _123419 f op m h1 h2)). Qed.
Lemma lem6189760 (p : Prop) : p = (term379 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6189761 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : ((term347 _123419 op m n f) = (term367 _123419 op m f n)) = (term1525 _123419 op m f n).
Proof. exact (@lem6189760 ((term347 _123419 op m n f) = (term367 _123419 op m f n))). Qed.
Lemma lem6189762 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : (term1525 _123419 op m f n) = ((term347 _123419 op m n f) = (term367 _123419 op m f n)).
Proof. exact (SYM (@lem6189761 _123419 op m f n)). Qed.
Lemma lem6189763 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) (h1 : term1526 _123419 op m f n) : term1526 _123419 op m f n.
Proof. exact (h1). Qed.
Lemma lem6189764 {_123419 : Type'} : term382 _123419.
Proof. exact (@lem5712802 _123419). Qed.
Lemma lem6189768 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) (h1 : term1527 _123419 op m f n) : term1527 _123419 op m f n.
Proof. exact (h1). Qed.
Lemma lem6189769 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : term1528 _123419 op m f n.
Proof. exact (fun h0 : term1527 _123419 op m f n => @lem6189768 _123419 op m f n h0). Qed.
Lemma lem6189770 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) (h1 : term1528 _123419 op m f n) : term1528 _123419 op m f n.
Proof. exact (h1). Qed.
Lemma lem6189771 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) (h1 : term1527 _123419 op m f n) : term1527 _123419 op m f n.
Proof. exact (h1). Qed.
Lemma lem6189772 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) (h1 : term1527 _123419 op m f n) (h2 : term1528 _123419 op m f n) : term1527 _123419 op m f n.
Proof. exact (@lem6189770 _123419 op m f n h2 (@lem6189771 _123419 op m f n h1)). Qed.
Lemma lem6189773 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) (h1 : term1527 _123419 op m f n) : term1529 _123419 op m f n.
Proof. exact (fun h0 : term1528 _123419 op m f n => @lem6189772 _123419 op m f n h1 h0). Qed.
Lemma lem6189774 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) (h1 : term1528 _123419 op m f n) : term1528 _123419 op m f n.
Proof. exact (h1). Qed.
Lemma lem6189775 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) (h1 : term1527 _123419 op m f n) (h2 : term1528 _123419 op m f n) : term1527 _123419 op m f n.
Proof. exact (@lem6189773 _123419 op m f n h1 (@lem6189774 _123419 op m f n h2)). Qed.
Lemma lem6189776 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) (h1 : term1528 _123419 op m f n) : term1528 _123419 op m f n.
Proof. exact (fun h0 : term1527 _123419 op m f n => @lem6189775 _123419 op m f n h0 h1). Qed.
Lemma lem6189777 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : term1530 _123419 op m f n.
Proof. exact (fun h0 : term1528 _123419 op m f n => @lem6189776 _123419 op m f n h0). Qed.
Lemma lem6189780 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : term1528 _123419 op m f n.
Proof. exact (@lem6189777 _123419 op m f n (@lem6189769 _123419 op m f n)). Qed.
Lemma lem6189781 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : term1528 _123419 op m f n.
Proof. exact (@lem6189780 _123419 op m f n). Qed.
Lemma lem6189805 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6189806 {_123419 : Type'} : (term1531 _123419) = (term1532 _123419).
Proof. exact (@lem6189805 (term382 _123419)). Qed.
Lemma lem6189839 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : (term1533 _123419 op m f n) = (term1533 _123419 op m f n).
Proof. exact (eq_refl (term1533 _123419 op m f n)). Qed.
Lemma lem6189840 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : (term1534 _123419 op m f n) = (term1535 _123419 op m f n).
Proof. exact (MK_COMB (@lem6189839 _123419 op m f n) (@lem6189806 _123419)). Qed.
Lemma lem6189843 (m : nat) (n : nat) : (term253 m n) = (term253 m n).
Proof. exact (eq_refl (term253 m n)). Qed.
Lemma lem6189844 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : (term1536 _123419 op m f n) = (term1537 _123419 op m f n).
Proof. exact (MK_COMB (@lem6189843 m n) (@lem6189840 _123419 op m f n)). Qed.
Lemma lem6189847 {_123419 : Type'} (op : type1400 _123419) : (term196 _123419 op) = (term196 _123419 op).
Proof. exact (eq_refl (term196 _123419 op)). Qed.
Lemma lem6189848 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : (term1527 _123419 op m f n) = (term1538 _123419 op m f n).
Proof. exact (MK_COMB (@lem6189847 _123419 op) (@lem6189844 _123419 op m f n)). Qed.
Lemma lem6189851 {_123419 : Type'} (m : nat) (f : nat -> _123419) (n : nat) : (term1539 _123419 m f n) = (term1540 _123419 m f n).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6189848 _123419 op m f n)). Qed.
Lemma lem6189852 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6189853 {_123419 : Type'} (m : nat) (f : nat -> _123419) (n : nat) : (term1541 _123419 m f n) = (term1542 _123419 m f n).
Proof. exact (MK_COMB (@lem6189852 _123419) (@lem6189851 _123419 m f n)). Qed.
Lemma lem6189858 {_123419 : Type'} (f : nat -> _123419) (n : nat) : (term1543 _123419 f n) = (term1544 _123419 f n).
Proof. exact (fun_ext (fun m : nat => @lem6189853 _123419 m f n)). Qed.
Lemma lem6189859 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6189860 {_123419 : Type'} (f : nat -> _123419) (n : nat) : (term1545 _123419 f n) = (term1546 _123419 f n).
Proof. exact (MK_COMB (@lem6189859) (@lem6189858 _123419 f n)). Qed.
Lemma lem6189865 {_123419 : Type'} (n : nat) : (term1547 _123419 n) = (term1548 _123419 n).
Proof. exact (fun_ext (fun f : nat -> _123419 => @lem6189860 _123419 f n)). Qed.
Lemma lem6189866 {_123419 : Type'} : (@all (nat -> _123419)) = (@all (nat -> _123419)).
Proof. exact (eq_refl (@all (nat -> _123419))). Qed.
Lemma lem6189867 {_123419 : Type'} (n : nat) : (term1549 _123419 n) = (term1550 _123419 n).
Proof. exact (MK_COMB (@lem6189866 _123419) (@lem6189865 _123419 n)). Qed.
Lemma lem6189872 {_123419 : Type'} : (term1551 _123419) = (term1552 _123419).
Proof. exact (fun_ext (fun n : nat => @lem6189867 _123419 n)). Qed.
Lemma lem6189873 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6189882 {_123419 : Type'} : (term1553 _123419) = (term1554 _123419).
Proof. exact (MK_COMB (@lem6189873) (@lem6189872 _123419)). Qed.
Lemma lem6189883 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : ((term432 _123419 op x) = x) = ((term432 _123419 op x) = x).
Proof. exact (eq_refl ((term432 _123419 op x) = x)). Qed.
Lemma lem6189884 {_123419 : Type'} (op : type1400 _123419) : (term433 _123419 op) = (term433 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6189883 _123419 op x)). Qed.
Lemma lem6189885 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6189886 {_123419 : Type'} (op : type1400 _123419) : (term434 _123419 op) = (term434 _123419 op).
Proof. exact (MK_COMB (@lem6189885 _123419) (@lem6189884 _123419 op)). Qed.
Lemma lem6189887 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : ((term435 _123419 x op y z) = (term436 _123419 op x y z)) = ((term435 _123419 x op y z) = (term436 _123419 op x y z)).
Proof. exact (eq_refl ((term435 _123419 x op y z) = (term436 _123419 op x y z))). Qed.
Lemma lem6189888 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term437 _123419 op x y) = (term437 _123419 op x y).
Proof. exact (fun_ext (fun z : _123419 => @lem6189887 _123419 op x y z)). Qed.
Lemma lem6189889 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6189890 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term438 _123419 op x y) = (term438 _123419 op x y).
Proof. exact (MK_COMB (@lem6189889 _123419) (@lem6189888 _123419 op x y)). Qed.
Lemma lem6189891 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term439 _123419 op x) = (term439 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6189890 _123419 op x y)). Qed.
Lemma lem6189892 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6189893 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term440 _123419 op x) = (term440 _123419 op x).
Proof. exact (MK_COMB (@lem6189892 _123419) (@lem6189891 _123419 op x)). Qed.
Lemma lem6189894 {_123419 : Type'} (op : type1400 _123419) : (term441 _123419 op) = (term441 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6189893 _123419 op x)). Qed.
Lemma lem6189895 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6189896 {_123419 : Type'} (op : type1400 _123419) : (term442 _123419 op) = (term442 _123419 op).
Proof. exact (MK_COMB (@lem6189895 _123419) (@lem6189894 _123419 op)). Qed.
Lemma lem6189897 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6189898 {_123419 : Type'} (op : type1400 _123419) : (term443 _123419 op) = (term443 _123419 op).
Proof. exact (MK_COMB (@lem6189897) (@lem6189896 _123419 op)). Qed.
Lemma lem6189899 {_123419 : Type'} (op : type1400 _123419) : (term444 _123419 op) = (term444 _123419 op).
Proof. exact (MK_COMB (@lem6189898 _123419 op) (@lem6189886 _123419 op)). Qed.
Lemma lem6189900 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : ((op x y) = (op y x)) = ((op x y) = (op y x)).
Proof. exact (eq_refl ((op x y) = (op y x))). Qed.
Lemma lem6189901 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term445 _123419 op x) = (term445 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6189900 _123419 op y x)). Qed.
Lemma lem6189902 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6189903 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term446 _123419 op x) = (term446 _123419 op x).
Proof. exact (MK_COMB (@lem6189902 _123419) (@lem6189901 _123419 op x)). Qed.
Lemma lem6189904 {_123419 : Type'} (op : type1400 _123419) : (term447 _123419 op) = (term447 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6189903 _123419 op x)). Qed.
Lemma lem6189905 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6189906 {_123419 : Type'} (op : type1400 _123419) : (term448 _123419 op) = (term448 _123419 op).
Proof. exact (MK_COMB (@lem6189905 _123419) (@lem6189904 _123419 op)). Qed.
Lemma lem6189907 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6189908 {_123419 : Type'} (op : type1400 _123419) : (term449 _123419 op) = (term449 _123419 op).
Proof. exact (MK_COMB (@lem6189907) (@lem6189906 _123419 op)). Qed.
Lemma lem6189909 {_123419 : Type'} (op : type1400 _123419) : (term450 _123419 op) = (term450 _123419 op).
Proof. exact (MK_COMB (@lem6189908 _123419 op) (@lem6189899 _123419 op)). Qed.
Lemma lem6189912 {_123419 : Type'} (op : type1400 _123419) : (term451 _123419 op) = (term451 _123419 op).
Proof. exact (eq_refl (term451 _123419 op)). Qed.
Lemma lem6189913 {_123419 : Type'} (op : type1400 _123419) : ((@monoidal _123419 op) = (term450 _123419 op)) = ((@monoidal _123419 op) = (term450 _123419 op)).
Proof. exact (MK_COMB (@lem6189912 _123419 op) (@lem6189909 _123419 op)). Qed.
Lemma lem6189914 {_123419 : Type'} : (term452 _123419) = (term452 _123419).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6189913 _123419 op)). Qed.
Lemma lem6189915 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6189916 {_123419 : Type'} : (term382 _123419) = (term382 _123419).
Proof. exact (MK_COMB (@lem6189915 _123419) (@lem6189914 _123419)). Qed.
Lemma lem6189917 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6189918 {_123419 : Type'} : (term1532 _123419) = (term1532 _123419).
Proof. exact (MK_COMB (@lem6189917) (@lem6189916 _123419)). Qed.
Lemma lem6189923 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : (term1533 _123419 op m f n) = (term1533 _123419 op m f n).
Proof. exact (eq_refl (term1533 _123419 op m f n)). Qed.
Lemma lem6189924 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : (term1535 _123419 op m f n) = (term1535 _123419 op m f n).
Proof. exact (MK_COMB (@lem6189923 _123419 op m f n) (@lem6189918 _123419)). Qed.
Lemma lem6189927 (m : nat) (n : nat) : (term253 m n) = (term253 m n).
Proof. exact (eq_refl (term253 m n)). Qed.
Lemma lem6189928 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : (term1537 _123419 op m f n) = (term1537 _123419 op m f n).
Proof. exact (MK_COMB (@lem6189927 m n) (@lem6189924 _123419 op m f n)). Qed.
Lemma lem6189931 {_123419 : Type'} (op : type1400 _123419) : (term196 _123419 op) = (term196 _123419 op).
Proof. exact (eq_refl (term196 _123419 op)). Qed.
Lemma lem6189932 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : (term1538 _123419 op m f n) = (term1538 _123419 op m f n).
Proof. exact (MK_COMB (@lem6189931 _123419 op) (@lem6189928 _123419 op m f n)). Qed.
Lemma lem6189933 {_123419 : Type'} (m : nat) (f : nat -> _123419) (n : nat) : (term1540 _123419 m f n) = (term1540 _123419 m f n).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6189932 _123419 op m f n)). Qed.
Lemma lem6189934 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6189935 {_123419 : Type'} (m : nat) (f : nat -> _123419) (n : nat) : (term1542 _123419 m f n) = (term1542 _123419 m f n).
Proof. exact (MK_COMB (@lem6189934 _123419) (@lem6189933 _123419 m f n)). Qed.
Lemma lem6189936 {_123419 : Type'} (f : nat -> _123419) (n : nat) : (term1544 _123419 f n) = (term1544 _123419 f n).
Proof. exact (fun_ext (fun m : nat => @lem6189935 _123419 m f n)). Qed.
Lemma lem6189937 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6189938 {_123419 : Type'} (f : nat -> _123419) (n : nat) : (term1546 _123419 f n) = (term1546 _123419 f n).
Proof. exact (MK_COMB (@lem6189937) (@lem6189936 _123419 f n)). Qed.
Lemma lem6189939 {_123419 : Type'} (n : nat) : (term1548 _123419 n) = (term1548 _123419 n).
Proof. exact (fun_ext (fun f : nat -> _123419 => @lem6189938 _123419 f n)). Qed.
Lemma lem6189940 {_123419 : Type'} : (@all (nat -> _123419)) = (@all (nat -> _123419)).
Proof. exact (eq_refl (@all (nat -> _123419))). Qed.
Lemma lem6189941 {_123419 : Type'} (n : nat) : (term1550 _123419 n) = (term1550 _123419 n).
Proof. exact (MK_COMB (@lem6189940 _123419) (@lem6189939 _123419 n)). Qed.
Lemma lem6189942 {_123419 : Type'} : (term1552 _123419) = (term1552 _123419).
Proof. exact (fun_ext (fun n : nat => @lem6189941 _123419 n)). Qed.
Lemma lem6189943 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6189944 {_123419 : Type'} : (term1554 _123419) = (term1554 _123419).
Proof. exact (MK_COMB (@lem6189943) (@lem6189942 _123419)). Qed.
Lemma lem6190023 {_123419 : Type'} : (term1553 _123419) = (term1554 _123419).
Proof. exact (TRANS (@lem6189882 _123419) (@lem6189944 _123419)). Qed.
Lemma lem6190024 {_123419 : Type'} : (term1554 _123419) = (term1553 _123419).
Proof. exact (SYM (@lem6190023 _123419)). Qed.
Lemma lem6190028 {_123419 : Type'} (h1 : term382 _123419) : term382 _123419.
Proof. exact (h1). Qed.
Lemma lem6190034 {_123419 : Type'} (op : type1400 _123419) (h1 : @monoidal _123419 op) : @monoidal _123419 op.
Proof. exact (h1). Qed.
Lemma lem6190046 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) (h1 : term1526 _123419 op m f n) : term1526 _123419 op m f n.
Proof. exact (h1). Qed.
Lemma lem6190050 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : ((op x y) = (op y x)) = ((op x y) = (op y x)).
Proof. exact (eq_refl ((op x y) = (op y x))). Qed.
Lemma lem6190051 {_123419 : Type'} (P : _123419 -> Prop) : (term453 _123419 P) = (term454 _123419 P).
Proof. exact (@lem18392 _123419 P). Qed.
Lemma lem6190052 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term455 _123419 op x) = (term456 _123419 op x).
Proof. exact (@lem6190051 _123419 (term445 _123419 op x)). Qed.
Lemma lem6190053 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (term457 _123419 op x y) = ((op x y) = (op y x)).
Proof. exact (eq_refl (term457 _123419 op x y)). Qed.
Lemma lem6190054 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6190056 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (term458 _123419 op x y) = (term459 _123419 op y x).
Proof. exact (MK_COMB (@lem6190054) (@lem6190053 _123419 op y x)). Qed.
Lemma lem6190057 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term460 _123419 op x) = (term461 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6190056 _123419 op y x)). Qed.
Lemma lem6190058 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190059 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term456 _123419 op x) = (term462 _123419 op x).
Proof. exact (MK_COMB (@lem6190058 _123419) (@lem6190057 _123419 op x)). Qed.
Lemma lem6190060 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term455 _123419 op x) = (term462 _123419 op x).
Proof. exact (TRANS (@lem6190052 _123419 op x) (@lem6190059 _123419 op x)). Qed.
Lemma lem6190061 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term445 _123419 op x) = (term445 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6190050 _123419 op y x)). Qed.
Lemma lem6190062 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6190063 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term446 _123419 op x) = (term446 _123419 op x).
Proof. exact (MK_COMB (@lem6190062 _123419) (@lem6190061 _123419 op x)). Qed.
Lemma lem6190064 {_123419 : Type'} (P : _123419 -> Prop) : (term453 _123419 P) = (term454 _123419 P).
Proof. exact (@lem18392 _123419 P). Qed.
Lemma lem6190065 {_123419 : Type'} (op : type1400 _123419) : (term463 _123419 op) = (term464 _123419 op).
Proof. exact (@lem6190064 _123419 (term447 _123419 op)). Qed.
Lemma lem6190066 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term465 _123419 op x) = (term446 _123419 op x).
Proof. exact (eq_refl (term465 _123419 op x)). Qed.
Lemma lem6190067 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6190068 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term466 _123419 op x) = (term455 _123419 op x).
Proof. exact (MK_COMB (@lem6190067) (@lem6190066 _123419 op x)). Qed.
Lemma lem6190069 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term466 _123419 op x) = (term462 _123419 op x).
Proof. exact (TRANS (@lem6190068 _123419 op x) (@lem6190060 _123419 op x)). Qed.
Lemma lem6190070 {_123419 : Type'} (op : type1400 _123419) : (term467 _123419 op) = (term468 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6190069 _123419 op x)). Qed.
Lemma lem6190071 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190072 {_123419 : Type'} (op : type1400 _123419) : (term464 _123419 op) = (term469 _123419 op).
Proof. exact (MK_COMB (@lem6190071 _123419) (@lem6190070 _123419 op)). Qed.
Lemma lem6190073 {_123419 : Type'} (op : type1400 _123419) : (term463 _123419 op) = (term469 _123419 op).
Proof. exact (TRANS (@lem6190065 _123419 op) (@lem6190072 _123419 op)). Qed.
Lemma lem6190074 {_123419 : Type'} (op : type1400 _123419) : (term447 _123419 op) = (term447 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6190063 _123419 op x)). Qed.
Lemma lem6190075 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6190076 {_123419 : Type'} (op : type1400 _123419) : (term448 _123419 op) = (term448 _123419 op).
Proof. exact (MK_COMB (@lem6190075 _123419) (@lem6190074 _123419 op)). Qed.
Lemma lem6190078 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : ((term435 _123419 x op y z) = (term436 _123419 op x y z)) = ((term435 _123419 x op y z) = (term436 _123419 op x y z)).
Proof. exact (eq_refl ((term435 _123419 x op y z) = (term436 _123419 op x y z))). Qed.
Lemma lem6190079 {_123419 : Type'} (P : _123419 -> Prop) : (term453 _123419 P) = (term454 _123419 P).
Proof. exact (@lem18392 _123419 P). Qed.
Lemma lem6190080 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term470 _123419 op x y) = (term471 _123419 op x y).
Proof. exact (@lem6190079 _123419 (term437 _123419 op x y)). Qed.
Lemma lem6190081 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : (term472 _123419 op x y z) = ((term435 _123419 x op y z) = (term436 _123419 op x y z)).
Proof. exact (eq_refl (term472 _123419 op x y z)). Qed.
Lemma lem6190082 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6190084 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : (term473 _123419 op x y z) = (term474 _123419 op x y z).
Proof. exact (MK_COMB (@lem6190082) (@lem6190081 _123419 op x y z)). Qed.
Lemma lem6190085 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term475 _123419 op x y) = (term476 _123419 op x y).
Proof. exact (fun_ext (fun z : _123419 => @lem6190084 _123419 op x y z)). Qed.
Lemma lem6190086 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190087 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term471 _123419 op x y) = (term477 _123419 op x y).
Proof. exact (MK_COMB (@lem6190086 _123419) (@lem6190085 _123419 op x y)). Qed.
Lemma lem6190088 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term470 _123419 op x y) = (term477 _123419 op x y).
Proof. exact (TRANS (@lem6190080 _123419 op x y) (@lem6190087 _123419 op x y)). Qed.
Lemma lem6190089 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term437 _123419 op x y) = (term437 _123419 op x y).
Proof. exact (fun_ext (fun z : _123419 => @lem6190078 _123419 op x y z)). Qed.
Lemma lem6190090 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6190091 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term438 _123419 op x y) = (term438 _123419 op x y).
Proof. exact (MK_COMB (@lem6190090 _123419) (@lem6190089 _123419 op x y)). Qed.
Lemma lem6190092 {_123419 : Type'} (P : _123419 -> Prop) : (term453 _123419 P) = (term454 _123419 P).
Proof. exact (@lem18392 _123419 P). Qed.
Lemma lem6190093 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term478 _123419 op x) = (term479 _123419 op x).
Proof. exact (@lem6190092 _123419 (term439 _123419 op x)). Qed.
Lemma lem6190094 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term480 _123419 op x y) = (term438 _123419 op x y).
Proof. exact (eq_refl (term480 _123419 op x y)). Qed.
Lemma lem6190095 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6190096 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term481 _123419 op x y) = (term470 _123419 op x y).
Proof. exact (MK_COMB (@lem6190095) (@lem6190094 _123419 op x y)). Qed.
Lemma lem6190097 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term481 _123419 op x y) = (term477 _123419 op x y).
Proof. exact (TRANS (@lem6190096 _123419 op x y) (@lem6190088 _123419 op x y)). Qed.
Lemma lem6190098 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term482 _123419 op x) = (term483 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6190097 _123419 op x y)). Qed.
Lemma lem6190099 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190100 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term479 _123419 op x) = (term484 _123419 op x).
Proof. exact (MK_COMB (@lem6190099 _123419) (@lem6190098 _123419 op x)). Qed.
Lemma lem6190101 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term478 _123419 op x) = (term484 _123419 op x).
Proof. exact (TRANS (@lem6190093 _123419 op x) (@lem6190100 _123419 op x)). Qed.
Lemma lem6190102 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term439 _123419 op x) = (term439 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6190091 _123419 op x y)). Qed.
Lemma lem6190103 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6190104 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term440 _123419 op x) = (term440 _123419 op x).
Proof. exact (MK_COMB (@lem6190103 _123419) (@lem6190102 _123419 op x)). Qed.
Lemma lem6190105 {_123419 : Type'} (P : _123419 -> Prop) : (term453 _123419 P) = (term454 _123419 P).
Proof. exact (@lem18392 _123419 P). Qed.
Lemma lem6190106 {_123419 : Type'} (op : type1400 _123419) : (term485 _123419 op) = (term486 _123419 op).
Proof. exact (@lem6190105 _123419 (term441 _123419 op)). Qed.
Lemma lem6190107 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term487 _123419 op x) = (term440 _123419 op x).
Proof. exact (eq_refl (term487 _123419 op x)). Qed.
Lemma lem6190108 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6190109 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term488 _123419 op x) = (term478 _123419 op x).
Proof. exact (MK_COMB (@lem6190108) (@lem6190107 _123419 op x)). Qed.
Lemma lem6190110 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term488 _123419 op x) = (term484 _123419 op x).
Proof. exact (TRANS (@lem6190109 _123419 op x) (@lem6190101 _123419 op x)). Qed.
Lemma lem6190111 {_123419 : Type'} (op : type1400 _123419) : (term489 _123419 op) = (term490 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6190110 _123419 op x)). Qed.
Lemma lem6190112 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190113 {_123419 : Type'} (op : type1400 _123419) : (term486 _123419 op) = (term491 _123419 op).
Proof. exact (MK_COMB (@lem6190112 _123419) (@lem6190111 _123419 op)). Qed.
Lemma lem6190114 {_123419 : Type'} (op : type1400 _123419) : (term485 _123419 op) = (term491 _123419 op).
Proof. exact (TRANS (@lem6190106 _123419 op) (@lem6190113 _123419 op)). Qed.
Lemma lem6190115 {_123419 : Type'} (op : type1400 _123419) : (term441 _123419 op) = (term441 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6190104 _123419 op x)). Qed.
Lemma lem6190116 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6190117 {_123419 : Type'} (op : type1400 _123419) : (term442 _123419 op) = (term442 _123419 op).
Proof. exact (MK_COMB (@lem6190116 _123419) (@lem6190115 _123419 op)). Qed.
Lemma lem6190119 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : ((term432 _123419 op x) = x) = ((term432 _123419 op x) = x).
Proof. exact (eq_refl ((term432 _123419 op x) = x)). Qed.
Lemma lem6190120 {_123419 : Type'} (P : _123419 -> Prop) : (term453 _123419 P) = (term454 _123419 P).
Proof. exact (@lem18392 _123419 P). Qed.
Lemma lem6190121 {_123419 : Type'} (op : type1400 _123419) : (term492 _123419 op) = (term493 _123419 op).
Proof. exact (@lem6190120 _123419 (term433 _123419 op)). Qed.
Lemma lem6190122 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term494 _123419 op x) = ((term432 _123419 op x) = x).
Proof. exact (eq_refl (term494 _123419 op x)). Qed.
Lemma lem6190123 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6190125 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term495 _123419 op x) = (term496 _123419 op x).
Proof. exact (MK_COMB (@lem6190123) (@lem6190122 _123419 op x)). Qed.
Lemma lem6190126 {_123419 : Type'} (op : type1400 _123419) : (term497 _123419 op) = (term498 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6190125 _123419 op x)). Qed.
Lemma lem6190127 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190128 {_123419 : Type'} (op : type1400 _123419) : (term493 _123419 op) = (term499 _123419 op).
Proof. exact (MK_COMB (@lem6190127 _123419) (@lem6190126 _123419 op)). Qed.
Lemma lem6190129 {_123419 : Type'} (op : type1400 _123419) : (term492 _123419 op) = (term499 _123419 op).
Proof. exact (TRANS (@lem6190121 _123419 op) (@lem6190128 _123419 op)). Qed.
Lemma lem6190130 {_123419 : Type'} (op : type1400 _123419) : (term433 _123419 op) = (term433 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6190119 _123419 op x)). Qed.
Lemma lem6190131 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6190132 {_123419 : Type'} (op : type1400 _123419) : (term434 _123419 op) = (term434 _123419 op).
Proof. exact (MK_COMB (@lem6190131 _123419) (@lem6190130 _123419 op)). Qed.
Lemma lem6190133 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6190134 {_123419 : Type'} (op : type1400 _123419) : (term500 _123419 op) = (term501 _123419 op).
Proof. exact (MK_COMB (@lem6190133) (@lem6190114 _123419 op)). Qed.
Lemma lem6190135 {_123419 : Type'} (op : type1400 _123419) : (term502 _123419 op) = (term503 _123419 op).
Proof. exact (MK_COMB (@lem6190134 _123419 op) (@lem6190129 _123419 op)). Qed.
Lemma lem6190136 {_123419 : Type'} (op : type1400 _123419) : (term504 _123419 op) = (term502 _123419 op).
Proof. exact (@lem17045 (term442 _123419 op) (term434 _123419 op)). Qed.
Lemma lem6190137 {_123419 : Type'} (op : type1400 _123419) : (term504 _123419 op) = (term503 _123419 op).
Proof. exact (TRANS (@lem6190136 _123419 op) (@lem6190135 _123419 op)). Qed.
Lemma lem6190138 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6190139 {_123419 : Type'} (op : type1400 _123419) : (term443 _123419 op) = (term443 _123419 op).
Proof. exact (MK_COMB (@lem6190138) (@lem6190117 _123419 op)). Qed.
Lemma lem6190140 {_123419 : Type'} (op : type1400 _123419) : (term444 _123419 op) = (term444 _123419 op).
Proof. exact (MK_COMB (@lem6190139 _123419 op) (@lem6190132 _123419 op)). Qed.
Lemma lem6190141 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6190142 {_123419 : Type'} (op : type1400 _123419) : (term505 _123419 op) = (term506 _123419 op).
Proof. exact (MK_COMB (@lem6190141) (@lem6190073 _123419 op)). Qed.
Lemma lem6190143 {_123419 : Type'} (op : type1400 _123419) : (term507 _123419 op) = (term508 _123419 op).
Proof. exact (MK_COMB (@lem6190142 _123419 op) (@lem6190137 _123419 op)). Qed.
Lemma lem6190144 {_123419 : Type'} (op : type1400 _123419) : (term509 _123419 op) = (term507 _123419 op).
Proof. exact (@lem17045 (term448 _123419 op) (term444 _123419 op)). Qed.
Lemma lem6190145 {_123419 : Type'} (op : type1400 _123419) : (term509 _123419 op) = (term508 _123419 op).
Proof. exact (TRANS (@lem6190144 _123419 op) (@lem6190143 _123419 op)). Qed.
Lemma lem6190146 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6190147 {_123419 : Type'} (op : type1400 _123419) : (term449 _123419 op) = (term449 _123419 op).
Proof. exact (MK_COMB (@lem6190146) (@lem6190076 _123419 op)). Qed.
Lemma lem6190148 {_123419 : Type'} (op : type1400 _123419) : (term450 _123419 op) = (term450 _123419 op).
Proof. exact (MK_COMB (@lem6190147 _123419 op) (@lem6190140 _123419 op)). Qed.
Lemma lem6190150 {_123419 : Type'} (op : type1400 _123419) : (term510 _123419 op) = (term510 _123419 op).
Proof. exact (eq_refl (term510 _123419 op)). Qed.
Lemma lem6190151 {_123419 : Type'} (op : type1400 _123419) : (term511 _123419 op) = (term511 _123419 op).
Proof. exact (MK_COMB (@lem6190150 _123419 op) (@lem6190148 _123419 op)). Qed.
Lemma lem6190153 {_123419 : Type'} (op : type1400 _123419) : (term512 _123419 op) = (term512 _123419 op).
Proof. exact (eq_refl (term512 _123419 op)). Qed.
Lemma lem6190154 {_123419 : Type'} (op : type1400 _123419) : (term513 _123419 op) = (term514 _123419 op).
Proof. exact (MK_COMB (@lem6190153 _123419 op) (@lem6190145 _123419 op)). Qed.
Lemma lem6190155 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6190156 {_123419 : Type'} (op : type1400 _123419) : (term515 _123419 op) = (term516 _123419 op).
Proof. exact (MK_COMB (@lem6190155) (@lem6190154 _123419 op)). Qed.
Lemma lem6190157 {_123419 : Type'} (op : type1400 _123419) : (term517 _123419 op) = (term518 _123419 op).
Proof. exact (MK_COMB (@lem6190156 _123419 op) (@lem6190151 _123419 op)). Qed.
Lemma lem6190158 {_123419 : Type'} (op : type1400 _123419) : ((@monoidal _123419 op) = (term450 _123419 op)) = (term517 _123419 op).
Proof. exact (@lem17784 (@monoidal _123419 op) (term450 _123419 op)). Qed.
Lemma lem6190159 {_123419 : Type'} (op : type1400 _123419) : ((@monoidal _123419 op) = (term450 _123419 op)) = (term518 _123419 op).
Proof. exact (TRANS (@lem6190158 _123419 op) (@lem6190157 _123419 op)). Qed.
Lemma lem6190160 {_123419 : Type'} : (term452 _123419) = (term519 _123419).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6190159 _123419 op)). Qed.
Lemma lem6190161 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6190162 {_123419 : Type'} : (term382 _123419) = (term520 _123419).
Proof. exact (MK_COMB (@lem6190161 _123419) (@lem6190160 _123419)). Qed.
Lemma lem6190164 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term521 A P Q) = (term522 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6190165 {_123419 : Type'} (P : type403 _123419) (Q : type403 _123419) : (term523 _123419 P Q) = (term524 _123419 P Q).
Proof. exact (@lem6190164 (type1400 _123419) P Q). Qed.
Lemma lem6190166 {_123419 : Type'} : (term525 _123419) = (term526 _123419).
Proof. exact (@lem6190165 _123419 (term527 _123419) (term528 _123419)). Qed.
Lemma lem6190167 {_123419 : Type'} (op : type1400 _123419) : (term529 _123419 op) = (term514 _123419 op).
Proof. exact (eq_refl (term529 _123419 op)). Qed.
Lemma lem6190168 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6190169 {_123419 : Type'} (op : type1400 _123419) : (term530 _123419 op) = (term516 _123419 op).
Proof. exact (MK_COMB (@lem6190168) (@lem6190167 _123419 op)). Qed.
Lemma lem6190170 {_123419 : Type'} (op : type1400 _123419) : (term531 _123419 op) = (term511 _123419 op).
Proof. exact (eq_refl (term531 _123419 op)). Qed.
Lemma lem6190171 {_123419 : Type'} (op : type1400 _123419) : (term532 _123419 op) = (term518 _123419 op).
Proof. exact (MK_COMB (@lem6190169 _123419 op) (@lem6190170 _123419 op)). Qed.
Lemma lem6190172 {_123419 : Type'} : (term533 _123419) = (term519 _123419).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6190171 _123419 op)). Qed.
Lemma lem6190173 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6190174 {_123419 : Type'} : (term525 _123419) = (term520 _123419).
Proof. exact (MK_COMB (@lem6190173 _123419) (@lem6190172 _123419)). Qed.
Lemma lem6190175 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6190176 {_123419 : Type'} : (term534 _123419) = (term535 _123419).
Proof. exact (MK_COMB (@lem6190175) (@lem6190174 _123419)). Qed.
Lemma lem6190177 {_123419 : Type'} (op : type1400 _123419) : (term529 _123419 op) = (term514 _123419 op).
Proof. exact (eq_refl (term529 _123419 op)). Qed.
Lemma lem6190178 {_123419 : Type'} : (term536 _123419) = (term527 _123419).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6190177 _123419 op)). Qed.
Lemma lem6190179 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6190180 {_123419 : Type'} : (term537 _123419) = (term538 _123419).
Proof. exact (MK_COMB (@lem6190179 _123419) (@lem6190178 _123419)). Qed.
Lemma lem6190181 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6190182 {_123419 : Type'} : (term539 _123419) = (term540 _123419).
Proof. exact (MK_COMB (@lem6190181) (@lem6190180 _123419)). Qed.
Lemma lem6190183 {_123419 : Type'} (op : type1400 _123419) : (term531 _123419 op) = (term511 _123419 op).
Proof. exact (eq_refl (term531 _123419 op)). Qed.
Lemma lem6190184 {_123419 : Type'} : (term541 _123419) = (term528 _123419).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6190183 _123419 op)). Qed.
Lemma lem6190185 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6190186 {_123419 : Type'} : (term542 _123419) = (term543 _123419).
Proof. exact (MK_COMB (@lem6190185 _123419) (@lem6190184 _123419)). Qed.
Lemma lem6190187 {_123419 : Type'} : (term526 _123419) = (term544 _123419).
Proof. exact (MK_COMB (@lem6190182 _123419) (@lem6190186 _123419)). Qed.
Lemma lem6190188 {_123419 : Type'} : ((term525 _123419) = (term526 _123419)) = ((term520 _123419) = (term544 _123419)).
Proof. exact (MK_COMB (@lem6190176 _123419) (@lem6190187 _123419)). Qed.
Lemma lem6190189 {_123419 : Type'} : (term520 _123419) = (term544 _123419).
Proof. exact (EQ_MP (@lem6190188 _123419) (@lem6190166 _123419)). Qed.
Lemma lem6190315 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term545 A P Q) = (term546 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6190316 {_123419 : Type'} (P : _123419 -> Prop) (Q : _123419 -> Prop) : (term545 _123419 P Q) = (term546 _123419 P Q).
Proof. exact (@lem6190315 _123419 P Q). Qed.
Lemma lem6190317 {_123419 : Type'} (op : type1400 _123419) : (term547 _123419 op) = (term548 _123419 op).
Proof. exact (@lem6190316 _123419 (term490 _123419 op) (term498 _123419 op)). Qed.
Lemma lem6190318 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term549 _123419 op x) = (term484 _123419 op x).
Proof. exact (eq_refl (term549 _123419 op x)). Qed.
Lemma lem6190319 {_123419 : Type'} (op : type1400 _123419) : (term550 _123419 op) = (term490 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6190318 _123419 op x)). Qed.
Lemma lem6190320 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190321 {_123419 : Type'} (op : type1400 _123419) : (term551 _123419 op) = (term491 _123419 op).
Proof. exact (MK_COMB (@lem6190320 _123419) (@lem6190319 _123419 op)). Qed.
Lemma lem6190322 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6190323 {_123419 : Type'} (op : type1400 _123419) : (term552 _123419 op) = (term501 _123419 op).
Proof. exact (MK_COMB (@lem6190322) (@lem6190321 _123419 op)). Qed.
Lemma lem6190324 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term553 _123419 op x) = (term496 _123419 op x).
Proof. exact (eq_refl (term553 _123419 op x)). Qed.
Lemma lem6190325 {_123419 : Type'} (op : type1400 _123419) : (term554 _123419 op) = (term498 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6190324 _123419 op x)). Qed.
Lemma lem6190326 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190327 {_123419 : Type'} (op : type1400 _123419) : (term555 _123419 op) = (term499 _123419 op).
Proof. exact (MK_COMB (@lem6190326 _123419) (@lem6190325 _123419 op)). Qed.
Lemma lem6190328 {_123419 : Type'} (op : type1400 _123419) : (term547 _123419 op) = (term503 _123419 op).
Proof. exact (MK_COMB (@lem6190323 _123419 op) (@lem6190327 _123419 op)). Qed.
Lemma lem6190329 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6190330 {_123419 : Type'} (op : type1400 _123419) : (term556 _123419 op) = (term557 _123419 op).
Proof. exact (MK_COMB (@lem6190329) (@lem6190328 _123419 op)). Qed.
Lemma lem6190331 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term549 _123419 op x) = (term484 _123419 op x).
Proof. exact (eq_refl (term549 _123419 op x)). Qed.
Lemma lem6190332 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6190333 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term558 _123419 op x) = (term559 _123419 op x).
Proof. exact (MK_COMB (@lem6190332) (@lem6190331 _123419 op x)). Qed.
Lemma lem6190334 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term553 _123419 op x) = (term496 _123419 op x).
Proof. exact (eq_refl (term553 _123419 op x)). Qed.
Lemma lem6190335 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term560 _123419 op x) = (term561 _123419 op x).
Proof. exact (MK_COMB (@lem6190333 _123419 op x) (@lem6190334 _123419 op x)). Qed.
Lemma lem6190336 {_123419 : Type'} (op : type1400 _123419) : (term562 _123419 op) = (term563 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6190335 _123419 op x)). Qed.
Lemma lem6190337 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190338 {_123419 : Type'} (op : type1400 _123419) : (term548 _123419 op) = (term564 _123419 op).
Proof. exact (MK_COMB (@lem6190337 _123419) (@lem6190336 _123419 op)). Qed.
Lemma lem6190339 {_123419 : Type'} (op : type1400 _123419) : ((term547 _123419 op) = (term548 _123419 op)) = ((term503 _123419 op) = (term564 _123419 op)).
Proof. exact (MK_COMB (@lem6190330 _123419 op) (@lem6190338 _123419 op)). Qed.
Lemma lem6190340 {_123419 : Type'} (op : type1400 _123419) : (term503 _123419 op) = (term564 _123419 op).
Proof. exact (EQ_MP (@lem6190339 _123419 op) (@lem6190317 _123419 op)). Qed.
Lemma lem6190342 {A : Type'} (P : A -> Prop) (Q : Prop) : (term565 A P Q) = (term566 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6190343 {_123419 : Type'} (P : _123419 -> Prop) (Q : Prop) : (term565 _123419 P Q) = (term566 _123419 P Q).
Proof. exact (@lem6190342 _123419 P Q). Qed.
Lemma lem6190344 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term567 _123419 op x) = (term568 _123419 op x).
Proof. exact (@lem6190343 _123419 (term483 _123419 op x) (term496 _123419 op x)). Qed.
Lemma lem6190345 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term569 _123419 op x y) = (term477 _123419 op x y).
Proof. exact (eq_refl (term569 _123419 op x y)). Qed.
Lemma lem6190346 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term570 _123419 op x) = (term483 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6190345 _123419 op x y)). Qed.
Lemma lem6190347 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190348 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term571 _123419 op x) = (term484 _123419 op x).
Proof. exact (MK_COMB (@lem6190347 _123419) (@lem6190346 _123419 op x)). Qed.
Lemma lem6190349 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6190350 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term572 _123419 op x) = (term559 _123419 op x).
Proof. exact (MK_COMB (@lem6190349) (@lem6190348 _123419 op x)). Qed.
Lemma lem6190351 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term496 _123419 op x) = (term496 _123419 op x).
Proof. exact (eq_refl (term496 _123419 op x)). Qed.
Lemma lem6190352 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term567 _123419 op x) = (term561 _123419 op x).
Proof. exact (MK_COMB (@lem6190350 _123419 op x) (@lem6190351 _123419 op x)). Qed.
Lemma lem6190353 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6190354 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term573 _123419 op x) = (term574 _123419 op x).
Proof. exact (MK_COMB (@lem6190353) (@lem6190352 _123419 op x)). Qed.
Lemma lem6190355 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term569 _123419 op x y) = (term477 _123419 op x y).
Proof. exact (eq_refl (term569 _123419 op x y)). Qed.
Lemma lem6190356 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6190357 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term575 _123419 op x y) = (term576 _123419 op x y).
Proof. exact (MK_COMB (@lem6190356) (@lem6190355 _123419 op x y)). Qed.
Lemma lem6190358 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term496 _123419 op x) = (term496 _123419 op x).
Proof. exact (eq_refl (term496 _123419 op x)). Qed.
Lemma lem6190359 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term577 _123419 y op x) = (term578 _123419 y op x).
Proof. exact (MK_COMB (@lem6190357 _123419 op x y) (@lem6190358 _123419 op x)). Qed.
Lemma lem6190360 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term579 _123419 op x) = (term580 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6190359 _123419 y op x)). Qed.
Lemma lem6190361 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190362 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term568 _123419 op x) = (term581 _123419 op x).
Proof. exact (MK_COMB (@lem6190361 _123419) (@lem6190360 _123419 op x)). Qed.
Lemma lem6190363 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : ((term567 _123419 op x) = (term568 _123419 op x)) = ((term561 _123419 op x) = (term581 _123419 op x)).
Proof. exact (MK_COMB (@lem6190354 _123419 op x) (@lem6190362 _123419 op x)). Qed.
Lemma lem6190364 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term561 _123419 op x) = (term581 _123419 op x).
Proof. exact (EQ_MP (@lem6190363 _123419 op x) (@lem6190344 _123419 op x)). Qed.
Lemma lem6190366 {A : Type'} (P : A -> Prop) (Q : Prop) : (term565 A P Q) = (term566 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6190367 {_123419 : Type'} (P : _123419 -> Prop) (Q : Prop) : (term565 _123419 P Q) = (term566 _123419 P Q).
Proof. exact (@lem6190366 _123419 P Q). Qed.
Lemma lem6190368 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term582 _123419 y op x) = (term583 _123419 y op x).
Proof. exact (@lem6190367 _123419 (term476 _123419 op x y) (term496 _123419 op x)). Qed.
Lemma lem6190369 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : (term584 _123419 op x y z) = (term474 _123419 op x y z).
Proof. exact (eq_refl (term584 _123419 op x y z)). Qed.
Lemma lem6190370 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term585 _123419 op x y) = (term476 _123419 op x y).
Proof. exact (fun_ext (fun z : _123419 => @lem6190369 _123419 op x y z)). Qed.
Lemma lem6190371 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190372 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term586 _123419 op x y) = (term477 _123419 op x y).
Proof. exact (MK_COMB (@lem6190371 _123419) (@lem6190370 _123419 op x y)). Qed.
Lemma lem6190373 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6190374 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term587 _123419 op x y) = (term576 _123419 op x y).
Proof. exact (MK_COMB (@lem6190373) (@lem6190372 _123419 op x y)). Qed.
Lemma lem6190375 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term496 _123419 op x) = (term496 _123419 op x).
Proof. exact (eq_refl (term496 _123419 op x)). Qed.
Lemma lem6190376 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term582 _123419 y op x) = (term578 _123419 y op x).
Proof. exact (MK_COMB (@lem6190374 _123419 op x y) (@lem6190375 _123419 op x)). Qed.
Lemma lem6190377 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6190378 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term588 _123419 y op x) = (term589 _123419 y op x).
Proof. exact (MK_COMB (@lem6190377) (@lem6190376 _123419 y op x)). Qed.
Lemma lem6190379 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : (term584 _123419 op x y z) = (term474 _123419 op x y z).
Proof. exact (eq_refl (term584 _123419 op x y z)). Qed.
Lemma lem6190380 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6190381 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : (term590 _123419 op x y z) = (term591 _123419 op x y z).
Proof. exact (MK_COMB (@lem6190380) (@lem6190379 _123419 op x y z)). Qed.
Lemma lem6190382 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term496 _123419 op x) = (term496 _123419 op x).
Proof. exact (eq_refl (term496 _123419 op x)). Qed.
Lemma lem6190383 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term592 _123419 y z op x) = (term593 _123419 y z op x).
Proof. exact (MK_COMB (@lem6190381 _123419 op x y z) (@lem6190382 _123419 op x)). Qed.
Lemma lem6190384 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term594 _123419 y op x) = (term595 _123419 y op x).
Proof. exact (fun_ext (fun z : _123419 => @lem6190383 _123419 y z op x)). Qed.
Lemma lem6190385 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190386 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term583 _123419 y op x) = (term596 _123419 y op x).
Proof. exact (MK_COMB (@lem6190385 _123419) (@lem6190384 _123419 y op x)). Qed.
Lemma lem6190387 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : ((term582 _123419 y op x) = (term583 _123419 y op x)) = ((term578 _123419 y op x) = (term596 _123419 y op x)).
Proof. exact (MK_COMB (@lem6190378 _123419 y op x) (@lem6190386 _123419 y op x)). Qed.
Lemma lem6190388 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term578 _123419 y op x) = (term596 _123419 y op x).
Proof. exact (EQ_MP (@lem6190387 _123419 y op x) (@lem6190368 _123419 y op x)). Qed.
Lemma lem6190389 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term580 _123419 op x) = (term597 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6190388 _123419 y op x)). Qed.
Lemma lem6190390 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190391 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term581 _123419 op x) = (term598 _123419 op x).
Proof. exact (MK_COMB (@lem6190390 _123419) (@lem6190389 _123419 op x)). Qed.
Lemma lem6190392 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term561 _123419 op x) = (term598 _123419 op x).
Proof. exact (TRANS (@lem6190364 _123419 op x) (@lem6190391 _123419 op x)). Qed.
Lemma lem6190393 {_123419 : Type'} (op : type1400 _123419) : (term563 _123419 op) = (term599 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6190392 _123419 op x)). Qed.
Lemma lem6190394 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190395 {_123419 : Type'} (op : type1400 _123419) : (term564 _123419 op) = (term600 _123419 op).
Proof. exact (MK_COMB (@lem6190394 _123419) (@lem6190393 _123419 op)). Qed.
Lemma lem6190396 {_123419 : Type'} (op : type1400 _123419) : (term503 _123419 op) = (term600 _123419 op).
Proof. exact (TRANS (@lem6190340 _123419 op) (@lem6190395 _123419 op)). Qed.
Lemma lem6190397 {_123419 : Type'} (op : type1400 _123419) : (term506 _123419 op) = (term506 _123419 op).
Proof. exact (eq_refl (term506 _123419 op)). Qed.
Lemma lem6190398 {_123419 : Type'} (op : type1400 _123419) : (term508 _123419 op) = (term601 _123419 op).
Proof. exact (MK_COMB (@lem6190397 _123419 op) (@lem6190396 _123419 op)). Qed.
Lemma lem6190400 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term545 A P Q) = (term546 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6190401 {_123419 : Type'} (P : _123419 -> Prop) (Q : _123419 -> Prop) : (term545 _123419 P Q) = (term546 _123419 P Q).
Proof. exact (@lem6190400 _123419 P Q). Qed.
Lemma lem6190402 {_123419 : Type'} (op : type1400 _123419) : (term602 _123419 op) = (term603 _123419 op).
Proof. exact (@lem6190401 _123419 (term468 _123419 op) (term599 _123419 op)). Qed.
Lemma lem6190403 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term604 _123419 op x) = (term462 _123419 op x).
Proof. exact (eq_refl (term604 _123419 op x)). Qed.
Lemma lem6190404 {_123419 : Type'} (op : type1400 _123419) : (term605 _123419 op) = (term468 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6190403 _123419 op x)). Qed.
Lemma lem6190405 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190406 {_123419 : Type'} (op : type1400 _123419) : (term606 _123419 op) = (term469 _123419 op).
Proof. exact (MK_COMB (@lem6190405 _123419) (@lem6190404 _123419 op)). Qed.
Lemma lem6190407 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6190408 {_123419 : Type'} (op : type1400 _123419) : (term607 _123419 op) = (term506 _123419 op).
Proof. exact (MK_COMB (@lem6190407) (@lem6190406 _123419 op)). Qed.
Lemma lem6190409 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term608 _123419 op x) = (term598 _123419 op x).
Proof. exact (eq_refl (term608 _123419 op x)). Qed.
Lemma lem6190410 {_123419 : Type'} (op : type1400 _123419) : (term609 _123419 op) = (term599 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6190409 _123419 op x)). Qed.
Lemma lem6190411 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190412 {_123419 : Type'} (op : type1400 _123419) : (term610 _123419 op) = (term600 _123419 op).
Proof. exact (MK_COMB (@lem6190411 _123419) (@lem6190410 _123419 op)). Qed.
Lemma lem6190413 {_123419 : Type'} (op : type1400 _123419) : (term602 _123419 op) = (term601 _123419 op).
Proof. exact (MK_COMB (@lem6190408 _123419 op) (@lem6190412 _123419 op)). Qed.
Lemma lem6190414 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6190415 {_123419 : Type'} (op : type1400 _123419) : (term611 _123419 op) = (term612 _123419 op).
Proof. exact (MK_COMB (@lem6190414) (@lem6190413 _123419 op)). Qed.
Lemma lem6190416 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term604 _123419 op x) = (term462 _123419 op x).
Proof. exact (eq_refl (term604 _123419 op x)). Qed.
Lemma lem6190417 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6190418 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term613 _123419 op x) = (term614 _123419 op x).
Proof. exact (MK_COMB (@lem6190417) (@lem6190416 _123419 op x)). Qed.
Lemma lem6190419 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term608 _123419 op x) = (term598 _123419 op x).
Proof. exact (eq_refl (term608 _123419 op x)). Qed.
Lemma lem6190420 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term615 _123419 op x) = (term616 _123419 op x).
Proof. exact (MK_COMB (@lem6190418 _123419 op x) (@lem6190419 _123419 op x)). Qed.
Lemma lem6190421 {_123419 : Type'} (op : type1400 _123419) : (term617 _123419 op) = (term618 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6190420 _123419 op x)). Qed.
Lemma lem6190422 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190423 {_123419 : Type'} (op : type1400 _123419) : (term603 _123419 op) = (term619 _123419 op).
Proof. exact (MK_COMB (@lem6190422 _123419) (@lem6190421 _123419 op)). Qed.
Lemma lem6190424 {_123419 : Type'} (op : type1400 _123419) : ((term602 _123419 op) = (term603 _123419 op)) = ((term601 _123419 op) = (term619 _123419 op)).
Proof. exact (MK_COMB (@lem6190415 _123419 op) (@lem6190423 _123419 op)). Qed.
Lemma lem6190425 {_123419 : Type'} (op : type1400 _123419) : (term601 _123419 op) = (term619 _123419 op).
Proof. exact (EQ_MP (@lem6190424 _123419 op) (@lem6190402 _123419 op)). Qed.
Lemma lem6190427 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term545 A P Q) = (term546 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6190428 {_123419 : Type'} (P : _123419 -> Prop) (Q : _123419 -> Prop) : (term545 _123419 P Q) = (term546 _123419 P Q).
Proof. exact (@lem6190427 _123419 P Q). Qed.
Lemma lem6190429 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term620 _123419 op x) = (term621 _123419 op x).
Proof. exact (@lem6190428 _123419 (term461 _123419 op x) (term597 _123419 op x)). Qed.
Lemma lem6190430 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (term622 _123419 op x y) = (term459 _123419 op y x).
Proof. exact (eq_refl (term622 _123419 op x y)). Qed.
Lemma lem6190431 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term623 _123419 op x) = (term461 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6190430 _123419 op y x)). Qed.
Lemma lem6190432 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190433 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term624 _123419 op x) = (term462 _123419 op x).
Proof. exact (MK_COMB (@lem6190432 _123419) (@lem6190431 _123419 op x)). Qed.
Lemma lem6190434 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6190435 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term625 _123419 op x) = (term614 _123419 op x).
Proof. exact (MK_COMB (@lem6190434) (@lem6190433 _123419 op x)). Qed.
Lemma lem6190436 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term626 _123419 op x y) = (term596 _123419 y op x).
Proof. exact (eq_refl (term626 _123419 op x y)). Qed.
Lemma lem6190437 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term627 _123419 op x) = (term597 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6190436 _123419 y op x)). Qed.
Lemma lem6190438 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190439 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term628 _123419 op x) = (term598 _123419 op x).
Proof. exact (MK_COMB (@lem6190438 _123419) (@lem6190437 _123419 op x)). Qed.
Lemma lem6190440 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term620 _123419 op x) = (term616 _123419 op x).
Proof. exact (MK_COMB (@lem6190435 _123419 op x) (@lem6190439 _123419 op x)). Qed.
Lemma lem6190441 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6190442 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term629 _123419 op x) = (term630 _123419 op x).
Proof. exact (MK_COMB (@lem6190441) (@lem6190440 _123419 op x)). Qed.
Lemma lem6190443 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (term622 _123419 op x y) = (term459 _123419 op y x).
Proof. exact (eq_refl (term622 _123419 op x y)). Qed.
Lemma lem6190444 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6190445 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (term631 _123419 op x y) = (term632 _123419 op y x).
Proof. exact (MK_COMB (@lem6190444) (@lem6190443 _123419 op y x)). Qed.
Lemma lem6190446 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term626 _123419 op x y) = (term596 _123419 y op x).
Proof. exact (eq_refl (term626 _123419 op x y)). Qed.
Lemma lem6190447 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term633 _123419 op x y) = (term634 _123419 y op x).
Proof. exact (MK_COMB (@lem6190445 _123419 op y x) (@lem6190446 _123419 y op x)). Qed.
Lemma lem6190448 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term635 _123419 op x) = (term636 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6190447 _123419 y op x)). Qed.
Lemma lem6190449 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190450 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term621 _123419 op x) = (term637 _123419 op x).
Proof. exact (MK_COMB (@lem6190449 _123419) (@lem6190448 _123419 op x)). Qed.
Lemma lem6190451 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : ((term620 _123419 op x) = (term621 _123419 op x)) = ((term616 _123419 op x) = (term637 _123419 op x)).
Proof. exact (MK_COMB (@lem6190442 _123419 op x) (@lem6190450 _123419 op x)). Qed.
Lemma lem6190452 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term616 _123419 op x) = (term637 _123419 op x).
Proof. exact (EQ_MP (@lem6190451 _123419 op x) (@lem6190429 _123419 op x)). Qed.
Lemma lem6190454 {A : Type'} (P : Prop) (Q : A -> Prop) : (term638 A P Q) = (term639 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6190455 {_123419 : Type'} (P : Prop) (Q : _123419 -> Prop) : (term638 _123419 P Q) = (term639 _123419 P Q).
Proof. exact (@lem6190454 _123419 P Q). Qed.
Lemma lem6190456 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term640 _123419 y op x) = (term641 _123419 y op x).
Proof. exact (@lem6190455 _123419 (term459 _123419 op y x) (term595 _123419 y op x)). Qed.
Lemma lem6190457 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term642 _123419 y op x z) = (term593 _123419 y z op x).
Proof. exact (eq_refl (term642 _123419 y op x z)). Qed.
Lemma lem6190458 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term643 _123419 y op x) = (term595 _123419 y op x).
Proof. exact (fun_ext (fun z : _123419 => @lem6190457 _123419 y z op x)). Qed.
Lemma lem6190459 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190460 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term644 _123419 y op x) = (term596 _123419 y op x).
Proof. exact (MK_COMB (@lem6190459 _123419) (@lem6190458 _123419 y op x)). Qed.
Lemma lem6190461 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (term632 _123419 op y x) = (term632 _123419 op y x).
Proof. exact (eq_refl (term632 _123419 op y x)). Qed.
Lemma lem6190462 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term640 _123419 y op x) = (term634 _123419 y op x).
Proof. exact (MK_COMB (@lem6190461 _123419 op y x) (@lem6190460 _123419 y op x)). Qed.
Lemma lem6190463 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6190464 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term645 _123419 y op x) = (term646 _123419 y op x).
Proof. exact (MK_COMB (@lem6190463) (@lem6190462 _123419 y op x)). Qed.
Lemma lem6190465 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term642 _123419 y op x z) = (term593 _123419 y z op x).
Proof. exact (eq_refl (term642 _123419 y op x z)). Qed.
Lemma lem6190466 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (term632 _123419 op y x) = (term632 _123419 op y x).
Proof. exact (eq_refl (term632 _123419 op y x)). Qed.
Lemma lem6190467 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term647 _123419 y op x z) = (term648 _123419 y z op x).
Proof. exact (MK_COMB (@lem6190466 _123419 op y x) (@lem6190465 _123419 y z op x)). Qed.
Lemma lem6190468 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term649 _123419 y op x) = (term650 _123419 y op x).
Proof. exact (fun_ext (fun z : _123419 => @lem6190467 _123419 y z op x)). Qed.
Lemma lem6190469 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190470 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term641 _123419 y op x) = (term651 _123419 y op x).
Proof. exact (MK_COMB (@lem6190469 _123419) (@lem6190468 _123419 y op x)). Qed.
Lemma lem6190471 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : ((term640 _123419 y op x) = (term641 _123419 y op x)) = ((term634 _123419 y op x) = (term651 _123419 y op x)).
Proof. exact (MK_COMB (@lem6190464 _123419 y op x) (@lem6190470 _123419 y op x)). Qed.
Lemma lem6190472 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term634 _123419 y op x) = (term651 _123419 y op x).
Proof. exact (EQ_MP (@lem6190471 _123419 y op x) (@lem6190456 _123419 y op x)). Qed.
Lemma lem6190473 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term636 _123419 op x) = (term652 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6190472 _123419 y op x)). Qed.
Lemma lem6190474 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190475 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term637 _123419 op x) = (term653 _123419 op x).
Proof. exact (MK_COMB (@lem6190474 _123419) (@lem6190473 _123419 op x)). Qed.
Lemma lem6190476 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term616 _123419 op x) = (term653 _123419 op x).
Proof. exact (TRANS (@lem6190452 _123419 op x) (@lem6190475 _123419 op x)). Qed.
Lemma lem6190477 {_123419 : Type'} (op : type1400 _123419) : (term618 _123419 op) = (term654 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6190476 _123419 op x)). Qed.
Lemma lem6190478 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190479 {_123419 : Type'} (op : type1400 _123419) : (term619 _123419 op) = (term655 _123419 op).
Proof. exact (MK_COMB (@lem6190478 _123419) (@lem6190477 _123419 op)). Qed.
Lemma lem6190480 {_123419 : Type'} (op : type1400 _123419) : (term601 _123419 op) = (term655 _123419 op).
Proof. exact (TRANS (@lem6190425 _123419 op) (@lem6190479 _123419 op)). Qed.
Lemma lem6190481 {_123419 : Type'} (op : type1400 _123419) : (term508 _123419 op) = (term655 _123419 op).
Proof. exact (TRANS (@lem6190398 _123419 op) (@lem6190480 _123419 op)). Qed.
Lemma lem6190482 {_123419 : Type'} (op : type1400 _123419) : (term512 _123419 op) = (term512 _123419 op).
Proof. exact (eq_refl (term512 _123419 op)). Qed.
Lemma lem6190483 {_123419 : Type'} (op : type1400 _123419) : (term514 _123419 op) = (term656 _123419 op).
Proof. exact (MK_COMB (@lem6190482 _123419 op) (@lem6190481 _123419 op)). Qed.
Lemma lem6190485 {A : Type'} (P : Prop) (Q : A -> Prop) : (term638 A P Q) = (term639 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6190486 {_123419 : Type'} (P : Prop) (Q : _123419 -> Prop) : (term638 _123419 P Q) = (term639 _123419 P Q).
Proof. exact (@lem6190485 _123419 P Q). Qed.
Lemma lem6190487 {_123419 : Type'} (op : type1400 _123419) : (term657 _123419 op) = (term658 _123419 op).
Proof. exact (@lem6190486 _123419 (@monoidal _123419 op) (term654 _123419 op)). Qed.
Lemma lem6190488 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term659 _123419 op x) = (term653 _123419 op x).
Proof. exact (eq_refl (term659 _123419 op x)). Qed.
Lemma lem6190489 {_123419 : Type'} (op : type1400 _123419) : (term660 _123419 op) = (term654 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6190488 _123419 op x)). Qed.
Lemma lem6190490 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190491 {_123419 : Type'} (op : type1400 _123419) : (term661 _123419 op) = (term655 _123419 op).
Proof. exact (MK_COMB (@lem6190490 _123419) (@lem6190489 _123419 op)). Qed.
Lemma lem6190492 {_123419 : Type'} (op : type1400 _123419) : (term512 _123419 op) = (term512 _123419 op).
Proof. exact (eq_refl (term512 _123419 op)). Qed.
Lemma lem6190493 {_123419 : Type'} (op : type1400 _123419) : (term657 _123419 op) = (term656 _123419 op).
Proof. exact (MK_COMB (@lem6190492 _123419 op) (@lem6190491 _123419 op)). Qed.
Lemma lem6190494 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6190495 {_123419 : Type'} (op : type1400 _123419) : (term662 _123419 op) = (term663 _123419 op).
Proof. exact (MK_COMB (@lem6190494) (@lem6190493 _123419 op)). Qed.
Lemma lem6190496 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term659 _123419 op x) = (term653 _123419 op x).
Proof. exact (eq_refl (term659 _123419 op x)). Qed.
Lemma lem6190497 {_123419 : Type'} (op : type1400 _123419) : (term512 _123419 op) = (term512 _123419 op).
Proof. exact (eq_refl (term512 _123419 op)). Qed.
Lemma lem6190498 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term664 _123419 op x) = (term665 _123419 op x).
Proof. exact (MK_COMB (@lem6190497 _123419 op) (@lem6190496 _123419 op x)). Qed.
Lemma lem6190499 {_123419 : Type'} (op : type1400 _123419) : (term666 _123419 op) = (term667 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6190498 _123419 op x)). Qed.
Lemma lem6190500 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190501 {_123419 : Type'} (op : type1400 _123419) : (term658 _123419 op) = (term668 _123419 op).
Proof. exact (MK_COMB (@lem6190500 _123419) (@lem6190499 _123419 op)). Qed.
Lemma lem6190502 {_123419 : Type'} (op : type1400 _123419) : ((term657 _123419 op) = (term658 _123419 op)) = ((term656 _123419 op) = (term668 _123419 op)).
Proof. exact (MK_COMB (@lem6190495 _123419 op) (@lem6190501 _123419 op)). Qed.
Lemma lem6190503 {_123419 : Type'} (op : type1400 _123419) : (term656 _123419 op) = (term668 _123419 op).
Proof. exact (EQ_MP (@lem6190502 _123419 op) (@lem6190487 _123419 op)). Qed.
Lemma lem6190505 {A : Type'} (P : Prop) (Q : A -> Prop) : (term638 A P Q) = (term639 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6190506 {_123419 : Type'} (P : Prop) (Q : _123419 -> Prop) : (term638 _123419 P Q) = (term639 _123419 P Q).
Proof. exact (@lem6190505 _123419 P Q). Qed.
Lemma lem6190507 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term669 _123419 op x) = (term670 _123419 op x).
Proof. exact (@lem6190506 _123419 (@monoidal _123419 op) (term652 _123419 op x)). Qed.
Lemma lem6190508 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term671 _123419 op x y) = (term651 _123419 y op x).
Proof. exact (eq_refl (term671 _123419 op x y)). Qed.
Lemma lem6190509 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term672 _123419 op x) = (term652 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6190508 _123419 y op x)). Qed.
Lemma lem6190510 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190511 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term673 _123419 op x) = (term653 _123419 op x).
Proof. exact (MK_COMB (@lem6190510 _123419) (@lem6190509 _123419 op x)). Qed.
Lemma lem6190512 {_123419 : Type'} (op : type1400 _123419) : (term512 _123419 op) = (term512 _123419 op).
Proof. exact (eq_refl (term512 _123419 op)). Qed.
Lemma lem6190513 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term669 _123419 op x) = (term665 _123419 op x).
Proof. exact (MK_COMB (@lem6190512 _123419 op) (@lem6190511 _123419 op x)). Qed.
Lemma lem6190514 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6190515 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term674 _123419 op x) = (term675 _123419 op x).
Proof. exact (MK_COMB (@lem6190514) (@lem6190513 _123419 op x)). Qed.
Lemma lem6190516 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term671 _123419 op x y) = (term651 _123419 y op x).
Proof. exact (eq_refl (term671 _123419 op x y)). Qed.
Lemma lem6190517 {_123419 : Type'} (op : type1400 _123419) : (term512 _123419 op) = (term512 _123419 op).
Proof. exact (eq_refl (term512 _123419 op)). Qed.
Lemma lem6190518 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term676 _123419 op x y) = (term677 _123419 y op x).
Proof. exact (MK_COMB (@lem6190517 _123419 op) (@lem6190516 _123419 y op x)). Qed.
Lemma lem6190519 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term678 _123419 op x) = (term679 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6190518 _123419 y op x)). Qed.
Lemma lem6190520 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190521 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term670 _123419 op x) = (term680 _123419 op x).
Proof. exact (MK_COMB (@lem6190520 _123419) (@lem6190519 _123419 op x)). Qed.
Lemma lem6190522 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : ((term669 _123419 op x) = (term670 _123419 op x)) = ((term665 _123419 op x) = (term680 _123419 op x)).
Proof. exact (MK_COMB (@lem6190515 _123419 op x) (@lem6190521 _123419 op x)). Qed.
Lemma lem6190523 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term665 _123419 op x) = (term680 _123419 op x).
Proof. exact (EQ_MP (@lem6190522 _123419 op x) (@lem6190507 _123419 op x)). Qed.
Lemma lem6190525 {A : Type'} (P : Prop) (Q : A -> Prop) : (term638 A P Q) = (term639 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6190526 {_123419 : Type'} (P : Prop) (Q : _123419 -> Prop) : (term638 _123419 P Q) = (term639 _123419 P Q).
Proof. exact (@lem6190525 _123419 P Q). Qed.
Lemma lem6190527 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term681 _123419 y op x) = (term682 _123419 y op x).
Proof. exact (@lem6190526 _123419 (@monoidal _123419 op) (term650 _123419 y op x)). Qed.
Lemma lem6190528 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term683 _123419 y op x z) = (term648 _123419 y z op x).
Proof. exact (eq_refl (term683 _123419 y op x z)). Qed.
Lemma lem6190529 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term684 _123419 y op x) = (term650 _123419 y op x).
Proof. exact (fun_ext (fun z : _123419 => @lem6190528 _123419 y z op x)). Qed.
Lemma lem6190530 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190531 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term685 _123419 y op x) = (term651 _123419 y op x).
Proof. exact (MK_COMB (@lem6190530 _123419) (@lem6190529 _123419 y op x)). Qed.
Lemma lem6190532 {_123419 : Type'} (op : type1400 _123419) : (term512 _123419 op) = (term512 _123419 op).
Proof. exact (eq_refl (term512 _123419 op)). Qed.
Lemma lem6190533 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term681 _123419 y op x) = (term677 _123419 y op x).
Proof. exact (MK_COMB (@lem6190532 _123419 op) (@lem6190531 _123419 y op x)). Qed.
Lemma lem6190534 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6190535 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term686 _123419 y op x) = (term687 _123419 y op x).
Proof. exact (MK_COMB (@lem6190534) (@lem6190533 _123419 y op x)). Qed.
Lemma lem6190536 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term683 _123419 y op x z) = (term648 _123419 y z op x).
Proof. exact (eq_refl (term683 _123419 y op x z)). Qed.
Lemma lem6190537 {_123419 : Type'} (op : type1400 _123419) : (term512 _123419 op) = (term512 _123419 op).
Proof. exact (eq_refl (term512 _123419 op)). Qed.
Lemma lem6190538 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term688 _123419 y op x z) = (term689 _123419 y z op x).
Proof. exact (MK_COMB (@lem6190537 _123419 op) (@lem6190536 _123419 y z op x)). Qed.
Lemma lem6190539 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term690 _123419 y op x) = (term691 _123419 y op x).
Proof. exact (fun_ext (fun z : _123419 => @lem6190538 _123419 y z op x)). Qed.
Lemma lem6190540 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190541 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term682 _123419 y op x) = (term692 _123419 y op x).
Proof. exact (MK_COMB (@lem6190540 _123419) (@lem6190539 _123419 y op x)). Qed.
Lemma lem6190542 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : ((term681 _123419 y op x) = (term682 _123419 y op x)) = ((term677 _123419 y op x) = (term692 _123419 y op x)).
Proof. exact (MK_COMB (@lem6190535 _123419 y op x) (@lem6190541 _123419 y op x)). Qed.
Lemma lem6190543 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term677 _123419 y op x) = (term692 _123419 y op x).
Proof. exact (EQ_MP (@lem6190542 _123419 y op x) (@lem6190527 _123419 y op x)). Qed.
Lemma lem6190544 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term679 _123419 op x) = (term693 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6190543 _123419 y op x)). Qed.
Lemma lem6190545 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190546 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term680 _123419 op x) = (term694 _123419 op x).
Proof. exact (MK_COMB (@lem6190545 _123419) (@lem6190544 _123419 op x)). Qed.
Lemma lem6190547 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term665 _123419 op x) = (term694 _123419 op x).
Proof. exact (TRANS (@lem6190523 _123419 op x) (@lem6190546 _123419 op x)). Qed.
Lemma lem6190548 {_123419 : Type'} (op : type1400 _123419) : (term667 _123419 op) = (term695 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6190547 _123419 op x)). Qed.
Lemma lem6190549 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190550 {_123419 : Type'} (op : type1400 _123419) : (term668 _123419 op) = (term696 _123419 op).
Proof. exact (MK_COMB (@lem6190549 _123419) (@lem6190548 _123419 op)). Qed.
Lemma lem6190551 {_123419 : Type'} (op : type1400 _123419) : (term656 _123419 op) = (term696 _123419 op).
Proof. exact (TRANS (@lem6190503 _123419 op) (@lem6190550 _123419 op)). Qed.
Lemma lem6190552 {_123419 : Type'} (op : type1400 _123419) : (term514 _123419 op) = (term696 _123419 op).
Proof. exact (TRANS (@lem6190483 _123419 op) (@lem6190551 _123419 op)). Qed.
Lemma lem6190553 {_123419 : Type'} : (term527 _123419) = (term697 _123419).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6190552 _123419 op)). Qed.
Lemma lem6190554 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6190555 {_123419 : Type'} : (term538 _123419) = (term698 _123419).
Proof. exact (MK_COMB (@lem6190554 _123419) (@lem6190553 _123419)). Qed.
Lemma lem6190557 {A B : Type'} (P : type1413 A B) : (term699 A B P) = (term700 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6190558 {_123419 : Type'} (P : type401 _123419) : (term701 _123419 P) = (term702 _123419 P).
Proof. exact (@lem6190557 (type1400 _123419) _123419 P). Qed.
Lemma lem6190559 {_123419 : Type'} : (term703 _123419) = (term704 _123419).
Proof. exact (@lem6190558 _123419 (term705 _123419)). Qed.
Lemma lem6190560 {_123419 : Type'} (op : type1400 _123419) : (term706 _123419 op) = (term695 _123419 op).
Proof. exact (eq_refl (term706 _123419 op)). Qed.
Lemma lem6190561 {_123419 : Type'} (x : _123419) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6190562 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term707 _123419 op x) = (term708 _123419 op x).
Proof. exact (MK_COMB (@lem6190560 _123419 op) (@lem6190561 _123419 x)). Qed.
Lemma lem6190563 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term708 _123419 op x) = (term694 _123419 op x).
Proof. exact (eq_refl (term708 _123419 op x)). Qed.
Lemma lem6190564 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term707 _123419 op x) = (term694 _123419 op x).
Proof. exact (TRANS (@lem6190562 _123419 op x) (@lem6190563 _123419 op x)). Qed.
Lemma lem6190565 {_123419 : Type'} (op : type1400 _123419) : (term709 _123419 op) = (term695 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6190564 _123419 op x)). Qed.
Lemma lem6190566 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190567 {_123419 : Type'} (op : type1400 _123419) : (term710 _123419 op) = (term696 _123419 op).
Proof. exact (MK_COMB (@lem6190566 _123419) (@lem6190565 _123419 op)). Qed.
Lemma lem6190568 {_123419 : Type'} : (term711 _123419) = (term697 _123419).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6190567 _123419 op)). Qed.
Lemma lem6190569 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6190570 {_123419 : Type'} : (term703 _123419) = (term698 _123419).
Proof. exact (MK_COMB (@lem6190569 _123419) (@lem6190568 _123419)). Qed.
Lemma lem6190571 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6190572 {_123419 : Type'} : (term712 _123419) = (term713 _123419).
Proof. exact (MK_COMB (@lem6190571) (@lem6190570 _123419)). Qed.
Lemma lem6190573 {_123419 : Type'} (op : type1400 _123419) : (term706 _123419 op) = (term695 _123419 op).
Proof. exact (eq_refl (term706 _123419 op)). Qed.
Lemma lem6190574 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (x op) = (x op).
Proof. exact (eq_refl (x op)). Qed.
Lemma lem6190575 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (term714 _123419 x op) = (term715 _123419 x op).
Proof. exact (MK_COMB (@lem6190573 _123419 op) (@lem6190574 _123419 x op)). Qed.
Lemma lem6190576 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (term715 _123419 x op) = (term716 _123419 x op).
Proof. exact (eq_refl (term715 _123419 x op)). Qed.
Lemma lem6190577 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (term714 _123419 x op) = (term716 _123419 x op).
Proof. exact (TRANS (@lem6190575 _123419 x op) (@lem6190576 _123419 x op)). Qed.
Lemma lem6190578 {_123419 : Type'} (x : type402 _123419) : (term717 _123419 x) = (term718 _123419 x).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6190577 _123419 x op)). Qed.
Lemma lem6190579 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6190580 {_123419 : Type'} (x : type402 _123419) : (term719 _123419 x) = (term720 _123419 x).
Proof. exact (MK_COMB (@lem6190579 _123419) (@lem6190578 _123419 x)). Qed.
Lemma lem6190581 {_123419 : Type'} : (term721 _123419) = (term722 _123419).
Proof. exact (fun_ext (fun x : type402 _123419 => @lem6190580 _123419 x)). Qed.
Lemma lem6190582 {_123419 : Type'} : (@ex ((_123419 -> _123419 -> _123419) -> _123419)) = (@ex ((_123419 -> _123419 -> _123419) -> _123419)).
Proof. exact (eq_refl (@ex ((_123419 -> _123419 -> _123419) -> _123419))). Qed.
Lemma lem6190583 {_123419 : Type'} : (term704 _123419) = (term723 _123419).
Proof. exact (MK_COMB (@lem6190582 _123419) (@lem6190581 _123419)). Qed.
Lemma lem6190584 {_123419 : Type'} : ((term703 _123419) = (term704 _123419)) = ((term698 _123419) = (term723 _123419)).
Proof. exact (MK_COMB (@lem6190572 _123419) (@lem6190583 _123419)). Qed.
Lemma lem6190585 {_123419 : Type'} : (term698 _123419) = (term723 _123419).
Proof. exact (EQ_MP (@lem6190584 _123419) (@lem6190559 _123419)). Qed.
Lemma lem6190587 {A B : Type'} (P : type1413 A B) : (term699 A B P) = (term700 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6190588 {_123419 : Type'} (P : type401 _123419) : (term701 _123419 P) = (term702 _123419 P).
Proof. exact (@lem6190587 (type1400 _123419) _123419 P). Qed.
Lemma lem6190589 {_123419 : Type'} (x : type402 _123419) : (term724 _123419 x) = (term725 _123419 x).
Proof. exact (@lem6190588 _123419 (term726 _123419 x)). Qed.
Lemma lem6190590 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (term727 _123419 x op) = (term728 _123419 x op).
Proof. exact (eq_refl (term727 _123419 x op)). Qed.
Lemma lem6190591 {_123419 : Type'} (y : _123419) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6190592 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) (y : _123419) : (term729 _123419 x op y) = (term730 _123419 x op y).
Proof. exact (MK_COMB (@lem6190590 _123419 x op) (@lem6190591 _123419 y)). Qed.
Lemma lem6190593 {_123419 : Type'} (y : _123419) (x : type402 _123419) (op : type1400 _123419) : (term730 _123419 x op y) = (term731 _123419 y x op).
Proof. exact (eq_refl (term730 _123419 x op y)). Qed.
Lemma lem6190594 {_123419 : Type'} (y : _123419) (x : type402 _123419) (op : type1400 _123419) : (term729 _123419 x op y) = (term731 _123419 y x op).
Proof. exact (TRANS (@lem6190592 _123419 x op y) (@lem6190593 _123419 y x op)). Qed.
Lemma lem6190595 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (term732 _123419 x op) = (term728 _123419 x op).
Proof. exact (fun_ext (fun y : _123419 => @lem6190594 _123419 y x op)). Qed.
Lemma lem6190596 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190597 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (term733 _123419 x op) = (term716 _123419 x op).
Proof. exact (MK_COMB (@lem6190596 _123419) (@lem6190595 _123419 x op)). Qed.
Lemma lem6190598 {_123419 : Type'} (x : type402 _123419) : (term734 _123419 x) = (term718 _123419 x).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6190597 _123419 x op)). Qed.
Lemma lem6190599 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6190600 {_123419 : Type'} (x : type402 _123419) : (term724 _123419 x) = (term720 _123419 x).
Proof. exact (MK_COMB (@lem6190599 _123419) (@lem6190598 _123419 x)). Qed.
Lemma lem6190601 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6190602 {_123419 : Type'} (x : type402 _123419) : (term735 _123419 x) = (term736 _123419 x).
Proof. exact (MK_COMB (@lem6190601) (@lem6190600 _123419 x)). Qed.
Lemma lem6190603 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (term727 _123419 x op) = (term728 _123419 x op).
Proof. exact (eq_refl (term727 _123419 x op)). Qed.
Lemma lem6190604 {_123419 : Type'} (y : type402 _123419) (op : type1400 _123419) : (y op) = (y op).
Proof. exact (eq_refl (y op)). Qed.
Lemma lem6190605 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (op : type1400 _123419) : (term737 _123419 x y op) = (term738 _123419 x y op).
Proof. exact (MK_COMB (@lem6190603 _123419 x op) (@lem6190604 _123419 y op)). Qed.
Lemma lem6190606 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) (op : type1400 _123419) : (term738 _123419 x y op) = (term739 _123419 y x op).
Proof. exact (eq_refl (term738 _123419 x y op)). Qed.
Lemma lem6190607 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) (op : type1400 _123419) : (term737 _123419 x y op) = (term739 _123419 y x op).
Proof. exact (TRANS (@lem6190605 _123419 x y op) (@lem6190606 _123419 y x op)). Qed.
Lemma lem6190608 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term740 _123419 x y) = (term741 _123419 y x).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6190607 _123419 y x op)). Qed.
Lemma lem6190609 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6190610 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term742 _123419 x y) = (term743 _123419 y x).
Proof. exact (MK_COMB (@lem6190609 _123419) (@lem6190608 _123419 y x)). Qed.
Lemma lem6190611 {_123419 : Type'} (x : type402 _123419) : (term744 _123419 x) = (term745 _123419 x).
Proof. exact (fun_ext (fun y : type402 _123419 => @lem6190610 _123419 y x)). Qed.
Lemma lem6190612 {_123419 : Type'} : (@ex ((_123419 -> _123419 -> _123419) -> _123419)) = (@ex ((_123419 -> _123419 -> _123419) -> _123419)).
Proof. exact (eq_refl (@ex ((_123419 -> _123419 -> _123419) -> _123419))). Qed.
Lemma lem6190613 {_123419 : Type'} (x : type402 _123419) : (term725 _123419 x) = (term746 _123419 x).
Proof. exact (MK_COMB (@lem6190612 _123419) (@lem6190611 _123419 x)). Qed.
Lemma lem6190614 {_123419 : Type'} (x : type402 _123419) : ((term724 _123419 x) = (term725 _123419 x)) = ((term720 _123419 x) = (term746 _123419 x)).
Proof. exact (MK_COMB (@lem6190602 _123419 x) (@lem6190613 _123419 x)). Qed.
Lemma lem6190615 {_123419 : Type'} (x : type402 _123419) : (term720 _123419 x) = (term746 _123419 x).
Proof. exact (EQ_MP (@lem6190614 _123419 x) (@lem6190589 _123419 x)). Qed.
Lemma lem6190617 {A B : Type'} (P : type1413 A B) : (term699 A B P) = (term700 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6190618 {_123419 : Type'} (P : type401 _123419) : (term701 _123419 P) = (term702 _123419 P).
Proof. exact (@lem6190617 (type1400 _123419) _123419 P). Qed.
Lemma lem6190619 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term747 _123419 y x) = (term748 _123419 y x).
Proof. exact (@lem6190618 _123419 (term749 _123419 y x)). Qed.
Lemma lem6190620 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) (op : type1400 _123419) : (term750 _123419 y x op) = (term751 _123419 y x op).
Proof. exact (eq_refl (term750 _123419 y x op)). Qed.
Lemma lem6190621 {_123419 : Type'} (z : _123419) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem6190622 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) (op : type1400 _123419) (z : _123419) : (term752 _123419 y x op z) = (term753 _123419 y x op z).
Proof. exact (MK_COMB (@lem6190620 _123419 y x op) (@lem6190621 _123419 z)). Qed.
Lemma lem6190623 {_123419 : Type'} (y : type402 _123419) (z : _123419) (x : type402 _123419) (op : type1400 _123419) : (term753 _123419 y x op z) = (term754 _123419 y z x op).
Proof. exact (eq_refl (term753 _123419 y x op z)). Qed.
Lemma lem6190624 {_123419 : Type'} (y : type402 _123419) (z : _123419) (x : type402 _123419) (op : type1400 _123419) : (term752 _123419 y x op z) = (term754 _123419 y z x op).
Proof. exact (TRANS (@lem6190622 _123419 y x op z) (@lem6190623 _123419 y z x op)). Qed.
Lemma lem6190625 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) (op : type1400 _123419) : (term755 _123419 y x op) = (term751 _123419 y x op).
Proof. exact (fun_ext (fun z : _123419 => @lem6190624 _123419 y z x op)). Qed.
Lemma lem6190626 {_123419 : Type'} : (@ex _123419) = (@ex _123419).
Proof. exact (eq_refl (@ex _123419)). Qed.
Lemma lem6190627 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) (op : type1400 _123419) : (term756 _123419 y x op) = (term739 _123419 y x op).
Proof. exact (MK_COMB (@lem6190626 _123419) (@lem6190625 _123419 y x op)). Qed.
Lemma lem6190628 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term757 _123419 y x) = (term741 _123419 y x).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6190627 _123419 y x op)). Qed.
Lemma lem6190629 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6190630 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term747 _123419 y x) = (term743 _123419 y x).
Proof. exact (MK_COMB (@lem6190629 _123419) (@lem6190628 _123419 y x)). Qed.
Lemma lem6190631 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6190632 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term758 _123419 y x) = (term759 _123419 y x).
Proof. exact (MK_COMB (@lem6190631) (@lem6190630 _123419 y x)). Qed.
Lemma lem6190633 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) (op : type1400 _123419) : (term750 _123419 y x op) = (term751 _123419 y x op).
Proof. exact (eq_refl (term750 _123419 y x op)). Qed.
Lemma lem6190634 {_123419 : Type'} (z : type402 _123419) (op : type1400 _123419) : (z op) = (z op).
Proof. exact (eq_refl (z op)). Qed.
Lemma lem6190635 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) (z : type402 _123419) (op : type1400 _123419) : (term760 _123419 y x z op) = (term761 _123419 y x z op).
Proof. exact (MK_COMB (@lem6190633 _123419 y x op) (@lem6190634 _123419 z op)). Qed.
Lemma lem6190636 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (op : type1400 _123419) : (term761 _123419 y x z op) = (term762 _123419 y z x op).
Proof. exact (eq_refl (term761 _123419 y x z op)). Qed.
Lemma lem6190637 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (op : type1400 _123419) : (term760 _123419 y x z op) = (term762 _123419 y z x op).
Proof. exact (TRANS (@lem6190635 _123419 y x z op) (@lem6190636 _123419 y z x op)). Qed.
Lemma lem6190638 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) : (term763 _123419 y x z) = (term764 _123419 y z x).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6190637 _123419 y z x op)). Qed.
Lemma lem6190639 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6190640 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) : (term765 _123419 y x z) = (term766 _123419 y z x).
Proof. exact (MK_COMB (@lem6190639 _123419) (@lem6190638 _123419 y z x)). Qed.
Lemma lem6190641 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term767 _123419 y x) = (term768 _123419 y x).
Proof. exact (fun_ext (fun z : type402 _123419 => @lem6190640 _123419 y z x)). Qed.
Lemma lem6190642 {_123419 : Type'} : (@ex ((_123419 -> _123419 -> _123419) -> _123419)) = (@ex ((_123419 -> _123419 -> _123419) -> _123419)).
Proof. exact (eq_refl (@ex ((_123419 -> _123419 -> _123419) -> _123419))). Qed.
Lemma lem6190643 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term748 _123419 y x) = (term769 _123419 y x).
Proof. exact (MK_COMB (@lem6190642 _123419) (@lem6190641 _123419 y x)). Qed.
Lemma lem6190644 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : ((term747 _123419 y x) = (term748 _123419 y x)) = ((term743 _123419 y x) = (term769 _123419 y x)).
Proof. exact (MK_COMB (@lem6190632 _123419 y x) (@lem6190643 _123419 y x)). Qed.
Lemma lem6190645 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term743 _123419 y x) = (term769 _123419 y x).
Proof. exact (EQ_MP (@lem6190644 _123419 y x) (@lem6190619 _123419 y x)). Qed.
Lemma lem6190646 {_123419 : Type'} (x : type402 _123419) : (term745 _123419 x) = (term770 _123419 x).
Proof. exact (fun_ext (fun y : type402 _123419 => @lem6190645 _123419 y x)). Qed.
Lemma lem6190647 {_123419 : Type'} : (@ex ((_123419 -> _123419 -> _123419) -> _123419)) = (@ex ((_123419 -> _123419 -> _123419) -> _123419)).
Proof. exact (eq_refl (@ex ((_123419 -> _123419 -> _123419) -> _123419))). Qed.
Lemma lem6190648 {_123419 : Type'} (x : type402 _123419) : (term746 _123419 x) = (term771 _123419 x).
Proof. exact (MK_COMB (@lem6190647 _123419) (@lem6190646 _123419 x)). Qed.
Lemma lem6190649 {_123419 : Type'} (x : type402 _123419) : (term720 _123419 x) = (term771 _123419 x).
Proof. exact (TRANS (@lem6190615 _123419 x) (@lem6190648 _123419 x)). Qed.
Lemma lem6190650 {_123419 : Type'} : (term722 _123419) = (term772 _123419).
Proof. exact (fun_ext (fun x : type402 _123419 => @lem6190649 _123419 x)). Qed.
Lemma lem6190651 {_123419 : Type'} : (@ex ((_123419 -> _123419 -> _123419) -> _123419)) = (@ex ((_123419 -> _123419 -> _123419) -> _123419)).
Proof. exact (eq_refl (@ex ((_123419 -> _123419 -> _123419) -> _123419))). Qed.
Lemma lem6190652 {_123419 : Type'} : (term723 _123419) = (term773 _123419).
Proof. exact (MK_COMB (@lem6190651 _123419) (@lem6190650 _123419)). Qed.
Lemma lem6190653 {_123419 : Type'} : (term698 _123419) = (term773 _123419).
Proof. exact (TRANS (@lem6190585 _123419) (@lem6190652 _123419)). Qed.
Lemma lem6190654 {_123419 : Type'} : (term538 _123419) = (term773 _123419).
Proof. exact (TRANS (@lem6190555 _123419) (@lem6190653 _123419)). Qed.
Lemma lem6190655 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6190656 {_123419 : Type'} : (term540 _123419) = (term774 _123419).
Proof. exact (MK_COMB (@lem6190655) (@lem6190654 _123419)). Qed.
Lemma lem6190657 {_123419 : Type'} : (term543 _123419) = (term543 _123419).
Proof. exact (eq_refl (term543 _123419)). Qed.
Lemma lem6190658 {_123419 : Type'} : (term544 _123419) = (term775 _123419).
Proof. exact (MK_COMB (@lem6190656 _123419) (@lem6190657 _123419)). Qed.
Lemma lem6190660 {A : Type'} (P : A -> Prop) (Q : Prop) : (term776 A P Q) = (term777 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6190661 {_123419 : Type'} (P : type82 _123419) (Q : Prop) : (term778 _123419 P Q) = (term779 _123419 P Q).
Proof. exact (@lem6190660 (type402 _123419) P Q). Qed.
Lemma lem6190662 {_123419 : Type'} : (term780 _123419) = (term781 _123419).
Proof. exact (@lem6190661 _123419 (term772 _123419) (term543 _123419)). Qed.
Lemma lem6190663 {_123419 : Type'} (x : type402 _123419) : (term782 _123419 x) = (term771 _123419 x).
Proof. exact (eq_refl (term782 _123419 x)). Qed.
Lemma lem6190664 {_123419 : Type'} : (term783 _123419) = (term772 _123419).
Proof. exact (fun_ext (fun x : type402 _123419 => @lem6190663 _123419 x)). Qed.
Lemma lem6190665 {_123419 : Type'} : (@ex ((_123419 -> _123419 -> _123419) -> _123419)) = (@ex ((_123419 -> _123419 -> _123419) -> _123419)).
Proof. exact (eq_refl (@ex ((_123419 -> _123419 -> _123419) -> _123419))). Qed.
Lemma lem6190666 {_123419 : Type'} : (term784 _123419) = (term773 _123419).
Proof. exact (MK_COMB (@lem6190665 _123419) (@lem6190664 _123419)). Qed.
Lemma lem6190667 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6190668 {_123419 : Type'} : (term785 _123419) = (term774 _123419).
Proof. exact (MK_COMB (@lem6190667) (@lem6190666 _123419)). Qed.
Lemma lem6190669 {_123419 : Type'} : (term543 _123419) = (term543 _123419).
Proof. exact (eq_refl (term543 _123419)). Qed.
Lemma lem6190670 {_123419 : Type'} : (term780 _123419) = (term775 _123419).
Proof. exact (MK_COMB (@lem6190668 _123419) (@lem6190669 _123419)). Qed.
Lemma lem6190671 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6190672 {_123419 : Type'} : (term786 _123419) = (term787 _123419).
Proof. exact (MK_COMB (@lem6190671) (@lem6190670 _123419)). Qed.
Lemma lem6190673 {_123419 : Type'} (x : type402 _123419) : (term782 _123419 x) = (term771 _123419 x).
Proof. exact (eq_refl (term782 _123419 x)). Qed.
Lemma lem6190674 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6190675 {_123419 : Type'} (x : type402 _123419) : (term788 _123419 x) = (term789 _123419 x).
Proof. exact (MK_COMB (@lem6190674) (@lem6190673 _123419 x)). Qed.
Lemma lem6190676 {_123419 : Type'} : (term543 _123419) = (term543 _123419).
Proof. exact (eq_refl (term543 _123419)). Qed.
Lemma lem6190677 {_123419 : Type'} (x : type402 _123419) : (term790 _123419 x) = (term791 _123419 x).
Proof. exact (MK_COMB (@lem6190675 _123419 x) (@lem6190676 _123419)). Qed.
Lemma lem6190678 {_123419 : Type'} : (term792 _123419) = (term793 _123419).
Proof. exact (fun_ext (fun x : type402 _123419 => @lem6190677 _123419 x)). Qed.
Lemma lem6190679 {_123419 : Type'} : (@ex ((_123419 -> _123419 -> _123419) -> _123419)) = (@ex ((_123419 -> _123419 -> _123419) -> _123419)).
Proof. exact (eq_refl (@ex ((_123419 -> _123419 -> _123419) -> _123419))). Qed.
Lemma lem6190680 {_123419 : Type'} : (term781 _123419) = (term794 _123419).
Proof. exact (MK_COMB (@lem6190679 _123419) (@lem6190678 _123419)). Qed.
Lemma lem6190681 {_123419 : Type'} : ((term780 _123419) = (term781 _123419)) = ((term775 _123419) = (term794 _123419)).
Proof. exact (MK_COMB (@lem6190672 _123419) (@lem6190680 _123419)). Qed.
Lemma lem6190682 {_123419 : Type'} : (term775 _123419) = (term794 _123419).
Proof. exact (EQ_MP (@lem6190681 _123419) (@lem6190662 _123419)). Qed.
Lemma lem6190684 {A : Type'} (P : A -> Prop) (Q : Prop) : (term776 A P Q) = (term777 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6190685 {_123419 : Type'} (P : type82 _123419) (Q : Prop) : (term778 _123419 P Q) = (term779 _123419 P Q).
Proof. exact (@lem6190684 (type402 _123419) P Q). Qed.
Lemma lem6190686 {_123419 : Type'} (x : type402 _123419) : (term795 _123419 x) = (term796 _123419 x).
Proof. exact (@lem6190685 _123419 (term770 _123419 x) (term543 _123419)). Qed.
Lemma lem6190687 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term797 _123419 x y) = (term769 _123419 y x).
Proof. exact (eq_refl (term797 _123419 x y)). Qed.
Lemma lem6190688 {_123419 : Type'} (x : type402 _123419) : (term798 _123419 x) = (term770 _123419 x).
Proof. exact (fun_ext (fun y : type402 _123419 => @lem6190687 _123419 y x)). Qed.
Lemma lem6190689 {_123419 : Type'} : (@ex ((_123419 -> _123419 -> _123419) -> _123419)) = (@ex ((_123419 -> _123419 -> _123419) -> _123419)).
Proof. exact (eq_refl (@ex ((_123419 -> _123419 -> _123419) -> _123419))). Qed.
Lemma lem6190690 {_123419 : Type'} (x : type402 _123419) : (term799 _123419 x) = (term771 _123419 x).
Proof. exact (MK_COMB (@lem6190689 _123419) (@lem6190688 _123419 x)). Qed.
Lemma lem6190691 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6190692 {_123419 : Type'} (x : type402 _123419) : (term800 _123419 x) = (term789 _123419 x).
Proof. exact (MK_COMB (@lem6190691) (@lem6190690 _123419 x)). Qed.
Lemma lem6190693 {_123419 : Type'} : (term543 _123419) = (term543 _123419).
Proof. exact (eq_refl (term543 _123419)). Qed.
Lemma lem6190694 {_123419 : Type'} (x : type402 _123419) : (term795 _123419 x) = (term791 _123419 x).
Proof. exact (MK_COMB (@lem6190692 _123419 x) (@lem6190693 _123419)). Qed.
Lemma lem6190695 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6190696 {_123419 : Type'} (x : type402 _123419) : (term801 _123419 x) = (term802 _123419 x).
Proof. exact (MK_COMB (@lem6190695) (@lem6190694 _123419 x)). Qed.
Lemma lem6190697 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term797 _123419 x y) = (term769 _123419 y x).
Proof. exact (eq_refl (term797 _123419 x y)). Qed.
Lemma lem6190698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6190699 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term803 _123419 x y) = (term804 _123419 y x).
Proof. exact (MK_COMB (@lem6190698) (@lem6190697 _123419 y x)). Qed.
Lemma lem6190700 {_123419 : Type'} : (term543 _123419) = (term543 _123419).
Proof. exact (eq_refl (term543 _123419)). Qed.
Lemma lem6190701 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term805 _123419 x y) = (term806 _123419 y x).
Proof. exact (MK_COMB (@lem6190699 _123419 y x) (@lem6190700 _123419)). Qed.
Lemma lem6190702 {_123419 : Type'} (x : type402 _123419) : (term807 _123419 x) = (term808 _123419 x).
Proof. exact (fun_ext (fun y : type402 _123419 => @lem6190701 _123419 y x)). Qed.
Lemma lem6190703 {_123419 : Type'} : (@ex ((_123419 -> _123419 -> _123419) -> _123419)) = (@ex ((_123419 -> _123419 -> _123419) -> _123419)).
Proof. exact (eq_refl (@ex ((_123419 -> _123419 -> _123419) -> _123419))). Qed.
Lemma lem6190704 {_123419 : Type'} (x : type402 _123419) : (term796 _123419 x) = (term809 _123419 x).
Proof. exact (MK_COMB (@lem6190703 _123419) (@lem6190702 _123419 x)). Qed.
Lemma lem6190705 {_123419 : Type'} (x : type402 _123419) : ((term795 _123419 x) = (term796 _123419 x)) = ((term791 _123419 x) = (term809 _123419 x)).
Proof. exact (MK_COMB (@lem6190696 _123419 x) (@lem6190704 _123419 x)). Qed.
Lemma lem6190706 {_123419 : Type'} (x : type402 _123419) : (term791 _123419 x) = (term809 _123419 x).
Proof. exact (EQ_MP (@lem6190705 _123419 x) (@lem6190686 _123419 x)). Qed.
Lemma lem6190708 {A : Type'} (P : A -> Prop) (Q : Prop) : (term776 A P Q) = (term777 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6190709 {_123419 : Type'} (P : type82 _123419) (Q : Prop) : (term778 _123419 P Q) = (term779 _123419 P Q).
Proof. exact (@lem6190708 (type402 _123419) P Q). Qed.
Lemma lem6190710 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term810 _123419 y x) = (term811 _123419 y x).
Proof. exact (@lem6190709 _123419 (term768 _123419 y x) (term543 _123419)). Qed.
Lemma lem6190711 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) : (term812 _123419 y x z) = (term766 _123419 y z x).
Proof. exact (eq_refl (term812 _123419 y x z)). Qed.
Lemma lem6190712 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term813 _123419 y x) = (term768 _123419 y x).
Proof. exact (fun_ext (fun z : type402 _123419 => @lem6190711 _123419 y z x)). Qed.
Lemma lem6190713 {_123419 : Type'} : (@ex ((_123419 -> _123419 -> _123419) -> _123419)) = (@ex ((_123419 -> _123419 -> _123419) -> _123419)).
Proof. exact (eq_refl (@ex ((_123419 -> _123419 -> _123419) -> _123419))). Qed.
Lemma lem6190714 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term814 _123419 y x) = (term769 _123419 y x).
Proof. exact (MK_COMB (@lem6190713 _123419) (@lem6190712 _123419 y x)). Qed.
Lemma lem6190715 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6190716 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term815 _123419 y x) = (term804 _123419 y x).
Proof. exact (MK_COMB (@lem6190715) (@lem6190714 _123419 y x)). Qed.
Lemma lem6190717 {_123419 : Type'} : (term543 _123419) = (term543 _123419).
Proof. exact (eq_refl (term543 _123419)). Qed.
Lemma lem6190718 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term810 _123419 y x) = (term806 _123419 y x).
Proof. exact (MK_COMB (@lem6190716 _123419 y x) (@lem6190717 _123419)). Qed.
Lemma lem6190719 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6190720 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term816 _123419 y x) = (term817 _123419 y x).
Proof. exact (MK_COMB (@lem6190719) (@lem6190718 _123419 y x)). Qed.
Lemma lem6190721 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) : (term812 _123419 y x z) = (term766 _123419 y z x).
Proof. exact (eq_refl (term812 _123419 y x z)). Qed.
Lemma lem6190722 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6190723 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) : (term818 _123419 y x z) = (term819 _123419 y z x).
Proof. exact (MK_COMB (@lem6190722) (@lem6190721 _123419 y z x)). Qed.
Lemma lem6190724 {_123419 : Type'} : (term543 _123419) = (term543 _123419).
Proof. exact (eq_refl (term543 _123419)). Qed.
Lemma lem6190725 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) : (term820 _123419 y x z) = (term821 _123419 y z x).
Proof. exact (MK_COMB (@lem6190723 _123419 y z x) (@lem6190724 _123419)). Qed.
Lemma lem6190726 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term822 _123419 y x) = (term823 _123419 y x).
Proof. exact (fun_ext (fun z : type402 _123419 => @lem6190725 _123419 y z x)). Qed.
Lemma lem6190727 {_123419 : Type'} : (@ex ((_123419 -> _123419 -> _123419) -> _123419)) = (@ex ((_123419 -> _123419 -> _123419) -> _123419)).
Proof. exact (eq_refl (@ex ((_123419 -> _123419 -> _123419) -> _123419))). Qed.
Lemma lem6190728 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term811 _123419 y x) = (term824 _123419 y x).
Proof. exact (MK_COMB (@lem6190727 _123419) (@lem6190726 _123419 y x)). Qed.
Lemma lem6190729 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : ((term810 _123419 y x) = (term811 _123419 y x)) = ((term806 _123419 y x) = (term824 _123419 y x)).
Proof. exact (MK_COMB (@lem6190720 _123419 y x) (@lem6190728 _123419 y x)). Qed.
Lemma lem6190730 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) : (term806 _123419 y x) = (term824 _123419 y x).
Proof. exact (EQ_MP (@lem6190729 _123419 y x) (@lem6190710 _123419 y x)). Qed.
Lemma lem6190731 {_123419 : Type'} (x : type402 _123419) : (term808 _123419 x) = (term825 _123419 x).
Proof. exact (fun_ext (fun y : type402 _123419 => @lem6190730 _123419 y x)). Qed.
Lemma lem6190732 {_123419 : Type'} : (@ex ((_123419 -> _123419 -> _123419) -> _123419)) = (@ex ((_123419 -> _123419 -> _123419) -> _123419)).
Proof. exact (eq_refl (@ex ((_123419 -> _123419 -> _123419) -> _123419))). Qed.
Lemma lem6190733 {_123419 : Type'} (x : type402 _123419) : (term809 _123419 x) = (term826 _123419 x).
Proof. exact (MK_COMB (@lem6190732 _123419) (@lem6190731 _123419 x)). Qed.
Lemma lem6190734 {_123419 : Type'} (x : type402 _123419) : (term791 _123419 x) = (term826 _123419 x).
Proof. exact (TRANS (@lem6190706 _123419 x) (@lem6190733 _123419 x)). Qed.
Lemma lem6190735 {_123419 : Type'} : (term793 _123419) = (term827 _123419).
Proof. exact (fun_ext (fun x : type402 _123419 => @lem6190734 _123419 x)). Qed.
Lemma lem6190736 {_123419 : Type'} : (@ex ((_123419 -> _123419 -> _123419) -> _123419)) = (@ex ((_123419 -> _123419 -> _123419) -> _123419)).
Proof. exact (eq_refl (@ex ((_123419 -> _123419 -> _123419) -> _123419))). Qed.
Lemma lem6190737 {_123419 : Type'} : (term794 _123419) = (term828 _123419).
Proof. exact (MK_COMB (@lem6190736 _123419) (@lem6190735 _123419)). Qed.
Lemma lem6190738 {_123419 : Type'} : (term775 _123419) = (term828 _123419).
Proof. exact (TRANS (@lem6190682 _123419) (@lem6190737 _123419)). Qed.
Lemma lem6190739 {_123419 : Type'} : (term544 _123419) = (term828 _123419).
Proof. exact (TRANS (@lem6190658 _123419) (@lem6190738 _123419)). Qed.
Lemma lem6190740 {_123419 : Type'} : (term520 _123419) = (term828 _123419).
Proof. exact (TRANS (@lem6190189 _123419) (@lem6190739 _123419)). Qed.
Lemma lem6190741 {_123419 : Type'} : (term382 _123419) = (term828 _123419).
Proof. exact (TRANS (@lem6190162 _123419) (@lem6190740 _123419)). Qed.
Lemma lem6190742 {_123419 : Type'} (h1 : term382 _123419) : term828 _123419.
Proof. exact (EQ_MP (@lem6190741 _123419) (@lem6190028 _123419 h1)). Qed.
Lemma lem6190743 {_123419 : Type'} (x : type402 _123419) (h1 : term826 _123419 x) : term826 _123419 x.
Proof. exact (h1). Qed.
Lemma lem6190744 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) (h1 : term824 _123419 y x) : term824 _123419 y x.
Proof. exact (h1). Qed.
Lemma lem6190745 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (h1 : term821 _123419 y z x) : term821 _123419 y z x.
Proof. exact (h1). Qed.
Lemma lem6190750 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6190751 {_123419 : Type'} (f : type403 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> Prop) f x).
Proof. exact (@lem6190750 (type1400 _123419) Prop f x). Qed.
Lemma lem6190753 {_123419 : Type'} (op : type1400 _123419) : (@monoidal _123419 op) = (@I ((_123419 -> _123419 -> _123419) -> Prop) (@monoidal _123419) op).
Proof. exact (@lem6190751 _123419 (@monoidal _123419) op). Qed.
Lemma lem6190780 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6190781 {_123419 : Type'} : (@eq _123419) = (@eq _123419).
Proof. exact (eq_refl (@eq _123419)). Qed.
Lemma lem6190782 {_123419 : Type'} (op : type1400 _123419) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6190783 {_123419 : Type'} (f : nat -> _123419) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6190788 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6190789 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem6190788 nat nat f x). Qed.
Lemma lem6190791 (n : nat) : (S n) = (@I (nat -> nat) S n).
Proof. exact (@lem6190789 S n). Qed.
Lemma lem6190792 {_123419 : Type'} (f : nat -> _123419) (n : nat) : (term1555 _123419 f n) = (term1556 _123419 f n).
Proof. exact (MK_COMB (@lem6190783 _123419 f) (@lem6190791 n)). Qed.
Lemma lem6190794 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6190795 {_123419 : Type'} (f : nat -> _123419) (x : nat) : (f x) = (@I (nat -> _123419) f x).
Proof. exact (@lem6190794 nat _123419 f x). Qed.
Lemma lem6190796 {_123419 : Type'} (f : nat -> _123419) (n : nat) : (term1556 _123419 f n) = (term1557 _123419 f n).
Proof. exact (@lem6190795 _123419 f (@I (nat -> nat) S n)). Qed.
Lemma lem6190797 {_123419 : Type'} (f : nat -> _123419) (n : nat) : (term1555 _123419 f n) = (term1557 _123419 f n).
Proof. exact (TRANS (@lem6190792 _123419 f n) (@lem6190796 _123419 f n)). Qed.
Lemma lem6190806 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6190807 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem6190806 nat type1605 f x). Qed.
Lemma lem6190808 (m : nat) : (dotdot m) = (@I (nat -> nat -> nat -> Prop) dotdot m).
Proof. exact (@lem6190807 dotdot m). Qed.
Lemma lem6190809 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem6190810 (m : nat) (n : nat) : (dotdot m n) = (@I (nat -> nat -> nat -> Prop) dotdot m n).
Proof. exact (MK_COMB (@lem6190808 m) (@lem6190809 n)). Qed.
Lemma lem6190812 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6190813 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem6190812 nat (nat -> Prop) f x). Qed.
Lemma lem6190814 (m : nat) (n : nat) : (@I (nat -> nat -> nat -> Prop) dotdot m n) = (term1558 m n).
Proof. exact (@lem6190813 (@I (nat -> nat -> nat -> Prop) dotdot m) n). Qed.
Lemma lem6190816 (m : nat) (n : nat) : (dotdot m n) = (term1558 m n).
Proof. exact (TRANS (@lem6190810 m n) (@lem6190814 m n)). Qed.
Lemma lem6190817 {_123419 : Type'} (f : nat -> _123419) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6190818 {_123419 : Type'} (op : type1400 _123419) : (@iterate _123419 nat op) = (@iterate _123419 nat op).
Proof. exact (eq_refl (@iterate _123419 nat op)). Qed.
Lemma lem6190819 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) : (term1559 _123419 op m n) = (term1560 _123419 op m n).
Proof. exact (MK_COMB (@lem6190818 _123419 op) (@lem6190816 m n)). Qed.
Lemma lem6190820 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term247 _123419 op m n f) = (term1561 _123419 op m n f).
Proof. exact (MK_COMB (@lem6190819 _123419 op m n) (@lem6190817 _123419 f)). Qed.
Lemma lem6190822 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6190823 {_123419 : Type'} (f : type400 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> (nat -> Prop) -> (nat -> _123419) -> _123419) f x).
Proof. exact (@lem6190822 (type1400 _123419) (type983 _123419) f x). Qed.
Lemma lem6190824 {_123419 : Type'} (op : type1400 _123419) : (@iterate _123419 nat op) = (@I ((_123419 -> _123419 -> _123419) -> (nat -> Prop) -> (nat -> _123419) -> _123419) (@iterate _123419 nat) op).
Proof. exact (@lem6190823 _123419 (@iterate _123419 nat) op). Qed.
Lemma lem6190825 (m : nat) (n : nat) : (term1558 m n) = (term1558 m n).
Proof. exact (eq_refl (term1558 m n)). Qed.
Lemma lem6190826 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) : (term1560 _123419 op m n) = (term1562 _123419 op m n).
Proof. exact (MK_COMB (@lem6190824 _123419 op) (@lem6190825 m n)). Qed.
Lemma lem6190828 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6190829 {_123419 : Type'} (f : type983 _123419) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> (nat -> _123419) -> _123419) f x).
Proof. exact (@lem6190828 (nat -> Prop) (type975 _123419) f x). Qed.
Lemma lem6190830 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) : (term1562 _123419 op m n) = (term1563 _123419 op m n).
Proof. exact (@lem6190829 _123419 (@I ((_123419 -> _123419 -> _123419) -> (nat -> Prop) -> (nat -> _123419) -> _123419) (@iterate _123419 nat) op) (term1558 m n)). Qed.
Lemma lem6190831 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) : (term1560 _123419 op m n) = (term1563 _123419 op m n).
Proof. exact (TRANS (@lem6190826 _123419 op m n) (@lem6190830 _123419 op m n)). Qed.
Lemma lem6190832 {_123419 : Type'} (f : nat -> _123419) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6190833 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term1561 _123419 op m n f) = (term1564 _123419 op m n f).
Proof. exact (MK_COMB (@lem6190831 _123419 op m n) (@lem6190832 _123419 f)). Qed.
Lemma lem6190835 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6190836 {_123419 : Type'} (f : type975 _123419) (x : nat -> _123419) : (f x) = (@I ((nat -> _123419) -> _123419) f x).
Proof. exact (@lem6190835 (nat -> _123419) _123419 f x). Qed.
Lemma lem6190837 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term1564 _123419 op m n f) = (term1565 _123419 op m n f).
Proof. exact (@lem6190836 _123419 (term1563 _123419 op m n) f). Qed.
Lemma lem6190838 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term1561 _123419 op m n f) = (term1565 _123419 op m n f).
Proof. exact (TRANS (@lem6190833 _123419 op m n f) (@lem6190837 _123419 op m n f)). Qed.
Lemma lem6190839 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term247 _123419 op m n f) = (term1565 _123419 op m n f).
Proof. exact (TRANS (@lem6190820 _123419 op m n f) (@lem6190838 _123419 op m n f)). Qed.
Lemma lem6190840 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (n : nat) : (term1566 _123419 op f n) = (term1567 _123419 op f n).
Proof. exact (MK_COMB (@lem6190782 _123419 op) (@lem6190797 _123419 f n)). Qed.
Lemma lem6190841 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term347 _123419 op m n f) = (term1568 _123419 op m n f).
Proof. exact (MK_COMB (@lem6190840 _123419 op f n) (@lem6190839 _123419 op m n f)). Qed.
Lemma lem6190843 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6190844 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6190843 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6190845 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (n : nat) : (term1567 _123419 op f n) = (term1569 _123419 op f n).
Proof. exact (@lem6190844 _123419 op (term1557 _123419 f n)). Qed.
Lemma lem6190846 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term1565 _123419 op m n f) = (term1565 _123419 op m n f).
Proof. exact (eq_refl (term1565 _123419 op m n f)). Qed.
Lemma lem6190847 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term1568 _123419 op m n f) = (term1570 _123419 op m n f).
Proof. exact (MK_COMB (@lem6190845 _123419 op f n) (@lem6190846 _123419 op m n f)). Qed.
Lemma lem6190849 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6190850 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6190849 _123419 _123419 f x). Qed.
Lemma lem6190851 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term1570 _123419 op m n f) = (term1571 _123419 op m n f).
Proof. exact (@lem6190850 _123419 (term1569 _123419 op f n) (term1565 _123419 op m n f)). Qed.
Lemma lem6190852 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term1568 _123419 op m n f) = (term1571 _123419 op m n f).
Proof. exact (TRANS (@lem6190847 _123419 op m n f) (@lem6190851 _123419 op m n f)). Qed.
Lemma lem6190853 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term347 _123419 op m n f) = (term1571 _123419 op m n f).
Proof. exact (TRANS (@lem6190841 _123419 op m n f) (@lem6190852 _123419 op m n f)). Qed.
Lemma lem6190854 {_123419 : Type'} (op : type1400 _123419) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6190863 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6190864 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem6190863 nat type1605 f x). Qed.
Lemma lem6190865 (m : nat) : (dotdot m) = (@I (nat -> nat -> nat -> Prop) dotdot m).
Proof. exact (@lem6190864 dotdot m). Qed.
Lemma lem6190866 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem6190867 (m : nat) (n : nat) : (dotdot m n) = (@I (nat -> nat -> nat -> Prop) dotdot m n).
Proof. exact (MK_COMB (@lem6190865 m) (@lem6190866 n)). Qed.
Lemma lem6190869 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6190870 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem6190869 nat (nat -> Prop) f x). Qed.
Lemma lem6190871 (m : nat) (n : nat) : (@I (nat -> nat -> nat -> Prop) dotdot m n) = (term1558 m n).
Proof. exact (@lem6190870 (@I (nat -> nat -> nat -> Prop) dotdot m) n). Qed.
Lemma lem6190873 (m : nat) (n : nat) : (dotdot m n) = (term1558 m n).
Proof. exact (TRANS (@lem6190867 m n) (@lem6190871 m n)). Qed.
Lemma lem6190874 {_123419 : Type'} (f : nat -> _123419) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6190875 {_123419 : Type'} (op : type1400 _123419) : (@iterate _123419 nat op) = (@iterate _123419 nat op).
Proof. exact (eq_refl (@iterate _123419 nat op)). Qed.
Lemma lem6190876 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) : (term1559 _123419 op m n) = (term1560 _123419 op m n).
Proof. exact (MK_COMB (@lem6190875 _123419 op) (@lem6190873 m n)). Qed.
Lemma lem6190877 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term247 _123419 op m n f) = (term1561 _123419 op m n f).
Proof. exact (MK_COMB (@lem6190876 _123419 op m n) (@lem6190874 _123419 f)). Qed.
Lemma lem6190879 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6190880 {_123419 : Type'} (f : type400 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> (nat -> Prop) -> (nat -> _123419) -> _123419) f x).
Proof. exact (@lem6190879 (type1400 _123419) (type983 _123419) f x). Qed.
Lemma lem6190881 {_123419 : Type'} (op : type1400 _123419) : (@iterate _123419 nat op) = (@I ((_123419 -> _123419 -> _123419) -> (nat -> Prop) -> (nat -> _123419) -> _123419) (@iterate _123419 nat) op).
Proof. exact (@lem6190880 _123419 (@iterate _123419 nat) op). Qed.
Lemma lem6190882 (m : nat) (n : nat) : (term1558 m n) = (term1558 m n).
Proof. exact (eq_refl (term1558 m n)). Qed.
Lemma lem6190883 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) : (term1560 _123419 op m n) = (term1562 _123419 op m n).
Proof. exact (MK_COMB (@lem6190881 _123419 op) (@lem6190882 m n)). Qed.
Lemma lem6190885 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6190886 {_123419 : Type'} (f : type983 _123419) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> (nat -> _123419) -> _123419) f x).
Proof. exact (@lem6190885 (nat -> Prop) (type975 _123419) f x). Qed.
Lemma lem6190887 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) : (term1562 _123419 op m n) = (term1563 _123419 op m n).
Proof. exact (@lem6190886 _123419 (@I ((_123419 -> _123419 -> _123419) -> (nat -> Prop) -> (nat -> _123419) -> _123419) (@iterate _123419 nat) op) (term1558 m n)). Qed.
Lemma lem6190888 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) : (term1560 _123419 op m n) = (term1563 _123419 op m n).
Proof. exact (TRANS (@lem6190883 _123419 op m n) (@lem6190887 _123419 op m n)). Qed.
Lemma lem6190889 {_123419 : Type'} (f : nat -> _123419) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6190890 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term1561 _123419 op m n f) = (term1564 _123419 op m n f).
Proof. exact (MK_COMB (@lem6190888 _123419 op m n) (@lem6190889 _123419 f)). Qed.
Lemma lem6190892 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6190893 {_123419 : Type'} (f : type975 _123419) (x : nat -> _123419) : (f x) = (@I ((nat -> _123419) -> _123419) f x).
Proof. exact (@lem6190892 (nat -> _123419) _123419 f x). Qed.
Lemma lem6190894 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term1564 _123419 op m n f) = (term1565 _123419 op m n f).
Proof. exact (@lem6190893 _123419 (term1563 _123419 op m n) f). Qed.
Lemma lem6190895 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term1561 _123419 op m n f) = (term1565 _123419 op m n f).
Proof. exact (TRANS (@lem6190890 _123419 op m n f) (@lem6190894 _123419 op m n f)). Qed.
Lemma lem6190896 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term247 _123419 op m n f) = (term1565 _123419 op m n f).
Proof. exact (TRANS (@lem6190877 _123419 op m n f) (@lem6190895 _123419 op m n f)). Qed.
Lemma lem6190897 {_123419 : Type'} (f : nat -> _123419) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6190902 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6190903 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem6190902 nat nat f x). Qed.
Lemma lem6190905 (n : nat) : (S n) = (@I (nat -> nat) S n).
Proof. exact (@lem6190903 S n). Qed.
Lemma lem6190906 {_123419 : Type'} (f : nat -> _123419) (n : nat) : (term1555 _123419 f n) = (term1556 _123419 f n).
Proof. exact (MK_COMB (@lem6190897 _123419 f) (@lem6190905 n)). Qed.
Lemma lem6190908 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6190909 {_123419 : Type'} (f : nat -> _123419) (x : nat) : (f x) = (@I (nat -> _123419) f x).
Proof. exact (@lem6190908 nat _123419 f x). Qed.
Lemma lem6190910 {_123419 : Type'} (f : nat -> _123419) (n : nat) : (term1556 _123419 f n) = (term1557 _123419 f n).
Proof. exact (@lem6190909 _123419 f (@I (nat -> nat) S n)). Qed.
Lemma lem6190911 {_123419 : Type'} (f : nat -> _123419) (n : nat) : (term1555 _123419 f n) = (term1557 _123419 f n).
Proof. exact (TRANS (@lem6190906 _123419 f n) (@lem6190910 _123419 f n)). Qed.
Lemma lem6190912 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term1572 _123419 op m n f) = (term1573 _123419 op m n f).
Proof. exact (MK_COMB (@lem6190854 _123419 op) (@lem6190896 _123419 op m n f)). Qed.
Lemma lem6190913 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : (term367 _123419 op m f n) = (term1574 _123419 op m f n).
Proof. exact (MK_COMB (@lem6190912 _123419 op m n f) (@lem6190911 _123419 f n)). Qed.
Lemma lem6190915 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6190916 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6190915 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6190917 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term1573 _123419 op m n f) = (term1575 _123419 op m n f).
Proof. exact (@lem6190916 _123419 op (term1565 _123419 op m n f)). Qed.
Lemma lem6190918 {_123419 : Type'} (f : nat -> _123419) (n : nat) : (term1557 _123419 f n) = (term1557 _123419 f n).
Proof. exact (eq_refl (term1557 _123419 f n)). Qed.
Lemma lem6190919 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : (term1574 _123419 op m f n) = (term1576 _123419 op m f n).
Proof. exact (MK_COMB (@lem6190917 _123419 op m n f) (@lem6190918 _123419 f n)). Qed.
Lemma lem6190921 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6190922 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6190921 _123419 _123419 f x). Qed.
Lemma lem6190923 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : (term1576 _123419 op m f n) = (term1577 _123419 op m f n).
Proof. exact (@lem6190922 _123419 (term1575 _123419 op m n f) (term1557 _123419 f n)). Qed.
Lemma lem6190924 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : (term1574 _123419 op m f n) = (term1577 _123419 op m f n).
Proof. exact (TRANS (@lem6190919 _123419 op m f n) (@lem6190923 _123419 op m f n)). Qed.
Lemma lem6190925 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : (term367 _123419 op m f n) = (term1577 _123419 op m f n).
Proof. exact (TRANS (@lem6190913 _123419 op m f n) (@lem6190924 _123419 op m f n)). Qed.
Lemma lem6190926 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : (term378 _123419 op m n f) = (term1578 _123419 op m n f).
Proof. exact (MK_COMB (@lem6190781 _123419) (@lem6190853 _123419 op m n f)). Qed.
Lemma lem6190927 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : ((term347 _123419 op m n f) = (term367 _123419 op m f n)) = ((term1571 _123419 op m n f) = (term1577 _123419 op m f n)).
Proof. exact (MK_COMB (@lem6190926 _123419 op m n f) (@lem6190925 _123419 op m f n)). Qed.
Lemma lem6190928 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : (term1526 _123419 op m f n) = (term1579 _123419 op m f n).
Proof. exact (MK_COMB (@lem6190780) (@lem6190927 _123419 op m f n)). Qed.
Lemma lem6190930 {_123419 : Type'} : (@eq _123419) = (@eq _123419).
Proof. exact (eq_refl (@eq _123419)). Qed.
Lemma lem6190931 {_123419 : Type'} (op : type1400 _123419) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6190936 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6190937 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6190936 (type1400 _123419) _123419 f x). Qed.
Lemma lem6190939 {_123419 : Type'} (op : type1400 _123419) : (@neutral _123419 op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) (@neutral _123419) op).
Proof. exact (@lem6190937 _123419 (@neutral _123419) op). Qed.
Lemma lem6190940 {_123419 : Type'} (x : _123419) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6190941 {_123419 : Type'} (op : type1400 _123419) : (term1208 _123419 op) = (term1209 _123419 op).
Proof. exact (MK_COMB (@lem6190931 _123419 op) (@lem6190939 _123419 op)). Qed.
Lemma lem6190942 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term432 _123419 op x) = (term1210 _123419 op x).
Proof. exact (MK_COMB (@lem6190941 _123419 op) (@lem6190940 _123419 x)). Qed.
Lemma lem6190944 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6190945 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6190944 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6190946 {_123419 : Type'} (op : type1400 _123419) : (term1209 _123419 op) = (term1211 _123419 op).
Proof. exact (@lem6190945 _123419 op (@I ((_123419 -> _123419 -> _123419) -> _123419) (@neutral _123419) op)). Qed.
Lemma lem6190947 {_123419 : Type'} (x : _123419) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6190948 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1210 _123419 op x) = (term1212 _123419 op x).
Proof. exact (MK_COMB (@lem6190946 _123419 op) (@lem6190947 _123419 x)). Qed.
Lemma lem6190950 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6190951 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6190950 _123419 _123419 f x). Qed.
Lemma lem6190952 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1212 _123419 op x) = (term1213 _123419 op x).
Proof. exact (@lem6190951 _123419 (term1211 _123419 op) x). Qed.
Lemma lem6190953 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1210 _123419 op x) = (term1213 _123419 op x).
Proof. exact (TRANS (@lem6190948 _123419 op x) (@lem6190952 _123419 op x)). Qed.
Lemma lem6190954 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term432 _123419 op x) = (term1213 _123419 op x).
Proof. exact (TRANS (@lem6190942 _123419 op x) (@lem6190953 _123419 op x)). Qed.
Lemma lem6190955 {_123419 : Type'} (x : _123419) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6190956 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1214 _123419 op x) = (term1215 _123419 op x).
Proof. exact (MK_COMB (@lem6190930 _123419) (@lem6190954 _123419 op x)). Qed.
Lemma lem6190957 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : ((term432 _123419 op x) = x) = ((term1213 _123419 op x) = x).
Proof. exact (MK_COMB (@lem6190956 _123419 op x) (@lem6190955 _123419 x)). Qed.
Lemma lem6190958 {_123419 : Type'} (op : type1400 _123419) : (term433 _123419 op) = (term1216 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6190957 _123419 op x)). Qed.
Lemma lem6190959 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6190960 {_123419 : Type'} (op : type1400 _123419) : (term434 _123419 op) = (term1217 _123419 op).
Proof. exact (MK_COMB (@lem6190959 _123419) (@lem6190958 _123419 op)). Qed.
Lemma lem6190961 {_123419 : Type'} : (@eq _123419) = (@eq _123419).
Proof. exact (eq_refl (@eq _123419)). Qed.
Lemma lem6190970 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6190971 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6190970 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6190972 {_123419 : Type'} (op : type1400 _123419) (y : _123419) : (op y) = (@I (_123419 -> _123419 -> _123419) op y).
Proof. exact (@lem6190971 _123419 op y). Qed.
Lemma lem6190973 {_123419 : Type'} (z : _123419) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem6190974 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (z : _123419) : (op y z) = (@I (_123419 -> _123419 -> _123419) op y z).
Proof. exact (MK_COMB (@lem6190972 _123419 op y) (@lem6190973 _123419 z)). Qed.
Lemma lem6190976 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6190977 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6190976 _123419 _123419 f x). Qed.
Lemma lem6190978 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (z : _123419) : (@I (_123419 -> _123419 -> _123419) op y z) = (term1218 _123419 op y z).
Proof. exact (@lem6190977 _123419 (@I (_123419 -> _123419 -> _123419) op y) z). Qed.
Lemma lem6190980 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (z : _123419) : (op y z) = (term1218 _123419 op y z).
Proof. exact (TRANS (@lem6190974 _123419 op y z) (@lem6190978 _123419 op y z)). Qed.
Lemma lem6190981 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (op x) = (op x).
Proof. exact (eq_refl (op x)). Qed.
Lemma lem6190982 {_123419 : Type'} (x : _123419) (op : type1400 _123419) (y : _123419) (z : _123419) : (term435 _123419 x op y z) = (term1219 _123419 x op y z).
Proof. exact (MK_COMB (@lem6190981 _123419 op x) (@lem6190980 _123419 op y z)). Qed.
Lemma lem6190984 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6190985 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6190984 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6190986 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (op x) = (@I (_123419 -> _123419 -> _123419) op x).
Proof. exact (@lem6190985 _123419 op x). Qed.
Lemma lem6190987 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (z : _123419) : (term1218 _123419 op y z) = (term1218 _123419 op y z).
Proof. exact (eq_refl (term1218 _123419 op y z)). Qed.
Lemma lem6190988 {_123419 : Type'} (x : _123419) (op : type1400 _123419) (y : _123419) (z : _123419) : (term1219 _123419 x op y z) = (term1220 _123419 x op y z).
Proof. exact (MK_COMB (@lem6190986 _123419 op x) (@lem6190987 _123419 op y z)). Qed.
Lemma lem6190990 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6190991 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6190990 _123419 _123419 f x). Qed.
Lemma lem6190992 {_123419 : Type'} (x : _123419) (op : type1400 _123419) (y : _123419) (z : _123419) : (term1220 _123419 x op y z) = (term1221 _123419 x op y z).
Proof. exact (@lem6190991 _123419 (@I (_123419 -> _123419 -> _123419) op x) (term1218 _123419 op y z)). Qed.
Lemma lem6190993 {_123419 : Type'} (x : _123419) (op : type1400 _123419) (y : _123419) (z : _123419) : (term1219 _123419 x op y z) = (term1221 _123419 x op y z).
Proof. exact (TRANS (@lem6190988 _123419 x op y z) (@lem6190992 _123419 x op y z)). Qed.
Lemma lem6190994 {_123419 : Type'} (x : _123419) (op : type1400 _123419) (y : _123419) (z : _123419) : (term435 _123419 x op y z) = (term1221 _123419 x op y z).
Proof. exact (TRANS (@lem6190982 _123419 x op y z) (@lem6190993 _123419 x op y z)). Qed.
Lemma lem6190995 {_123419 : Type'} (op : type1400 _123419) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6191002 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191003 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6191002 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6191004 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (op x) = (@I (_123419 -> _123419 -> _123419) op x).
Proof. exact (@lem6191003 _123419 op x). Qed.
Lemma lem6191005 {_123419 : Type'} (y : _123419) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6191006 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (op x y) = (@I (_123419 -> _123419 -> _123419) op x y).
Proof. exact (MK_COMB (@lem6191004 _123419 op x) (@lem6191005 _123419 y)). Qed.
Lemma lem6191008 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191009 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6191008 _123419 _123419 f x). Qed.
Lemma lem6191010 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (@I (_123419 -> _123419 -> _123419) op x y) = (term1218 _123419 op x y).
Proof. exact (@lem6191009 _123419 (@I (_123419 -> _123419 -> _123419) op x) y). Qed.
Lemma lem6191012 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (op x y) = (term1218 _123419 op x y).
Proof. exact (TRANS (@lem6191006 _123419 op x y) (@lem6191010 _123419 op x y)). Qed.
Lemma lem6191013 {_123419 : Type'} (z : _123419) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem6191014 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term1222 _123419 op x y) = (term1223 _123419 op x y).
Proof. exact (MK_COMB (@lem6190995 _123419 op) (@lem6191012 _123419 op x y)). Qed.
Lemma lem6191015 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : (term436 _123419 op x y z) = (term1224 _123419 op x y z).
Proof. exact (MK_COMB (@lem6191014 _123419 op x y) (@lem6191013 _123419 z)). Qed.
Lemma lem6191017 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191018 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6191017 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6191019 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term1223 _123419 op x y) = (term1225 _123419 op x y).
Proof. exact (@lem6191018 _123419 op (term1218 _123419 op x y)). Qed.
Lemma lem6191020 {_123419 : Type'} (z : _123419) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem6191021 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : (term1224 _123419 op x y z) = (term1226 _123419 op x y z).
Proof. exact (MK_COMB (@lem6191019 _123419 op x y) (@lem6191020 _123419 z)). Qed.
Lemma lem6191023 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191024 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6191023 _123419 _123419 f x). Qed.
Lemma lem6191025 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : (term1226 _123419 op x y z) = (term1227 _123419 op x y z).
Proof. exact (@lem6191024 _123419 (term1225 _123419 op x y) z). Qed.
Lemma lem6191026 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : (term1224 _123419 op x y z) = (term1227 _123419 op x y z).
Proof. exact (TRANS (@lem6191021 _123419 op x y z) (@lem6191025 _123419 op x y z)). Qed.
Lemma lem6191027 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : (term436 _123419 op x y z) = (term1227 _123419 op x y z).
Proof. exact (TRANS (@lem6191015 _123419 op x y z) (@lem6191026 _123419 op x y z)). Qed.
Lemma lem6191028 {_123419 : Type'} (x : _123419) (op : type1400 _123419) (y : _123419) (z : _123419) : (term1228 _123419 x op y z) = (term1229 _123419 x op y z).
Proof. exact (MK_COMB (@lem6190961 _123419) (@lem6190994 _123419 x op y z)). Qed.
Lemma lem6191029 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : ((term435 _123419 x op y z) = (term436 _123419 op x y z)) = ((term1221 _123419 x op y z) = (term1227 _123419 op x y z)).
Proof. exact (MK_COMB (@lem6191028 _123419 x op y z) (@lem6191027 _123419 op x y z)). Qed.
Lemma lem6191030 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term437 _123419 op x y) = (term1230 _123419 op x y).
Proof. exact (fun_ext (fun z : _123419 => @lem6191029 _123419 op x y z)). Qed.
Lemma lem6191031 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191032 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term438 _123419 op x y) = (term1231 _123419 op x y).
Proof. exact (MK_COMB (@lem6191031 _123419) (@lem6191030 _123419 op x y)). Qed.
Lemma lem6191033 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term439 _123419 op x) = (term1232 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6191032 _123419 op x y)). Qed.
Lemma lem6191034 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191035 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term440 _123419 op x) = (term1233 _123419 op x).
Proof. exact (MK_COMB (@lem6191034 _123419) (@lem6191033 _123419 op x)). Qed.
Lemma lem6191036 {_123419 : Type'} (op : type1400 _123419) : (term441 _123419 op) = (term1234 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6191035 _123419 op x)). Qed.
Lemma lem6191037 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191038 {_123419 : Type'} (op : type1400 _123419) : (term442 _123419 op) = (term1235 _123419 op).
Proof. exact (MK_COMB (@lem6191037 _123419) (@lem6191036 _123419 op)). Qed.
Lemma lem6191039 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6191040 {_123419 : Type'} (op : type1400 _123419) : (term443 _123419 op) = (term1236 _123419 op).
Proof. exact (MK_COMB (@lem6191039) (@lem6191038 _123419 op)). Qed.
Lemma lem6191041 {_123419 : Type'} (op : type1400 _123419) : (term444 _123419 op) = (term1237 _123419 op).
Proof. exact (MK_COMB (@lem6191040 _123419 op) (@lem6190960 _123419 op)). Qed.
Lemma lem6191042 {_123419 : Type'} : (@eq _123419) = (@eq _123419).
Proof. exact (eq_refl (@eq _123419)). Qed.
Lemma lem6191049 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191050 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6191049 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6191051 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (op x) = (@I (_123419 -> _123419 -> _123419) op x).
Proof. exact (@lem6191050 _123419 op x). Qed.
Lemma lem6191052 {_123419 : Type'} (y : _123419) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6191053 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (op x y) = (@I (_123419 -> _123419 -> _123419) op x y).
Proof. exact (MK_COMB (@lem6191051 _123419 op x) (@lem6191052 _123419 y)). Qed.
Lemma lem6191055 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191056 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6191055 _123419 _123419 f x). Qed.
Lemma lem6191057 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (@I (_123419 -> _123419 -> _123419) op x y) = (term1218 _123419 op x y).
Proof. exact (@lem6191056 _123419 (@I (_123419 -> _123419 -> _123419) op x) y). Qed.
Lemma lem6191059 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (op x y) = (term1218 _123419 op x y).
Proof. exact (TRANS (@lem6191053 _123419 op x y) (@lem6191057 _123419 op x y)). Qed.
Lemma lem6191066 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191067 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6191066 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6191068 {_123419 : Type'} (op : type1400 _123419) (y : _123419) : (op y) = (@I (_123419 -> _123419 -> _123419) op y).
Proof. exact (@lem6191067 _123419 op y). Qed.
Lemma lem6191069 {_123419 : Type'} (x : _123419) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6191070 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (op y x) = (@I (_123419 -> _123419 -> _123419) op y x).
Proof. exact (MK_COMB (@lem6191068 _123419 op y) (@lem6191069 _123419 x)). Qed.
Lemma lem6191072 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191073 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6191072 _123419 _123419 f x). Qed.
Lemma lem6191074 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (@I (_123419 -> _123419 -> _123419) op y x) = (term1218 _123419 op y x).
Proof. exact (@lem6191073 _123419 (@I (_123419 -> _123419 -> _123419) op y) x). Qed.
Lemma lem6191076 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (op y x) = (term1218 _123419 op y x).
Proof. exact (TRANS (@lem6191070 _123419 op y x) (@lem6191074 _123419 op y x)). Qed.
Lemma lem6191077 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term1238 _123419 op x y) = (term1239 _123419 op x y).
Proof. exact (MK_COMB (@lem6191042 _123419) (@lem6191059 _123419 op x y)). Qed.
Lemma lem6191078 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : ((op x y) = (op y x)) = ((term1218 _123419 op x y) = (term1218 _123419 op y x)).
Proof. exact (MK_COMB (@lem6191077 _123419 op x y) (@lem6191076 _123419 op y x)). Qed.
Lemma lem6191079 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term445 _123419 op x) = (term1240 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6191078 _123419 op y x)). Qed.
Lemma lem6191080 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191081 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term446 _123419 op x) = (term1241 _123419 op x).
Proof. exact (MK_COMB (@lem6191080 _123419) (@lem6191079 _123419 op x)). Qed.
Lemma lem6191082 {_123419 : Type'} (op : type1400 _123419) : (term447 _123419 op) = (term1242 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6191081 _123419 op x)). Qed.
Lemma lem6191083 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191084 {_123419 : Type'} (op : type1400 _123419) : (term448 _123419 op) = (term1243 _123419 op).
Proof. exact (MK_COMB (@lem6191083 _123419) (@lem6191082 _123419 op)). Qed.
Lemma lem6191085 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6191086 {_123419 : Type'} (op : type1400 _123419) : (term449 _123419 op) = (term1244 _123419 op).
Proof. exact (MK_COMB (@lem6191085) (@lem6191084 _123419 op)). Qed.
Lemma lem6191087 {_123419 : Type'} (op : type1400 _123419) : (term450 _123419 op) = (term1245 _123419 op).
Proof. exact (MK_COMB (@lem6191086 _123419 op) (@lem6191041 _123419 op)). Qed.
Lemma lem6191088 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6191093 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191094 {_123419 : Type'} (f : type403 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> Prop) f x).
Proof. exact (@lem6191093 (type1400 _123419) Prop f x). Qed.
Lemma lem6191096 {_123419 : Type'} (op : type1400 _123419) : (@monoidal _123419 op) = (@I ((_123419 -> _123419 -> _123419) -> Prop) (@monoidal _123419) op).
Proof. exact (@lem6191094 _123419 (@monoidal _123419) op). Qed.
Lemma lem6191097 {_123419 : Type'} (op : type1400 _123419) : (term1246 _123419 op) = (term1247 _123419 op).
Proof. exact (MK_COMB (@lem6191088) (@lem6191096 _123419 op)). Qed.
Lemma lem6191098 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6191099 {_123419 : Type'} (op : type1400 _123419) : (term510 _123419 op) = (term1248 _123419 op).
Proof. exact (MK_COMB (@lem6191098) (@lem6191097 _123419 op)). Qed.
Lemma lem6191100 {_123419 : Type'} (op : type1400 _123419) : (term511 _123419 op) = (term1249 _123419 op).
Proof. exact (MK_COMB (@lem6191099 _123419 op) (@lem6191087 _123419 op)). Qed.
Lemma lem6191101 {_123419 : Type'} : (term528 _123419) = (term1250 _123419).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6191100 _123419 op)). Qed.
Lemma lem6191102 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6191103 {_123419 : Type'} : (term543 _123419) = (term1251 _123419).
Proof. exact (MK_COMB (@lem6191102 _123419) (@lem6191101 _123419)). Qed.
Lemma lem6191104 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6191105 {_123419 : Type'} : (@eq _123419) = (@eq _123419).
Proof. exact (eq_refl (@eq _123419)). Qed.
Lemma lem6191106 {_123419 : Type'} (op : type1400 _123419) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6191111 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191112 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6191111 (type1400 _123419) _123419 f x). Qed.
Lemma lem6191114 {_123419 : Type'} (op : type1400 _123419) : (@neutral _123419 op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) (@neutral _123419) op).
Proof. exact (@lem6191112 _123419 (@neutral _123419) op). Qed.
Lemma lem6191119 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191120 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6191119 (type1400 _123419) _123419 f x). Qed.
Lemma lem6191122 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (x op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) x op).
Proof. exact (@lem6191120 _123419 x op). Qed.
Lemma lem6191123 {_123419 : Type'} (op : type1400 _123419) : (term1208 _123419 op) = (term1209 _123419 op).
Proof. exact (MK_COMB (@lem6191106 _123419 op) (@lem6191114 _123419 op)). Qed.
Lemma lem6191124 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (term1252 _123419 x op) = (term1253 _123419 x op).
Proof. exact (MK_COMB (@lem6191123 _123419 op) (@lem6191122 _123419 x op)). Qed.
Lemma lem6191126 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191127 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6191126 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6191128 {_123419 : Type'} (op : type1400 _123419) : (term1209 _123419 op) = (term1211 _123419 op).
Proof. exact (@lem6191127 _123419 op (@I ((_123419 -> _123419 -> _123419) -> _123419) (@neutral _123419) op)). Qed.
Lemma lem6191129 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (@I ((_123419 -> _123419 -> _123419) -> _123419) x op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) x op).
Proof. exact (eq_refl (@I ((_123419 -> _123419 -> _123419) -> _123419) x op)). Qed.
Lemma lem6191130 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (term1253 _123419 x op) = (term1254 _123419 x op).
Proof. exact (MK_COMB (@lem6191128 _123419 op) (@lem6191129 _123419 x op)). Qed.
Lemma lem6191132 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191133 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6191132 _123419 _123419 f x). Qed.
Lemma lem6191134 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (term1254 _123419 x op) = (term1255 _123419 x op).
Proof. exact (@lem6191133 _123419 (term1211 _123419 op) (@I ((_123419 -> _123419 -> _123419) -> _123419) x op)). Qed.
Lemma lem6191135 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (term1253 _123419 x op) = (term1255 _123419 x op).
Proof. exact (TRANS (@lem6191130 _123419 x op) (@lem6191134 _123419 x op)). Qed.
Lemma lem6191136 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (term1252 _123419 x op) = (term1255 _123419 x op).
Proof. exact (TRANS (@lem6191124 _123419 x op) (@lem6191135 _123419 x op)). Qed.
Lemma lem6191141 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191142 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6191141 (type1400 _123419) _123419 f x). Qed.
Lemma lem6191144 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (x op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) x op).
Proof. exact (@lem6191142 _123419 x op). Qed.
Lemma lem6191145 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (term1256 _123419 x op) = (term1257 _123419 x op).
Proof. exact (MK_COMB (@lem6191105 _123419) (@lem6191136 _123419 x op)). Qed.
Lemma lem6191146 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : ((term1252 _123419 x op) = (x op)) = ((term1255 _123419 x op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) x op)).
Proof. exact (MK_COMB (@lem6191145 _123419 x op) (@lem6191144 _123419 x op)). Qed.
Lemma lem6191147 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (term1258 _123419 x op) = (term1259 _123419 x op).
Proof. exact (MK_COMB (@lem6191104) (@lem6191146 _123419 x op)). Qed.
Lemma lem6191148 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6191149 {_123419 : Type'} : (@eq _123419) = (@eq _123419).
Proof. exact (eq_refl (@eq _123419)). Qed.
Lemma lem6191150 {_123419 : Type'} (op : type1400 _123419) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6191155 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191156 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6191155 (type1400 _123419) _123419 f x). Qed.
Lemma lem6191158 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (x op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) x op).
Proof. exact (@lem6191156 _123419 x op). Qed.
Lemma lem6191159 {_123419 : Type'} (op : type1400 _123419) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6191164 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191165 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6191164 (type1400 _123419) _123419 f x). Qed.
Lemma lem6191167 {_123419 : Type'} (y : type402 _123419) (op : type1400 _123419) : (y op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) y op).
Proof. exact (@lem6191165 _123419 y op). Qed.
Lemma lem6191172 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191173 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6191172 (type1400 _123419) _123419 f x). Qed.
Lemma lem6191175 {_123419 : Type'} (z : type402 _123419) (op : type1400 _123419) : (z op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) z op).
Proof. exact (@lem6191173 _123419 z op). Qed.
Lemma lem6191176 {_123419 : Type'} (y : type402 _123419) (op : type1400 _123419) : (term1260 _123419 y op) = (term1261 _123419 y op).
Proof. exact (MK_COMB (@lem6191159 _123419 op) (@lem6191167 _123419 y op)). Qed.
Lemma lem6191177 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (op : type1400 _123419) : (term1262 _123419 y z op) = (term1263 _123419 y z op).
Proof. exact (MK_COMB (@lem6191176 _123419 y op) (@lem6191175 _123419 z op)). Qed.
Lemma lem6191179 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191180 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6191179 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6191181 {_123419 : Type'} (y : type402 _123419) (op : type1400 _123419) : (term1261 _123419 y op) = (term1264 _123419 y op).
Proof. exact (@lem6191180 _123419 op (@I ((_123419 -> _123419 -> _123419) -> _123419) y op)). Qed.
Lemma lem6191182 {_123419 : Type'} (z : type402 _123419) (op : type1400 _123419) : (@I ((_123419 -> _123419 -> _123419) -> _123419) z op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) z op).
Proof. exact (eq_refl (@I ((_123419 -> _123419 -> _123419) -> _123419) z op)). Qed.
Lemma lem6191183 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (op : type1400 _123419) : (term1263 _123419 y z op) = (term1265 _123419 y z op).
Proof. exact (MK_COMB (@lem6191181 _123419 y op) (@lem6191182 _123419 z op)). Qed.
Lemma lem6191185 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191186 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6191185 _123419 _123419 f x). Qed.
Lemma lem6191187 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (op : type1400 _123419) : (term1265 _123419 y z op) = (term1266 _123419 y z op).
Proof. exact (@lem6191186 _123419 (term1264 _123419 y op) (@I ((_123419 -> _123419 -> _123419) -> _123419) z op)). Qed.
Lemma lem6191188 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (op : type1400 _123419) : (term1263 _123419 y z op) = (term1266 _123419 y z op).
Proof. exact (TRANS (@lem6191183 _123419 y z op) (@lem6191187 _123419 y z op)). Qed.
Lemma lem6191189 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (op : type1400 _123419) : (term1262 _123419 y z op) = (term1266 _123419 y z op).
Proof. exact (TRANS (@lem6191177 _123419 y z op) (@lem6191188 _123419 y z op)). Qed.
Lemma lem6191190 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (term1260 _123419 x op) = (term1261 _123419 x op).
Proof. exact (MK_COMB (@lem6191150 _123419 op) (@lem6191158 _123419 x op)). Qed.
Lemma lem6191191 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (z : type402 _123419) (op : type1400 _123419) : (term1267 _123419 x y z op) = (term1268 _123419 x y z op).
Proof. exact (MK_COMB (@lem6191190 _123419 x op) (@lem6191189 _123419 y z op)). Qed.
Lemma lem6191193 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191194 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6191193 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6191195 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (term1261 _123419 x op) = (term1264 _123419 x op).
Proof. exact (@lem6191194 _123419 op (@I ((_123419 -> _123419 -> _123419) -> _123419) x op)). Qed.
Lemma lem6191196 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (op : type1400 _123419) : (term1266 _123419 y z op) = (term1266 _123419 y z op).
Proof. exact (eq_refl (term1266 _123419 y z op)). Qed.
Lemma lem6191197 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (z : type402 _123419) (op : type1400 _123419) : (term1268 _123419 x y z op) = (term1269 _123419 x y z op).
Proof. exact (MK_COMB (@lem6191195 _123419 x op) (@lem6191196 _123419 y z op)). Qed.
Lemma lem6191199 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191200 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6191199 _123419 _123419 f x). Qed.
Lemma lem6191201 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (z : type402 _123419) (op : type1400 _123419) : (term1269 _123419 x y z op) = (term1270 _123419 x y z op).
Proof. exact (@lem6191200 _123419 (term1264 _123419 x op) (term1266 _123419 y z op)). Qed.
Lemma lem6191202 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (z : type402 _123419) (op : type1400 _123419) : (term1268 _123419 x y z op) = (term1270 _123419 x y z op).
Proof. exact (TRANS (@lem6191197 _123419 x y z op) (@lem6191201 _123419 x y z op)). Qed.
Lemma lem6191203 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (z : type402 _123419) (op : type1400 _123419) : (term1267 _123419 x y z op) = (term1270 _123419 x y z op).
Proof. exact (TRANS (@lem6191191 _123419 x y z op) (@lem6191202 _123419 x y z op)). Qed.
Lemma lem6191204 {_123419 : Type'} (op : type1400 _123419) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6191205 {_123419 : Type'} (op : type1400 _123419) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6191210 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191211 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6191210 (type1400 _123419) _123419 f x). Qed.
Lemma lem6191213 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (x op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) x op).
Proof. exact (@lem6191211 _123419 x op). Qed.
Lemma lem6191218 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191219 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6191218 (type1400 _123419) _123419 f x). Qed.
Lemma lem6191221 {_123419 : Type'} (y : type402 _123419) (op : type1400 _123419) : (y op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) y op).
Proof. exact (@lem6191219 _123419 y op). Qed.
Lemma lem6191222 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (term1260 _123419 x op) = (term1261 _123419 x op).
Proof. exact (MK_COMB (@lem6191205 _123419 op) (@lem6191213 _123419 x op)). Qed.
Lemma lem6191223 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (op : type1400 _123419) : (term1262 _123419 x y op) = (term1263 _123419 x y op).
Proof. exact (MK_COMB (@lem6191222 _123419 x op) (@lem6191221 _123419 y op)). Qed.
Lemma lem6191225 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191226 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6191225 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6191227 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (term1261 _123419 x op) = (term1264 _123419 x op).
Proof. exact (@lem6191226 _123419 op (@I ((_123419 -> _123419 -> _123419) -> _123419) x op)). Qed.
Lemma lem6191228 {_123419 : Type'} (y : type402 _123419) (op : type1400 _123419) : (@I ((_123419 -> _123419 -> _123419) -> _123419) y op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) y op).
Proof. exact (eq_refl (@I ((_123419 -> _123419 -> _123419) -> _123419) y op)). Qed.
Lemma lem6191229 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (op : type1400 _123419) : (term1263 _123419 x y op) = (term1265 _123419 x y op).
Proof. exact (MK_COMB (@lem6191227 _123419 x op) (@lem6191228 _123419 y op)). Qed.
Lemma lem6191231 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191232 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6191231 _123419 _123419 f x). Qed.
Lemma lem6191233 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (op : type1400 _123419) : (term1265 _123419 x y op) = (term1266 _123419 x y op).
Proof. exact (@lem6191232 _123419 (term1264 _123419 x op) (@I ((_123419 -> _123419 -> _123419) -> _123419) y op)). Qed.
Lemma lem6191234 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (op : type1400 _123419) : (term1263 _123419 x y op) = (term1266 _123419 x y op).
Proof. exact (TRANS (@lem6191229 _123419 x y op) (@lem6191233 _123419 x y op)). Qed.
Lemma lem6191235 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (op : type1400 _123419) : (term1262 _123419 x y op) = (term1266 _123419 x y op).
Proof. exact (TRANS (@lem6191223 _123419 x y op) (@lem6191234 _123419 x y op)). Qed.
Lemma lem6191240 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191241 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6191240 (type1400 _123419) _123419 f x). Qed.
Lemma lem6191243 {_123419 : Type'} (z : type402 _123419) (op : type1400 _123419) : (z op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) z op).
Proof. exact (@lem6191241 _123419 z op). Qed.
Lemma lem6191244 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (op : type1400 _123419) : (term1271 _123419 x y op) = (term1272 _123419 x y op).
Proof. exact (MK_COMB (@lem6191204 _123419 op) (@lem6191235 _123419 x y op)). Qed.
Lemma lem6191245 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (z : type402 _123419) (op : type1400 _123419) : (term1273 _123419 x y z op) = (term1274 _123419 x y z op).
Proof. exact (MK_COMB (@lem6191244 _123419 x y op) (@lem6191243 _123419 z op)). Qed.
Lemma lem6191247 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191248 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6191247 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6191249 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (op : type1400 _123419) : (term1272 _123419 x y op) = (term1275 _123419 x y op).
Proof. exact (@lem6191248 _123419 op (term1266 _123419 x y op)). Qed.
Lemma lem6191250 {_123419 : Type'} (z : type402 _123419) (op : type1400 _123419) : (@I ((_123419 -> _123419 -> _123419) -> _123419) z op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) z op).
Proof. exact (eq_refl (@I ((_123419 -> _123419 -> _123419) -> _123419) z op)). Qed.
Lemma lem6191251 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (z : type402 _123419) (op : type1400 _123419) : (term1274 _123419 x y z op) = (term1276 _123419 x y z op).
Proof. exact (MK_COMB (@lem6191249 _123419 x y op) (@lem6191250 _123419 z op)). Qed.
Lemma lem6191253 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191254 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6191253 _123419 _123419 f x). Qed.
Lemma lem6191255 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (z : type402 _123419) (op : type1400 _123419) : (term1276 _123419 x y z op) = (term1277 _123419 x y z op).
Proof. exact (@lem6191254 _123419 (term1275 _123419 x y op) (@I ((_123419 -> _123419 -> _123419) -> _123419) z op)). Qed.
Lemma lem6191256 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (z : type402 _123419) (op : type1400 _123419) : (term1274 _123419 x y z op) = (term1277 _123419 x y z op).
Proof. exact (TRANS (@lem6191251 _123419 x y z op) (@lem6191255 _123419 x y z op)). Qed.
Lemma lem6191257 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (z : type402 _123419) (op : type1400 _123419) : (term1273 _123419 x y z op) = (term1277 _123419 x y z op).
Proof. exact (TRANS (@lem6191245 _123419 x y z op) (@lem6191256 _123419 x y z op)). Qed.
Lemma lem6191258 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (z : type402 _123419) (op : type1400 _123419) : (term1278 _123419 x y z op) = (term1279 _123419 x y z op).
Proof. exact (MK_COMB (@lem6191149 _123419) (@lem6191203 _123419 x y z op)). Qed.
Lemma lem6191259 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (z : type402 _123419) (op : type1400 _123419) : ((term1267 _123419 x y z op) = (term1273 _123419 x y z op)) = ((term1270 _123419 x y z op) = (term1277 _123419 x y z op)).
Proof. exact (MK_COMB (@lem6191258 _123419 x y z op) (@lem6191257 _123419 x y z op)). Qed.
Lemma lem6191260 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (z : type402 _123419) (op : type1400 _123419) : (term1280 _123419 x y z op) = (term1281 _123419 x y z op).
Proof. exact (MK_COMB (@lem6191148) (@lem6191259 _123419 x y z op)). Qed.
Lemma lem6191261 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6191262 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (z : type402 _123419) (op : type1400 _123419) : (term1282 _123419 x y z op) = (term1283 _123419 x y z op).
Proof. exact (MK_COMB (@lem6191261) (@lem6191260 _123419 x y z op)). Qed.
Lemma lem6191263 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (op : type1400 _123419) : (term1284 _123419 y z x op) = (term1285 _123419 y z x op).
Proof. exact (MK_COMB (@lem6191262 _123419 x y z op) (@lem6191147 _123419 x op)). Qed.
Lemma lem6191264 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6191265 {_123419 : Type'} : (@eq _123419) = (@eq _123419).
Proof. exact (eq_refl (@eq _123419)). Qed.
Lemma lem6191266 {_123419 : Type'} (op : type1400 _123419) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6191271 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191272 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6191271 (type1400 _123419) _123419 f x). Qed.
Lemma lem6191274 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (x op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) x op).
Proof. exact (@lem6191272 _123419 x op). Qed.
Lemma lem6191279 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191280 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6191279 (type1400 _123419) _123419 f x). Qed.
Lemma lem6191282 {_123419 : Type'} (y : type402 _123419) (op : type1400 _123419) : (y op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) y op).
Proof. exact (@lem6191280 _123419 y op). Qed.
Lemma lem6191283 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (term1260 _123419 x op) = (term1261 _123419 x op).
Proof. exact (MK_COMB (@lem6191266 _123419 op) (@lem6191274 _123419 x op)). Qed.
Lemma lem6191284 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (op : type1400 _123419) : (term1262 _123419 x y op) = (term1263 _123419 x y op).
Proof. exact (MK_COMB (@lem6191283 _123419 x op) (@lem6191282 _123419 y op)). Qed.
Lemma lem6191286 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191287 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6191286 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6191288 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (term1261 _123419 x op) = (term1264 _123419 x op).
Proof. exact (@lem6191287 _123419 op (@I ((_123419 -> _123419 -> _123419) -> _123419) x op)). Qed.
Lemma lem6191289 {_123419 : Type'} (y : type402 _123419) (op : type1400 _123419) : (@I ((_123419 -> _123419 -> _123419) -> _123419) y op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) y op).
Proof. exact (eq_refl (@I ((_123419 -> _123419 -> _123419) -> _123419) y op)). Qed.
Lemma lem6191290 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (op : type1400 _123419) : (term1263 _123419 x y op) = (term1265 _123419 x y op).
Proof. exact (MK_COMB (@lem6191288 _123419 x op) (@lem6191289 _123419 y op)). Qed.
Lemma lem6191292 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191293 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6191292 _123419 _123419 f x). Qed.
Lemma lem6191294 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (op : type1400 _123419) : (term1265 _123419 x y op) = (term1266 _123419 x y op).
Proof. exact (@lem6191293 _123419 (term1264 _123419 x op) (@I ((_123419 -> _123419 -> _123419) -> _123419) y op)). Qed.
Lemma lem6191295 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (op : type1400 _123419) : (term1263 _123419 x y op) = (term1266 _123419 x y op).
Proof. exact (TRANS (@lem6191290 _123419 x y op) (@lem6191294 _123419 x y op)). Qed.
Lemma lem6191296 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (op : type1400 _123419) : (term1262 _123419 x y op) = (term1266 _123419 x y op).
Proof. exact (TRANS (@lem6191284 _123419 x y op) (@lem6191295 _123419 x y op)). Qed.
Lemma lem6191297 {_123419 : Type'} (op : type1400 _123419) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6191302 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191303 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6191302 (type1400 _123419) _123419 f x). Qed.
Lemma lem6191305 {_123419 : Type'} (y : type402 _123419) (op : type1400 _123419) : (y op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) y op).
Proof. exact (@lem6191303 _123419 y op). Qed.
Lemma lem6191310 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191311 {_123419 : Type'} (f : type402 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> _123419) f x).
Proof. exact (@lem6191310 (type1400 _123419) _123419 f x). Qed.
Lemma lem6191313 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (x op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) x op).
Proof. exact (@lem6191311 _123419 x op). Qed.
Lemma lem6191314 {_123419 : Type'} (y : type402 _123419) (op : type1400 _123419) : (term1260 _123419 y op) = (term1261 _123419 y op).
Proof. exact (MK_COMB (@lem6191297 _123419 op) (@lem6191305 _123419 y op)). Qed.
Lemma lem6191315 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) (op : type1400 _123419) : (term1262 _123419 y x op) = (term1263 _123419 y x op).
Proof. exact (MK_COMB (@lem6191314 _123419 y op) (@lem6191313 _123419 x op)). Qed.
Lemma lem6191317 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191318 {_123419 : Type'} (f : type1400 _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419 -> _123419) f x).
Proof. exact (@lem6191317 _123419 (_123419 -> _123419) f x). Qed.
Lemma lem6191319 {_123419 : Type'} (y : type402 _123419) (op : type1400 _123419) : (term1261 _123419 y op) = (term1264 _123419 y op).
Proof. exact (@lem6191318 _123419 op (@I ((_123419 -> _123419 -> _123419) -> _123419) y op)). Qed.
Lemma lem6191320 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) : (@I ((_123419 -> _123419 -> _123419) -> _123419) x op) = (@I ((_123419 -> _123419 -> _123419) -> _123419) x op).
Proof. exact (eq_refl (@I ((_123419 -> _123419 -> _123419) -> _123419) x op)). Qed.
Lemma lem6191321 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) (op : type1400 _123419) : (term1263 _123419 y x op) = (term1265 _123419 y x op).
Proof. exact (MK_COMB (@lem6191319 _123419 y op) (@lem6191320 _123419 x op)). Qed.
Lemma lem6191323 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191324 {_123419 : Type'} (f : _123419 -> _123419) (x : _123419) : (f x) = (@I (_123419 -> _123419) f x).
Proof. exact (@lem6191323 _123419 _123419 f x). Qed.
Lemma lem6191325 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) (op : type1400 _123419) : (term1265 _123419 y x op) = (term1266 _123419 y x op).
Proof. exact (@lem6191324 _123419 (term1264 _123419 y op) (@I ((_123419 -> _123419 -> _123419) -> _123419) x op)). Qed.
Lemma lem6191326 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) (op : type1400 _123419) : (term1263 _123419 y x op) = (term1266 _123419 y x op).
Proof. exact (TRANS (@lem6191321 _123419 y x op) (@lem6191325 _123419 y x op)). Qed.
Lemma lem6191327 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) (op : type1400 _123419) : (term1262 _123419 y x op) = (term1266 _123419 y x op).
Proof. exact (TRANS (@lem6191315 _123419 y x op) (@lem6191326 _123419 y x op)). Qed.
Lemma lem6191328 {_123419 : Type'} (x : type402 _123419) (y : type402 _123419) (op : type1400 _123419) : (term1286 _123419 x y op) = (term1287 _123419 x y op).
Proof. exact (MK_COMB (@lem6191265 _123419) (@lem6191296 _123419 x y op)). Qed.
Lemma lem6191329 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) (op : type1400 _123419) : ((term1262 _123419 x y op) = (term1262 _123419 y x op)) = ((term1266 _123419 x y op) = (term1266 _123419 y x op)).
Proof. exact (MK_COMB (@lem6191328 _123419 x y op) (@lem6191327 _123419 y x op)). Qed.
Lemma lem6191330 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) (op : type1400 _123419) : (term1288 _123419 y x op) = (term1289 _123419 y x op).
Proof. exact (MK_COMB (@lem6191264) (@lem6191329 _123419 y x op)). Qed.
Lemma lem6191331 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6191332 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) (op : type1400 _123419) : (term1290 _123419 y x op) = (term1291 _123419 y x op).
Proof. exact (MK_COMB (@lem6191331) (@lem6191330 _123419 y x op)). Qed.
Lemma lem6191333 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (op : type1400 _123419) : (term1292 _123419 y z x op) = (term1293 _123419 y z x op).
Proof. exact (MK_COMB (@lem6191332 _123419 y x op) (@lem6191263 _123419 y z x op)). Qed.
Lemma lem6191338 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6191339 {_123419 : Type'} (f : type403 _123419) (x : type1400 _123419) : (f x) = (@I ((_123419 -> _123419 -> _123419) -> Prop) f x).
Proof. exact (@lem6191338 (type1400 _123419) Prop f x). Qed.
Lemma lem6191341 {_123419 : Type'} (op : type1400 _123419) : (@monoidal _123419 op) = (@I ((_123419 -> _123419 -> _123419) -> Prop) (@monoidal _123419) op).
Proof. exact (@lem6191339 _123419 (@monoidal _123419) op). Qed.
Lemma lem6191342 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6191343 {_123419 : Type'} (op : type1400 _123419) : (term512 _123419 op) = (term1294 _123419 op).
Proof. exact (MK_COMB (@lem6191342) (@lem6191341 _123419 op)). Qed.
Lemma lem6191344 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (op : type1400 _123419) : (term762 _123419 y z x op) = (term1295 _123419 y z x op).
Proof. exact (MK_COMB (@lem6191343 _123419 op) (@lem6191333 _123419 y z x op)). Qed.
Lemma lem6191345 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) : (term764 _123419 y z x) = (term1296 _123419 y z x).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6191344 _123419 y z x op)). Qed.
Lemma lem6191346 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6191347 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) : (term766 _123419 y z x) = (term1297 _123419 y z x).
Proof. exact (MK_COMB (@lem6191346 _123419) (@lem6191345 _123419 y z x)). Qed.
Lemma lem6191348 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6191349 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) : (term819 _123419 y z x) = (term1298 _123419 y z x).
Proof. exact (MK_COMB (@lem6191348) (@lem6191347 _123419 y z x)). Qed.
Lemma lem6191350 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) : (term821 _123419 y z x) = (term1299 _123419 y z x).
Proof. exact (MK_COMB (@lem6191349 _123419 y z x) (@lem6191103 _123419)). Qed.
Lemma lem6191351 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (h1 : term821 _123419 y z x) : term1299 _123419 y z x.
Proof. exact (EQ_MP (@lem6191350 _123419 y z x) (@lem6190745 _123419 y z x h1)). Qed.
Lemma lem6191352 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (h1 : term821 _123419 y z x) : term1251 _123419.
Proof. exact (proj2 (@lem6191351 _123419 y z x h1)). Qed.
Lemma lem6191392 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term522 A P Q) = (term521 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6191393 {_123419 : Type'} (P : _123419 -> Prop) (Q : _123419 -> Prop) : (term522 _123419 P Q) = (term521 _123419 P Q).
Proof. exact (@lem6191392 _123419 P Q). Qed.
Lemma lem6191394 {_123419 : Type'} (op : type1400 _123419) : (term1300 _123419 op) = (term1301 _123419 op).
Proof. exact (@lem6191393 _123419 (term1234 _123419 op) (term1216 _123419 op)). Qed.
Lemma lem6191395 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1302 _123419 op x) = (term1233 _123419 op x).
Proof. exact (eq_refl (term1302 _123419 op x)). Qed.
Lemma lem6191396 {_123419 : Type'} (op : type1400 _123419) : (term1303 _123419 op) = (term1234 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6191395 _123419 op x)). Qed.
Lemma lem6191397 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191398 {_123419 : Type'} (op : type1400 _123419) : (term1304 _123419 op) = (term1235 _123419 op).
Proof. exact (MK_COMB (@lem6191397 _123419) (@lem6191396 _123419 op)). Qed.
Lemma lem6191399 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6191400 {_123419 : Type'} (op : type1400 _123419) : (term1305 _123419 op) = (term1236 _123419 op).
Proof. exact (MK_COMB (@lem6191399) (@lem6191398 _123419 op)). Qed.
Lemma lem6191401 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1306 _123419 op x) = ((term1213 _123419 op x) = x).
Proof. exact (eq_refl (term1306 _123419 op x)). Qed.
Lemma lem6191402 {_123419 : Type'} (op : type1400 _123419) : (term1307 _123419 op) = (term1216 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6191401 _123419 op x)). Qed.
Lemma lem6191403 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191404 {_123419 : Type'} (op : type1400 _123419) : (term1308 _123419 op) = (term1217 _123419 op).
Proof. exact (MK_COMB (@lem6191403 _123419) (@lem6191402 _123419 op)). Qed.
Lemma lem6191405 {_123419 : Type'} (op : type1400 _123419) : (term1300 _123419 op) = (term1237 _123419 op).
Proof. exact (MK_COMB (@lem6191400 _123419 op) (@lem6191404 _123419 op)). Qed.
Lemma lem6191406 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6191407 {_123419 : Type'} (op : type1400 _123419) : (term1309 _123419 op) = (term1310 _123419 op).
Proof. exact (MK_COMB (@lem6191406) (@lem6191405 _123419 op)). Qed.
Lemma lem6191408 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1302 _123419 op x) = (term1233 _123419 op x).
Proof. exact (eq_refl (term1302 _123419 op x)). Qed.
Lemma lem6191409 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6191410 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1311 _123419 op x) = (term1312 _123419 op x).
Proof. exact (MK_COMB (@lem6191409) (@lem6191408 _123419 op x)). Qed.
Lemma lem6191411 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1306 _123419 op x) = ((term1213 _123419 op x) = x).
Proof. exact (eq_refl (term1306 _123419 op x)). Qed.
Lemma lem6191412 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1313 _123419 op x) = (term1314 _123419 op x).
Proof. exact (MK_COMB (@lem6191410 _123419 op x) (@lem6191411 _123419 op x)). Qed.
Lemma lem6191413 {_123419 : Type'} (op : type1400 _123419) : (term1315 _123419 op) = (term1316 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6191412 _123419 op x)). Qed.
Lemma lem6191414 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191415 {_123419 : Type'} (op : type1400 _123419) : (term1301 _123419 op) = (term1317 _123419 op).
Proof. exact (MK_COMB (@lem6191414 _123419) (@lem6191413 _123419 op)). Qed.
Lemma lem6191416 {_123419 : Type'} (op : type1400 _123419) : ((term1300 _123419 op) = (term1301 _123419 op)) = ((term1237 _123419 op) = (term1317 _123419 op)).
Proof. exact (MK_COMB (@lem6191407 _123419 op) (@lem6191415 _123419 op)). Qed.
Lemma lem6191417 {_123419 : Type'} (op : type1400 _123419) : (term1237 _123419 op) = (term1317 _123419 op).
Proof. exact (EQ_MP (@lem6191416 _123419 op) (@lem6191394 _123419 op)). Qed.
Lemma lem6191419 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1318 A P Q) = (term1319 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem6191420 {_123419 : Type'} (P : _123419 -> Prop) (Q : Prop) : (term1318 _123419 P Q) = (term1319 _123419 P Q).
Proof. exact (@lem6191419 _123419 P Q). Qed.
Lemma lem6191421 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1320 _123419 op x) = (term1321 _123419 op x).
Proof. exact (@lem6191420 _123419 (term1232 _123419 op x) ((term1213 _123419 op x) = x)). Qed.
Lemma lem6191422 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term1322 _123419 op x y) = (term1231 _123419 op x y).
Proof. exact (eq_refl (term1322 _123419 op x y)). Qed.
Lemma lem6191423 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1323 _123419 op x) = (term1232 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6191422 _123419 op x y)). Qed.
Lemma lem6191424 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191425 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1324 _123419 op x) = (term1233 _123419 op x).
Proof. exact (MK_COMB (@lem6191424 _123419) (@lem6191423 _123419 op x)). Qed.
Lemma lem6191426 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6191427 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1325 _123419 op x) = (term1312 _123419 op x).
Proof. exact (MK_COMB (@lem6191426) (@lem6191425 _123419 op x)). Qed.
Lemma lem6191428 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : ((term1213 _123419 op x) = x) = ((term1213 _123419 op x) = x).
Proof. exact (eq_refl ((term1213 _123419 op x) = x)). Qed.
Lemma lem6191429 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1320 _123419 op x) = (term1314 _123419 op x).
Proof. exact (MK_COMB (@lem6191427 _123419 op x) (@lem6191428 _123419 op x)). Qed.
Lemma lem6191430 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6191431 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1326 _123419 op x) = (term1327 _123419 op x).
Proof. exact (MK_COMB (@lem6191430) (@lem6191429 _123419 op x)). Qed.
Lemma lem6191432 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term1322 _123419 op x y) = (term1231 _123419 op x y).
Proof. exact (eq_refl (term1322 _123419 op x y)). Qed.
Lemma lem6191433 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6191434 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term1328 _123419 op x y) = (term1329 _123419 op x y).
Proof. exact (MK_COMB (@lem6191433) (@lem6191432 _123419 op x y)). Qed.
Lemma lem6191435 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : ((term1213 _123419 op x) = x) = ((term1213 _123419 op x) = x).
Proof. exact (eq_refl ((term1213 _123419 op x) = x)). Qed.
Lemma lem6191436 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1330 _123419 y op x) = (term1331 _123419 y op x).
Proof. exact (MK_COMB (@lem6191434 _123419 op x y) (@lem6191435 _123419 op x)). Qed.
Lemma lem6191437 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1332 _123419 op x) = (term1333 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6191436 _123419 y op x)). Qed.
Lemma lem6191438 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191439 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1321 _123419 op x) = (term1334 _123419 op x).
Proof. exact (MK_COMB (@lem6191438 _123419) (@lem6191437 _123419 op x)). Qed.
Lemma lem6191440 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : ((term1320 _123419 op x) = (term1321 _123419 op x)) = ((term1314 _123419 op x) = (term1334 _123419 op x)).
Proof. exact (MK_COMB (@lem6191431 _123419 op x) (@lem6191439 _123419 op x)). Qed.
Lemma lem6191441 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1314 _123419 op x) = (term1334 _123419 op x).
Proof. exact (EQ_MP (@lem6191440 _123419 op x) (@lem6191421 _123419 op x)). Qed.
Lemma lem6191443 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1318 A P Q) = (term1319 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem6191444 {_123419 : Type'} (P : _123419 -> Prop) (Q : Prop) : (term1318 _123419 P Q) = (term1319 _123419 P Q).
Proof. exact (@lem6191443 _123419 P Q). Qed.
Lemma lem6191445 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1335 _123419 y op x) = (term1336 _123419 y op x).
Proof. exact (@lem6191444 _123419 (term1230 _123419 op x y) ((term1213 _123419 op x) = x)). Qed.
Lemma lem6191446 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : (term1337 _123419 op x y z) = ((term1221 _123419 x op y z) = (term1227 _123419 op x y z)).
Proof. exact (eq_refl (term1337 _123419 op x y z)). Qed.
Lemma lem6191447 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term1338 _123419 op x y) = (term1230 _123419 op x y).
Proof. exact (fun_ext (fun z : _123419 => @lem6191446 _123419 op x y z)). Qed.
Lemma lem6191448 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191449 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term1339 _123419 op x y) = (term1231 _123419 op x y).
Proof. exact (MK_COMB (@lem6191448 _123419) (@lem6191447 _123419 op x y)). Qed.
Lemma lem6191450 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6191451 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) : (term1340 _123419 op x y) = (term1329 _123419 op x y).
Proof. exact (MK_COMB (@lem6191450) (@lem6191449 _123419 op x y)). Qed.
Lemma lem6191452 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : ((term1213 _123419 op x) = x) = ((term1213 _123419 op x) = x).
Proof. exact (eq_refl ((term1213 _123419 op x) = x)). Qed.
Lemma lem6191453 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1335 _123419 y op x) = (term1331 _123419 y op x).
Proof. exact (MK_COMB (@lem6191451 _123419 op x y) (@lem6191452 _123419 op x)). Qed.
Lemma lem6191454 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6191455 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1341 _123419 y op x) = (term1342 _123419 y op x).
Proof. exact (MK_COMB (@lem6191454) (@lem6191453 _123419 y op x)). Qed.
Lemma lem6191456 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : (term1337 _123419 op x y z) = ((term1221 _123419 x op y z) = (term1227 _123419 op x y z)).
Proof. exact (eq_refl (term1337 _123419 op x y z)). Qed.
Lemma lem6191457 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6191458 {_123419 : Type'} (op : type1400 _123419) (x : _123419) (y : _123419) (z : _123419) : (term1343 _123419 op x y z) = (term1344 _123419 op x y z).
Proof. exact (MK_COMB (@lem6191457) (@lem6191456 _123419 op x y z)). Qed.
Lemma lem6191459 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : ((term1213 _123419 op x) = x) = ((term1213 _123419 op x) = x).
Proof. exact (eq_refl ((term1213 _123419 op x) = x)). Qed.
Lemma lem6191460 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term1345 _123419 y z op x) = (term1346 _123419 y z op x).
Proof. exact (MK_COMB (@lem6191458 _123419 op x y z) (@lem6191459 _123419 op x)). Qed.
Lemma lem6191461 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1347 _123419 y op x) = (term1348 _123419 y op x).
Proof. exact (fun_ext (fun z : _123419 => @lem6191460 _123419 y z op x)). Qed.
Lemma lem6191462 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191463 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1336 _123419 y op x) = (term1349 _123419 y op x).
Proof. exact (MK_COMB (@lem6191462 _123419) (@lem6191461 _123419 y op x)). Qed.
Lemma lem6191464 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : ((term1335 _123419 y op x) = (term1336 _123419 y op x)) = ((term1331 _123419 y op x) = (term1349 _123419 y op x)).
Proof. exact (MK_COMB (@lem6191455 _123419 y op x) (@lem6191463 _123419 y op x)). Qed.
Lemma lem6191465 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1331 _123419 y op x) = (term1349 _123419 y op x).
Proof. exact (EQ_MP (@lem6191464 _123419 y op x) (@lem6191445 _123419 y op x)). Qed.
Lemma lem6191466 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1333 _123419 op x) = (term1350 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6191465 _123419 y op x)). Qed.
Lemma lem6191467 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191468 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1334 _123419 op x) = (term1351 _123419 op x).
Proof. exact (MK_COMB (@lem6191467 _123419) (@lem6191466 _123419 op x)). Qed.
Lemma lem6191469 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1314 _123419 op x) = (term1351 _123419 op x).
Proof. exact (TRANS (@lem6191441 _123419 op x) (@lem6191468 _123419 op x)). Qed.
Lemma lem6191470 {_123419 : Type'} (op : type1400 _123419) : (term1316 _123419 op) = (term1352 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6191469 _123419 op x)). Qed.
Lemma lem6191471 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191472 {_123419 : Type'} (op : type1400 _123419) : (term1317 _123419 op) = (term1353 _123419 op).
Proof. exact (MK_COMB (@lem6191471 _123419) (@lem6191470 _123419 op)). Qed.
Lemma lem6191473 {_123419 : Type'} (op : type1400 _123419) : (term1237 _123419 op) = (term1353 _123419 op).
Proof. exact (TRANS (@lem6191417 _123419 op) (@lem6191472 _123419 op)). Qed.
Lemma lem6191474 {_123419 : Type'} (op : type1400 _123419) : (term1244 _123419 op) = (term1244 _123419 op).
Proof. exact (eq_refl (term1244 _123419 op)). Qed.
Lemma lem6191475 {_123419 : Type'} (op : type1400 _123419) : (term1245 _123419 op) = (term1354 _123419 op).
Proof. exact (MK_COMB (@lem6191474 _123419 op) (@lem6191473 _123419 op)). Qed.
Lemma lem6191477 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term522 A P Q) = (term521 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6191478 {_123419 : Type'} (P : _123419 -> Prop) (Q : _123419 -> Prop) : (term522 _123419 P Q) = (term521 _123419 P Q).
Proof. exact (@lem6191477 _123419 P Q). Qed.
Lemma lem6191479 {_123419 : Type'} (op : type1400 _123419) : (term1355 _123419 op) = (term1356 _123419 op).
Proof. exact (@lem6191478 _123419 (term1242 _123419 op) (term1352 _123419 op)). Qed.
Lemma lem6191480 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1357 _123419 op x) = (term1241 _123419 op x).
Proof. exact (eq_refl (term1357 _123419 op x)). Qed.
Lemma lem6191481 {_123419 : Type'} (op : type1400 _123419) : (term1358 _123419 op) = (term1242 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6191480 _123419 op x)). Qed.
Lemma lem6191482 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191483 {_123419 : Type'} (op : type1400 _123419) : (term1359 _123419 op) = (term1243 _123419 op).
Proof. exact (MK_COMB (@lem6191482 _123419) (@lem6191481 _123419 op)). Qed.
Lemma lem6191484 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6191485 {_123419 : Type'} (op : type1400 _123419) : (term1360 _123419 op) = (term1244 _123419 op).
Proof. exact (MK_COMB (@lem6191484) (@lem6191483 _123419 op)). Qed.
Lemma lem6191486 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1361 _123419 op x) = (term1351 _123419 op x).
Proof. exact (eq_refl (term1361 _123419 op x)). Qed.
Lemma lem6191487 {_123419 : Type'} (op : type1400 _123419) : (term1362 _123419 op) = (term1352 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6191486 _123419 op x)). Qed.
Lemma lem6191488 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191489 {_123419 : Type'} (op : type1400 _123419) : (term1363 _123419 op) = (term1353 _123419 op).
Proof. exact (MK_COMB (@lem6191488 _123419) (@lem6191487 _123419 op)). Qed.
Lemma lem6191490 {_123419 : Type'} (op : type1400 _123419) : (term1355 _123419 op) = (term1354 _123419 op).
Proof. exact (MK_COMB (@lem6191485 _123419 op) (@lem6191489 _123419 op)). Qed.
Lemma lem6191491 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6191492 {_123419 : Type'} (op : type1400 _123419) : (term1364 _123419 op) = (term1365 _123419 op).
Proof. exact (MK_COMB (@lem6191491) (@lem6191490 _123419 op)). Qed.
Lemma lem6191493 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1357 _123419 op x) = (term1241 _123419 op x).
Proof. exact (eq_refl (term1357 _123419 op x)). Qed.
Lemma lem6191494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6191495 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1366 _123419 op x) = (term1367 _123419 op x).
Proof. exact (MK_COMB (@lem6191494) (@lem6191493 _123419 op x)). Qed.
Lemma lem6191496 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1361 _123419 op x) = (term1351 _123419 op x).
Proof. exact (eq_refl (term1361 _123419 op x)). Qed.
Lemma lem6191497 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1368 _123419 op x) = (term1369 _123419 op x).
Proof. exact (MK_COMB (@lem6191495 _123419 op x) (@lem6191496 _123419 op x)). Qed.
Lemma lem6191498 {_123419 : Type'} (op : type1400 _123419) : (term1370 _123419 op) = (term1371 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6191497 _123419 op x)). Qed.
Lemma lem6191499 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191500 {_123419 : Type'} (op : type1400 _123419) : (term1356 _123419 op) = (term1372 _123419 op).
Proof. exact (MK_COMB (@lem6191499 _123419) (@lem6191498 _123419 op)). Qed.
Lemma lem6191501 {_123419 : Type'} (op : type1400 _123419) : ((term1355 _123419 op) = (term1356 _123419 op)) = ((term1354 _123419 op) = (term1372 _123419 op)).
Proof. exact (MK_COMB (@lem6191492 _123419 op) (@lem6191500 _123419 op)). Qed.
Lemma lem6191502 {_123419 : Type'} (op : type1400 _123419) : (term1354 _123419 op) = (term1372 _123419 op).
Proof. exact (EQ_MP (@lem6191501 _123419 op) (@lem6191479 _123419 op)). Qed.
Lemma lem6191504 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term522 A P Q) = (term521 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6191505 {_123419 : Type'} (P : _123419 -> Prop) (Q : _123419 -> Prop) : (term522 _123419 P Q) = (term521 _123419 P Q).
Proof. exact (@lem6191504 _123419 P Q). Qed.
Lemma lem6191506 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1373 _123419 op x) = (term1374 _123419 op x).
Proof. exact (@lem6191505 _123419 (term1240 _123419 op x) (term1350 _123419 op x)). Qed.
Lemma lem6191507 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (term1375 _123419 op x y) = ((term1218 _123419 op x y) = (term1218 _123419 op y x)).
Proof. exact (eq_refl (term1375 _123419 op x y)). Qed.
Lemma lem6191508 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1376 _123419 op x) = (term1240 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6191507 _123419 op y x)). Qed.
Lemma lem6191509 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191510 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1377 _123419 op x) = (term1241 _123419 op x).
Proof. exact (MK_COMB (@lem6191509 _123419) (@lem6191508 _123419 op x)). Qed.
Lemma lem6191511 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6191512 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1378 _123419 op x) = (term1367 _123419 op x).
Proof. exact (MK_COMB (@lem6191511) (@lem6191510 _123419 op x)). Qed.
Lemma lem6191513 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1379 _123419 op x y) = (term1349 _123419 y op x).
Proof. exact (eq_refl (term1379 _123419 op x y)). Qed.
Lemma lem6191514 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1380 _123419 op x) = (term1350 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6191513 _123419 y op x)). Qed.
Lemma lem6191515 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191516 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1381 _123419 op x) = (term1351 _123419 op x).
Proof. exact (MK_COMB (@lem6191515 _123419) (@lem6191514 _123419 op x)). Qed.
Lemma lem6191517 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1373 _123419 op x) = (term1369 _123419 op x).
Proof. exact (MK_COMB (@lem6191512 _123419 op x) (@lem6191516 _123419 op x)). Qed.
Lemma lem6191518 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6191519 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1382 _123419 op x) = (term1383 _123419 op x).
Proof. exact (MK_COMB (@lem6191518) (@lem6191517 _123419 op x)). Qed.
Lemma lem6191520 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (term1375 _123419 op x y) = ((term1218 _123419 op x y) = (term1218 _123419 op y x)).
Proof. exact (eq_refl (term1375 _123419 op x y)). Qed.
Lemma lem6191521 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6191522 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (term1384 _123419 op x y) = (term1385 _123419 op y x).
Proof. exact (MK_COMB (@lem6191521) (@lem6191520 _123419 op y x)). Qed.
Lemma lem6191523 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1379 _123419 op x y) = (term1349 _123419 y op x).
Proof. exact (eq_refl (term1379 _123419 op x y)). Qed.
Lemma lem6191524 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1386 _123419 op x y) = (term1387 _123419 y op x).
Proof. exact (MK_COMB (@lem6191522 _123419 op y x) (@lem6191523 _123419 y op x)). Qed.
Lemma lem6191525 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1388 _123419 op x) = (term1389 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6191524 _123419 y op x)). Qed.
Lemma lem6191526 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191527 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1374 _123419 op x) = (term1390 _123419 op x).
Proof. exact (MK_COMB (@lem6191526 _123419) (@lem6191525 _123419 op x)). Qed.
Lemma lem6191528 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : ((term1373 _123419 op x) = (term1374 _123419 op x)) = ((term1369 _123419 op x) = (term1390 _123419 op x)).
Proof. exact (MK_COMB (@lem6191519 _123419 op x) (@lem6191527 _123419 op x)). Qed.
Lemma lem6191529 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1369 _123419 op x) = (term1390 _123419 op x).
Proof. exact (EQ_MP (@lem6191528 _123419 op x) (@lem6191506 _123419 op x)). Qed.
Lemma lem6191531 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1391 A P Q) = (term1392 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem6191532 {_123419 : Type'} (P : Prop) (Q : _123419 -> Prop) : (term1391 _123419 P Q) = (term1392 _123419 P Q).
Proof. exact (@lem6191531 _123419 P Q). Qed.
Lemma lem6191533 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1393 _123419 y op x) = (term1394 _123419 y op x).
Proof. exact (@lem6191532 _123419 ((term1218 _123419 op x y) = (term1218 _123419 op y x)) (term1348 _123419 y op x)). Qed.
Lemma lem6191534 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term1395 _123419 y op x z) = (term1346 _123419 y z op x).
Proof. exact (eq_refl (term1395 _123419 y op x z)). Qed.
Lemma lem6191535 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1396 _123419 y op x) = (term1348 _123419 y op x).
Proof. exact (fun_ext (fun z : _123419 => @lem6191534 _123419 y z op x)). Qed.
Lemma lem6191536 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191537 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1397 _123419 y op x) = (term1349 _123419 y op x).
Proof. exact (MK_COMB (@lem6191536 _123419) (@lem6191535 _123419 y op x)). Qed.
Lemma lem6191538 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (term1385 _123419 op y x) = (term1385 _123419 op y x).
Proof. exact (eq_refl (term1385 _123419 op y x)). Qed.
Lemma lem6191539 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1393 _123419 y op x) = (term1387 _123419 y op x).
Proof. exact (MK_COMB (@lem6191538 _123419 op y x) (@lem6191537 _123419 y op x)). Qed.
Lemma lem6191540 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6191541 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1398 _123419 y op x) = (term1399 _123419 y op x).
Proof. exact (MK_COMB (@lem6191540) (@lem6191539 _123419 y op x)). Qed.
Lemma lem6191542 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term1395 _123419 y op x z) = (term1346 _123419 y z op x).
Proof. exact (eq_refl (term1395 _123419 y op x z)). Qed.
Lemma lem6191543 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (term1385 _123419 op y x) = (term1385 _123419 op y x).
Proof. exact (eq_refl (term1385 _123419 op y x)). Qed.
Lemma lem6191544 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term1400 _123419 y op x z) = (term1401 _123419 y z op x).
Proof. exact (MK_COMB (@lem6191543 _123419 op y x) (@lem6191542 _123419 y z op x)). Qed.
Lemma lem6191545 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1402 _123419 y op x) = (term1403 _123419 y op x).
Proof. exact (fun_ext (fun z : _123419 => @lem6191544 _123419 y z op x)). Qed.
Lemma lem6191546 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191547 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1394 _123419 y op x) = (term1404 _123419 y op x).
Proof. exact (MK_COMB (@lem6191546 _123419) (@lem6191545 _123419 y op x)). Qed.
Lemma lem6191548 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : ((term1393 _123419 y op x) = (term1394 _123419 y op x)) = ((term1387 _123419 y op x) = (term1404 _123419 y op x)).
Proof. exact (MK_COMB (@lem6191541 _123419 y op x) (@lem6191547 _123419 y op x)). Qed.
Lemma lem6191549 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1387 _123419 y op x) = (term1404 _123419 y op x).
Proof. exact (EQ_MP (@lem6191548 _123419 y op x) (@lem6191533 _123419 y op x)). Qed.
Lemma lem6191550 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1389 _123419 op x) = (term1405 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6191549 _123419 y op x)). Qed.
Lemma lem6191551 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191552 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1390 _123419 op x) = (term1406 _123419 op x).
Proof. exact (MK_COMB (@lem6191551 _123419) (@lem6191550 _123419 op x)). Qed.
Lemma lem6191553 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1369 _123419 op x) = (term1406 _123419 op x).
Proof. exact (TRANS (@lem6191529 _123419 op x) (@lem6191552 _123419 op x)). Qed.
Lemma lem6191554 {_123419 : Type'} (op : type1400 _123419) : (term1371 _123419 op) = (term1407 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6191553 _123419 op x)). Qed.
Lemma lem6191555 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191556 {_123419 : Type'} (op : type1400 _123419) : (term1372 _123419 op) = (term1408 _123419 op).
Proof. exact (MK_COMB (@lem6191555 _123419) (@lem6191554 _123419 op)). Qed.
Lemma lem6191557 {_123419 : Type'} (op : type1400 _123419) : (term1354 _123419 op) = (term1408 _123419 op).
Proof. exact (TRANS (@lem6191502 _123419 op) (@lem6191556 _123419 op)). Qed.
Lemma lem6191558 {_123419 : Type'} (op : type1400 _123419) : (term1245 _123419 op) = (term1408 _123419 op).
Proof. exact (TRANS (@lem6191475 _123419 op) (@lem6191557 _123419 op)). Qed.
Lemma lem6191559 {_123419 : Type'} (op : type1400 _123419) : (term1248 _123419 op) = (term1248 _123419 op).
Proof. exact (eq_refl (term1248 _123419 op)). Qed.
Lemma lem6191560 {_123419 : Type'} (op : type1400 _123419) : (term1249 _123419 op) = (term1409 _123419 op).
Proof. exact (MK_COMB (@lem6191559 _123419 op) (@lem6191558 _123419 op)). Qed.
Lemma lem6191562 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1410 A P Q) = (term1411 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem6191563 {_123419 : Type'} (P : Prop) (Q : _123419 -> Prop) : (term1410 _123419 P Q) = (term1411 _123419 P Q).
Proof. exact (@lem6191562 _123419 P Q). Qed.
Lemma lem6191564 {_123419 : Type'} (op : type1400 _123419) : (term1412 _123419 op) = (term1413 _123419 op).
Proof. exact (@lem6191563 _123419 (term1247 _123419 op) (term1407 _123419 op)). Qed.
Lemma lem6191565 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1414 _123419 op x) = (term1406 _123419 op x).
Proof. exact (eq_refl (term1414 _123419 op x)). Qed.
Lemma lem6191566 {_123419 : Type'} (op : type1400 _123419) : (term1415 _123419 op) = (term1407 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6191565 _123419 op x)). Qed.
Lemma lem6191567 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191568 {_123419 : Type'} (op : type1400 _123419) : (term1416 _123419 op) = (term1408 _123419 op).
Proof. exact (MK_COMB (@lem6191567 _123419) (@lem6191566 _123419 op)). Qed.
Lemma lem6191569 {_123419 : Type'} (op : type1400 _123419) : (term1248 _123419 op) = (term1248 _123419 op).
Proof. exact (eq_refl (term1248 _123419 op)). Qed.
Lemma lem6191570 {_123419 : Type'} (op : type1400 _123419) : (term1412 _123419 op) = (term1409 _123419 op).
Proof. exact (MK_COMB (@lem6191569 _123419 op) (@lem6191568 _123419 op)). Qed.
Lemma lem6191571 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6191572 {_123419 : Type'} (op : type1400 _123419) : (term1417 _123419 op) = (term1418 _123419 op).
Proof. exact (MK_COMB (@lem6191571) (@lem6191570 _123419 op)). Qed.
Lemma lem6191573 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1414 _123419 op x) = (term1406 _123419 op x).
Proof. exact (eq_refl (term1414 _123419 op x)). Qed.
Lemma lem6191574 {_123419 : Type'} (op : type1400 _123419) : (term1248 _123419 op) = (term1248 _123419 op).
Proof. exact (eq_refl (term1248 _123419 op)). Qed.
Lemma lem6191575 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1419 _123419 op x) = (term1420 _123419 op x).
Proof. exact (MK_COMB (@lem6191574 _123419 op) (@lem6191573 _123419 op x)). Qed.
Lemma lem6191576 {_123419 : Type'} (op : type1400 _123419) : (term1421 _123419 op) = (term1422 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6191575 _123419 op x)). Qed.
Lemma lem6191577 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191578 {_123419 : Type'} (op : type1400 _123419) : (term1413 _123419 op) = (term1423 _123419 op).
Proof. exact (MK_COMB (@lem6191577 _123419) (@lem6191576 _123419 op)). Qed.
Lemma lem6191579 {_123419 : Type'} (op : type1400 _123419) : ((term1412 _123419 op) = (term1413 _123419 op)) = ((term1409 _123419 op) = (term1423 _123419 op)).
Proof. exact (MK_COMB (@lem6191572 _123419 op) (@lem6191578 _123419 op)). Qed.
Lemma lem6191580 {_123419 : Type'} (op : type1400 _123419) : (term1409 _123419 op) = (term1423 _123419 op).
Proof. exact (EQ_MP (@lem6191579 _123419 op) (@lem6191564 _123419 op)). Qed.
Lemma lem6191582 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1410 A P Q) = (term1411 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem6191583 {_123419 : Type'} (P : Prop) (Q : _123419 -> Prop) : (term1410 _123419 P Q) = (term1411 _123419 P Q).
Proof. exact (@lem6191582 _123419 P Q). Qed.
Lemma lem6191584 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1424 _123419 op x) = (term1425 _123419 op x).
Proof. exact (@lem6191583 _123419 (term1247 _123419 op) (term1405 _123419 op x)). Qed.
Lemma lem6191585 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1426 _123419 op x y) = (term1404 _123419 y op x).
Proof. exact (eq_refl (term1426 _123419 op x y)). Qed.
Lemma lem6191586 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1427 _123419 op x) = (term1405 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6191585 _123419 y op x)). Qed.
Lemma lem6191587 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191588 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1428 _123419 op x) = (term1406 _123419 op x).
Proof. exact (MK_COMB (@lem6191587 _123419) (@lem6191586 _123419 op x)). Qed.
Lemma lem6191589 {_123419 : Type'} (op : type1400 _123419) : (term1248 _123419 op) = (term1248 _123419 op).
Proof. exact (eq_refl (term1248 _123419 op)). Qed.
Lemma lem6191590 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1424 _123419 op x) = (term1420 _123419 op x).
Proof. exact (MK_COMB (@lem6191589 _123419 op) (@lem6191588 _123419 op x)). Qed.
Lemma lem6191591 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6191592 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1429 _123419 op x) = (term1430 _123419 op x).
Proof. exact (MK_COMB (@lem6191591) (@lem6191590 _123419 op x)). Qed.
Lemma lem6191593 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1426 _123419 op x y) = (term1404 _123419 y op x).
Proof. exact (eq_refl (term1426 _123419 op x y)). Qed.
Lemma lem6191594 {_123419 : Type'} (op : type1400 _123419) : (term1248 _123419 op) = (term1248 _123419 op).
Proof. exact (eq_refl (term1248 _123419 op)). Qed.
Lemma lem6191595 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1431 _123419 op x y) = (term1432 _123419 y op x).
Proof. exact (MK_COMB (@lem6191594 _123419 op) (@lem6191593 _123419 y op x)). Qed.
Lemma lem6191596 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1433 _123419 op x) = (term1434 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6191595 _123419 y op x)). Qed.
Lemma lem6191597 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191598 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1425 _123419 op x) = (term1435 _123419 op x).
Proof. exact (MK_COMB (@lem6191597 _123419) (@lem6191596 _123419 op x)). Qed.
Lemma lem6191599 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : ((term1424 _123419 op x) = (term1425 _123419 op x)) = ((term1420 _123419 op x) = (term1435 _123419 op x)).
Proof. exact (MK_COMB (@lem6191592 _123419 op x) (@lem6191598 _123419 op x)). Qed.
Lemma lem6191600 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1420 _123419 op x) = (term1435 _123419 op x).
Proof. exact (EQ_MP (@lem6191599 _123419 op x) (@lem6191584 _123419 op x)). Qed.
Lemma lem6191602 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1410 A P Q) = (term1411 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem6191603 {_123419 : Type'} (P : Prop) (Q : _123419 -> Prop) : (term1410 _123419 P Q) = (term1411 _123419 P Q).
Proof. exact (@lem6191602 _123419 P Q). Qed.
Lemma lem6191604 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1436 _123419 y op x) = (term1437 _123419 y op x).
Proof. exact (@lem6191603 _123419 (term1247 _123419 op) (term1403 _123419 y op x)). Qed.
Lemma lem6191605 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term1438 _123419 y op x z) = (term1401 _123419 y z op x).
Proof. exact (eq_refl (term1438 _123419 y op x z)). Qed.
Lemma lem6191606 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1439 _123419 y op x) = (term1403 _123419 y op x).
Proof. exact (fun_ext (fun z : _123419 => @lem6191605 _123419 y z op x)). Qed.
Lemma lem6191607 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191608 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1440 _123419 y op x) = (term1404 _123419 y op x).
Proof. exact (MK_COMB (@lem6191607 _123419) (@lem6191606 _123419 y op x)). Qed.
Lemma lem6191609 {_123419 : Type'} (op : type1400 _123419) : (term1248 _123419 op) = (term1248 _123419 op).
Proof. exact (eq_refl (term1248 _123419 op)). Qed.
Lemma lem6191610 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1436 _123419 y op x) = (term1432 _123419 y op x).
Proof. exact (MK_COMB (@lem6191609 _123419 op) (@lem6191608 _123419 y op x)). Qed.
Lemma lem6191611 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6191612 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1441 _123419 y op x) = (term1442 _123419 y op x).
Proof. exact (MK_COMB (@lem6191611) (@lem6191610 _123419 y op x)). Qed.
Lemma lem6191613 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term1438 _123419 y op x z) = (term1401 _123419 y z op x).
Proof. exact (eq_refl (term1438 _123419 y op x z)). Qed.
Lemma lem6191614 {_123419 : Type'} (op : type1400 _123419) : (term1248 _123419 op) = (term1248 _123419 op).
Proof. exact (eq_refl (term1248 _123419 op)). Qed.
Lemma lem6191615 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term1443 _123419 y op x z) = (term1444 _123419 y z op x).
Proof. exact (MK_COMB (@lem6191614 _123419 op) (@lem6191613 _123419 y z op x)). Qed.
Lemma lem6191616 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1445 _123419 y op x) = (term1446 _123419 y op x).
Proof. exact (fun_ext (fun z : _123419 => @lem6191615 _123419 y z op x)). Qed.
Lemma lem6191617 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191618 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1437 _123419 y op x) = (term1447 _123419 y op x).
Proof. exact (MK_COMB (@lem6191617 _123419) (@lem6191616 _123419 y op x)). Qed.
Lemma lem6191619 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : ((term1436 _123419 y op x) = (term1437 _123419 y op x)) = ((term1432 _123419 y op x) = (term1447 _123419 y op x)).
Proof. exact (MK_COMB (@lem6191612 _123419 y op x) (@lem6191618 _123419 y op x)). Qed.
Lemma lem6191620 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1432 _123419 y op x) = (term1447 _123419 y op x).
Proof. exact (EQ_MP (@lem6191619 _123419 y op x) (@lem6191604 _123419 y op x)). Qed.
Lemma lem6191621 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1434 _123419 op x) = (term1448 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6191620 _123419 y op x)). Qed.
Lemma lem6191622 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191623 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1435 _123419 op x) = (term1449 _123419 op x).
Proof. exact (MK_COMB (@lem6191622 _123419) (@lem6191621 _123419 op x)). Qed.
Lemma lem6191624 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1420 _123419 op x) = (term1449 _123419 op x).
Proof. exact (TRANS (@lem6191600 _123419 op x) (@lem6191623 _123419 op x)). Qed.
Lemma lem6191625 {_123419 : Type'} (op : type1400 _123419) : (term1422 _123419 op) = (term1450 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6191624 _123419 op x)). Qed.
Lemma lem6191626 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191627 {_123419 : Type'} (op : type1400 _123419) : (term1423 _123419 op) = (term1451 _123419 op).
Proof. exact (MK_COMB (@lem6191626 _123419) (@lem6191625 _123419 op)). Qed.
Lemma lem6191628 {_123419 : Type'} (op : type1400 _123419) : (term1409 _123419 op) = (term1451 _123419 op).
Proof. exact (TRANS (@lem6191580 _123419 op) (@lem6191627 _123419 op)). Qed.
Lemma lem6191629 {_123419 : Type'} (op : type1400 _123419) : (term1249 _123419 op) = (term1451 _123419 op).
Proof. exact (TRANS (@lem6191560 _123419 op) (@lem6191628 _123419 op)). Qed.
Lemma lem6191630 {_123419 : Type'} : (term1250 _123419) = (term1452 _123419).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6191629 _123419 op)). Qed.
Lemma lem6191631 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6191632 {_123419 : Type'} : (term1251 _123419) = (term1453 _123419).
Proof. exact (MK_COMB (@lem6191631 _123419) (@lem6191630 _123419)). Qed.
Lemma lem6191646 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term1444 _123419 y z op x) = (term1454 _123419 y z op x).
Proof. exact (@lem19490 ((term1218 _123419 op x y) = (term1218 _123419 op y x)) (term1247 _123419 op) (term1346 _123419 y z op x)). Qed.
Lemma lem6191653 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term1455 _123419 y z op x) = (term1456 _123419 y z op x).
Proof. exact (@lem19490 ((term1221 _123419 x op y z) = (term1227 _123419 op x y z)) (term1247 _123419 op) ((term1213 _123419 op x) = x)). Qed.
Lemma lem6191656 {_123419 : Type'} (op : type1400 _123419) (y : _123419) (x : _123419) : (term1457 _123419 op y x) = (term1457 _123419 op y x).
Proof. exact (eq_refl (term1457 _123419 op y x)). Qed.
Lemma lem6191657 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term1454 _123419 y z op x) = (term1458 _123419 y z op x).
Proof. exact (MK_COMB (@lem6191656 _123419 op y x) (@lem6191653 _123419 y z op x)). Qed.
Lemma lem6191659 {_123419 : Type'} (y : _123419) (z : _123419) (op : type1400 _123419) (x : _123419) : (term1444 _123419 y z op x) = (term1458 _123419 y z op x).
Proof. exact (TRANS (@lem6191646 _123419 y z op x) (@lem6191657 _123419 y z op x)). Qed.
Lemma lem6191660 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1446 _123419 y op x) = (term1459 _123419 y op x).
Proof. exact (fun_ext (fun z : _123419 => @lem6191659 _123419 y z op x)). Qed.
Lemma lem6191661 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191662 {_123419 : Type'} (y : _123419) (op : type1400 _123419) (x : _123419) : (term1447 _123419 y op x) = (term1460 _123419 y op x).
Proof. exact (MK_COMB (@lem6191661 _123419) (@lem6191660 _123419 y op x)). Qed.
Lemma lem6191663 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1448 _123419 op x) = (term1461 _123419 op x).
Proof. exact (fun_ext (fun y : _123419 => @lem6191662 _123419 y op x)). Qed.
Lemma lem6191664 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191665 {_123419 : Type'} (op : type1400 _123419) (x : _123419) : (term1449 _123419 op x) = (term1462 _123419 op x).
Proof. exact (MK_COMB (@lem6191664 _123419) (@lem6191663 _123419 op x)). Qed.
Lemma lem6191666 {_123419 : Type'} (op : type1400 _123419) : (term1450 _123419 op) = (term1463 _123419 op).
Proof. exact (fun_ext (fun x : _123419 => @lem6191665 _123419 op x)). Qed.
Lemma lem6191667 {_123419 : Type'} : (@all _123419) = (@all _123419).
Proof. exact (eq_refl (@all _123419)). Qed.
Lemma lem6191668 {_123419 : Type'} (op : type1400 _123419) : (term1451 _123419 op) = (term1464 _123419 op).
Proof. exact (MK_COMB (@lem6191667 _123419) (@lem6191666 _123419 op)). Qed.
Lemma lem6191669 {_123419 : Type'} : (term1452 _123419) = (term1465 _123419).
Proof. exact (fun_ext (fun op : type1400 _123419 => @lem6191668 _123419 op)). Qed.
Lemma lem6191670 {_123419 : Type'} : (@all (_123419 -> _123419 -> _123419)) = (@all (_123419 -> _123419 -> _123419)).
Proof. exact (eq_refl (@all (_123419 -> _123419 -> _123419))). Qed.
Lemma lem6191671 {_123419 : Type'} : (term1453 _123419) = (term1466 _123419).
Proof. exact (MK_COMB (@lem6191670 _123419) (@lem6191669 _123419)). Qed.
Lemma lem6191672 {_123419 : Type'} : (term1251 _123419) = (term1466 _123419).
Proof. exact (TRANS (@lem6191632 _123419) (@lem6191671 _123419)). Qed.
Lemma lem6191673 {_123419 : Type'} (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (h1 : term821 _123419 y z x) : term1466 _123419.
Proof. exact (EQ_MP (@lem6191672 _123419) (@lem6191352 _123419 y z x h1)). Qed.
Lemma lem6191677 {_123419 : Type'} (_78849 : type1400 _123419) (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (h1 : term821 _123419 y z x) : term1467 _123419 _78849.
Proof. exact (@lem6191673 _123419 y z x h1 _78849). Qed.
Lemma lem6191678 {_123419 : Type'} (_78849 : type1400 _123419) : (term1467 _123419 _78849) = (term1464 _123419 _78849).
Proof. exact (eq_refl (term1467 _123419 _78849)). Qed.
Lemma lem6191679 {_123419 : Type'} (_78849 : type1400 _123419) (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (h1 : term821 _123419 y z x) : term1464 _123419 _78849.
Proof. exact (EQ_MP (@lem6191678 _123419 _78849) (@lem6191677 _123419 _78849 y z x h1)). Qed.
Lemma lem6191680 {_123419 : Type'} (_78849 : type1400 _123419) (_78850 : _123419) (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (h1 : term821 _123419 y z x) : term1468 _123419 _78849 _78850.
Proof. exact (@lem6191679 _123419 _78849 y z x h1 _78850). Qed.
Lemma lem6191681 {_123419 : Type'} (_78849 : type1400 _123419) (_78850 : _123419) : (term1468 _123419 _78849 _78850) = (term1462 _123419 _78849 _78850).
Proof. exact (eq_refl (term1468 _123419 _78849 _78850)). Qed.
Lemma lem6191682 {_123419 : Type'} (_78849 : type1400 _123419) (_78850 : _123419) (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (h1 : term821 _123419 y z x) : term1462 _123419 _78849 _78850.
Proof. exact (EQ_MP (@lem6191681 _123419 _78849 _78850) (@lem6191680 _123419 _78849 _78850 y z x h1)). Qed.
Lemma lem6191683 {_123419 : Type'} (_78849 : type1400 _123419) (_78850 : _123419) (_78851 : _123419) (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (h1 : term821 _123419 y z x) : term1469 _123419 _78849 _78850 _78851.
Proof. exact (@lem6191682 _123419 _78849 _78850 y z x h1 _78851). Qed.
Lemma lem6191684 {_123419 : Type'} (_78851 : _123419) (_78849 : type1400 _123419) (_78850 : _123419) : (term1469 _123419 _78849 _78850 _78851) = (term1460 _123419 _78851 _78849 _78850).
Proof. exact (eq_refl (term1469 _123419 _78849 _78850 _78851)). Qed.
Lemma lem6191685 {_123419 : Type'} (_78851 : _123419) (_78849 : type1400 _123419) (_78850 : _123419) (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (h1 : term821 _123419 y z x) : term1460 _123419 _78851 _78849 _78850.
Proof. exact (EQ_MP (@lem6191684 _123419 _78851 _78849 _78850) (@lem6191683 _123419 _78849 _78850 _78851 y z x h1)). Qed.
Lemma lem6191686 {_123419 : Type'} (_78851 : _123419) (_78849 : type1400 _123419) (_78850 : _123419) (_78852 : _123419) (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (h1 : term821 _123419 y z x) : term1470 _123419 _78851 _78849 _78850 _78852.
Proof. exact (@lem6191685 _123419 _78851 _78849 _78850 y z x h1 _78852). Qed.
Lemma lem6191687 {_123419 : Type'} (_78851 : _123419) (_78852 : _123419) (_78849 : type1400 _123419) (_78850 : _123419) : (term1470 _123419 _78851 _78849 _78850 _78852) = (term1458 _123419 _78851 _78852 _78849 _78850).
Proof. exact (eq_refl (term1470 _123419 _78851 _78849 _78850 _78852)). Qed.
Lemma lem6191688 {_123419 : Type'} (_78851 : _123419) (_78852 : _123419) (_78849 : type1400 _123419) (_78850 : _123419) (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (h1 : term821 _123419 y z x) : term1458 _123419 _78851 _78852 _78849 _78850.
Proof. exact (EQ_MP (@lem6191687 _123419 _78851 _78852 _78849 _78850) (@lem6191686 _123419 _78851 _78849 _78850 _78852 y z x h1)). Qed.
Lemma lem6191698 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) (h1 : term1526 _123419 op m f n) : term1579 _123419 op m f n.
Proof. exact (EQ_MP (@lem6190928 _123419 op m f n) (@lem6190046 _123419 op m f n h1)). Qed.
Lemma lem6191718 {_123419 : Type'} (_78849 : type1400 _123419) (_78851 : _123419) (_78850 : _123419) (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (h1 : term821 _123419 y z x) : term1471 _123419 _78849 _78851 _78850.
Proof. exact (proj1 (@lem6191688 _123419 _78851 (@el _123419) _78849 _78850 y z x h1)). Qed.
Lemma lem6191948 {_123419 : Type'} (op : type1400 _123419) (h1 : @monoidal _123419 op) : @I ((_123419 -> _123419 -> _123419) -> Prop) (@monoidal _123419) op.
Proof. exact (EQ_MP (@lem6190753 _123419 op) (@lem6190034 _123419 op h1)). Qed.
Lemma lem6191949 {_123419 : Type'} (op : type1400 _123419) (h1 : @monoidal _123419 op) : term1474 _123419 op.
Proof. exact (fun h0 : term1247 _123419 op => @lem6191948 _123419 op h1). Qed.
Lemma lem6191951 (p : Prop) : (term1475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6191952 {_123419 : Type'} (op : type1400 _123419) : (term1474 _123419 op) = (@I ((_123419 -> _123419 -> _123419) -> Prop) (@monoidal _123419) op).
Proof. exact (@lem6191951 (@I ((_123419 -> _123419 -> _123419) -> Prop) (@monoidal _123419) op)). Qed.
Lemma lem6191953 {_123419 : Type'} (op : type1400 _123419) (h1 : @monoidal _123419 op) : @I ((_123419 -> _123419 -> _123419) -> Prop) (@monoidal _123419) op.
Proof. exact (EQ_MP (@lem6191952 _123419 op) (@lem6191949 _123419 op h1)). Qed.
Lemma lem6191959 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6191960 {_123419 : Type'} (_78851 : _123419) (_78850 : _123419) (_78849 : type1400 _123419) : (term1471 _123419 _78849 _78851 _78850) = (term1476 _123419 _78851 _78850 _78849).
Proof. exact (@lem6191959 ((term1218 _123419 _78849 _78850 _78851) = (term1218 _123419 _78849 _78851 _78850)) (term1247 _123419 _78849)). Qed.
Lemma lem6191968 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6191969 {_123419 : Type'} (_78851 : _123419) (_78850 : _123419) (_78849 : type1400 _123419) : (term1477 _123419 _78849 _78851 _78850) = (term1478 _123419 _78851 _78850 _78849).
Proof. exact (MK_COMB (@lem6191968) (@lem6191960 _123419 _78851 _78850 _78849)). Qed.
Lemma lem6191977 {_123419 : Type'} (_78851 : _123419) (_78850 : _123419) (_78849 : type1400 _123419) : (term1476 _123419 _78851 _78850 _78849) = (term1476 _123419 _78851 _78850 _78849).
Proof. exact (eq_refl (term1476 _123419 _78851 _78850 _78849)). Qed.
Lemma lem6191978 {_123419 : Type'} (_78851 : _123419) (_78850 : _123419) (_78849 : type1400 _123419) : ((term1471 _123419 _78849 _78851 _78850) = (term1476 _123419 _78851 _78850 _78849)) = ((term1476 _123419 _78851 _78850 _78849) = (term1476 _123419 _78851 _78850 _78849)).
Proof. exact (MK_COMB (@lem6191969 _123419 _78851 _78850 _78849) (@lem6191977 _123419 _78851 _78850 _78849)). Qed.
Lemma lem6191980 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6191981 (x : Prop) : (x = x) = True.
Proof. exact (@lem6191980 Prop x). Qed.
Lemma lem6191982 {_123419 : Type'} (_78851 : _123419) (_78850 : _123419) (_78849 : type1400 _123419) : ((term1476 _123419 _78851 _78850 _78849) = (term1476 _123419 _78851 _78850 _78849)) = True.
Proof. exact (@lem6191981 (term1476 _123419 _78851 _78850 _78849)). Qed.
Lemma lem6191983 {_123419 : Type'} (_78851 : _123419) (_78850 : _123419) (_78849 : type1400 _123419) : ((term1471 _123419 _78849 _78851 _78850) = (term1476 _123419 _78851 _78850 _78849)) = True.
Proof. exact (TRANS (@lem6191978 _123419 _78851 _78850 _78849) (@lem6191982 _123419 _78851 _78850 _78849)). Qed.
Lemma lem6191984 {_123419 : Type'} (_78851 : _123419) (_78850 : _123419) (_78849 : type1400 _123419) : True = ((term1471 _123419 _78849 _78851 _78850) = (term1476 _123419 _78851 _78850 _78849)).
Proof. exact (SYM (@lem6191983 _123419 _78851 _78850 _78849)). Qed.
Lemma lem6191985 {_123419 : Type'} (_78851 : _123419) (_78850 : _123419) (_78849 : type1400 _123419) : (term1471 _123419 _78849 _78851 _78850) = (term1476 _123419 _78851 _78850 _78849).
Proof. exact (EQ_MP (@lem6191984 _123419 _78851 _78850 _78849) (@lem0)). Qed.
Lemma lem6191986 {_123419 : Type'} (_78851 : _123419) (_78850 : _123419) (_78849 : type1400 _123419) (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (h1 : term821 _123419 y z x) : term1476 _123419 _78851 _78850 _78849.
Proof. exact (EQ_MP (@lem6191985 _123419 _78851 _78850 _78849) (@lem6191718 _123419 _78849 _78851 _78850 y z x h1)). Qed.
Lemma lem6191988 (b : Prop) (a : Prop) : (a \/ b) = (term1479 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6191989 {_123419 : Type'} (_78849 : type1400 _123419) (_78851 : _123419) (_78850 : _123419) : (term1476 _123419 _78851 _78850 _78849) = (term1480 _123419 _78849 _78851 _78850).
Proof. exact (@lem6191988 (term1247 _123419 _78849) ((term1218 _123419 _78849 _78850 _78851) = (term1218 _123419 _78849 _78851 _78850))). Qed.
Lemma lem6191991 (a : Prop) : (term55 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6191992 {_123419 : Type'} (_78849 : type1400 _123419) : (term1481 _123419 _78849) = (@I ((_123419 -> _123419 -> _123419) -> Prop) (@monoidal _123419) _78849).
Proof. exact (@lem6191991 (@I ((_123419 -> _123419 -> _123419) -> Prop) (@monoidal _123419) _78849)). Qed.
Lemma lem6191993 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6191994 {_123419 : Type'} (_78849 : type1400 _123419) : (term1482 _123419 _78849) = (term1483 _123419 _78849).
Proof. exact (MK_COMB (@lem6191993) (@lem6191992 _123419 _78849)). Qed.
Lemma lem6191995 {_123419 : Type'} (_78849 : type1400 _123419) (_78851 : _123419) (_78850 : _123419) : ((term1218 _123419 _78849 _78850 _78851) = (term1218 _123419 _78849 _78851 _78850)) = ((term1218 _123419 _78849 _78850 _78851) = (term1218 _123419 _78849 _78851 _78850)).
Proof. exact (eq_refl ((term1218 _123419 _78849 _78850 _78851) = (term1218 _123419 _78849 _78851 _78850))). Qed.
Lemma lem6191996 {_123419 : Type'} (_78849 : type1400 _123419) (_78851 : _123419) (_78850 : _123419) : (term1480 _123419 _78849 _78851 _78850) = (term1484 _123419 _78849 _78851 _78850).
Proof. exact (MK_COMB (@lem6191994 _123419 _78849) (@lem6191995 _123419 _78849 _78851 _78850)). Qed.
Lemma lem6191997 {_123419 : Type'} (_78849 : type1400 _123419) (_78851 : _123419) (_78850 : _123419) : (term1476 _123419 _78851 _78850 _78849) = (term1484 _123419 _78849 _78851 _78850).
Proof. exact (TRANS (@lem6191989 _123419 _78849 _78851 _78850) (@lem6191996 _123419 _78849 _78851 _78850)). Qed.
Lemma lem6192000 {_123419 : Type'} (_78849 : type1400 _123419) (_78851 : _123419) (_78850 : _123419) (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (h1 : term821 _123419 y z x) : term1484 _123419 _78849 _78851 _78850.
Proof. exact (EQ_MP (@lem6191997 _123419 _78849 _78851 _78850) (@lem6191986 _123419 _78851 _78850 _78849 y z x h1)). Qed.
Lemma lem6192001 {_123419 : Type'} (_78849 : type1400 _123419) (_78851 : _123419) (_78850 : _123419) (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (h1 : term821 _123419 y z x) : term1484 _123419 _78849 _78851 _78850.
Proof. exact (@lem6192000 _123419 _78849 _78851 _78850 y z x h1). Qed.
Lemma lem6192002 {_123419 : Type'} (op : type1400 _123419) (_78851 : _123419) (_78850 : _123419) (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (h1 : term821 _123419 y z x) : term1484 _123419 op _78851 _78850.
Proof. exact (@lem6192001 _123419 op _78851 _78850 y z x h1). Qed.
Lemma lem6192005 {_123419 : Type'} (_78851 : _123419) (_78850 : _123419) (op : type1400 _123419) (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (h1 : @monoidal _123419 op) (h2 : term821 _123419 y z x) : (term1218 _123419 op _78850 _78851) = (term1218 _123419 op _78851 _78850).
Proof. exact (@lem6192002 _123419 op _78851 _78850 y z x h2 (@lem6191953 _123419 op h1)). Qed.
Lemma lem6192006 {_123419 : Type'} (_78851 : _123419) (_78850 : _123419) (op : type1400 _123419) (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (h1 : @monoidal _123419 op) (h2 : term821 _123419 y z x) : (term1218 _123419 op _78850 _78851) = (term1218 _123419 op _78851 _78850).
Proof. exact (@lem6192005 _123419 _78851 _78850 op y z x h1 h2). Qed.
Lemma lem6192007 {_123419 : Type'} (m : nat) (f : nat -> _123419) (n : nat) (op : type1400 _123419) (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (h1 : @monoidal _123419 op) (h2 : term821 _123419 y z x) : (term1571 _123419 op m n f) = (term1577 _123419 op m f n).
Proof. exact (@lem6192006 _123419 (term1565 _123419 op m n f) (term1557 _123419 f n) op y z x h1 h2). Qed.
Lemma lem6192008 {_123419 : Type'} (m : nat) (f : nat -> _123419) (n : nat) (op : type1400 _123419) (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (h1 : @monoidal _123419 op) (h2 : term821 _123419 y z x) : term1580 _123419 op m f n.
Proof. exact (fun h0 : term1579 _123419 op m f n => @lem6192007 _123419 m f n op y z x h1 h2). Qed.
Lemma lem6192010 (p : Prop) : (term1475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6192011 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : (term1580 _123419 op m f n) = ((term1571 _123419 op m n f) = (term1577 _123419 op m f n)).
Proof. exact (@lem6192010 ((term1571 _123419 op m n f) = (term1577 _123419 op m f n))). Qed.
Lemma lem6192012 {_123419 : Type'} (m : nat) (f : nat -> _123419) (n : nat) (op : type1400 _123419) (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (h1 : @monoidal _123419 op) (h2 : term821 _123419 y z x) : (term1571 _123419 op m n f) = (term1577 _123419 op m f n).
Proof. exact (EQ_MP (@lem6192011 _123419 op m f n) (@lem6192008 _123419 m f n op y z x h1 h2)). Qed.
Lemma lem6192015 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6192017 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : (term1579 _123419 op m f n) = (term1581 _123419 op m f n).
Proof. exact (@lem6192015 ((term1571 _123419 op m n f) = (term1577 _123419 op m f n))). Qed.
Lemma lem6192020 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) (h1 : term1526 _123419 op m f n) : term1581 _123419 op m f n.
Proof. exact (EQ_MP (@lem6192017 _123419 op m f n) (@lem6191698 _123419 op m f n h1)). Qed.
Lemma lem6192023 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (h1 : @monoidal _123419 op) (h2 : term1526 _123419 op m f n) (h3 : term821 _123419 y z x) : False.
Proof. exact (@lem6192020 _123419 op m f n h2 (@lem6192012 _123419 m f n op y z x h1 h3)). Qed.
Lemma lem6192024 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (h1 : @monoidal _123419 op) (h2 : term1526 _123419 op m f n) (h3 : term821 _123419 y z x) : term1521.
Proof. exact (fun h0 : ~ False => @lem6192023 _123419 op m f n y z x h1 h2 h3). Qed.
Lemma lem6192026 (p : Prop) : (term1475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6192027 : term1521 = False.
Proof. exact (@lem6192026 False). Qed.
Lemma lem6192028 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) (y : type402 _123419) (z : type402 _123419) (x : type402 _123419) (h1 : @monoidal _123419 op) (h2 : term1526 _123419 op m f n) (h3 : term821 _123419 y z x) : False.
Proof. exact (EQ_MP (@lem6192027) (@lem6192024 _123419 op m f n y z x h1 h2 h3)). Qed.
Lemma lem6192029 {_123419 : Type'} (y : type402 _123419) (x : type402 _123419) (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) (h1 : term824 _123419 y x) (h2 : @monoidal _123419 op) (h3 : term1526 _123419 op m f n) : False.
Proof. exact (ex_elim (@lem6190744 _123419 y x h1) (fun z : type402 _123419 => fun h0 : term823 _123419 y x z => @lem6192028 _123419 op m f n y z x h2 h3 h0)). Qed.
Lemma lem6192030 {_123419 : Type'} (x : type402 _123419) (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) (h1 : term826 _123419 x) (h2 : @monoidal _123419 op) (h3 : term1526 _123419 op m f n) : False.
Proof. exact (ex_elim (@lem6190743 _123419 x h1) (fun y : type402 _123419 => fun h0 : term825 _123419 x y => @lem6192029 _123419 y x op m f n h0 h2 h3)). Qed.
Lemma lem6192031 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) (h1 : term382 _123419) (h2 : @monoidal _123419 op) (h3 : term1526 _123419 op m f n) : False.
Proof. exact (ex_elim (@lem6190742 _123419 h1) (fun x : type402 _123419 => fun h0 : term827 _123419 x => @lem6192030 _123419 x op m f n h0 h2 h3)). Qed.
Lemma lem6192032 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) (h1 : term382 _123419) (h2 : @monoidal _123419 op) (h3 : term1526 _123419 op m f n) : (term1526 _123419 op m f n) = False.
Proof. exact (prop_ext (fun h4 : term1526 _123419 op m f n => @lem6192031 _123419 op m f n h1 h2 h3) (fun h4 : False => @lem6190046 _123419 op m f n h3)). Qed.
Lemma lem6192033 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) (h1 : term382 _123419) (h2 : @monoidal _123419 op) (h3 : term1526 _123419 op m f n) : False.
Proof. exact (EQ_MP (@lem6192032 _123419 op m f n h1 h2 h3) (@lem6190046 _123419 op m f n h3)). Qed.
Lemma lem6192034 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) (h1 : term382 _123419) (h2 : @monoidal _123419 op) (h3 : term1526 _123419 op m f n) : (@monoidal _123419 op) = False.
Proof. exact (prop_ext (fun h4 : @monoidal _123419 op => @lem6192033 _123419 op m f n h1 h2 h3) (fun h4 : False => @lem6190034 _123419 op h2)). Qed.
Lemma lem6192035 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) (h1 : term382 _123419) (h2 : @monoidal _123419 op) (h3 : term1526 _123419 op m f n) : False.
Proof. exact (EQ_MP (@lem6192034 _123419 op m f n h1 h2 h3) (@lem6190034 _123419 op h2)). Qed.
Lemma lem6192036 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) (h1 : @monoidal _123419 op) (h2 : term1526 _123419 op m f n) : term1531 _123419.
Proof. exact (fun h0 : term382 _123419 => @lem6192035 _123419 op m f n h0 h1 h2). Qed.
Lemma lem6192037 {_123419 : Type'} : (term1531 _123419) = (term1532 _123419).
Proof. exact (@lem69 (term382 _123419)). Qed.
Lemma lem6192038 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) (h1 : @monoidal _123419 op) (h2 : term1526 _123419 op m f n) : term1532 _123419.
Proof. exact (EQ_MP (@lem6192037 _123419) (@lem6192036 _123419 op m f n h1 h2)). Qed.
Lemma lem6192039 {_123419 : Type'} (m : nat) (f : nat -> _123419) (n : nat) (op : type1400 _123419) (h1 : @monoidal _123419 op) : term1535 _123419 op m f n.
Proof. exact (fun h0 : term1526 _123419 op m f n => @lem6192038 _123419 op m f n h1 h0). Qed.
Lemma lem6192040 {_123419 : Type'} (m : nat) (f : nat -> _123419) (n : nat) (op : type1400 _123419) (h1 : @monoidal _123419 op) : term1537 _123419 op m f n.
Proof. exact (fun h0 : term245 m n => @lem6192039 _123419 m f n op h1). Qed.
Lemma lem6192041 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : term1538 _123419 op m f n.
Proof. exact (fun h0 : @monoidal _123419 op => @lem6192040 _123419 m f n op h0). Qed.
Lemma lem6192046 {_123419 : Type'} (m : nat) (f : nat -> _123419) (n : nat) : term1542 _123419 m f n.
Proof. exact (fun op : type1400 _123419 => @lem6192041 _123419 op m f n). Qed.
Lemma lem6192051 {_123419 : Type'} (f : nat -> _123419) (n : nat) : term1546 _123419 f n.
Proof. exact (fun m : nat => @lem6192046 _123419 m f n). Qed.
Lemma lem6192056 {_123419 : Type'} (n : nat) : term1550 _123419 n.
Proof. exact (fun f : nat -> _123419 => @lem6192051 _123419 f n). Qed.
Lemma lem6192061 {_123419 : Type'} : term1554 _123419.
Proof. exact (fun n : nat => @lem6192056 _123419 n). Qed.
Lemma lem6192062 {_123419 : Type'} : term1553 _123419.
Proof. exact (EQ_MP (@lem6190024 _123419) (@lem6192061 _123419)). Qed.
Lemma lem6192063 {_123419 : Type'} (n : nat) : term1582 _123419 n.
Proof. exact (@lem6192062 _123419 n). Qed.
Lemma lem6192064 {_123419 : Type'} (n : nat) : (term1582 _123419 n) = (term1549 _123419 n).
Proof. exact (eq_refl (term1582 _123419 n)). Qed.
Lemma lem6192065 {_123419 : Type'} (n : nat) : term1549 _123419 n.
Proof. exact (EQ_MP (@lem6192064 _123419 n) (@lem6192063 _123419 n)). Qed.
Lemma lem6192066 {_123419 : Type'} (n : nat) (f : nat -> _123419) : term1583 _123419 n f.
Proof. exact (@lem6192065 _123419 n f). Qed.
Lemma lem6192067 {_123419 : Type'} (f : nat -> _123419) (n : nat) : (term1583 _123419 n f) = (term1545 _123419 f n).
Proof. exact (eq_refl (term1583 _123419 n f)). Qed.
Lemma lem6192068 {_123419 : Type'} (f : nat -> _123419) (n : nat) : term1545 _123419 f n.
Proof. exact (EQ_MP (@lem6192067 _123419 f n) (@lem6192066 _123419 n f)). Qed.
Lemma lem6192069 {_123419 : Type'} (f : nat -> _123419) (n : nat) (m : nat) : term1584 _123419 f n m.
Proof. exact (@lem6192068 _123419 f n m). Qed.
Lemma lem6192070 {_123419 : Type'} (m : nat) (f : nat -> _123419) (n : nat) : (term1584 _123419 f n m) = (term1541 _123419 m f n).
Proof. exact (eq_refl (term1584 _123419 f n m)). Qed.
Lemma lem6192071 {_123419 : Type'} (m : nat) (f : nat -> _123419) (n : nat) : term1541 _123419 m f n.
Proof. exact (EQ_MP (@lem6192070 _123419 m f n) (@lem6192069 _123419 f n m)). Qed.
Lemma lem6192072 {_123419 : Type'} (m : nat) (f : nat -> _123419) (n : nat) (op : type1400 _123419) : term1585 _123419 m f n op.
Proof. exact (@lem6192071 _123419 m f n op). Qed.
Lemma lem6192073 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : (term1585 _123419 m f n op) = (term1527 _123419 op m f n).
Proof. exact (eq_refl (term1585 _123419 m f n op)). Qed.
Lemma lem6192074 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : term1527 _123419 op m f n.
Proof. exact (EQ_MP (@lem6192073 _123419 op m f n) (@lem6192072 _123419 m f n op)). Qed.
Lemma lem6192076 {_123419 : Type'} (op : type1400 _123419) (m : nat) (f : nat -> _123419) (n : nat) : term1527 _123419 op m f n.
Proof. exact (@lem6189781 _123419 op m f n (@lem6192074 _123419 op m f n)). Qed.
Lemma lem6192077 {_123419 : Type'} (m : nat) (f : nat -> _123419) (n : nat) (op : type1400 _123419) (h1 : @monoidal _123419 op) : term1536 _123419 op m f n.
Proof. exact (@lem6192076 _123419 op m f n (@lem6184862 _123419 op h1)). Qed.
Lemma lem6192078 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (n : nat) (h1 : @monoidal _123419 op) (h2 : term245 m n) : term1534 _123419 op m f n.
Proof. exact (@lem6192077 _123419 m f n op h1 (@lem6184931 m n h2)). Qed.
Lemma lem6192079 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (m : nat) (n : nat) (h1 : @monoidal _123419 op) (h2 : term1526 _123419 op m f n) (h3 : term245 m n) : term1531 _123419.
Proof. exact (@lem6192078 _123419 f op m n h1 h3 (@lem6189763 _123419 op m f n h2)). Qed.
Lemma lem6192080 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (m : nat) (n : nat) (h1 : @monoidal _123419 op) (h2 : term1526 _123419 op m f n) (h3 : term245 m n) : False.
Proof. exact (@lem6192079 _123419 op f m n h1 h2 h3 (@lem6189764 _123419)). Qed.
Lemma lem6192081 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (m : nat) (n : nat) (h1 : @monoidal _123419 op) (h2 : term1526 _123419 op m f n) (h3 : term245 m n) : (term1526 _123419 op m f n) = False.
Proof. exact (prop_ext (fun h4 : term1526 _123419 op m f n => @lem6192080 _123419 op f m n h1 h2 h3) (fun h4 : False => @lem6189763 _123419 op m f n h2)). Qed.
Lemma lem6192082 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (m : nat) (n : nat) (h1 : @monoidal _123419 op) (h2 : term1526 _123419 op m f n) (h3 : term245 m n) : False.
Proof. exact (EQ_MP (@lem6192081 _123419 op f m n h1 h2 h3) (@lem6189763 _123419 op m f n h2)). Qed.
Lemma lem6192083 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (n : nat) (h1 : @monoidal _123419 op) (h2 : term245 m n) : term1525 _123419 op m f n.
Proof. exact (fun h0 : term1526 _123419 op m f n => @lem6192082 _123419 op f m n h1 h0 h2). Qed.
Lemma lem6192084 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (n : nat) (h1 : @monoidal _123419 op) (h2 : term245 m n) : (term347 _123419 op m n f) = (term367 _123419 op m f n).
Proof. exact (EQ_MP (@lem6189762 _123419 op m f n) (@lem6192083 _123419 f op m n h1 h2)). Qed.
Lemma lem6192085 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (n : nat) (h1 : @monoidal _123419 op) (h2 : term245 m n) : (term364 _123419 op m n f) = (term367 _123419 op m f n).
Proof. exact (EQ_MP (@lem6185654 _123419 op m f n) (@lem6192084 _123419 f op m n h1 h2)). Qed.
Lemma lem6192086 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (h1 : @monoidal _123419 op) (h2 : m = (NUMERAL 0)) : (term324 _123419 f op) = (term327 _123419 f).
Proof. exact (EQ_MP (@lem6185632 _123419 op f) (@lem6189758 _123419 f op m h1 h2)). Qed.
Lemma lem6192087 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (n : nat) (h1 : @monoidal _123419 op) (h2 : term245 m n) : (term252 _123419 op m n f) = (term264 _123419 op m n f).
Proof. exact (EQ_MP (@lem6185534 _123419 f op m n h1 h2) (@lem6192085 _123419 f op m n h1 h2)). Qed.
Lemma lem6192088 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (h1 : @monoidal _123419 op) (h2 : m = (NUMERAL 0)) : (term216 _123419 op f) = (term228 _123419 f op).
Proof. exact (EQ_MP (@lem6185201 _123419 f op h1) (@lem6192086 _123419 f op m h1 h2)). Qed.
Lemma lem6192089 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (m : nat) (n : nat) (h1 : term267 m n) : (term247 _123419 op m n f) = (term185 _123419 op m n f).
Proof. exact (EQ_MP (@lem6184962 _123419 op f m n h1) (@lem6185608 _123419 op m n f)). Qed.
Lemma lem6192090 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (m : nat) (n : nat) (h1 : term267 m n) : (term267 m n) = ((term247 _123419 op m n f) = (term185 _123419 op m n f)).
Proof. exact (prop_ext (fun h2 : term267 m n => @lem6192089 _123419 op f m n h1) (fun h2 : (term247 _123419 op m n f) = (term185 _123419 op m n f) => @lem6184947 m n h1)). Qed.
Lemma lem6192091 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) (m : nat) (n : nat) (h1 : term267 m n) : (term247 _123419 op m n f) = (term185 _123419 op m n f).
Proof. exact (EQ_MP (@lem6192090 _123419 op f m n h1) (@lem6184947 m n h1)). Qed.
Lemma lem6192092 {_123419 : Type'} (op : type1400 _123419) (m : nat) (n : nat) (f : nat -> _123419) : term250 _123419 op m n f.
Proof. exact (fun h0 : term267 m n => @lem6192091 _123419 op f m n h0). Qed.
Lemma lem6192093 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (n : nat) (h1 : @monoidal _123419 op) (h2 : term245 m n) : (term252 _123419 op m n f) = (term185 _123419 op m n f).
Proof. exact (EQ_MP (@lem6184946 _123419 op f m n h2) (@lem6192087 _123419 f op m n h1 h2)). Qed.
Lemma lem6192094 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (n : nat) (h1 : @monoidal _123419 op) (h2 : term245 m n) : (term245 m n) = ((term252 _123419 op m n f) = (term185 _123419 op m n f)).
Proof. exact (prop_ext (fun h3 : term245 m n => @lem6192093 _123419 f op m n h1 h2) (fun h3 : (term252 _123419 op m n f) = (term185 _123419 op m n f) => @lem6184931 m n h2)). Qed.
Lemma lem6192095 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (n : nat) (h1 : @monoidal _123419 op) (h2 : term245 m n) : (term252 _123419 op m n f) = (term185 _123419 op m n f).
Proof. exact (EQ_MP (@lem6192094 _123419 f op m n h1 h2) (@lem6184931 m n h2)). Qed.
Lemma lem6192096 {_123419 : Type'} (m : nat) (n : nat) (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : term255 _123419 op m n f.
Proof. exact (fun h0 : term245 m n => @lem6192095 _123419 f op m n h1 h0). Qed.
Lemma lem6192097 {_123419 : Type'} (m : nat) (n : nat) (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : term258 _123419 op m n f.
Proof. exact (conj (@lem6192096 _123419 m n f op h1) (@lem6192092 _123419 op m n f)). Qed.
Lemma lem6192098 {_123419 : Type'} (m : nat) (n : nat) (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : (term182 _123419 op m n f) = (term185 _123419 op m n f).
Proof. exact (EQ_MP (@lem6184930 _123419 op m n f) (@lem6192097 _123419 m n f op h1)). Qed.
Lemma lem6192099 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (h1 : @monoidal _123419 op) (h2 : term231 m) : (@iterate _123419 nat op (@EMPTY nat) f) = (term172 _123419 m f op).
Proof. exact (EQ_MP (@lem6184912 _123419 f op m h2) (@lem6185295 _123419 f op h1)). Qed.
Lemma lem6192100 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (h1 : @monoidal _123419 op) (h2 : term231 m) : (term231 m) = ((@iterate _123419 nat op (@EMPTY nat) f) = (term172 _123419 m f op)).
Proof. exact (prop_ext (fun h3 : term231 m => @lem6192099 _123419 f op m h1 h2) (fun h3 : (@iterate _123419 nat op (@EMPTY nat) f) = (term172 _123419 m f op) => @lem6184897 m h2)). Qed.
Lemma lem6192101 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (h1 : @monoidal _123419 op) (h2 : term231 m) : (@iterate _123419 nat op (@EMPTY nat) f) = (term172 _123419 m f op).
Proof. exact (EQ_MP (@lem6192100 _123419 f op m h1 h2) (@lem6184897 m h2)). Qed.
Lemma lem6192102 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : term214 _123419 m f op.
Proof. exact (fun h0 : term231 m => @lem6192101 _123419 f op m h1 h0). Qed.
Lemma lem6192103 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (h1 : @monoidal _123419 op) (h2 : m = (NUMERAL 0)) : (term216 _123419 op f) = (term172 _123419 m f op).
Proof. exact (EQ_MP (@lem6184896 _123419 f op m h2) (@lem6192088 _123419 f op m h1 h2)). Qed.
Lemma lem6192104 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (h1 : @monoidal _123419 op) (h2 : m = (NUMERAL 0)) : (m = (NUMERAL 0)) = ((term216 _123419 op f) = (term172 _123419 m f op)).
Proof. exact (prop_ext (fun h3 : m = (NUMERAL 0) => @lem6192103 _123419 f op m h1 h2) (fun h3 : (term216 _123419 op f) = (term172 _123419 m f op) => @lem6184881 m h2)). Qed.
Lemma lem6192105 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (m : nat) (h1 : @monoidal _123419 op) (h2 : m = (NUMERAL 0)) : (term216 _123419 op f) = (term172 _123419 m f op).
Proof. exact (EQ_MP (@lem6192104 _123419 f op m h1 h2) (@lem6184881 m h2)). Qed.
Lemma lem6192106 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : term219 _123419 m f op.
Proof. exact (fun h0 : m = (NUMERAL 0) => @lem6192105 _123419 f op m h1 h0). Qed.
Lemma lem6192107 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : term222 _123419 m f op.
Proof. exact (conj (@lem6192106 _123419 m f op h1) (@lem6192102 _123419 m f op h1)). Qed.
Lemma lem6192108 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : (term169 _123419 op m f) = (term172 _123419 m f op).
Proof. exact (EQ_MP (@lem6184880 _123419 m f op) (@lem6192107 _123419 m f op h1)). Qed.
Lemma lem6192113 {_123419 : Type'} (m : nat) (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : term189 _123419 op m f.
Proof. exact (fun n : nat => @lem6192098 _123419 m n f op h1). Qed.
Lemma lem6192118 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : term193 _123419 op f.
Proof. exact (fun m : nat => @lem6192113 _123419 m f op h1). Qed.
Lemma lem6192123 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : term176 _123419 f op.
Proof. exact (fun m : nat => @lem6192108 _123419 m f op h1). Qed.
Lemma lem6192124 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : term195 _123419 op f.
Proof. exact (conj (@lem6192123 _123419 f op h1) (@lem6192118 _123419 f op h1)). Qed.
Lemma lem6192125 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : (@monoidal _123419 op) = (term195 _123419 op f).
Proof. exact (prop_ext (fun h2 : @monoidal _123419 op => @lem6192124 _123419 f op h1) (fun h2 : term195 _123419 op f => @lem6184862 _123419 op h1)). Qed.
Lemma lem6192126 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) (h1 : @monoidal _123419 op) : term195 _123419 op f.
Proof. exact (EQ_MP (@lem6192125 _123419 f op h1) (@lem6184862 _123419 op h1)). Qed.
Lemma lem6192127 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : term198 _123419 op f.
Proof. exact (fun h0 : @monoidal _123419 op => @lem6192126 _123419 f op h0). Qed.
Lemma lem6192132 {_123419 : Type'} (f : nat -> _123419) : term202 _123419 f.
Proof. exact (fun op : type1400 _123419 => @lem6192127 _123419 op f). Qed.
Lemma lem6192133 {_123419 : Type'} (f : nat -> _123419) : term201 _123419 f.
Proof. exact (EQ_MP (@lem6184861 _123419 f) (@lem6192132 _123419 f)). Qed.
